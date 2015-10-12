(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      constInfo.ML
    Author:     Moa Johansson, University of Edinburgh
                moa.johansson@ed.ac.uk                
           and  Lucas Dixon, University of Edinburgh
                               
*)
(* -------------------------------------------------------------------------*)
(*  Structure for storing information about constants related to synthesis
    of inductive conjectures. In particular, what constants are allowed to 
    occur where in a synthesis attempt. 
*)
(* -------------------------------------------------------------------------*)

structure SynthNames = struct 

  (* Names for constants: We store ConstInfo in tables and sets of these names *)
  structure Constant :> SSTR_NAME = SStrName;
  
  (* Names of positions where arguments can occur. (integers) *)
  structure ArgPos = IntName;
  
  (* Names of constraints *)             
  structure Constraint :> SSTR_INT_NAME = SStrIntName;
   
  (* Names of holes (ie. meta-variables) in a synthesis attempt *)
  structure Hole :> SSTR_INT_NAME = SStrIntName;

end;

(* Constraint Information *)
signature CONSTRAINTS =
sig

type Constr (* type of a constraint *)
type ConstInfo (* information about a constant, including its constraints *)
type T; (* = ConstInfo Constant.NTab.T ; a table of constraints *)

val init : Proof.context -> ConstraintParams.T -> T

val pretty : Proof.context -> T -> Pretty.T
val print : Proof.context -> T -> unit

val pretty_constr : Constr -> Pretty.T
val print_constr : Constr -> unit

val pretty_constinfo : Proof.context -> ConstInfo -> Pretty.T
val print_constinfo : Proof.context -> ConstInfo -> unit

end;


structure Constraints = 
struct
  
  exception missing_constant of string * Term.term
  exception constraint_exp of string;

  local open SynthNames in   

  (* Better representation. If a constraint is on the top-level, we should have holes and not
  LocalIndex. The constraintName in a LocalIndex refer to its parent. *)
  datatype argref = 
           (* int is an argument of the named constraint *)
           LocalIndex of Constraint.name * int
         (* name of meta-var in synthesised term *)
         | Hole of Hole.name 
         (* temporarily used to keep track of where variables are, 
          while converting to LocalIndex representation; ignore lambdas *)
         | Path of int list;
  
  (* Types for constriaints *)
  datatype Constr = Equal of argref list
                  | NotSimult of (argref * Constraint.name)  list
                  | IfThen of argref * (Constant.name * Constraint.name)
                  | NotAllowed of argref * Constant.name
                  | VarNotAllowed of argref * string
  
  (* Information about constants *)
  (* note: constraints can involve several arguments *)
  (* IMPROVE: make it T *)
  datatype ConstInfo = CInfo of
           { name : Constant.name,
             min_size: int, (* number of arguments + 1 *)
             typ : Term.typ, (* most general type of const *) 
             args : (int * Trm.typ) list, (* const is function, then arg (number, typ) *)
             commute_opt : Trm.T option, (* term of commutativity theorem *)
             commuted_defs : Trm.T list, (* definition with args commuted by commute thm *)
             assoc_opt : Trm.T option, (* term of assoc theorem *)
             allowedTab : (Constant.NSet.T) ArgPos.NTab.T, (* arg number => allowed constants *)
             constrTab : Constr Constraint.NTab.T, (* all constraints on arguments *)
             start_constrs : (argref list * Constraint.name) list, (* initial constraints on args of this constant *)
             weight : int (* A weight to be used by LPO for ordering equations *)                
           };
  
  type T = ConstInfo Constant.NTab.T;

  fun pretty_arg (LocalIndex (n,i)) = 
      Pretty.block [Pretty.str "LocalIndex( Constraint: ", 
                    Constraint.pretty_name n,
                    Pretty.str ", int: ", 
                    Pretty.str (Int.toString i),
                    Pretty.str ")"]
    | pretty_arg (Hole n) = 
      Pretty.block [Pretty.str "Hole ",  Hole.pretty_name n]
    | pretty_arg (Path l) = 
      Pretty.block [Pretty.str "Path ",  
                    Pretty.list "[" "]" (map (Pretty.str o Int.toString) l)];
  
  fun pretty_constr (Equal l) =
      Pretty.block [Pretty.str "Equal ", 
                    Pretty.list "[" "]" (map pretty_arg l)]
    | pretty_constr (NotSimult l) =
      Pretty.block [Pretty.str "NotSumult ", 
                    Pretty.list "[" "]"
                      (map (fn (a,n) => 
                               Pretty.block [
                               Pretty.str "(",
                               pretty_arg a,
                               Pretty.str ", ",
                               Constraint.pretty_name n,
                               Pretty.str ")"]
                               ) l)]
    | pretty_constr (IfThen (a, (constn, constrn))) = 
         Pretty.block [Pretty.str "IfThen(", 
                       pretty_arg a,
                       Pretty.str " => (",
                       Constant.pretty_name constn,
                       Pretty.str ", ",
                       Constraint.pretty_name constrn,
                       Pretty.str ")"]
    | pretty_constr (NotAllowed (a, constn)) = 
      Pretty.block [Pretty.str "NotAllowed(", 
                    pretty_arg a,
                    Pretty.str ", ",
                    Constant.pretty_name constn,
                    Pretty.str ")"]
    | pretty_constr (VarNotAllowed (a,s)) = 
      Pretty.block [Pretty.str "VarNotAllowed(", 
                    pretty_arg a,
                    Pretty.str ", ",
                    Pretty.str s,
                    Pretty.str ")"];
  
  val print_constr = Pretty.writeln o pretty_constr;
  
  fun pretty_opt f NONE = Pretty.str "NONE"
    | pretty_opt f (SOME x) = f x;
  fun pretty_bool true = Pretty.str "true"
    | pretty_bool false = Pretty.str "false";
  
  fun pretty_constinfo ctxt (CInfo rep) = 
      Pretty.chunks 
      [
       Pretty.block [Pretty.str "name:", Constant.pretty_name (#name rep)],
       Pretty.block [Pretty.str "min_size:", (Pretty.str o Int.toString) (#min_size rep)],
       Pretty.block [Pretty.str "typ:", Trm.pretty_typ ctxt (#typ rep)],
       Pretty.block [Pretty.str "args: ", 
                     Pretty.list "[" "]" 
                                 (map (fn (i,ty) => 
                                          Pretty.block 
                                            [(Pretty.str o Int.toString) i, Trm.pretty_typ ctxt ty])
                                      (#args rep))],
       Pretty.block [Pretty.str "commute_opt: ",  
                     pretty_opt (Trm.pretty ctxt) (#commute_opt rep)],
       Pretty.block [Pretty.str "commuted_defs: ",
                     Pretty.list "[" "]" (map (Trm.pretty ctxt) (#commuted_defs rep))],
       Pretty.block [Pretty.str "assoc_opt : ",
                     pretty_opt (Trm.pretty ctxt) (#assoc_opt rep)] ,
       Pretty.block [Pretty.str "allowedTab: ", 
                     ArgPos.NTab.pretty Constant.NSet.pretty (#allowedTab rep)],
       Pretty.block [Pretty.str "constrTab: ", 
                     Constraint.NTab.pretty pretty_constr (#constrTab rep)],
       Pretty.block [Pretty.str "start_constrs: ", 
                     Pretty.list "[" "]" 
                                 (map (fn (args,n) => 
                                          Pretty.block [Constraint.pretty_name n,
                                                        Pretty.str " : ",
                                                        Pretty.list "{" "}" 
                                                                    (map pretty_arg args)])
                                      (#start_constrs rep))],
       Pretty.block [Pretty.str "LPO weight: ", (Pretty.str o Int.toString) (#weight rep)]
      ];
  
  val print_constinfo = Pretty.writeln oo pretty_constinfo;
  
  (*-- Pretty printing -- *)
  fun pretty_const const_nm = Pretty.str ((Constant.dest const_nm)^", ");
  fun print_allowed_tab atab = Pretty.writeln (ArgPos.NTab.pretty (Pretty.block o (map pretty_const)) atab);

  fun pretty ctxt = Constant.NTab.pretty (pretty_constinfo ctxt);
  val print = Pretty.writeln oo pretty;

  (* Default name for constraints *)
  val default_cnm = Constraint.mk ("C",0);
  
  fun get_name (CInfo info) = #name info;
  fun get_allowedTab (CInfo info) = #allowedTab info;
  fun get_typ (CInfo info) = (#typ info);
  fun get_args (CInfo info) = (#args info);                     
  fun get_argnms (CInfo info) = map fst (#args info);
  fun get_commute_opt  (CInfo info) = (#commute_opt info);
  fun get_commuted_defs (CInfo info) = (#commuted_defs info);
  fun get_assoc_opt  (CInfo info) = (#assoc_opt info);
  fun get_minsize (CInfo info) = (#min_size info);
  fun get_constrTab (CInfo info) = #constrTab info;
  fun get_start_constrs (CInfo info) = #start_constrs info;
  fun get_weight (CInfo info) = #weight info;
  
  fun lookup_const ci_tab const = 
      Constant.NTab.lookup ci_tab const;
  
  fun all_smaller_consts ci_tab maxsize =
      filter (fn (nm,ci) => (get_minsize ci) <= maxsize) (Constant.NTab.list_of ci_tab);
  
  fun update_const_info_tab constInfo ci_tab =
      Constant.NTab.update ((get_name constInfo), constInfo) ci_tab
  
  fun get_constraint ctab cnm = 
      (case (Constraint.NTab.lookup ctab cnm) of
         SOME c => c
       | NONE => raise constraint_exp 
         ("get_constraint: Constraint " ^ (Pretty.string_of (Constraint.NTab.pretty_name cnm)) 
          ^ " is not in table."));

  (* In the constant-info it is only relevant in which order arguments occur for a constant, hence integer rep.
     For synthesis, the arguments to constants are meta-varaibles with unique names, hence other rep. *)    
  exception arg_exp of string;
  
  fun lookup_allowed_atab atab arg = 
      case arg of 
        (LocalIndex (c, i)) => Constant.NSet.list_of (ArgPos.NTab.get atab i)
      | (Hole _) => raise arg_exp 
                          "Constraints.lookup_allowed: arg in wrong format (Hole), expects LocalIndex"
      | Path _ => raise arg_exp 
                          "Constraints.lookup_allowed: arg in wrong format (Path), expects LocalIndex";
  
  fun lookup_allowed constinfo arg = 
      lookup_allowed_atab (get_allowedTab constinfo) arg;
  
  fun lookup_allowed_index const_info arg_ind =
      ArgPos.NTab.lookup (get_allowedTab const_info) arg_ind;
  
  fun insert_allowed (arg_ind, consts) atab = 
      ArgPos.NTab.ins (arg_ind, Constant.NSet.of_list consts) atab
  
  fun add_to_allowed arg_ind const atab =
      ArgPos.NTab.update (arg_ind, Constant.NSet.add const (ArgPos.NTab.get atab arg_ind)) atab;
  
  fun delete_from_allowed arg const atab = 
      case arg of 
        (LocalIndex (c,i)) => ArgPos.NTab.update (i, Constant.NSet.delete const (ArgPos.NTab.get atab i))
                                              atab
      | (Hole _) => raise arg_exp 
                          "Constraints.delete_from_allowed: arg in wrong format, expects LocalIndex (integer)"
      | Path _ => raise arg_exp 
                          "Constraints.insert_allowed: arg in wrong format (Path), expects LocalIndex (integer)";;
  
  fun del_from_allowedTab (CInfo {name = name, min_size = min_size, 
                                  typ =typ, args = args, commute_opt = commute_opt,
                                  assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                                  allowedTab = atab, constrTab =ctab, 
                                  start_constrs = s_cs, weight = w})
                          (arg, const) =
      CInfo {name = name, min_size = min_size, 
             typ =typ, args = args, commute_opt = commute_opt, assoc_opt = assoc_opt,
             commuted_defs = commuted_defs, 
             allowedTab = delete_from_allowed arg const atab,
             constrTab =ctab, start_constrs = s_cs, weight = w};
  
  fun set_allowedTab (CInfo {name = name, min_size = min_size, 
                                  typ =typ, args = args, commute_opt = commute_opt,
                                  assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                                  allowedTab = atab, constrTab =ctab, 
                                  start_constrs = s_cs, weight = w}) atab2 =
      CInfo {name = name, min_size = min_size, 
             typ =typ, args = args, commute_opt = commute_opt, assoc_opt = assoc_opt,
             commuted_defs = commuted_defs, 
             allowedTab = atab2,
             constrTab =ctab, start_constrs = s_cs, weight = w};
  
  fun all_constrs cinfo = Constraint.NTab.list_of (get_constrTab cinfo);
  
  fun set_constraints (CInfo {name = name, min_size = min_size, 
                              typ =typ, args = args, commute_opt = commute_opt,
                              assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                              start_constrs = s_cs, constrTab =ctab, 
                              allowedTab= atab, weight = w}) new_constrTab nw_start_constr =
      
      CInfo {name = name, min_size = min_size, 
             typ = typ, args = args, commute_opt = commute_opt, 
             assoc_opt = assoc_opt, commuted_defs = commuted_defs,
             allowedTab = atab, constrTab = new_constrTab,
             start_constrs = (nw_start_constr::s_cs), weight = w};
  
  fun set_commute_opt (CInfo {name = name, min_size = min_size, 
                              typ =typ, args = args, commute_opt = commute_opt,
                              assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                              start_constrs = s_cs, constrTab =ctab,
                              allowedTab= atab, weight = w}) new_commute_opt = 
        CInfo {name = name, min_size = min_size, 
               typ = typ, args = args, commute_opt = new_commute_opt,
               assoc_opt = assoc_opt, commuted_defs = commuted_defs,
               allowedTab = atab, constrTab = ctab, 
               start_constrs = s_cs, weight = w};
  
  fun update_commute_opt new_commute_opt constnm constInfos =
      let 
        val this_const_info = case (lookup_const constInfos constnm) of
                                SOME ci => ci 
                              | NONE => raise ERROR "update_commute_opt: constant doesn't exist"
        val new_const_info = 
            set_commute_opt this_const_info new_commute_opt
      in update_const_info_tab new_const_info constInfos end;
  
  fun set_commuted_defs (CInfo {name = name, min_size = min_size, 
                            typ =typ, args = args, commute_opt = commute_opt,
                            assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                            start_constrs = s_cs, constrTab =ctab, 
                            allowedTab= atab, weight = w}) new_comm_def = 
        CInfo {name = name, min_size = min_size, 
               typ = typ, args = args, commute_opt = commute_opt,
               assoc_opt = assoc_opt, commuted_defs = new_comm_def::commuted_defs,
               allowedTab = atab, constrTab = ctab, 
               start_constrs = s_cs, weight = w};
  
  fun update_commuted_defs new_com_def constInfos constnm =
      let 
        val this_const_info = case (lookup_const constInfos constnm) of
                                SOME ci => ci 
                              | NONE => raise ERROR "update_assoc_opt: constant doesn't exist"
        val new_const_info = 
            set_commuted_defs this_const_info new_com_def
      in update_const_info_tab new_const_info constInfos end;
  
  fun set_assoc_opt (CInfo {name = name, min_size = min_size, 
                            typ =typ, args = args, commute_opt = commute_opt,
                            assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                            start_constrs = s_cs, constrTab =ctab, 
                            allowedTab= atab, weight = w}) new_assoc_opt = 
        CInfo {name = name, min_size = min_size, 
               typ = typ, args = args, commute_opt = commute_opt,
               assoc_opt = new_assoc_opt, commuted_defs = commuted_defs,
               allowedTab = atab, constrTab = ctab, 
               start_constrs = s_cs, weight = w};
  
  fun update_assoc_opt new_assoc_opt constInfos constnm =
      let 
        val this_const_info = case (lookup_const constInfos constnm) of
                                SOME ci => ci 
                              | NONE => raise ERROR "update_assoc_opt: constant doesn't exist"
        val new_const_info = 
            set_assoc_opt this_const_info new_assoc_opt
      in update_const_info_tab new_const_info constInfos end;
  
  
  fun set_weight (CInfo {name = name, min_size = min_size, 
                                  typ =typ, args = args, commute_opt = commute_opt,
                                  assoc_opt = assoc_opt, commuted_defs = commuted_defs,
                                  allowedTab = atab, constrTab =ctab,
                                  start_constrs = s_cs, weight = oldw}) new_w=
      (CInfo {name = name, min_size = min_size, 
              typ =typ, args = args, commute_opt = commute_opt,
              assoc_opt = assoc_opt, commuted_defs = commuted_defs,
              allowedTab = atab, constrTab =ctab, 
              start_constrs = s_cs, weight = new_w});
     
  fun set_const_weights (const, w) constant_tab =
      let
        val cinfo = the (lookup_const constant_tab (Constant.mk const))
      in 
        update_const_info_tab (set_weight cinfo w) constant_tab
      end;
  
  (* -------------------------------------------------------- *)
  (*     Utility functions for working with "argref"s     *)
  
  (* Equality *)
  fun arg_eq (LocalIndex (c1, ind1), LocalIndex (c2, ind2)) =
      Constraint.NTab.name_eq (c1,c2) andalso ind1=ind2
    | arg_eq (Hole h1, Hole h2) =
      Hole.name_eq (h1, h2)
    | arg_eq (Path p1, Path p2) = 
      p1 = p2
    | arg_eq _ = false;
  
  fun arg_eq_holenm ((Hole h), holename) =
      Hole.name_eq (h, holename)
    | arg_eq_holenm _ = false;
   
  (* Check if Arg is a Hole *)
  fun opt_hole_of_arg (Hole hole_nm) = SOME hole_nm
    | opt_hole_of_arg (LocalIndex (c,i)) = NONE
    | opt_hole_of_arg (Path p) = NONE;
  
  
  fun update_arg_parent (arg, nw_parent_cnm) =
      case arg of
        LocalIndex (c,i) => LocalIndex (nw_parent_cnm,i)
      | Hole h => Hole h
      | Path p => Path p;
 
  (* -------------------------------------------------------- *)
  (* Messing around with types and type variables *)
  (* -------------------------------------------------------- *)
  
  (* ienv must have both vars of ty1 and ty2 *)
  fun could_typ_unify (ty1, ty2) ienv = 
      let 
        val unifs = SOME (TypUnify.unify (ty1,ty2) ienv)
            handle TUNIFY => NONE
            handle TYPE_MATCH => NONE       
      in
        is_some unifs
      end;
  
  fun varify_typ ty = 
      Trm.map_typ_tfrees 
        (fn ((nm,sort), typ) => Trm.mk_tvar(Trm.var_of_free_name nm, sort)) ty
  
  (* Note: We assume nothing has been instantiated yet, so we only need
  to rename thigs so they aren't the same as in typ.*)
  fun typ_unify_check ctyp typ avoidenv = 
      if Term.is_TVar typ then true
      else
        let 
          val (_,finaltyp) = Term.strip_type typ
          val (_,finalctyp) =  Term.strip_type ctyp
  
          val (renaming, ctyp2) = InstEnv.rename_typ_tvars 
                                           (InstEnv.init_renaming avoidenv)
                                         finalctyp
        in
          could_typ_unify (finaltyp, ctyp2) (InstEnv.avoid_of_renaming renaming)
        end;

  (* -------------------------------------------------------- *)
  (* Update constraints from rewrite rules  *)
  (* -------------------------------------------------------- *)
  fun constrs_from_paths var_path_tab constr_tab = 
      let 
        val paths = StrIntNTab.list_of var_path_tab
  
        fun path_constr ((var, paths), (var_ctab, ctab)) = 
            case paths of [] => (var_ctab, ctab)
                        | [p] => (var_ctab, ctab)
                        | (p::ps) => 
                          let 
                            val (eq_cname, nw_ctab) = 
                                Constraint.NTab.add (Constraint.mk ("C",0), 
                                               Equal ((map (fn arg => Path arg)) (p::ps))) ctab
                          in
                            (StrIntNTab.ins (var, eq_cname) var_ctab, nw_ctab)
                          end
      in
        List.foldl path_constr (StrIntNTab.empty, constr_tab) paths
      end;
  
  fun build_var_ctab constr_tab t = 
      let                       
        fun build_vtab_aux vtab path (t1$t2) = 
            let 
              val (c, args) = Term.strip_comb (t1$t2)
              (* Pair each arg with its index *)
              val indargs = Library.map_index I args
            in 
              List.foldl (fn ((ind,arg), vtab') => 
                        build_vtab_aux vtab' (path@[ind]) arg) vtab indargs 
            end
          | build_vtab_aux vtab path (Var(nm,ty)) = 
            (case (StrIntNTab.lookup vtab nm) of
               NONE => StrIntNTab.ins (nm, [path]) vtab
             | SOME locs => StrIntNTab.update (nm, path::locs) vtab) 
          | build_vtab_aux vtab _  _ = vtab
  
        val var_path_tab = build_vtab_aux StrIntNTab.empty [] t
            
      in
        constrs_from_paths var_path_tab constr_tab
      end;
  
  (* change the temporary representation of argument positions (int list)
     to one that names them after the constrint name which is at that pos. *)
  fun to_localIndex (path :int list) (constr_argnm :  Constraint.name * int) 
                    (cname : Constraint.name) (ctab :Constr Constraint.NTab.T) = 
      let 
        fun swap_rep (Path arg_path) = 
            if arg_path = path then
              LocalIndex (constr_argnm)
            else (Path arg_path) (* FIXME: probably  a bug here, raise error here instead *)
          | swap_rep (LocalIndex l) = (LocalIndex l)
          | swap_rep (Hole h) = (Hole h)
      in
        case Constraint.NTab.lookup ctab cname of
          NONE =>  raise ERROR "Evil bug exception: eqaulity constraint should have been here!"
        | SOME c => case c of 
                      Equal(args) => 
                      Constraint.NTab.update (cname, Equal(map swap_rep args)) ctab
                    | _ => ctab (* Assume we only need this for equalities now *) 
      end;
  
  (* If one constraint name that has been used to index argument ends up
  not being needed (as a top constraint) we must replace all its occurences
  with the constraint name of the actual top-constraint *)
  fun swap_cnm_in_arg nwcnm oldcnm arg =
      case arg of
        LocalIndex (constr, ind) =>
        if (Constraint.NTab.name_eq (constr, oldcnm))
        then LocalIndex(nwcnm,ind)
        else LocalIndex(constr, ind)
      | x => x
  
  fun swap_cnm nw_cnm old_cnm constr ctab =
      case (Constraint.NTab.get ctab constr) of
        NotAllowed (arg, const) => 
        Constraint.NTab.update (constr, 
                          NotAllowed (swap_cnm_in_arg nw_cnm old_cnm arg, const))
                         ctab
      | VarNotAllowed (arg, var) => 
        Constraint.NTab.update (constr, 
                          VarNotAllowed(swap_cnm_in_arg nw_cnm old_cnm arg, var))
                         ctab
      | IfThen (arg, (const, sub_cnm)) =>
        Constraint.NTab.update (constr,
                          IfThen (swap_cnm_in_arg nw_cnm old_cnm arg, (const, sub_cnm)))
                         ctab
      | NotSimult arg_constrs =>
        let 
          val nw_arg_constrs = 
              map (fn (arg, c) => (swap_cnm_in_arg nw_cnm old_cnm arg, c)) arg_constrs
        in 
          (List.foldl (fn (c, c_tab) => swap_cnm nw_cnm old_cnm c c_tab)
                 ctab (map snd arg_constrs))
            |> Constraint.NTab.update (constr, NotSimult nw_arg_constrs)
        end
      | Equal args => 
        Constraint.NTab.update (constr,
                          Equal (map (fn a => swap_cnm_in_arg nw_cnm old_cnm a) args))
                         ctab;
  (*    | Ref (arg, c) => 
        (swap_cnm nw_cnm old_cnm c ctab)
          |> Constraint.NTab.update (constr, Ref ((swap_cnm_in_arg nw_cnm old_cnm arg), c))
  *)
  
  (* Deals with terms like Var and Const, which will only generate a single constraint,
     that doesn't depend on any arguments *)
  fun constr_of_simple_term parent_cnm path var_constr_tab constr_tab (argind, t) =
      case t of 
        Var(varnm,ty) => (case (StrIntNTab.lookup var_constr_tab varnm) of
                           NONE => NONE
                         | SOME constr_nm => 
                            SOME(constr_nm,
                                to_localIndex path (parent_cnm, argind) constr_nm constr_tab) 
                          (* let 
                             val (nw_cname, nw_ctab) = 
                                 Constraint.NTab.add (default_cnm, 
                                                Ref (LocalIndex (parent_cnm, argind), constr_nm)) constr_tab
                             val nw_ctab2 = 
                                 to_localIndex path (nw_cname, argind) constr_nm nw_ctab
                           in
                             SOME(nw_cname, nw_ctab2)
                           end *)
                           )
      | Const(const_nm,ty) => 
        SOME (Constraint.NTab.add (default_cnm, NotAllowed (LocalIndex (parent_cnm, argind), 
                                                      Constant.mk const_nm)) constr_tab)
      | _ => NONE; (* could just return unchanged *)
  
  
  fun constr_of_args parent_cnm path const_tab var_constr_tab constraints t =
      case t of
        (t1$t2) =>
        let 
          val (hd,args) = Term.strip_comb (t1$t2)
        in 
          if (Term.is_Const hd) then
            let
              val (c_nm, cty) = Term.dest_Const hd 
              val const_name = Constant.mk c_nm              
              val cinfo = the (lookup_const const_tab const_name)  
                  handle Option => raise missing_constant (c_nm, t)
              (* Important : argnms must be stored in same order as given back by
                  args_of_const, ie. left-to-right *)
              (*val named_args = (get_argnms cinfo) ~~ args *)
              val (app_args, other_args) = 
                  List.partition (fn (ind,argt) => 
                                     Trm.is_app argt) (Library.map_index I args)
              val (var_cnms, nw_constr_tab) = 
                  List.foldl (fn ((ind,arg), (constr_nms, constrs)) => 
                            let
                              val constr_opt = 
                                  constr_of_simple_term parent_cnm (path@[ind]) 
                                                        var_constr_tab constrs (ind,arg)
                            in 
                              case constr_opt of
                                SOME (nw_constrnm, nw_constr_tab) => 
                                (((ind, nw_constrnm)::constr_nms), nw_constr_tab)
                              | NONE => (constr_nms, constrs)
                            end
                        ) 
                        ([],constraints) other_args
   
              val (other_cnms, nw_constr_tab2) = 
                  List.foldl (fn ((ind,arg), (constrnms, constr_tab)) => 
                            let 
                              val constrs = 
                                  mk_constr_from_app_arg parent_cnm (path@[ind]) 
                                                    const_tab var_constr_tab constr_tab (ind,arg)
                            in case constrs of
                                 SOME(nw_constrnm, nw_constr_tab) =>
                                 (((ind, nw_constrnm)::constrnms), nw_constr_tab)
                               | NONE => (constrnms, constr_tab)
                            end)
                        ([], nw_constr_tab) app_args 
            in
              SOME((var_cnms @ other_cnms, nw_constr_tab2), const_name)
            end
            handle missing_constant (nm, t) => 
                     let val _ = writeln ("Unsupported Constant: "^nm) in NONE end
          else NONE
        end
      | _ => NONE
  
  and mk_constr_from_app_arg parent_cnm path const_tab var_constrs constrs (argind, argtrm) =
      let 
        val (this_constr_nm, constr_tab0) = Constraint.NTab.new_name default_cnm constrs
        val arg_constrs = constr_of_args this_constr_nm path const_tab var_constrs constr_tab0 argtrm
      in
        case arg_constrs of
          SOME ((arg_constr_names, constr_tab), const) => 
            (case arg_constr_names of
               [] => SOME(this_constr_nm,
                          Constraint.NTab.update (this_constr_nm, 
                                            NotAllowed(LocalIndex (parent_cnm, argind), const)) 
                                           constr_tab)
                    
             (* Don't matter which of the args have a constraint *) 
             | [(arg,c)] => 
               SOME (this_constr_nm,
                     Constraint.NTab.update (this_constr_nm, 
                                       IfThen (LocalIndex (parent_cnm, argind), (const, c))) 
                                      constr_tab)
                      
             | (c::cs) =>
               let 
                 val (ifcnm, constr_tab2) = 
                     Constraint.NTab.add (Constraint.mk ("C",2), 
                                    IfThen(LocalIndex (parent_cnm, argind), (const, this_constr_nm)))
                                   constr_tab
      (* Name the subconstraints of a NotSimult after the parent of the NotSimult, so subconstraints don't get confused*)
                 val constr_tab3 = 
                     (List.foldl (fn (c,ctab) => swap_cnm ifcnm this_constr_nm c ctab) 
                           constr_tab2 (map snd arg_constr_names))
                       |> Constraint.NTab.update (this_constr_nm, 
                                            NotSimult (map (fn (arg,cstrnm) => 
                                                               (LocalIndex (ifcnm,arg), cstrnm)) 
                                                           arg_constr_names))
               in 
                 SOME (ifcnm, constr_tab3)
               end
            ) 
        | NONE => NONE
      end;
  
exception mk_constr_exp of Term.term;
  (* Assume t is an application, or else rules isn;t insteresting *)
  fun mk_constr_from_trm const_tab t =
      case t of 
        (t1$t2) =>
        let
          val (hdtrm, args) = Term.strip_comb t
          val (c_nm, cty) = Term.dest_Const hdtrm               
          val cinfo = the (lookup_const const_tab (Constant.mk c_nm))  
              handle Option => raise missing_constant (c_nm, t)
          val constr_tab1 = get_constrTab cinfo
          val (var_constr_tab, constr_tab2) = build_var_ctab constr_tab1 t
          val (top_constr_nm, constr_tab3) = Constraint.NTab.new_name default_cnm constr_tab2
          val arg_constrs = constr_of_args top_constr_nm [] const_tab var_constr_tab constr_tab3  t
        in
          (case arg_constrs of
             SOME ((constr_nms, constr_tab), top_const) =>
             (case constr_nms of
                [] => NONE
              (* Note: use of 'top_constr_nm' in the arguments should be replaced by 'c'*)
              | [(arg,c)] => SOME([(LocalIndex (c,arg))], c, swap_cnm c top_constr_nm c constr_tab, top_const)  
              | (c::cs) => 
                let 
                  val cs' = map (fn (arg,cstrnm) => (LocalIndex (top_constr_nm, arg), cstrnm)) constr_nms
                  val constr_tab2 = 
                      Constraint.NTab.update (top_constr_nm, NotSimult cs') constr_tab 
                in SOME(map fst cs', top_constr_nm, constr_tab2, top_const) end
             )
           | NONE => NONE )
          handle missing_constant (nm,t) => 
                 let val _ = writeln ("Unsupported Constant: "^nm) in NONE end
        end
      | _ => NONE (* No constraints to generate *)
        handle TERM _ => 
               (* let val _ = Pretty.writeln(Pretty.str "mk_constr_exp, bad term:") 
                 val _ = Trm.print @{context} t; in *)
               raise (mk_constr_exp t);
  
  (* ----------------------------------------------------------------------------*)
  (* ----------------------------------------------------------------------------*)
  (* Remove 'del_constnm' from the domain of all arguments of 'const_nm' *)
  fun delete_from_all del_constnm (const_nm, cinfo) constant_tab = 
      let val _ = writeln
                    ("removing: " ^del_constnm^" from "^(Constant.dest const_nm))  
          (*val cinfo = the (lookup_const constant_tab const_nm) *)
      in List.foldl (fn ((arg_ind,_), nw_const_tab) => 
                  update_const_info_tab 
                         (del_from_allowedTab cinfo (LocalIndex
                                                    ((Constraint.mk ("dummy",0)), arg_ind), 
                                                    Constant.mk del_constnm))
                         nw_const_tab)
              constant_tab (get_args cinfo)     
      end;
 
(* Add the constraints generated from the term t *) 
  fun add_constraints_from_term t constant_tab = 
      case (mk_constr_from_trm constant_tab t) of
        SOME (constr_arg_opt, top_constr_nm, constr_tab, const_nm) =>
        let 
          val cinfo = the (lookup_const constant_tab const_nm)
        in
          case (get_constraint constr_tab top_constr_nm) of 
            (NotAllowed (arg, const_nm2)) =>
             (* val _ = writeln ("removing: "^(Constant.dest const_nm2)^
                                  " from "^(Constant.dest const_nm)) *)
              
            SOME (update_const_info_tab 
                    (del_from_allowedTab cinfo (arg, const_nm2)) 
                    constant_tab)
          (* More than one simple constraint *)
          | _ =>
            let (* val _ = writeln ("compound constraint: for " ^ (Constant.dest const_nm)) *)
              val cinfo2 = set_constraints cinfo constr_tab (constr_arg_opt, top_constr_nm)
            in 
              SOME (update_const_info_tab cinfo2 constant_tab)
            end
        end
      | NONE => NONE

  (* Adds constraints associated with the term lhs, which is supposed to be the LHS
     of some rule. *)
  fun add_constraints_from_lhs lhs constant_tab = 
      case lhs of 
        (t1$t2) => 
        (case (add_constraints_from_term lhs constant_tab) of
           SOME nw_constant_tab => nw_constant_tab
         | NONE  => 
          (* There are no constraints from LHS, so the rule is of the form f(t1
             ... t2) = ..., with t1...t2 all distinct variables.  This means that f
             should be disallowed from all domains, or this rule would apply. *)
           let 
             val lhs_constnm = (Term.strip_comb lhs)
                                 |> fst
                                 |> Term.dest_Const  
                                 |> fst
           in (* Remove this constant from *all* domains. *)
             Constant.NTab.fold (delete_from_all lhs_constnm) constant_tab constant_tab
           end)
          | _ => constant_tab; (* The LHS is a varaible or something silly *)
  


  (* ----------------------------------------------------------------------------*)
  (* Check if this is a commutativety theorem for some function (of 2 arguments) 
     returns SOME f where f is string name of constant that is a 2 arguemnt commutative function,
     according to the pair of terms "lhs = rhs". 
  *)
  fun tryget_commutative_symbol_of_term_eq (lhs,rhs) = 
      let val (lhs_f, lhs_args) = Term.strip_comb lhs
          val (rhs_f, rhs_args)  = Term.strip_comb rhs
      in if (Term.is_Const lhs_f andalso lhs_f = rhs_f) 
         then
           (case (lhs_args, rhs_args) of 
              ([a1, a2], [b1, b2]) => 
                 if (a1 = b2 andalso a2 = b1)
                 then SOME (Term.dest_Const lhs_f) else NONE
               | _ => NONE)
         else NONE
      end;

  (* Update constraints from a pair of terms corresponding to an equation/rewrite rule.
     if the rewrite is commutativty; treats it specially. *)
  fun add_constraints_from_eq (lhs,rhs) const_tab =
      (case tryget_commutative_symbol_of_term_eq (lhs,rhs) of
         SOME (const_nm,ty) => 
          ((* writeln (const_nm ^ " is commutative."); *)
          (* update_commute_opt (SOME (Const (const_nm,ty))) (Constant.mk const_nm) const_tab) *)
          update_commute_opt (SOME (HOLogic.mk_eq(lhs,rhs))) (Constant.mk const_nm) const_tab) 
       | NONE => add_constraints_from_lhs lhs const_tab);

  (*Generate a constraint from an arbitry term, i.e. *not a rewrite rule*. This generates
    constraints given by the whole term 't', i.e. stops IsaCoSy generating instances of t. *)
  fun add_constraints_from_whole_term t const_tab = 
      case (add_constraints_from_term t const_tab) of 
        SOME nw_ctab => nw_ctab | NONE => const_tab;

  (* Make a single constant-information for given constant 
     The argument `all_consts' is the constants that are allowed
     to occur as arguments to other functions, given types match.
     If we're initilising a theory from scratch, these are
     all functions and datatypes in it. Otherwise, it is a list 
     of pairs (const_name * const_type) which may include the
     constants already available as well as new ones. *)
  fun mk_constinfo ctxt all_consts (cname,typ) =          
      let 
        (* Need to swap 'a for ?'a in type, or else IsaCoSy won't find anything to put in domain.
          Or maybe we only want this for =, not the others or the search space gets too big?*)
        (*val typ = varify_typ ground_typ *)
        val ienv = InstEnv.init ctxt
        val (argtyps,_) = Term.strip_type typ  
        val ind_args = Library.map_index (fn (ind, ty) => (ind, ty)) argtyps                

        (* Check allowed_args so types match and build table. *)
        val initATab = 
            List.foldl (fn ((arg_ind,atyp), tab) =>
              let
                val possargs = filter (fn (cn,cty) => typ_unify_check cty atyp ienv) 
                                        all_consts
                val const_args = (map fst possargs) |> map Constant.mk      
              in insert_allowed (arg_ind, const_args) tab end)
              ArgPos.NTab.empty ind_args;  
        val cn = Constant.mk cname
      in
        (cn,
         CInfo{name = cn, 
              typ = typ,
              args = ind_args, (* As index * type pairs *)
              min_size = 1 + (List.length argtyps),
              commute_opt = NONE,
              commuted_defs = [],
              assoc_opt = NONE,
              allowedTab = initATab,
              constrTab =  Constraint.NTab.empty,
              start_constrs = [],
               weight = ~1})
      end;

  fun mk_constinfo' ctxt all_consts (index, (cname,typ)) =
      let 
        val (cnm, cinfo) = mk_constinfo ctxt all_consts (cname, typ)
      in
        (cnm, set_weight cinfo (index+1))
      end;



   
  (* Generate a ConstInfo suitable for function synthesis.
     Arguments:
        (string * typ) list := all constant symbols (for constraints)
        (string * typ) list := constant symbols (for synthesis with)
        (Term.term * Term.term) list := directed equations to make constraints from
     Returns: 
        ConstInfo Constant.NTab.T := constant information table

  *)
(*  fun init' ctxt (all_consts,synth_consts,eqs,_) =
      Constant.NTab.empty
          |> fold Constant.NTab.ins (map (mk_constinfo ctxt synth_consts) all_consts)
          |> fold add_constraints_from_eq eqs;
*)

  (* Also sets the LPO precedence in const-info *)
  fun init' ctxt (all_consts,synth_consts, eqs, arb_trms, sort_constsf) =
      Constant.NTab.empty
          |> fold Constant.NTab.ins (map_index (mk_constinfo' ctxt synth_consts)
                                         (sort_constsf all_consts))
          |> fold add_constraints_from_eq eqs
          |> fold add_constraints_from_whole_term arb_trms;

  fun init ctxt cparams =
      init' ctxt (Symtab.dest (ConstraintParams.get_cconsts cparams), 
                  Symtab.dest (ConstraintParams.get_consts cparams), 
                  ConstraintParams.get_termrws cparams,
                  ConstraintParams.get_constr_trms cparams,
                  ConstraintParams.get_sort_lpo_precf cparams);

  (* FIXME: These don't work and can't work... 
    we cannot write a function that adds new datatypes/constants to an existing const_info_tab, because constants will not know about the new possible instantiations. We cannot add the new constant to all existing ones because a constraint applied from a theorem may remove it... ? Need to check constraint language... maybe a proof to do here. *)
  (* --- Adding a new function to constant info table --- *)
  (* add newf to the domains of already existing functions of
     relevant type.*)
     (* 
  fun add_to_domain ctxt (newf, nwty) (constnm, cinfo) constInfoTab =
      let
        val allowed_tab = 
            fold (fn (ind,argty) => fn atab =>
                     if typ_unify_check nwty argty (InstEnv.init (ProofContext.theory_of ctxt)) 
                     then add_to_allowed ind (Constant.mk newf) atab     
                     else atab) 
                 (get_args cinfo) (get_allowedTab cinfo)
      in update_const_info_tab (set_allowedTab cinfo allowed_tab) constInfoTab end;
  *)

  (* Add the new function we are about to define to the constInfo tab,
     to make it available to synthesis. Note are assuming this is done
     for the purpose of generating right-hand sides of a function 
     which actually doesn't exist yet in the theory, so this constInfo should
     not be used for trying to syntheise theorems. *)  
  (* 
  fun add_new_fun_to_ctab ctxt (fname,ty) lh_sides constInfoTab =
        let 
          val other_consts = (Constant.NTab.list_of constInfoTab)
                               |> map (fn (nm,cinfo) => (Constant.dest nm, 
                                                        get_typ cinfo))
          val constInfoTab2 = Constant.NTab.fold (add_to_domain ctxt (fname,ty))
                                                constInfoTab constInfoTab
  
          val const_info =  Constant.NTab.ins 
                              (mk_constinfo ctxt ((fname,ty)::other_consts)
                                                       (fname,ty)) constInfoTab2
        in
          (* Generate constraints from the lh_side terms, don't need rhs reducible
             by lhs, this won't be valid function def.*)
          fold add_constraints_from_lhs lh_sides const_info
        end;
*)


end (* local *)
end;

(* *)
local structure CheckedConstraints : CONSTRAINTS = Constraints; 
in val _ = (); end;

(*install_pp (make_pp ["Constraints.Constraint", "T"] 
                    (Pretty.pprint o Constraints.Constraint.NTab.pretty_name));

install_pp (make_pp ["Constraints.Hole", "name"] 
                    (Pretty.pprint o Constraints.Hole.pretty_name));

install_pp (make_pp ["Constraints.ConstName", "name"] 
                    (Pretty.pprint o Constraints.Constant.pretty_name));*)
