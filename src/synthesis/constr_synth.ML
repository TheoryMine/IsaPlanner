(* *)
open SynthNames;
signature CONSTR_SYNTHESIS
= sig

type SynthTerm; (* type of terms being synthesised *)

(* create an initial synthesis term *)
val init_sterm : 
       Proof.context
    -> Constraints.T (* = Constraints.ConstInfo Constant.NTab.T; *)
    -> {size : int, max_vars : int} (* max term size max number of vars *)
    -> Term.typ (* type of top-meta-var *) 
    -> SynthTerm

(* as above, but has type var as top typ *)
val init_any_sterm : 
       Proof.context 
    -> Constraints.T (* = Constraints.ConstInfo Constant.NTab.T; *)
    -> int (* max term size *)
    -> int (* max number of vars *)
    -> SynthTerm

(* *)

(* pretty printing *)
val pretty_sterm : SynthTerm -> Pretty.T
val print_sterm : SynthTerm -> unit



(* TODO: generalise interface to work with term instead of constant name; i.e. always work with well-formed things, e.g. (Trueprop ?X) *)
val synthesise_terms' :
     Constant.name (* top level function symbol; maybe better to give top level type? *)
     -> (Hole.name -> term -> bool)  (* how to restrict fresh free vars *)
     -> {size : int, max_vars : int} (* terms size for synthesis, max_vars *)
     -> Proof.context 
     -> Constraints.T (* constants and constraints to use *)
     -> SynthTerm Seq.seq (* generated terms *)
(*
val synthesise_terms : 
       Constant.name (* constant to appear at the top *)
    -> (Hole.name -> Term.term -> bool) (* how to restrict fresh free vars *)
    -> {min_size : int, max_size : int, max_vars :int} (* min, max size of synthesised terms, 
                                                        max number of varaibles in synth term.*)
    -> Proof.context (* initial context *)
    -> Constraints.T (* initial theory constraints *)
    -> (Constraints.T * theory) (* updated constraints and theory *)
       * (term list (* conjectures *)
          * (term * (string * Thm.thm) * Thm.thm list) list (* theorem term, proof rep * Thm, lemmas *) 
         );
        
   (*    * ((term * (RState.T list)) list (* conjectures *)
           * (term * ( RState.T list)) list (* thms *) 
           );
    *)
*)
(* *)
val restr_synthesis : (Hole.name -> Term.term -> bool) (* how to restrict fresh free vars *)
      -> Constraints.T (* initial theory constraints *)
     -> Constant.name list (* constants to use *)
     -> (Constant.name * int) list (* constants not used so far ? *)
         * SynthTerm (* synth term so far *)
     -> SynthTerm Seq.seq; (* sterms *)


end;



(* *)
(* constraint based synthesis *)
structure ConstrSynthesis =
struct
local open Constraints; open SynthNames; in (* Constant and constraint Information *)



(* datatype of terms being synthesised. This is really a partial/schematic term, with 
   constraints attached to it. *)
datatype SynthTerm = Sterm of
         {term : Term.term,
          ienv : InstEnv.T,
          allowedTab : Constant.NSet.T Hole.NTab.T, (* meta-vars in term => allowed consts *)
          constrTab : Constr Constraint.NTab.T, (* constraints on term being synthesised *)
          holeConstrs : (Constraint.NSet.T) Hole.NTab.T, (* hole => constraints on that hole *)
          (* constr => parent or constr, links to other or members of the or-constraint *)
          constrDepTab : (Constraint.NSet.T) Constraint.NTab.T, 
          (* agenda of which hole to instantiate next *)
          hole_sizes : int Hole.NTab.T, (* size constraint for each hole *)
          holes_agenda : Hole.name list, (* holes agenda (ordered) for next instantiation *)
          max_vars : int (* Max number of different vars allowed *)
         };

(* fun get_theory (Sterm rep) = InstEnv.get_theory (#ienv rep); *)
fun get_ctxt (Sterm rep) = InstEnv.get_ctxt (#ienv rep);

fun pretty_sterm (st as Sterm rep) = 
    let val ctxt = get_ctxt st in
    Pretty.chunks 
    [
     Pretty.block [Pretty.str "term: ", Trm.pretty ctxt (#term rep)],
     Pretty.block [Pretty.str "ienv: ", InstEnv.pretty (#ienv rep)],
     Pretty.block [Pretty.str "allowed: ", 
                   Hole.NTab.pretty Constant.NSet.pretty (#allowedTab rep)],
     Pretty.block [Pretty.str "constr: ", 
                   Constraint.NTab.pretty Constraints.pretty_constr (#constrTab rep)],
     Pretty.block [Pretty.str "holeConstr: ", 
                   Hole.NTab.pretty Constraint.NSet.pretty (#holeConstrs rep)],
     Pretty.block [Pretty.str "constrDep: ", 
                   Constraint.NTab.pretty Constraint.NSet.pretty (#constrDepTab rep)],
     Pretty.block [Pretty.str "holes_size: ", 
                   Hole.NTab.pretty (Pretty.str o Int.toString) (#hole_sizes rep)],
    Pretty.block [Pretty.str "holes_agenda: ", 
                   Pretty.list "[" "]" (map Hole.pretty_name (#holes_agenda rep))],
     Pretty.block [Pretty.str "max_vars: ", Pretty.str (Int.toString (#max_vars rep))]
    ]
    end;

val print_sterm = Pretty.writeln o pretty_sterm;
fun print_constr_tab ctab = 
    Pretty.writeln (Constraint.NTab.pretty Constraints.pretty_constr ctab);
fun print_constr_dep_tab cdtab = 
    Pretty.writeln (Constraint.NTab.pretty Constraint.NSet.pretty cdtab);

(* create an initial sterm of just a variable of a given type. *)
fun init_sterm ctxt constInfoTab {size, max_vars} ty = 
    let 
      val n = Var.default_name;
      val hname = Hole.mk n;
      val t = Var (n, ty);
      val ienv = InstEnv.of_trm ctxt t;
    in
      Sterm {term = t,
             ienv = ienv,
             allowedTab = Hole.NTab.ins (hname, Constant.NTab.get_nameset constInfoTab) 
                            Hole.NTab.empty,
             constrTab = Constraint.NTab.empty,
             holeConstrs = Hole.NTab.empty,
             constrDepTab = Constraint.NTab.empty,
             hole_sizes = Hole.NTab.ins (hname,size) Hole.NTab.empty,
             holes_agenda = [hname],
             max_vars = max_vars}
    end;

(* create initial sterm of just variable with type variable as its type. *)
fun init_any_sterm ctxt constInfoTab max_size max_vars =
    init_sterm ctxt constInfoTab {size = max_size, max_vars = max_vars} 
      (TVar(TVar.default_name, []));


exception synthesise_exp of string;

(* Time spent in synthesis *)
val synth_time = Unsynchronized.ref Time.zeroTime;
val upd_constr_time = Unsynchronized.ref Time.zeroTime;
val subsumpt_time = Unsynchronized.ref Time.zeroTime;
val conj_tab = Unsynchronized.ref StrNTab.empty;
fun reset_conj_tab () = conj_tab := StrNTab.empty;

fun get_term (Sterm st) = #term st;
fun get_ienv (Sterm st) = #ienv st;
fun get_allowedTab (Sterm st) = #allowedTab st;
fun get_holes_agenda (Sterm st) = #holes_agenda st;
fun get_hole_sizes (Sterm st) = #hole_sizes st;
fun get_max_vars (Sterm st) = #max_vars st;
fun get_constrTab (Sterm st) = #constrTab st;
fun get_holeConstrs (Sterm st) = #holeConstrs st;
fun get_constrDepTab (Sterm st) = #constrDepTab st; 

(* IMPROVE: make a proper way of identifying active holes? *)
(* Moa: Therse is no such thing as in-active hole. *)
val is_hole = Hole.NTab.contains_name o get_hole_sizes;


fun update_holes_agenda f (Sterm rep) = 
    Sterm {term = #term rep,
           ienv = #ienv rep,
           allowedTab = #allowedTab rep,
           constrTab = #constrTab rep,
           holeConstrs = #holeConstrs rep,
           constrDepTab = #constrDepTab rep,
           hole_sizes = #hole_sizes rep,
           holes_agenda = f (#holes_agenda rep),
           max_vars = #max_vars rep
          };
val set_holes_agenda = update_holes_agenda o K;

fun update_max_vars f (Sterm rep) = 
    Sterm {term = #term rep,
           ienv = #ienv rep,
           allowedTab = #allowedTab rep,
           constrTab = #constrTab rep,
           holeConstrs = #holeConstrs rep,
           constrDepTab = #constrDepTab rep,
           hole_sizes = #hole_sizes rep,
           holes_agenda = #holes_agenda rep,
           max_vars = f (#max_vars rep)
          };
val set_max_vars = update_max_vars o K;

fun drop_from_holes_agenda n = 
    update_holes_agenda (filter (fn n2 => not (Hole.name_eq (n,n2))));

val get_hole_size = Hole.NTab.get o get_hole_sizes;
fun get_hole_type s h = InstEnv.get_typ_of_var (get_ienv s) (Hole.dest h);

fun reset_holes_agenda_from_term s = 
    set_holes_agenda (map (Hole.mk o fst) (Trm.vars_of (get_term s))) s;


fun constrs_of_hole strm hole = 
    case (Hole.NTab.lookup (get_holeConstrs strm) hole) of
      NONE => []
    | SOME cs => Constraint.NSet.list_of cs;

fun allowed_consts_of_hole strm hole =
    case (Hole.NTab.lookup (get_allowedTab strm) hole) of
      NONE => []
    | SOME cs => Constant.NSet.list_of cs;

fun del_from_allowedTab const hole atab =
    case (Hole.NTab.lookup atab hole) of 
      SOME consts => 
      Hole.NTab.update (hole, (Constant.NSet.delete const consts)) 
                     atab
    | NONE => atab; (* Should probably raise exeption here *)

fun del_from_holeConstrs constr hole hctab =
    case (Hole.NTab.lookup hctab hole) of 
      SOME constrs => 
      Hole.NTab.update (hole, (Constraint.NSet.delete constr constrs))
                     hctab
    | NONE => hctab; (* Should probably raise exeption here *)

fun add_to_holeConstrs constr hole hctab =
    case (Hole.NTab.lookup hctab hole) of 
      SOME constrs => Hole.NTab.update (hole, Constraint.NSet.add constr constrs) hctab
    | NONE => Hole.NTab.ins (hole, Constraint.NSet.add constr Constraint.NSet.empty) hctab;
  
fun add_constr_deps constr constr_to_add dep_tab =
    case (Constraint.NTab.lookup dep_tab constr)
     of NONE => Constraint.NTab.ins (constr, 
                                   (Constraint.NSet.add constr_to_add 
                                                            (Constraint.NSet.empty)))
                                  dep_tab
      | SOME set => Constraint.NTab.update (constr, (Constraint.NSet.add constr_to_add set))
                                         dep_tab;

(* Delete 'constr_to_del' from the dependenceies for 'constr' *)
fun del_from_constr_deps constr constr_to_del dep_tab  =
    case (Constraint.NTab.lookup dep_tab constr)
     of NONE => dep_tab
      | SOME set => Constraint.NTab.update (constr, (Constraint.NSet.delete constr_to_del set)) dep_tab;

(* Delete constr from constr_dep_tab, if it is present *)
fun del_constr_dep_if_present constr constr_dep_tab =
    case (Constraint.NTab.lookup constr_dep_tab constr) 
         of NONE => constr_dep_tab
          | SOME set => Constraint.NTab.delete constr constr_dep_tab;

(* The subconstraints that need to know about their super-constraint. *)
fun subconstrs_of_constr constr_tab constr =
    case constr of
      NotAllowed _ => []
    | VarNotAllowed _ => []
    | IfThen (arg, (const, constr)) => [constr]
    | NotSimult arg_constrs => map snd arg_constrs
    | Equal _ => [];

(* Create an initial dependency table, from some constraints imported
   from a constant. *)
fun init_constr_dep_tab constr_renamings const_constr_tab =
    Constraint.NTab.fold 
    (fn (old_nm, nw_nm) => fn constr_deps => 
        let 
          val constr = Constraint.NTab.get const_constr_tab old_nm
          val sub_constrs = (subconstrs_of_constr const_constr_tab constr)
                              |> map (fn sc_nm => 
                                         case Constraint.NTab.lookup constr_renamings sc_nm of
                                           NONE => sc_nm | SOME nw_sc => nw_sc)
        in
          List.foldl (fn (c, dtab) => add_constr_deps c nw_nm dtab) 
                constr_deps sub_constrs
        end) 
    constr_renamings Constraint.NTab.empty

fun update_constr_dep_tab constr_nms
                          (constr_tab : Constr Constraint.NTab.T) 
                          (dep_tab1 : Constraint.NSet.T Constraint.NTab.T) = 
    List.foldl (fn (nm, dep_tab) =>
              let 
                val constr = the (Constraint.NTab.lookup constr_tab nm)
                val sub_constrs = subconstrs_of_constr constr_tab constr
              in 
                List.foldl (fn (c, dtab) => add_constr_deps c nm dtab)
                      dep_tab sub_constrs
              end)
          dep_tab1 constr_nms;

(* --------------------------------------------------------*)
(* Deleting constraints in a safe way, from all tables     *)
(* --------------------------------------------------------*)

(* Only use this function to delete constraints, to make sure it is
   done right and deleted from all tables. *)

(* Build a set of all dependent constraint that should be deleted.
   We use a set as certain dependencies might try to include the
   same constraint several times *)
exception delete_exp of  Constraint.name * 
                         (Constraints.Constr Constraint.NTab.T *
                          Constraint.NSet.T Constraint.NTab.T)
fun mk_delete_set constr_tab constr_dep_tab constr_nm (delete_set1 : Constraint.NSet.T) =
  case (Constraint.NTab.lookup constr_tab constr_nm) of
    NONE => delete_set1 (* Try skipping this one if it doesn't exist *)
   (* raise delete_exp (constr_nm, (constr_tab, constr_dep_tab)) *)
  | SOME constr => 
    let 
      val del_set = Constraint.NSet.add constr_nm delete_set1
      val super_constrs = (case (Constraint.NTab.lookup constr_dep_tab constr_nm) of
                            NONE => Constraint.NSet.empty
                          | SOME dep_set => dep_set)
                            |> (fn constrs => 
                                  Constraint.NSet.remove_set 
                                    (Constraint.NSet.intersect del_set constrs) constrs)
                            
      val sub_constrs = (subconstrs_of_constr constr_tab constr)
                          |> Constraint.NSet.of_list
                          |> (fn constrs => 
                                Constraint.NSet.remove_set 
                                  (Constraint.NSet.intersect del_set constrs) constrs)
    in
      Constraint.NSet.fold (mk_delete_set constr_tab constr_dep_tab) 
                     (Constraint.NSet.union_merge super_constrs sub_constrs) del_set
    end;

(* Returns holes the constraint should be attached to. *)
fun holes_of_constr constr_nm constr_tab =
    let
      fun hole_of_arg (Hole hole_nm) = [hole_nm]
        | hole_of_arg (LocalIndex i) = []
        | hole_of_arg (Path p) = []

      val holes =
          case (Constraint.NTab.lookup constr_tab constr_nm) of
            NONE => raise ERROR "holes_of_constr: constraint doesn't exist."
          | SOME constr =>
            case constr of
              NotAllowed (arg, const) => hole_of_arg arg
            | VarNotAllowed (arg, var) => hole_of_arg arg
            | IfThen (arg, (const, constr)) => hole_of_arg arg
            | NotSimult arg_constrs => maps (hole_of_arg o fst) arg_constrs
            | Equal args => maps hole_of_arg args
    in
      holes
    end;

(* Delete constr_nm and any dependencies, they are no longer relevant. *)
fun drop_constraint constr_nm (constr_tab, hole_constrs, constr_dep_tab) =
    let 
      val delete_set = mk_delete_set constr_tab constr_dep_tab constr_nm 
                                    Constraint.NSet.empty
    in
      Constraint.NSet.fold (fn cnm => fn (ctab, hctab, cdtab) => 
                     (Constraint.NTab.delete cnm ctab,
                      List.foldl (fn (hole, hc_tab) => del_from_holeConstrs cnm hole hc_tab)
                           hctab (holes_of_constr cnm ctab),
                    (* Some deleted constraints have no dependencies, check *)
                     case (Constraint.NTab.lookup cdtab cnm) of 
                       NONE => cdtab
                     | SOME entry => Constraint.NTab.delete cnm cdtab) 
                     ) 
                     delete_set (constr_tab, hole_constrs, constr_dep_tab)
    end;

(* --------------------------------------------------------*)

(* Useful library function which was removed from Isabelle... *)
fun foldl_map f =
  let
    fun fold_aux (x, []) = (x, [])
      | fold_aux (x, y :: ys) =
          let
            val (x', y') = f (x, y);
            val (x'', ys') = fold_aux (x', ys);
          in (x'', y' :: ys') end;
  in fold_aux end;

fun apply_tvar_renaming renaming ((tvar_nm, sort), typ) =
    case (InstEnv.get_tvar_renaming renaming tvar_nm) of
      SOME(_,renamed_typ) => renamed_typ
     | NONE => typ                 

exception term_bit_exp of Constraints.ConstInfo * Constant.NSet.T Hole.NTab.T * InstEnv.T
(* Use a constant to create a little schema to plug into a hole.
   The arguments are Vars, with fresh names. Also set the entry in
   the allowedTab, to specify domain of poss instantiations for the
   new holes. *)
fun mk_new_term_bit const_info synth_allowed_tab ienv =
    let
      val (const_nm, const_typ) = (Constant.dest (Constraints.get_name const_info),
                                   Constraints.get_typ const_info)
      val arg_typs = Constraints.get_args const_info                            
      val (typ_renaming, nw_const_typ) = 
          InstEnv.rename_typ_tvars (InstEnv.init_renaming ienv) const_typ
      (* Should really just lookup the argument types from the argument list *)
      (*val (arg_typs, res_typ) = Term.strip_type nw_const_typ *)

      val ((nw_ienv, nw_allowed_tab), fresh_arg_nms) =
          foldl_map (fn ((ienv1, atab1), (arg_ind, ty)) =>
                    let 
                      val vartyp = Trm.map_typ_tvars (apply_tvar_renaming typ_renaming) ty
                      val (var, ienv2) = InstEnv.new_uninst_var (("h", 1), vartyp) ienv1
                      val allowed = the (Constraints.lookup_allowed_index const_info arg_ind)
                      val allowed_tab = Hole.NTab.ins (Hole.mk var, allowed) atab1
                    in ((ienv2, allowed_tab), (var, vartyp)) end)
            ((InstEnv.avoid_of_renaming typ_renaming, synth_allowed_tab), 
             (*(map_index I arg_typs)) *) arg_typs)
      val trm = 
          Term.list_comb (Const(const_nm, nw_const_typ), (map Trm.mk_var fresh_arg_nms))
    in
     (trm, fresh_arg_nms, nw_ienv, nw_allowed_tab)
    end;
    (* handle *** _ => raise term_bit_exp (const_info, synth_allowed_tab, ienv); *)


(* Updates the constraint-names in for an argument of the format used by Equals *)
fun rename_arg rename_map (LocalIndex (parent_constr_nm, argnm)) =      
      let 
        val nw_parent_nm = case (Constraint.NTab.lookup rename_map parent_constr_nm) of
                             NONE => parent_constr_nm | SOME nw_parent => nw_parent
      in
        LocalIndex (nw_parent_nm, argnm)
      end
  | rename_arg _ (Path i) = raise ERROR "rename_arg: Expecting LocalIndex, not Path"
  | rename_arg _ (Hole h) = raise ERROR "rename_arg: Expecting LocalIndex, not Hole";

exception rename_exp of  Constraint.name Constraint.NTab.T *
                         Constraints.Constr Constraint.NTab.T *
                         Constraints.Constr Constraint.NTab.T *
                         Constraint.name 
fun rename_constr_tab rename_map const_constr_tab constr_tab old_constr_nm =
    let 
      val constr = Constraints.get_constraint const_constr_tab old_constr_nm
      val nw_cnm = case (Constraint.NTab.lookup rename_map old_constr_nm) of
                           NONE => old_constr_nm | SOME nw_nm => nw_nm
    in
      case constr of 
        NotSimult nms => 
        let 
          val nw_sub_cnms = 
              map (fn (argnm, cnm) => 
                      case (Constraint.NTab.lookup rename_map cnm) of
                        NONE => (rename_arg rename_map argnm, cnm) 
                      | SOME nw_nm => (rename_arg rename_map argnm, nw_nm)) nms 

          val nw_constr_tab = Constraint.NTab.ins (nw_cnm, NotSimult nw_sub_cnms) constr_tab
        in
          List.foldl (fn (nm, ctab) => rename_constr_tab rename_map const_constr_tab ctab nm) 
                nw_constr_tab (map snd nms)            
        end
      | IfThen (arg_nm, (const_nm, constr_nm)) =>  
        let 
          val nw_sub_constr_nm = case (Constraint.NTab.lookup rename_map constr_nm) of
                                   NONE => constr_nm | SOME nw_nm => nw_nm

          val nw_constr_tab = 
              Constraint.NTab.ins (nw_cnm, 
                             IfThen(rename_arg rename_map arg_nm, 
                                    (const_nm, nw_sub_constr_nm))) constr_tab
        in  
          rename_constr_tab rename_map const_constr_tab nw_constr_tab constr_nm
        end
      | NotAllowed (arg_nm, const_nm) => 
        Constraint.NTab.ins (nw_cnm, NotAllowed (rename_arg rename_map arg_nm, const_nm)) 
                      constr_tab
      | VarNotAllowed (arg_nm, var_nm) =>
        Constraint.NTab.ins (nw_cnm, VarNotAllowed (rename_arg rename_map arg_nm, var_nm)) 
                      constr_tab
      (* Need to check if these have been added under new name already first! *)
      | Equal args => 
        (case (Constraint.NTab.lookup constr_tab nw_cnm) of
           NONE => Constraint.NTab.ins (nw_cnm, Equal (map (rename_arg rename_map) args)) 
                                 constr_tab
         | SOME c => constr_tab)  (* Added already *)
    end
    handle ERROR e => raise rename_exp (rename_map, const_constr_tab, constr_tab, old_constr_nm)
    ;

(* Change an argument-name to refer to a particular hole,
   not an index in the list of arguments. *)
fun argname_to_holerep hole_nms (LocalIndex (c, arg_ind)) =
    Hole(List.nth (hole_nms, arg_ind))
  | argname_to_holerep hole_nms (Hole holenm) = 
    (Hole holenm)
  | argname_to_holerep hole_nms (Path p) =
    raise ERROR "argname_to_holerep: Found Path, expect LocalIndex or Hole.";

(* Change the representation of the argName inside and arg-type
   to refer to a specific hole. *)
fun revise_arg hole_nms constr arg = 
      case arg of 
         LocalIndex (constr_nm, argind) => 
         if (Constraint.name_eq (constr_nm, constr)) then
           argname_to_holerep hole_nms (LocalIndex (constr_nm, argind))
         else LocalIndex (constr_nm, argind)
       | Path path => raise ERROR "revise_arg: Expects LocalIndex or Hole, got Path"
       | Hole h => Hole h


fun argnames_to_holerep hole_nms (parent_constr_opt, constr_nm) constr_tab =
    let 
      val constr = the (Constraint.NTab.lookup constr_tab constr_nm)
    in
      case constr of
        NotSimult arg_constr_nms => 
        let 
          val arg_constr =  
              case parent_constr_opt of
                NONE => constr_nm (* This is a top-level constraint *)
              | SOME parent => parent (* This is a sub-constraint *)
            val nw_constr_tab = 
                Constraint.NTab.update (constr_nm, 
                                  NotSimult 
                                    (map (fn (arg, sub_constr) => 
                                             (revise_arg hole_nms arg_constr arg, 
                                              sub_constr))
                                         arg_constr_nms))
                                 constr_tab
          in
            (* Also need to update the argument rep on subconstrs,
             as they refer to arguments at the same place in term tree. *) 
            List.foldl (fn (cnm, ctab) => 
                      argnames_to_holerep hole_nms (SOME arg_constr, cnm) ctab) 
                  nw_constr_tab (map snd arg_constr_nms)
          end
          
      | IfThen (arg_nm, (const_nm, sub_constr_nm)) =>
        Constraint.NTab.update (constr_nm, IfThen (argname_to_holerep hole_nms arg_nm, 
                                             (const_nm, sub_constr_nm))) constr_tab
      | NotAllowed (arg_nm, const_nm) =>
        Constraint.NTab.update (constr_nm, 
                          NotAllowed (argname_to_holerep hole_nms arg_nm, const_nm)) 
                         constr_tab
      | VarNotAllowed (arg_nm, var_nm) =>
        Constraint.NTab.update (constr_nm, 
                          VarNotAllowed (argname_to_holerep hole_nms arg_nm, var_nm))
                         constr_tab
      | Equal (args) => 
        let
          val arg_constr =  case parent_constr_opt of
                              NONE => constr_nm (* This is a top-level constraint *)
                            | SOME parent => parent (* This is a sub-constraint *)
        in
          Constraint.NTab.update (constr_nm, 
                            Equal (map (revise_arg hole_nms arg_constr) args)) 
                           constr_tab
        end 
    end;

fun rename_constraints const_constr_tab constr_tab =
    let 
      val init_renaming = Constraint.renaming_of_avoidset (Constraint.NTab.get_nameset constr_tab)
    in 
      List.foldl (fn (cnm, rnms) => snd (Constraint.rename1 cnm rnms)) 
            init_renaming (Constraint.NTab.keys const_constr_tab)
    end;

(* Gives back the relevant hole of this argument-name, or ERROR if its argument
   isn't in SynthRep *)
fun hole_of_argnm (Hole hole_nm) = hole_nm
  | hole_of_argnm (LocalIndex i) = raise ERROR "hole_of_argnm: Expected Hole, found LocalIndex."
  | hole_of_argnm (Path p) =  raise ERROR "hole_of_argnm: Expected Hole, found Path.";



(* Attach a constraints to a newly created holes and update tables accordingly *)
fun add_constr_to_new_holes (constr_nm :Constraint.NTab.name) (nw_hole_nms : Hole.name list)
                           (hole_constr_tab, constr_tab, allowed_tab : Constant.NSet.T Hole.NTab.T,
                           constr_dep_tab) =
    let 
      val constr = Constraint.NTab.get constr_tab constr_nm
    in
      case constr of
        (* Delete the constant from the domain of the hole. Safe to delete constraint
         as these are only top-level constraints and NotAllowed has no subconstraints.*)
        NotAllowed (arg_nm, const) => 
        (hole_constr_tab, Constraint.NTab.delete constr_nm constr_tab, 
         del_from_allowedTab const (hole_of_argnm arg_nm) allowed_tab,
         Constraint.NTab.delete constr_nm constr_dep_tab)
      | VarNotAllowed (arg_nm, var_nm) => 
        (add_to_holeConstrs constr_nm (hole_of_argnm arg_nm) hole_constr_tab,
         constr_tab, allowed_tab, constr_dep_tab)
      | IfThen (arg_nm, (const, sub_constr)) =>
          (add_to_holeConstrs constr_nm (hole_of_argnm arg_nm) hole_constr_tab,
           constr_tab, allowed_tab, constr_dep_tab)
      | NotSimult arg_constr_nms => 
        let 
          (* SOME of these holes may be old holes, only attach to new holes*)
          val hole_nms = 
              (map_filter Constraints.opt_hole_of_arg (map fst arg_constr_nms))
                |> filter (fn hole => Library.member Hole.name_eq nw_hole_nms hole)
        in
          (List.foldl (fn (hole, hc_tab) =>
                    add_to_holeConstrs constr_nm hole hc_tab) hole_constr_tab hole_nms,
          constr_tab, allowed_tab, constr_dep_tab)
        end
      | Equal args => 
        let 
          (* SOME of these holes may be old holes, only attach to new holes*)
          val hole_nms = 
              (map_filter opt_hole_of_arg args)
                |> filter (fn hole => Library.member Hole.name_eq nw_hole_nms hole)
        in
          (List.foldl (fn (hole, hc_tab) =>
                     add_to_holeConstrs constr_nm hole hc_tab) hole_constr_tab hole_nms,
           constr_tab, allowed_tab, constr_dep_tab)
        end
    end;

(* Attach constraint from a newly inserted constant to relevant holes, updateing tables.
NOTE: 'constr_nm' must be a top-level constraint. *)
fun attach_constr const_constr_tab rename_map hole_nms
                  (constr_nm, 
                   (hole_constr_tab, constr_tab, 
                    allowed_tab,
                    constr_dep_tab)) = 
    let 
      (* val rename_map = Constraint.nmap_of_renaming constr_rnms *)
      val nw_constr_nm = case (Constraint.NTab.lookup rename_map constr_nm) of
                           NONE => constr_nm | SOME nw_nm => nw_nm         
      val nw_constr_tab = 
          (rename_constr_tab rename_map const_constr_tab constr_tab constr_nm)
            |> argnames_to_holerep hole_nms (NONE, nw_constr_nm)
    in
      add_constr_to_new_holes nw_constr_nm hole_nms 
                             (hole_constr_tab, nw_constr_tab, 
                              allowed_tab, constr_dep_tab)
    end;


(* ---------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------*)
(* Updateing EXISTING constraints to new holes.                                     *)

(* ---------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------*)


fun lookup_dependencies constr_dep_tab constr =
    case (Constraint.NTab.lookup constr_dep_tab constr) of
      NONE => Constraint.NSet.empty
    | SOME set => set;

fun local_ind_of_arg arg1 =
    case arg1 of
      Path path => raise ERROR "local_ind__of_arg: found Path, expect LocalIndex"
    | LocalIndex (cnm, argnm) => (cnm, argnm)
    | Hole h => raise ERROR "local_ind_of_arg: found Hole, expect LocalIndex.";

exception not_sim_exp of Constraint.NTab.name * 
                         (Constraint.NSet.T Constraint.NTab.T *
                          Constraints.Constr Constraint.NTab.T)

(* Return name, and args of NotSimult, if this constr depend on one *)
fun get_not_sim_parents constr_nm constr_dep_tab constr_tab= 
          case (Constraint.NTab.lookup constr_dep_tab constr_nm)
           of NONE => []
            | SOME dep_set => 
              case (Constraint.NSet.list_of dep_set) of 
                [] => []
              | (c::cs) => 
                map_filter (fn cnm =>
                        (case (Constraint.NTab.get constr_tab cnm) of
                           NotSimult arg_constrs => SOME (cnm, arg_constrs)
                         | _ => NONE (*raise ERROR "get_not_sim_opt: Expected a NotSimult."*)))
                    (c::cs);

fun get_parents constr_nm constr_dep_tab constr_tab =
    case (Constraint.NTab.lookup constr_dep_tab constr_nm)
     of NONE => []
      | SOME dep_set => Constraint.NSet.list_of dep_set

(* If a NotSimult is a subconstraint of another NotSimult that has become
   obsolete, replace it with its child in its parent constraint. *) 
fun replace_sub_constr arg0 not_sim_nm  new_sub_constr (hole_constr_tab, constr_tab, constr_dep_tab) =
    case (get_not_sim_parents not_sim_nm constr_dep_tab constr_tab) of
      [] => (hole_constr_tab, constr_tab, constr_dep_tab)
    | (c::cs) => 
      List.foldl (fn  ((parent_not_sim, arg_constrs),  
                 (hole_constr_tab, constr_tab, constr_dep_tab))  =>
                let
                  val (arg_constrs2, hc_tab) = 
                      fold_map (fn (arg, c) => 
                                fn hc_tab => 
                                   if (Constraint.NTab.name_eq (c, not_sim_nm) 
                                       andalso arg_eq(arg0, arg)) 
                                   then ((arg, new_sub_constr), hc_tab)
                                      (*  This must be wrong, surely still attached to 
                                          the top-most NotSimult ? *)
                                    (*   add_to_holeConstrs new_sub_constr 
                                                            (hole_of_argnm arg) hc_tab *)
                                   else ((arg, c), hc_tab))
                               arg_constrs hole_constr_tab      
                in
                  (hc_tab, 
                   Constraint.NTab.update (parent_not_sim, NotSimult arg_constrs2) constr_tab,
                   add_constr_deps new_sub_constr parent_not_sim constr_dep_tab)
                end)
            (hole_constr_tab, constr_tab, constr_dep_tab) (c::cs);


exception NotSim_exp of 
  (Constraints.argref 
  * (Constraint.NTab.name * (Constraints.argref * Constraint.NTab.name) list)
  * Hole.name list 
  * (Constraint.NSet.T Hole.NTab.T 
     * Constraints.Constr Constraint.NTab.T 
     * Constant.NSet.T Hole.NTab.T 
     * Constraint.NSet.T Constraint.NTab.T))

(* If we checked a subconstraint that will dissapear without being
replaced by a child (as in the IfThen case below), and its part of a
NotSimult, need to update the NotSimult,
 to ensure its not obsolete. Note: This function may also be used when updating
an equality, in which case we may want to reuse the name of the equality
eg. for a NotAllowed constraint. This means we can keep dependencies with
other constraints. We do howeve need to make sure that the NotSimult is
not left in the constr_dep table. *)

fun check_not_sim_aux (arg, this_constr) (notsim_nm, arg_constrs) nw_holes 
                      (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) =
    let 
      (* Delete arg from the list of the NotSimult *)
      val arg_constrs2 = 
          Library.remove (fn (arg, (arg2, c)) => arg_eq (arg, arg2))
                         arg arg_constrs
    in
      case arg_constrs2 of
        [] => raise NotSim_exp (arg, (notsim_nm, arg_constrs), nw_holes,
                    (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab))               
      | [(arg, constr2)] => 
        (* Only one other constraint, no need to keep the NotSimult, 
         just keep the subconstraint on its own *)
        let 
          val (hc_tab, c_tab, a_tab, cd_tab) =
              add_constr_to_new_holes constr2 nw_holes
                                      (hole_constr_tab, constr_tab, 
                                       allowed_tab, constr_dep_tab)  
          (* Need to update all deps so they point to something new.
              Essentially just swap notsim_nm for constr2 in the parents parent.*)
          val (hc_tab2, c_tab2, cd_tab2) = 
              replace_sub_constr arg notsim_nm constr2 (hc_tab, c_tab, cd_tab)
        in
          (List.foldl (fn (hole, hctab) => del_from_holeConstrs notsim_nm hole hctab)
                 hc_tab2 (holes_of_constr notsim_nm c_tab2),
           Constraint.NTab.delete notsim_nm c_tab2, 
           a_tab, 
           (del_from_constr_deps constr2 notsim_nm cd_tab2)
             |> del_from_constr_deps this_constr notsim_nm
             |> del_constr_dep_if_present notsim_nm) (* Only delete if its there! *)
        end
      | (h::t) =>
        let
         (* Only delete if no other args of the NotSimult 
            talk about 'this_constr' *)
          val nw_cdtab = 
              if (member (fn (c, (arg, c2)) => Constraint.name_eq (c, c2))
                               arg_constrs2 this_constr)
              then constr_dep_tab
              else del_from_constr_deps this_constr notsim_nm constr_dep_tab
        in
        (hole_constr_tab,
         Constraint.NTab.update (notsim_nm, NotSimult arg_constrs2) constr_tab,
         allowed_tab, nw_cdtab)
        end
    end;

fun check_not_sims hole constr nw_holes (hole_constr_tab, constr_tab, 
                                        allowed_tab, constr_dep_tab) =
    let 
      val constrs_of_hole = 
          Hole.NTab.get hole_constr_tab hole
    in
      case (get_not_sim_parents constr constr_dep_tab constr_tab) of
        [] => NONE
      | (c::cs) => 
        SOME (List.foldl (fn ((notsim_nm, arg_constrs), (hctab, ctab, atab, cdtab)) =>  
                        check_not_sim_aux (Hole hole, constr) (notsim_nm, arg_constrs) 
                                          nw_holes 
                                          (hctab, ctab, atab, cdtab))
                    (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) 
                    (filter (fn (cnm, args) => Constraint.NSet.contains constrs_of_hole cnm) 
                            (c::cs))
             )
    end;

exception IfThen_exp of (Constraint.NTab.name * Constraint.NTab.name * 
                         (Constraint.NSet.T Hole.NTab.T *
                          Constraints.Constr Constraint.NTab.T *
                          Constraint.NSet.T Constraint.NTab.T))
(*  When and IfThen is a subconstraint of a NotSimult, 
    its child constraint replaces it in 
    the NotSimult. However, if the child is also a 
    NotSimult, they should be merged. *)

(* Little library function that only allows things to 
   be inserted in list if not a member already *)
fun insert1 f x [] = [x]
  | insert1 f x (h::t) = if (Library.member f (h::t) x)
                         then (h::t)
                         else (x::h::t)

fun put_children_in_not_sim_parent (not_sim_nm, arg_constrs) ifthen_constr ifthen_child_constr
                   (hole_constr_tab, constr_tab, constr_dep_tab) =
    let 
      val holes = holes_of_constr ifthen_child_constr constr_tab
      val arg_constrs2 = 
          Library.remove 
            (fn (rm_cnstr, (arg2, c2))  => Constraint.NTab.name_eq (rm_cnstr,c2))
            ifthen_constr arg_constrs
    in
      if (null holes) 
      then raise ERROR "put_children_in_not_sim_parent: No Holes."
      else
        case arg_constrs2 of
          [] => raise IfThen_exp (ifthen_constr, ifthen_child_constr, 
                            (hole_constr_tab, constr_tab, constr_dep_tab))
         (*raise ERROR "put_children_in_not_sim_parent: Empty NotSim!"*)
        | (ac::acs) => 
          let 
            val ((nw_hctab, nw_ctab, nw_cdtab), nw_args) =
                case (Constraint.NTab.get constr_tab ifthen_child_constr) of
                  NotSimult nw_arg_constrs => 
                  ((List.foldl (fn (h, hctab) => 
                              del_from_holeConstrs ifthen_child_constr h hctab) 
                          hole_constr_tab holes,
                    Constraint.NTab.delete ifthen_child_constr constr_tab,
                    (List.foldl (fn (c, cdt) => 
                               (del_from_constr_deps c ifthen_child_constr cdt)
                                 |> add_constr_deps c not_sim_nm)
                           constr_dep_tab (map snd nw_arg_constrs))
                      |> del_constr_dep_if_present ifthen_child_constr),
                   nw_arg_constrs)
                  
                | _ => ((hole_constr_tab, constr_tab, 
                         (add_constr_deps ifthen_child_constr not_sim_nm constr_dep_tab)
                           |> del_from_constr_deps ifthen_child_constr ifthen_constr), 
                        map (fn h => (Hole h, ifthen_child_constr)) holes)
            (* Make sure none of the nw_args weren't alrady in args_constrs2*)           
            val final_args = 
                List.foldl (fn ((a0, c0), all_args) => 
                          (insert1 
                             (fn ((arg, c), (arg1, c1)) => Constraints.arg_eq (arg, arg1))
                           (a0,c0) all_args))
                arg_constrs2 nw_args
          in
            (nw_hctab,
             Constraint.NTab.update (not_sim_nm, NotSimult (final_args)) nw_ctab,
             nw_cdtab)                        
          end
    end;


(* IfThen are allowed to occur as a sub-constraint of ONE NotSimult,
   nothing else. This function is called when an IfThen has been 
   triggered and is to be replaced by its sub-constraint.*)
fun propagate_if_then_constr (if_constr_nm : Constraint.NTab.name) 
                             (sub_constr : Constraint.NTab.name)
                             (hole_constr_tab, constr_tab : Constr Constraint.NTab.T, constr_dep_tab) =
    case (get_not_sim_parents if_constr_nm constr_dep_tab constr_tab) of
      [] => raise ERROR "propagate_if_then_constr: Should only be called if part of NotSimult."
    | [(cnm, arg_constrs)] => (* Should only have one parent constraint *)      
      let 
        val holes = holes_of_constr sub_constr constr_tab
      in
        (* It doesn't make sense to have an ifthen if there aren't any new holes *)
        if (null holes) 
        then
          raise IfThen_exp (if_constr_nm, sub_constr, 
                            (hole_constr_tab, constr_tab, constr_dep_tab))
        else   
          let 
            val (hctab, ctab, cdtab) = 
                put_children_in_not_sim_parent (cnm, arg_constrs) if_constr_nm sub_constr 
                               (hole_constr_tab, constr_tab, constr_dep_tab)       
          in 
            (List.foldl (fn (hole_nm, hctab) => 
                       add_to_holeConstrs cnm hole_nm hctab) 
                   hctab holes,
             ctab, 
             cdtab)
          end 
      end
    | _ => raise ERROR "propagate_if_then_constr: Constraint has too many parents.";
  
exception not_allowed_exp of Constraint.name * 
                             (Constraint.NSet.T Hole.NTab.T *
                              Constraints.Constr Constraint.NTab.T *
                              Constant.NSet.T Hole.NTab.T *
                              Constraint.NSet.T Constraint.NTab.T)

fun propagate_not_allowed hole (constr_nm : Constraint.NTab.name) nw_holes
                          (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) =
    case (check_not_sims hole constr_nm nw_holes
                     (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab)) of
      NONE => raise not_allowed_exp (constr_nm, (hole_constr_tab, constr_tab, 
                                                 allowed_tab, constr_dep_tab))
    | SOME tables => tables;


exception eq_exp of Constraint.name * Hole.name * Constant.name * 
                    (Constraint.NTab.name list Hole.NTab.T *
                     Constraints.Constr Constraint.NTab.T *
                     Constant.name list Hole.NTab.T *
                     Constraint.NSet.T Constraint.NTab.T)


fun get_other_eq_args holenm args =
    Library.remove (fn (h,a) => Constraints.arg_eq_holenm (a, h)) holenm args;

fun change_hole_constrs new_nm old_nm hole_constr_tab constr_tab = 
      List.foldl (fn (hole, hctab) => 
                (del_from_holeConstrs old_nm hole hctab)
                  |> add_to_holeConstrs new_nm hole)
      hole_constr_tab (holes_of_constr old_nm constr_tab);

(* Swap 'old_nm' for 'nw_nm' in the parent constraint of the argument.*)
exception rnm_in_parents_exp of 
    (Constraints.argref * Constraint.name) *
    Constraint.name *
    Constraints.Constr Constraint.NTab.T *
    Constraint.NSet.T Constraint.NTab.T 

fun rename_in_parents (arg, nw_nm) old_cnm (c_tab1, cd_tab1) =
    case (Constraint.NTab.lookup cd_tab1 old_cnm) of
      NONE => (c_tab1, cd_tab1)
    | SOME constr_set => 
      let
        fun rename parent_c (ctab, cdtab) =
            (case (Constraint.NTab.get ctab parent_c) of
               NotSimult arg_constrs => 
               (let  
                  val (update, others) =
                     List.partition (fn (arg1,c1) => 
                                        arg_eq(arg1, arg)
                                        andalso
                                        Constraint.NTab.name_eq(old_cnm, c1)) 
                                    arg_constrs
                in
                  case update of
                    [] => (ctab, cdtab)
                  | (ac::acs) => 
                    (Constraint.NTab.update(parent_c, NotSimult 
                                                 (others @ (map (fn (a,c) => 
                                                                     (a,nw_nm)) update)))
                                     ctab,
                     add_constr_deps nw_nm parent_c cdtab)
                end)
             | IfThen (arg1, (constant, constr)) => 
               if (Constraint.NTab.name_eq (old_cnm, constr))
               then 
                 (Constraint.NTab.update (parent_c, IfThen(arg1,(constant, nw_nm))) ctab,
                  add_constr_deps nw_nm parent_c cdtab)
               else (ctab, cdtab) (* This parent does not talk about relevant arg *)
                 (*raise rnm_in_parents_exp ((arg, nw_nm), old_cnm, c_tab1, cd_tab1) *)
             | _ => raise ERROR "rename in parent: Parent should be NotSimult or IfThen." 
            )
      in
        fold rename (Constraint.NSet.list_of constr_set)  (c_tab1, cd_tab1)
      end;


(* If the parent of the new holes were in a NotSimult, put the child holes & constrs 
   there to replace it. Otherwise just attach the new constraints to the new holes.*)
fun replace_in_parent (old_hole : Hole.name) nw_hole_constrs old_constr (hc_tab, c_tab, cd_tab) =
      case (Constraint.NTab.lookup cd_tab old_constr) of
        NONE => (List.foldl (fn ((nw_hole, nw_c), hctab) =>
                           add_to_holeConstrs nw_c nw_hole hctab) hc_tab nw_hole_constrs, 
                 c_tab, cd_tab)
      | SOME dep_set => 
          List.foldl (fn (cnm, (hctab,ctab,cdtab)) => 
                  case (Constraint.NTab.get ctab cnm) of
                    NotSimult arg_constrs =>
                    if (List.exists (fn (arg1,c) => Constraint.NTab.name_eq (old_constr, c) 
                                                    andalso arg_eq(Hole old_hole, arg1)) arg_constrs)
                    then
                      let 
                      val arg_constrs2 =
                          (Library.remove (fn (rm_cnstr, (arg2, c2)) => 
                                              Constraint.NTab.name_eq (rm_cnstr,c2) 
                                              andalso arg_eq(arg2, Hole old_hole))
                                          old_constr arg_constrs) 
                          @ (map (fn (h,c) => (Hole h, c)) nw_hole_constrs)
                      in
                        (List.foldl (fn ((nw_hole, nw_c), hctab1) => 
                                  add_to_holeConstrs cnm nw_hole hctab1) hctab nw_hole_constrs, 
                         Constraint.NTab.update(cnm, NotSimult arg_constrs2) ctab,
                         List.foldl (fn ((nw_hole, nw_c), cdtab1) => 
                                  add_constr_deps nw_c cnm cdtab1) cdtab nw_hole_constrs) 
                      end
                    else (hctab,ctab, cdtab)
                  | IfThen(arg, constr) => (hctab, ctab, cdtab) (* A parent of the old_constr, 
                                                                   but for some other arg, that isn't a hole *)
                  | _ =>  raise ERROR "replace in parent: Can only have NotSim or IfThen parents"
                ) (hc_tab, c_tab, cd_tab) (Constraint.NSet.list_of dep_set);


(* ---------------------------------------------------------------------------------*)
(* Propagate Equality constraints *)    
(* ---------------------------------------------------------------------------------*)

fun nth_from_each' n [] nlist = rev nlist  
  | nth_from_each' n (xs::xss) nlist = nth_from_each' n xss ((nth xs n)::nlist)

(* fixme: inefficent *)
fun nth_from_each max [] = []
  | nth_from_each max (xs::xss) = 
    map (fn n => nth_from_each' n (xs::xss) []) (0 upto max)


(* Update an equality*)

fun propagate_equality eq_constr_nm (hole : Hole.NTab.name) const_nm new_holes
                       (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) = 
    case (Constraint.NTab.get constr_tab eq_constr_nm) of
      Equal args =>  
      let         
        val other_args = get_other_eq_args hole args         
      in
        case new_holes of
          [] =>
          (case other_args of
             [] => raise ERROR "propagate equality: not eqaual to anything."
           | [other_arg] => 
             (case (Constraints.opt_hole_of_arg other_arg) of
                NONE => 
                let 
                  val nw_ctab = 
                      Constraint.NTab.update (eq_constr_nm, NotAllowed (other_arg, const_nm)) 
                                       constr_tab  
                in
                  case (check_not_sims hole eq_constr_nm new_holes
                                       (hole_constr_tab, nw_ctab, 
                                        allowed_tab, constr_dep_tab)) of
                    NONE => (hole_constr_tab, nw_ctab, 
                             allowed_tab, constr_dep_tab)
                  | SOME new_tables => new_tables
                end
              | SOME h => (* Exactly one other hole in equality,restrict its domain.*)
                let 
                  (* Delete the equality and all its dependencies, cleaning up *)
                  val (ctab, hctab, cdtab) = 
                      drop_constraint eq_constr_nm 
                                      (constr_tab, hole_constr_tab, constr_dep_tab)
                in
                  (* Remove const_nm from the domain of the other hole. *)
                  (hctab, ctab, del_from_allowedTab const_nm h allowed_tab, cdtab)
                end)
           | (other_arg::more_args) =>
             let 
               val (ctab2, notalloweds) = 
                   foldl_map (fn (ctab, other_arg) =>
                                 let 
                                   val (nm,ctab2) =  
                                       Constraint.NTab.add (default_cnm, 
                                                      NotAllowed(other_arg, const_nm)) 
                                                     ctab
                                 in (ctab2, (other_arg, nm)) end)
                             (constr_tab, other_args)

               val (nw_hctab, nw_ctab, nw_atab, nw_cdtab) =   
                   case (check_not_sims hole eq_constr_nm new_holes
                                        (hole_constr_tab, ctab2, 
                                         allowed_tab, constr_dep_tab)) of
                    NONE => (hole_constr_tab, ctab2, 
                             allowed_tab, constr_dep_tab)
                  | SOME new_tables => new_tables
             in
               (nw_hctab,
                Constraint.NTab.update (eq_constr_nm, NotSimult notalloweds) nw_ctab,
                nw_atab,
                List.foldl (fn ((arg,n_allowed), cdtab) => 
                          add_constr_deps n_allowed eq_constr_nm cdtab)
                      nw_cdtab notalloweds)
             end
          ) 
       (* One new hole *)
        | [nw_hole] => 
          let 
            (* Make names for IfThens we're going to insert *)
            val (ctab2, ifnms_args) = 
                foldl_map (fn (ctab,arg) => 
                              let val (nm, ctb) =
                                      Constraint.NTab.new_name default_cnm ctab
                              in (ctb, (arg,nm)) end) 
                          (constr_tab, other_args)
            (* Create a new equality on the new hole *)
            val (nw_eq, ctab3) =
                Constraint.NTab.add (default_cnm,
                               Equal((Hole nw_hole) :: 
                                     map (fn (oldarg,ifparent) => LocalIndex(ifparent, 0)) 
                                         ifnms_args)) ctab2
            (* Make IfThens on all other args and change the names in any parent to point
             to relevan IfThen instead of old equality. *) 
            val (ctab4,cdtab0) = List.foldl (fn ((arg, ifnm), (ctab, cdtab)) => 
                                  let 
                                    val nw_ctab =
                                        Constraint.NTab.update (ifnm, 
                                                          IfThen(arg, (const_nm, nw_eq))) 
                                                         ctab
                                  in
                   
                                    rename_in_parents (arg, ifnm) eq_constr_nm 
                                                      (nw_ctab, constr_dep_tab)
                                  end)
                        (ctab3,constr_dep_tab) ifnms_args
            (* If this equality was part of a NotSimult, replace it with new constraints
               on new holes. *)
            val (hctab1, ctab5, cdtab1) = 
                replace_in_parent hole [(nw_hole,nw_eq)] eq_constr_nm 
                                  (hole_constr_tab, ctab4, cdtab0)
            (* Update constraint dependencies *)
            val cdtab2 = update_constr_dep_tab (map snd ifnms_args) ctab5 cdtab1
        
          in
            (hctab1,
             Constraint.NTab.delete eq_constr_nm ctab5,
             allowed_tab,
             del_constr_dep_if_present eq_constr_nm cdtab2)
          end
        (* Several new holes *)
        | (nw_h::hs) =>
          let
            (* Make names for IfThens and NotSimults we're going to insert *)
            val (ctab2, cnms_args) = 
                foldl_map (fn (ctab,arg) => 
                              let val (ifnm, ctb1) =
                                      Constraint.NTab.new_name default_cnm ctab
                              in (ctb1, (arg,ifnm)) end) 
                          (constr_tab, other_args)

            (* Create a new equality for each new hole *)
            val (ctab3, nw_eqs) =
                foldl_map (fn (ctab, (ind, nw_hole)) => 
                          let val (eqnm, nw_ctab) = 
                                  Constraint.NTab.add 
                                    (default_cnm, Equal((Hole nw_hole) :: 
                                                        map (fn (oldarg,ifparent) => 
                                                                LocalIndex(ifparent, ind)) 
                                                            cnms_args)) ctab
                          in (nw_ctab, eqnm) end)
                      (ctab2, (map_index I new_holes))
    
            (* Make a NotSimult for each other argument *)
            val (ctab4, notsim_nms) = 
                foldl_map (fn (ctab,(oldarg, ifnm)) =>
                              let 
                                val arg_cnstrs =
                                    map (fn n => 
                                            (LocalIndex(ifnm, n), nth nw_eqs n))
                                        (0 upto (List.length nw_eqs -1))
                                val (notsim_nm, nw_ctab) =
                                    Constraint.NTab.add(default_cnm, NotSimult arg_cnstrs) ctab 
                              in (nw_ctab, notsim_nm) end) 
                          (ctab3, cnms_args)
            (* Make the IfThens for the other arguments *)
            val ctab5 = 
                List.foldl (fn (((oldarg,ifnm), not_simnm), ctab) =>
                          Constraint.NTab.update(ifnm, 
                                           IfThen(oldarg, (const_nm, not_simnm))) 
                                          ctab)
                ctab4 (cnms_args ~~ notsim_nms)

            (* Update constraint dependencies *)
            val cdtab2 = update_constr_dep_tab ((map snd cnms_args) @ notsim_nms)
                                               ctab5 constr_dep_tab
          in
            case (get_not_sim_parents eq_constr_nm cdtab2 ctab5) of
              [] => 
              (* Make a Not Simult on the new holes*)
              let 
                val (holes_notsim, ctab6) = 
                    Constraint.NTab.add(default_cnm, 
                                  NotSimult (map (fn (nw_h, nw_eq) => 
                                                     (Hole nw_h, nw_eq)) 
                                                 (new_holes ~~ nw_eqs))) 
                                 ctab5
              in
                add_constr_to_new_holes holes_notsim new_holes 
                                       (hole_constr_tab, ctab6, allowed_tab, cdtab2)
              end
            | (c::cs) =>   
              let val (hctab1, ctab6, cdtab3) = 
                      replace_in_parent hole (new_holes ~~ nw_eqs) eq_constr_nm 
                                        (hole_constr_tab, ctab5, cdtab2)
                val (ctab7, cdtab4) = 
                     (List.foldl (fn ((oldarg,ifnm), (ctab,cdtab)) =>
                           rename_in_parents (oldarg,ifnm) eq_constr_nm
                                             (ctab, cdtab))
                        (ctab6,cdtab3) cnms_args)
              in   
                (hctab1,
                 Constraint.NTab.delete eq_constr_nm ctab7,
                 allowed_tab,
                 del_constr_dep_if_present eq_constr_nm cdtab4) 
              end
          end
      end
    | _ => raise ERROR "propagate_equality: Expects Equal, found something else.";
          

(* Update an Equality constraint when one of its holes has been instantiated
   to a variable *)
fun propagate_equality_var eq_constr_nm hole (var_nm,var_typ) not_sim_opt
                           (hole_constr_tab, constr_tab, 
                            allowed_tab, constr_dep_tab) = 
    case (Constraint.NTab.get constr_tab eq_constr_nm) of
      Equal args =>  
      let         
        val other_args = get_other_eq_args hole args         
      in
        case other_args of
          [] => raise ERROR "propagate_equality_var: not eqaual to anything."
        | [other_arg] =>   
             let 
               val nw_ctab = 
                   Constraint.NTab.update (eq_constr_nm, 
                                     VarNotAllowed (other_arg, var_nm)) 
                                    constr_tab
             in
               case (check_not_sims hole eq_constr_nm []
                                    (hole_constr_tab, nw_ctab, 
                                     allowed_tab, constr_dep_tab)) of
                 NONE => (hole_constr_tab, nw_ctab, 
                          allowed_tab, constr_dep_tab)
               | SOME new_tables => new_tables
             end
        | (other_arg::more_args) =>
          let 
            val (ctab2, notalloweds) = 
                foldl_map (fn (ctab, other_arg) =>
                              let 
                                val (nm,ctab2) =  
                                    Constraint.NTab.add (default_cnm, 
                                                   VarNotAllowed(other_arg, var_nm)) 
                                                  ctab
                              in (ctab2, (other_arg, nm)) end)
                          (constr_tab, other_args)
                
            val (nw_hctab, nw_ctab, nw_atab, nw_cdtab) =   
                case (check_not_sims hole eq_constr_nm []
                                     (hole_constr_tab, ctab2, 
                                      allowed_tab, constr_dep_tab)) of
                  NONE => (hole_constr_tab, ctab2, 
                           allowed_tab, constr_dep_tab)
                | SOME new_tables => new_tables
          in
            case not_sim_opt of
              NONE => (* Add a new NotSimult *)
              (nw_hctab,
               Constraint.NTab.update (eq_constr_nm, NotSimult notalloweds) nw_ctab,
               nw_atab,
               List.foldl (fn ((arg,n_allowed), cdtab) => 
                         add_constr_deps n_allowed eq_constr_nm cdtab)
                     nw_cdtab notalloweds)
              (* Merge the new not-allowed constraints into the old NotSimult *)
            | SOME not_sim_nm => 
                case (Constraint.NTab.lookup nw_ctab not_sim_nm)
                 of NONE => (* The previous NotSimult parent was deleted, so make new *)
                    (nw_hctab,
                     Constraint.NTab.update (not_sim_nm, NotSimult notalloweds) nw_ctab,
                     nw_atab,
                     List.foldl (fn ((arg,n_allowed), cdtab) => 
                               add_constr_deps n_allowed eq_constr_nm cdtab)
                           nw_cdtab notalloweds)
                  | SOME (NotSimult arg_constrs) => (* arg_constrs no longer contain eq_constr *)
                    (nw_hctab,
                     Constraint.NTab.update (not_sim_nm, NotSimult (arg_constrs @ notalloweds)) nw_ctab,
                     nw_atab,
                     List.foldl (fn ((arg,n_allowed), cdtab) => 
                               add_constr_deps n_allowed not_sim_nm cdtab)
                           nw_cdtab notalloweds)
                  | _ => raise ERROR "propagate_equality_var: Constr supposed to be NotSimult" 

          end
      end
    | _ => raise ERROR "propagate_equality_var: Expects Equal, found something else.";

(* ---------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------*)
          
exception update_constr_exp of (Hole.NTab.name * Constant.name) * (Hole.NTab.name list) *
                                 (Constraint.NSet.T Hole.NTab.T *
                                 Constraints.Constr Constraint.NTab.T *
                                 Constant.NSet.T Hole.NTab.T *
                                 Constraint.NSet.T Constraint.NTab.T)
                                 * Constraint.name

(* hole has just been instantiated to the constant 'const_nm',
resulting in some new holes 'new_hole_nms'. 'constr_nm' is some old constraint on 'hole'. *)
fun update_constr_of_hole (hole : Hole.name, const_nm : Constant.name) 
                          (new_hole_nms : Hole.name list) 
                          (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) 
                          (constr_nm : Constraint.name) =
    let       
      val constr = Constraint.NTab.get constr_tab constr_nm
    in
      case constr of
        IfThen (arg, (const, sub_constr)) =>
        if (Constant.name_eq (const, const_nm)) (* triggered constraint *) 
        then   
          (let 
             val constr_tab2 = 
                    argnames_to_holerep new_hole_nms (SOME constr_nm, sub_constr) constr_tab
             val dependent_constrs = lookup_dependencies constr_dep_tab constr_nm
          in
            if (Constraint.NSet.is_empty dependent_constrs) 
            then
              let   
                val 
                (nw_hctab, nw_ctab, nw_atab, nw_cdtab) =
                add_constr_to_new_holes sub_constr new_hole_nms
                                       (hole_constr_tab, constr_tab2, 
                                        allowed_tab, constr_dep_tab)

              in (nw_hctab, Constraint.NTab.delete constr_nm nw_ctab, 
                  nw_atab, 
                  (* Some deleted constraints have no dependencies, check *)
                  (del_constr_dep_if_present constr_nm nw_cdtab)
                    |> del_from_constr_deps sub_constr constr_nm)
              end
            else
              let 
                val (nw_hctab, nw_ctab, nw_cdtab) =
                    propagate_if_then_constr constr_nm sub_constr 
                                             (hole_constr_tab, constr_tab2, constr_dep_tab)
              in (nw_hctab, Constraint.NTab.delete constr_nm nw_ctab, 
                  allowed_tab,
                (* Some deleted constraints have no dependencies, check *)
                  del_constr_dep_if_present constr_nm nw_cdtab)
              end
          end)
        else (* This constraint doesn't apply *)
          let
            val (c_tab, hc_tab, cd_tab) =  
                drop_constraint constr_nm (constr_tab, hole_constr_tab, constr_dep_tab)
          in
            (hc_tab, c_tab, allowed_tab, cd_tab)
          end
      
          (* Need to check if this is part of a subconstraint?*)
      | NotSimult arg_constrs =>
        (List.find (* find sub-constr on hole that got instantiated *)
           (fn (arg, c) => 
               case (opt_hole_of_arg arg) of
                 SOME arg_hole => Hole.name_eq (arg_hole, hole)
               | NONE => false) arg_constrs)
          |> the
          |> snd
          |> update_constr_of_hole (hole, const_nm) new_hole_nms 
          (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab)
      | NotAllowed (arg, const) =>
        if (Constant.name_eq (const, const_nm)) (* triggered constraint *) 
        then 
          (* There must be dependencies, otherwise const should have been removed
            from domain of hole *)
          (let 
            val (hc_tab, c_tab, a_tab, cd_tab) =
                 propagate_not_allowed hole constr_nm new_hole_nms
                                      (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab)
          in
             (hc_tab, Constraint.NTab.delete constr_nm c_tab, 
              a_tab, Constraint.NTab.delete constr_nm cd_tab)
          end)
        else 
          let val (c_tab, hc_tab, cd_tab) =  
                  drop_constraint constr_nm (constr_tab, hole_constr_tab, constr_dep_tab)
          in (hc_tab, c_tab, allowed_tab, cd_tab) end
      | Equal args => propagate_equality constr_nm hole const_nm new_hole_nms
                       (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab)
      | VarNotAllowed (arg, var) => 
        (* Just drop this, not applicable. *)
        let val (c_tab, hc_tab, cd_tab) =  
                drop_constraint constr_nm (constr_tab, hole_constr_tab, constr_dep_tab)
        in
          (hc_tab, c_tab, allowed_tab, cd_tab)
        end
  (*    | _ => raise ERROR "update_constr_of_hole: Constraint is Equality, should be Ref." *)
    end
     handle not_allowed_exp x => 
           raise update_constr_exp 
                 ((hole, const_nm), 
                  new_hole_nms, (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab), 
                          constr_nm)

(* Update the constraints for a hole that has been instantiated to a variable.
   We can drop all constraints except NotSimult and Equal. VarNotAllowed has
   already been taken into account, so they too are dropped. *)
exception prop_var_exp of 
          (Hole.name * Constraint.name *
           (Constraints.Constr Constraint.NTab.T *
            Constraint.NSet.T Constraint.NTab.T))
          *
          (Constraint.name * 
           (Constraints.Constr Constraint.NTab.T *
            Constraint.NSet.T Constraint.NTab.T))
fun propagate_var_constr hole constr_nm 
                         (hctab, ctab, atab, cdtab) = 
    case (check_not_sims hole constr_nm []
                         (hctab, ctab, atab, cdtab)) of
      NONE => raise ERROR "propagate_var_constr: No NotSimult parent!"
    | SOME tables => tables;
      

fun update_var_constr_of_hole hole (var_nm, var_typ) 
                              (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab)
                              constr_nm =
    let       
      val constr = Constraint.NTab.get constr_tab constr_nm
                   
      (* Update of a constraint that is part of a NotSimult *)
      fun update_subconstr hole (var_nm,var_typ) not_sim_nm
                           (hctab, ctab, atab, cdtab) sub_constr_nm =
          case (Constraint.NTab.get ctab sub_constr_nm) of
            VarNotAllowed(arg, v2) => 
            (if (var_nm = v2) then
              (let 
                 val (hc_tab, c_tab, a_tab, cd_tab) =
                      propagate_var_constr hole sub_constr_nm
                                          (hctab, ctab, atab, cdtab)
               in
                 (hc_tab, Constraint.NTab.delete sub_constr_nm c_tab, 
                  a_tab, Constraint.NTab.delete sub_constr_nm cd_tab)
               end)
            else update_var_constr_of_hole hole (var_nm, var_typ)
                                           (hctab, ctab, atab, cdtab) sub_constr_nm
            )
          | Equal args =>
            propagate_equality_var sub_constr_nm hole (var_nm,var_typ) (SOME not_sim_nm)
                                   (hole_constr_tab, constr_tab, 
                                    allowed_tab, constr_dep_tab)
          | _ => update_var_constr_of_hole hole (var_nm, var_typ)
                                           (hctab, ctab, atab, cdtab) sub_constr_nm
    in
      case constr of
        NotSimult arg_constrs => 
        (List.find (* find sub-constr on hole that got instantiated *)
           (fn (arg, c) => 
               case (opt_hole_of_arg arg) of
                 SOME arg_hole => Hole.name_eq (arg_hole, hole)
               | NONE => false) arg_constrs)
          |> the
          |> snd
          |> update_subconstr hole (var_nm,var_typ) constr_nm 
          (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab)
      | Equal args =>
        propagate_equality_var constr_nm hole (var_nm,var_typ) NONE
                               (hole_constr_tab, constr_tab, 
                                allowed_tab, constr_dep_tab)
        (* Delete constraints about constants or about variables other than the
         one we instantiated to *)
      |  _ => 
        let 
          val (c_tab, hc_tab, cd_tab) =  
              drop_constraint constr_nm (constr_tab, hole_constr_tab, constr_dep_tab)
        in
          (hc_tab, c_tab, allowed_tab, cd_tab)
        end
    end
    handle delete_exp (bad_constr_nm, (bad_ctab, bad_cdtab)) =>
           raise prop_var_exp ((hole, constr_nm, (constr_tab, constr_dep_tab)),
                               (bad_constr_nm, (bad_ctab, bad_cdtab)));

(* ---------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------*)
  
exception update_constr_exp2 of 
          (Hole.NTab.name * Constant.name) * (Hole.NTab.name list) *
          (Constraint.NSet.T Hole.NTab.T *
           Constraints.Constr Constraint.NTab.T *
           Constant.NSet.T Hole.NTab.T *
           Constraint.NSet.T Constraint.NTab.T)  
exception update_constr_exp3 of 
          (Hole.NTab.name * (string * Term.typ)) *
          (Constraint.NSet.T Hole.NTab.T *
           Constraints.Constr Constraint.NTab.T *
           Constant.NSet.T Hole.NTab.T *
           Constraint.NSet.T Constraint.NTab.T)  
exception update_constr_exp4 of 
          (Hole.NTab.name * Constant.name) * (Hole.NTab.name list) *
          (Constraints.argref * Constraint.name) *
          (Constraint.NSet.T Hole.NTab.T *
           Constraints.Constr Constraint.NTab.T *
           Constant.NSet.T Hole.NTab.T *
           Constraint.NSet.T Constraint.NTab.T)  

(* Make sure the dependecies in both tables are the same *)
val dbg_ref = Unsynchronized.ref NONE;
fun dbg_constr_dep c_tab cd_tab =
    let
      val deps = (Constraint.NTab.list_of c_tab)
                   |> map_filter (fn (nm, c) => 
                                 case c of 
                                   NotSimult arg_cs => SOME (nm, map snd arg_cs)
                                 | IfThen (arg, (const, sub_c)) => SOME (nm, [sub_c])
                                 | _ => NONE)
      fun check (parent_c, sub_cs) = 
          List.all (fn sub_c =>
                       case (Constraint.NTab.lookup cd_tab sub_c) of
                         SOME constraints => 
                         if (Constraint.NSet.contains constraints parent_c)
                         then true
                         else let val _ = dbg_ref:= SOME(parent_c, sub_c) in false end
                       | NONE => let val _ = dbg_ref:= SOME(parent_c, sub_c) in false end)
                   sub_cs
    in
      List.all check deps 
    end;

fun check_dups [] _ = NONE
  | check_dups ((arg, c) :: arg_cs) checked = 
    if
      ((List.exists (fn (a,c) => Constraints.arg_eq (arg,a)) arg_cs) 
       orelse
       (List.exists (fn (a,c) => Constraints.arg_eq (arg,a)) checked)) 
    then 
      SOME (arg, c)
    else check_dups arg_cs ((arg,c)::checked);

(* Update constraints that are already in the constraint table, 
that may now apply newly created holes. *)        
fun update_constrs_of_hole (hole, const_nm) new_hole_nms 
                           (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) =
    case (Hole.NTab.lookup hole_constr_tab hole) of
      NONE => (hole_constr_tab, constr_tab, 
               Hole.NTab.delete hole allowed_tab, constr_dep_tab)
    | SOME constrs =>
      let 
        val (hc_tab, c_tab, a_tab, cd_tab) =
            List.foldl (fn (constr, tables) => 
                      update_constr_of_hole (hole, const_nm) new_hole_nms tables constr)
                  (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) 
                  (Constraint.NSet.list_of constrs)
        (* Check for dodgy NotSimults 
        val _ = map (fn (nm, constr) => 
                    case constr of
                      NotSimult arg_constrs =>
                      (case (check_dups arg_constrs []) of
                         SOME (bad_arg, bad_constr) =>
                         raise update_constr_exp4 ((hole, const_nm), new_hole_nms,
                                                   (bad_arg, bad_constr), 
                                                   (hole_constr_tab, constr_tab, 
                                                   allowed_tab, constr_dep_tab))
                       | NONE => ())
                    | _ => ()) 
                    (Constraint.NTab.list_of c_tab)
         *)
        (* Check all constraints are about open holes, otherwise they
           shouldn't still be around. *)
       (* val constr_holes = 
            (maps (fn cnm => holes_of_constr cnm c_tab) (Constraint.NTab.keys c_tab))
              |> map Hole.NTab.string_of_name
        val holenm = let val (s,i) = (Hole.dest hole) in 
                       s^(Int.toString i) end
        val _ = if (holenm mem constr_holes) then
                  raise update_constr_exp2 ((hole, const_nm), new_hole_nms,
                                           (hole_constr_tab, constr_tab, 
                                            allowed_tab, constr_dep_tab))
                else ()
        (* Check the integrety of the constraint dependencies. *)
        val _ = if dbg_constr_dep c_tab cd_tab then ()
                else raise update_constr_exp2 ((hole, const_nm), new_hole_nms,
                                           (hole_constr_tab, constr_tab, 
                                            allowed_tab, constr_dep_tab))
        *)
      in
        (Hole.NTab.delete hole hc_tab, c_tab, 
         Hole.NTab.delete hole a_tab, cd_tab)
      end
           

(* Update constraints after instantiating a hole to a variable *)
fun update_var_constrs hole (var_nm, var_typ) (hctab, ctab, atab, cdtab) =
    case (Hole.NTab.lookup hctab hole) of
      NONE => (hctab, ctab, Hole.NTab.delete hole atab, cdtab) 
    | SOME cs => 
      let 
        val (hc_tab2, c_tab2, a_tab2, cd_tab2) = 
            List.foldl (fn (constr, tables) =>
                      update_var_constr_of_hole hole (var_nm, var_typ) tables constr)
                  (hctab, ctab, atab, cdtab) (Constraint.NSet.list_of cs)

        (* Check all constraints are about open holes, otherwise they
           shouldn't still be around. *)
   (*     val constr_holes = 
            (maps (fn cnm => holes_of_constr cnm c_tab2) (Constraint.NTab.keys c_tab2))
              |> map Hole.NTab.string_of_name
        val holenm = let val (s,i) = (Hole.dest hole) in 
                       s^(Int.toString i) end
        val _ = if (holenm mem constr_holes) then
                  raise update_constr_exp3 ((hole, (var_nm, var_typ)), 
                                           (hctab, ctab, atab, cdtab))
                else ()    
*)
        (* Check integity of constraint dependencies *)
    (*    val _ = if dbg_constr_dep c_tab2 cd_tab2 then ()
                else raise update_constr_exp3 ((hole, (var_nm, var_typ)),
                                               (hctab, ctab, 
                                                atab, cdtab)) 
     *)
        
      in
        (Hole.NTab.delete hole hc_tab2, c_tab2, 
         Hole.NTab.delete hole a_tab2, cd_tab2)
      end;

(* ---------------------------------------------------------------------------------*)
(* ---------------------------------------------------------------------------------*)

(* Make up possible sizes for holes *)
fun is_decr_size [] = true
  | is_decr_size [x] = true
  | is_decr_size ((h1,size1)::(h2,size2)::t) = 
    size1 >= size2 andalso (is_decr_size t);

(* assumes max_size > length(holes) *)
fun hole_size_combos commute_opt holes max_size =
    let 
      val num_holes = List.length holes
      val size_combs = 
          case holes of
            [] => []
          | [h] => [[(h,max_size)]]
          | (h::hs) => 
            maps (fn size =>
                     map (fn other_combo => (h,size)::other_combo) 
                         (hole_size_combos commute_opt hs (max_size - size)))
                 (1 upto (max_size - num_holes +1))
    in
    case commute_opt of
      NONE => 
      size_combs
    | SOME thm => 
      filter is_decr_size size_combs
    end;

exception inst_hole_exp of SynthTerm

fun inst_hole_with_const sterm hole const_info =     
    let           
      val typ = get_hole_type sterm hole;
      val size = get_hole_size sterm hole;

      val synth_trm = get_term sterm;
      val constr_tab = get_constrTab sterm;
      val hole_constrs = get_holeConstrs sterm;
      val constr_dep_tab = get_constrDepTab sterm;                       

      val (const_trm, fresh_holes, ienv, nw_allowed_tab) = 
          mk_new_term_bit const_info (get_allowedTab sterm) (get_ienv sterm);
      val fresh_hole_nms_typs = map (fn (nm,ty) => (Hole.mk nm, ty)) fresh_holes
      val fresh_hole_nms = map fst fresh_hole_nms_typs

      val hole_trm = Trm.mk_var (Hole.dest hole, typ)  
      val unifiers = (MyUnify.unifiers (ienv, [(hole_trm, const_trm)]))
                       |> Seq.map (fn ienv' => (ienv', InstEnv.inst_trm ienv' synth_trm))

      val const_constrs = Constraints.get_constrTab const_info
      val constr_renamings = (rename_constraints const_constrs constr_tab)
                               |> Constraint.nmap_of_renaming

      (* Add renamed constraints to the constraint-table and to the 
         table of constraints for each hole *)
      val (hole_constr_tab2, constr_tab2, allowed_tab2, constr_dep_tab1) = 
          (List.foldl (attach_constr const_constrs constr_renamings fresh_hole_nms)
                (hole_constrs, constr_tab, nw_allowed_tab, constr_dep_tab) 
                (map snd (Constraints.get_start_constrs const_info)))

       val renamed_constrs = 
          (map (fn cnm => 
                   case (Constraint.NTab.lookup constr_renamings cnm) of
                     NONE => cnm | SOME nw_cnm => nw_cnm)
               (Constraint.NTab.keys const_constrs))
      val constr_dep_tab2 = 
          update_constr_dep_tab renamed_constrs 
                                constr_tab2
                                (constr_dep_tab1)   

      val (hole_constr_tab3, constr_tab3, allowed_tab3, constr_dep_tab3) = 
          update_constrs_of_hole (hole, Constraints.get_name const_info) 
                                 fresh_hole_nms 
                                 (hole_constr_tab2, constr_tab2, allowed_tab2, constr_dep_tab2);

      (* Existing holes, not instantiated *)
      val remaining_holes = Library.remove Hole.name_eq hole (get_holes_agenda sterm)

      (* make all possible size constraints for new holes, sum of new hole sizes = (size - 1) *)
      val holesizes = get_hole_sizes sterm;
      val holesizes2list = 
          (hole_size_combos (get_commute_opt const_info) fresh_hole_nms (size-1))
            |> map (fn l => (fold Hole.NTab.ins l holesizes))
    in
      if (null holesizes2list) then 
        Seq.map (fn (ienv, trm) =>
                    Sterm{term = trm, 
                          ienv = ienv,
                          allowedTab = allowed_tab3, 
                          holes_agenda = remaining_holes,
                          hole_sizes = holesizes,
                          constrTab = constr_tab3,
                          holeConstrs = hole_constr_tab3,
                          constrDepTab = constr_dep_tab3,
                          max_vars = get_max_vars sterm})
                 unifiers 
      else 
        Seq.maps (fn (ienv, trm) => 
                     Seq.map (fn holesizes2 => 
                                 Sterm{term = trm, 
                                       ienv = ienv,
                                       allowedTab = allowed_tab3, 
                                       holes_agenda = fresh_hole_nms @ remaining_holes,
                                       hole_sizes = holesizes2,
                                       constrTab = constr_tab3,
                                       holeConstrs = hole_constr_tab3,
                                       constrDepTab = constr_dep_tab3,
                                       max_vars = get_max_vars sterm})
                             (Seq.of_list holesizes2list))
                 unifiers
    end;
(*    handle Hole.NTab.ATab.UNDEF key => raise inst_hole_exp sterm; *)



fun lookup_forbidden_vars hole constr_tab constr = 
    case (Constraint.NTab.get constr_tab constr) of
      VarNotAllowed (arg, var) => SOME var
  (*  | NotSimult args => 
      (case (List.find (fn (a,c) => arg_eq(a, Hole hole)) args) of
        NONE => raise ERROR "lookup_forbidden_vars: hole not in its constraint!"
        (* This isn't quite right, the var is still allowed,
           as long as the other constraints aren't... *)
      | SOME (holearg, c) => lookup_forbidden_vars hole constr_tab c) *)
    | _ => NONE;


(* update an strm with a given instantiation env and newly instantiated term 
   (helper function) 
*)
fun update_strm_with_inst hole strm (ienv, trm)  = 
    let 
      val (inst_ty, inst_trm) = InstEnv.get_var_inst ienv (Hole.dest hole)
      val (free_nm, free_typ) = Term.dest_Free inst_trm
      val (nw_hctab, nw_ctab, nw_atab, nw_cdtab) = 
          update_var_constrs hole (free_nm, free_typ)
            (get_holeConstrs strm, get_constrTab strm, get_allowedTab strm, get_constrDepTab strm)
    in
      Sterm{term = trm, 
            ienv = ienv,
            holes_agenda = Library.remove Hole.name_eq hole (get_holes_agenda strm),
            hole_sizes = get_hole_sizes strm,
            allowedTab = nw_atab,
            constrTab = nw_ctab,
            holeConstrs = nw_hctab,
            constrDepTab = nw_cdtab,
            max_vars = get_max_vars strm }
    end;

(* Instantiate a hole with a given free variable, if it is allowed.*)
fun inst_hole_with_given_freevar var_allowed_fn hole (free_nty as (n,ty)) strm =
    if get_hole_size strm hole <> 1 then NONE
    else let
      (* Constraints on this hole *)
      val hole_constrs = 
          case (Hole.NTab.lookup (get_holeConstrs strm) hole) of
            NONE => [] | SOME cs => Constraint.NSet.list_of cs;
      val forbidden_frees = 
          map_filter (lookup_forbidden_vars hole (get_constrTab strm)) hole_constrs;

      val t = get_term strm;
      val paramtab = Trm.params_of t;
      val is_fresh = case Trm.TrmParams.lookup paramtab n of NONE => false | SOME _ => true;
      
      (* check if this is a valid instantiaton *)
      val max_vars = get_max_vars strm;
      val max_vars_opt = if is_fresh then 
       (if ((var_allowed_fn hole t) andalso max_vars > 0) then 
          SOME (max_vars - 1)  else  NONE )  
      (* else if it is not fresh, check if a constraint rules out this freevar at this hole *)
      else if is_some (Library.find_first (fn m => n = m) forbidden_frees)
      then NONE else SOME max_vars
    in
      case max_vars_opt of NONE => NONE
         | SOME new_max_vars => 
           (get_ienv strm)
             |> (MyUnify.match [(Trm.mk_var (Hole.dest hole,get_hole_type strm hole), 
                                Free free_nty)])
             |> Option.map (fn ienv => (ienv, InstEnv.inst_trm ienv t))
             |> Option.map (update_strm_with_inst hole strm)
             |> Option.map (set_max_vars new_max_vars)
    end;


(* Instantiate a hole with a varaible. Only for holes of size 1.
   the 'var_allowed_fn' takes the hole and strm and decides if
   a new varible is allowed to occur here.*)
fun inst_hole_with_var var_allowed_fn strm hole =
    let
      val typ = get_hole_type strm hole;
      val size = get_hole_size strm hole;

      val synth_trm = get_term strm;
      val paramtab = Trm.params_of synth_trm;
      val constr_tab = get_constrTab strm;
      val hole_constr_tab = get_holeConstrs strm;
      val allowed_tab = get_allowedTab strm;
      val constr_dep_tab = get_constrDepTab strm;
      val max_vars = get_max_vars strm;

      (* Constraints on this hole *)
      val hole_constrs = 
          case (Hole.NTab.lookup hole_constr_tab hole) of
            NONE => [] | SOME cs => Constraint.NSet.list_of cs;
  
      val frees = (Trm.TrmParams.get_plist paramtab)
                    |> map (fn (nm,ty) => Free(nm,ty));

      val forbidden_frees = 
          map_filter (lookup_forbidden_vars hole constr_tab) hole_constrs;

      val allowed_frees = fold (Library.remove (fn (v1,free) => fst (Term.dest_Free free) = v1))
                               forbidden_frees frees;

      val hole_trm = Trm.mk_var (Hole.dest hole,typ);

      (* NOTE: Requires/Assumes depth first syntehsis order! *)
      val fresh_free =
          if (var_allowed_fn hole synth_trm andalso max_vars > 0)
          then (Trm.TrmParams.add1 ("a", typ) paramtab)
                 |> fst
                 |> (fn nm => [Free(nm,typ)])
          else []
      
      fun unify_frees_w_hole free_var_trms = 
          (Seq.of_list free_var_trms)
            |> Seq.maps (fn freevar => 
                            MyUnify.unifiers (get_ienv strm, 
                                              [(hole_trm, freevar)]))
            |> Seq.map (fn ienv => 
                           (ienv, InstEnv.inst_trm ienv synth_trm))
      val existing_frees_unifiers = unify_frees_w_hole allowed_frees
      val fresh_frees_unifiers = unify_frees_w_hole fresh_free

      val remaining_holes = Library.remove Hole.name_eq hole (get_holes_agenda strm)
      fun update_strm is_fresh (ienv, trm) = 
            let 
              val (inst_ty, inst_trm) = InstEnv.get_var_inst ienv (Hole.dest hole)
              val (free_nm, free_typ) = Term.dest_Free inst_trm
              val (nw_hctab, nw_ctab, nw_atab, nw_cdtab) = 
                  update_var_constrs hole (free_nm, free_typ)
                                     (hole_constr_tab, constr_tab, 
                                      allowed_tab, constr_dep_tab)
            in
              Sterm{term = trm, 
                    ienv = ienv,
                    holes_agenda = remaining_holes,
                    hole_sizes = get_hole_sizes strm,
                    allowedTab = nw_atab,
                    constrTab = nw_ctab,
                    holeConstrs = nw_hctab,
                    constrDepTab = nw_cdtab,
                    max_vars = if is_fresh 
                               then max_vars -1 else max_vars}
            end 
    in
      Seq.append
        (Seq.map (update_strm true) fresh_frees_unifiers)
        (Seq.map (update_strm false) existing_frees_unifiers)
    
    end;


(* ---------------------------------------------------------------------------------*)
datatype synth_step =
         FinishedSynth of SynthTerm
       | ProgressSynth of SynthTerm Seq.seq;

exception synth_bug_exp of SynthTerm;

(* Instantiate the next variable in the synth term "strm" *)
(* var_allowed_fn : hole -> strm -> bool = true if hole can be fresh in strm. 
   cinfoTab : Constraints.ConstInfo = background constraint table for synthesied
     part of theory. 
   strm : SynthTerm = the term being synthesied with current constraints. 
   returns : synth_step
*)
fun synthesise_1step var_allowed_fn cinfoTab strm = 
    case (get_holes_agenda strm) (* Idea: kept sorted *)
     of [] => FinishedSynth strm
      | (hole::hs) => 
        let val size = get_hole_size strm hole in
          if (size = 1)
          then 
            let 
              val const_infos = 
                  (allowed_consts_of_hole strm hole)
                    |> map (the o (Constant.NTab.lookup cinfoTab))
                    |> filter (fn cinfo => (Constraints.get_minsize cinfo) = size)
              val const_insts = 
                  (Seq.of_list const_infos) 
                    |> Seq.maps (inst_hole_with_const strm hole)
              val var_insts = inst_hole_with_var var_allowed_fn strm hole
            in ProgressSynth (Seq.append var_insts const_insts) end
          else
            let
              val const_infos = 
                  (allowed_consts_of_hole strm hole)
                    |> map (the o (Constant.NTab.lookup cinfoTab))
                    |> filter (fn cinfo => 
                                  let val minsize = Constraints.get_minsize cinfo
                                  in 1 < minsize andalso minsize <= size end)
            in
              ProgressSynth
                ((Seq.of_list const_infos) 
                   |> Seq.maps (inst_hole_with_const strm hole))
            end
        end
      (*  handle Eq_LData_HOL.bad_term_exp _ => raise synth_bug_exp strm; *)


(* lazy depth first search through synthesis of this size *)
fun synthesise var_allowed_fn cinfoTab s =
    let fun recf ss () = 
            (case Seq.pull ss 
              of NONE => NONE
               | SOME (hs,ss2) => 
                 (case synthesise_1step var_allowed_fn cinfoTab hs of 
                    ProgressSynth ss3 => recf (Seq.append ss3 ss2) ()
                  | FinishedSynth hs2 => SOME (hs2, Seq.make (recf ss2))))
    in Seq.make (recf (Seq.single s)) end;




(* Instantiate holes with constants, with the additional restrictions
   that certain function symbols needs to be used at least once.
   tot_minsize is the amount of space need to include each of the
   constants at least once. *)
fun restr_inst_hole_with_const sterm hole size unused_consts cinfo =
    let 
      (*val size = get_hole_size sterm hole;*)
      val unused_2 = 
            Library.remove (fn (cnm, (cnm2,size)) => 
                               Constant.name_eq (cnm,cnm2)) 
                           (Constraints.get_name cinfo) unused_consts
    in
      Seq.map (fn strm => (unused_2, strm))
              (inst_hole_with_const sterm hole cinfo)
    end;

fun restr_inst_hole_with_var var_allowed_fn sterm hole unused_consts =
    Seq.map (fn strm => (unused_consts, strm))
     (inst_hole_with_var var_allowed_fn sterm hole);

(* restricted synthesis: some constants must be used *)
fun restr_synthesis var_allowed_fn cinfoTab consts_to_use (unused_consts, sterm) =
    let 
      fun get_max [] m = m
        | get_max (size::t) m = if size > m then get_max t size
                                              else get_max t m
      val holes = get_holes_agenda sterm
      val largest_hole = get_max (map (get_hole_size sterm) holes) 0 
      val largest_unused_const = get_max (map snd unused_consts) 0
                         
    in 
      (* Check we fit in the things we still need*)
      if (largest_hole < largest_unused_const) 
      then Seq.empty (* failed to use all constants that must be used *)
      else 
        case holes 
         of [] => Seq.single sterm
          | (hole::hs) => 
            let 
              val size = get_hole_size sterm hole
            in 
              if (size = 1)
              then 
                let 
                  val const_infos = 
                      (allowed_consts_of_hole sterm hole)
                        |> map (the o (Constant.NTab.lookup cinfoTab))
                        |> filter (fn cinfo => 
                                      (Constraints.get_minsize cinfo) = size
                                      andalso (member Constant.name_eq 
                                                      consts_to_use 
                                                      (Constraints.get_name cinfo)))

                  val const_insts = 
                      (Seq.of_list const_infos) 
                        |> Seq.maps (restr_inst_hole_with_const sterm hole size
                                                           unused_consts)
                in
                  const_insts
                    |> Seq.append (restr_inst_hole_with_var var_allowed_fn 
                                                       sterm hole
                                                       unused_consts)
                    |> Seq.maps (restr_synthesis var_allowed_fn cinfoTab 
                                             consts_to_use)
                end
              else
                let
                  val const_infos = 
                      (allowed_consts_of_hole sterm hole)
                        |> map (the o (Constant.NTab.lookup cinfoTab))                   
                        |> filter (fn cinfo => 
                                      1 < (get_minsize cinfo) andalso 
                                      (get_minsize cinfo) <= size
                                      andalso (member Constant.name_eq 
                                                      consts_to_use 
                                                      (Constraints.get_name cinfo)))
                    
              in
                  (Seq.of_list const_infos)
                    |> Seq.maps (restr_inst_hole_with_const sterm 
                                                       hole size 
                                                       unused_consts)
                    |> Seq.maps (restr_synthesis var_allowed_fn cinfoTab consts_to_use) 
                end
            end
    end;
 

(* 
val strm = synthesise_upto_given_term
*)

(* an invariant that checks synthesised terms are correct *)
(* given theory and initial strm id function if good, else raises exception *)
fun certify_strm ctxt strm = 
    let val _ = Thm.cterm_of (Proof_Context.theory_of ctxt) (get_term strm) 
    in strm end;

(* the core synthesis setup function *)
fun synthesise_terms' top_const var_allowed_fn {size, max_vars} ctxt constInfoTab = 
    let 
      val top_cinfo = the (Constraints.lookup_const constInfoTab top_const) 
      val top_cnstrs = Constraints.get_constrTab top_cinfo

      val (init_trm, init_holes, ienv, allowed_tab1) =     
          mk_new_term_bit top_cinfo (Hole.NTab.empty) (InstEnv.init ctxt)
      val hole_nms_typs = map (fn (nm,ty) => (Hole.mk nm, ty)) init_holes
      val hole_nms = map fst hole_nms_typs;

      (* Debugging: make sure names here are different from the constant-info *)
      val init_constr_tab = Constraint.NTab.useup_names (Constraint.NTab.get_nameset top_cnstrs) 
                                                  Constraint.NTab.empty
      val constr_renamings = (rename_constraints top_cnstrs init_constr_tab)
                             |> Constraint.nmap_of_renaming
        
      val constr_dep_tab1 = 
          init_constr_dep_tab constr_renamings top_cnstrs

      (* Add renamed constraints to the constraint-table and to the table 
         of constraints for each hole *)
      val (hole_constr_tab, constr_tab, allowed_tab, constr_dep_tab) = 
          List.foldl (attach_constr top_cnstrs constr_renamings (map fst hole_nms_typs))
                (Hole.NTab.empty, init_constr_tab, allowed_tab1, constr_dep_tab1) 
                (map snd (Constraints.get_start_constrs top_cinfo))
      
      val commute_opt = Constraints.get_commute_opt top_cinfo
      
      val init_sterms = 
          map (fn holesizes =>
                  Sterm {term = init_trm,
                         ienv = ienv,
                         allowedTab = allowed_tab,
                         constrTab = constr_tab,
                         holeConstrs = hole_constr_tab,
                         constrDepTab = constr_dep_tab,
                         holes_agenda = hole_nms,
                         hole_sizes = holesizes,
                         max_vars = max_vars})
              ((hole_size_combos commute_opt hole_nms (size - 1))
                 |> map (fn l => (fold Hole.NTab.ins l Hole.NTab.empty)))
    in
      (Seq.of_list init_sterms)
        |> Seq.maps (synthesise var_allowed_fn constInfoTab)
        |> Seq.map (certify_strm ctxt) (* Invariant check: terms are well-formed. *)  
    end;


val counter_ex_counter = Unsynchronized.ref 0;
val size_stats = Unsynchronized.ref [];
val subsumpt_counter = Unsynchronized.ref 0;


fun reset_timers() = 
    let val _ = synth_time := Time.zeroTime
        val _ = upd_constr_time := Time.zeroTime
        val _ = subsumpt_time := Time.zeroTime    
        val _ = SynthPrfTools.prf_time := Time.zeroTime
        val _ = SynthPrfTools.counterex_time := Time.zeroTime
    in () end;

fun pretty_timers() = 
    Pretty.chunks 
    [Pretty.block 
       [Pretty.str "counterex_time:", 
        Pretty.str (Time.toString (!SynthPrfTools.counterex_time))],
     Pretty.block
       [Pretty.str "prf_time:", 
        Pretty.str (Time.toString (!SynthPrfTools.prf_time))],
     Pretty.block
       [Pretty.str "synth_time:", 
        Pretty.str (Time.toString (!synth_time))]];

val print_timers = Pretty.writeln o pretty_timers;
    

(* Checks the time for synthesis *)
fun timed_synthesise_terms' top_const var_allowed_fn 
                            {size, max_vars} ctxt cinfo_tab =
    let 
      val timer = Timer.startCPUTimer ()
      val synth_results = 
          synthesise_terms' top_const var_allowed_fn {size = size, max_vars = max_vars} 
            ctxt cinfo_tab
      val _ = synth_time := !synth_time + (#usr (Timer.checkCPUTimer timer))
    in synth_results end;

(* IMPROVE: this doesn't look like a good way to check timings: it's likely to be very small and 
   round down. *)
fun timed_update_constraints_term t cinfo = 
    let 
      val timer = Timer.startCPUTimer ()
      val nw_cinfo = Constraints.add_constraints_from_eq (ConstraintParams.termrw_of_term t) cinfo
      val _ = upd_constr_time := !upd_constr_time + (#usr (Timer.checkCPUTimer timer))
    in nw_cinfo end;

fun update_constraints_term t cinfo = 
    Constraints.add_constraints_from_eq (ConstraintParams.termrw_of_term t) cinfo;

(* With counter example checking and proof after each size. *)
(*fun synthesise_terms top_const var_allowed_fn {min_size, max_size, max_vars} 
                     ctxt constInfoTab = 
    let
      val subsumption_net = ref (SubsumptionNet.empty ctxt)
      val _ = counter_ex_counter := 0 (* Reset counter *)
      val _ = size_stats := []
      val _ = subsumpt_counter := 0
      val top_cinfo = the (Constraints.lookup_const constInfoTab top_const) 
      val top_const_minsize = Constraints.get_minsize top_cinfo
      val minsize = if (init_minsize < top_const_minsize) 
                     then top_const_minsize else init_minsize     

          (* Synthesise terms from the specified minimum size, up to the max size *)
      val (nw_cinfo_tab, new_ctxt, (conjs, thrms)) = 
          List.foldl (fn (this_size, (cinfo_tab, ctxt, (oldconjs, oldthrms))) => 
                        let 
                          (*
                          val cx_bfr = !counter_ex_counter
                          val synth_time_bfr = !synth_time
                          val upd_time_bfr = !upd_constr_time
                          val cx_time_bfr = !SynthPrfTools.counterex_time
                          val prf_time_bfr = !SynthPrfTools.prf_time
                          val subs_time_bfr = !subsumpt_time
                           *)

                          val cand_strms = 
                              synthesise_terms' top_const var_allowed_fn 
                                                {size = this_size, max_vars = max_vars} 
                                                ctxt cinfo_tab


                           (*   (timed_synthesise_terms' top_const var_allowed_fn 
                                                 {size = this_size, max_vars = max_vars} 
                                                 ctxt cinfo_tab *)
                           (*     |> Seq.filter (fn strm => 
                                              SynthPrfTools.timed_counter_ex_chk 
                                                counter_ex_counter ctxt 
                                                (get_term strm))
                                |> Seq.list_of *)
                          
                         (*     
                          val (ctxt2, proof_attempts) = 
                              Library.foldl_map (fn (ctxt1, strm) => 
                                            SynthPrfTools.ripple_timeout ctxt1   
                                              (*  SynthPrfTools.ripple_conjecture ctxt1 *)
                                              (get_term strm))
                                (ctxt, cand_strms)

                          val (conjs1, thrms1) = 
                              List.partition (fn (conj_t,thm_opt,lemmas) => is_some thm_opt)

                          val(conjs,thrms) =
                             (map (fn (conj_t,_,_) => conj_t) conjs1, 
                              map (fn (conj_t, thm_opt, lemmas) => (conj_t, the thm_opt, lemmas)) thrms1)
 
                          (* We synthesie more general terms first, so only 
                             need one pass over the terms. *)
                          val subs_bfr = !subsumpt_counter
                          val (snet, thrms') = filter_subsumed thrms (!subsumption_net)
                          val (snet2, conjs') = filter_subsumed conjs snet
                          val _ = subsumption_net := snet2
                          val _ = conj_tab := List.foldl (fn ((conj, rsts), tab) => 
                                                        snd (StrNTab.add ("conj_", conj) tab))
                                                    (!conj_tab) conjs (* incudes subsumed *)
*)
                         (* Do we want to re-orient the theorems here if they aren't
                             reducing the given order? Not important for rippling but
                             could make sense for presentation and constraints. *)
                          (* Update the constraints from new theorems *)

                          (* TODO: Generate constraints from lemmas too, at the moment there
                                    are none *)
                  (*        val cinfo_tab2 = 
                              List.foldl (fn ((thm_trm, thm_opt, lemmas), cinfo) => 
                                        timed_update_constraints_term 
                                         (Trm.change_frees_to_fresh_vars thm_trm) cinfo)
                                    cinfo_tab (thrms)
                   *)
                          (* Record the stats for this size *)
               (*           val _ = size_stats := 
                                  (this_size, {theorems = length thrms', conjs = length conjs',
                                               false_conjs = !counter_ex_counter - cx_bfr,
                                               subsumed = !subsumpt_counter - subs_bfr,
                                               synth_time = !synth_time - synth_time_bfr,
                                               update_time = !upd_constr_time - upd_time_bfr,
                                               subs_time = !subsumpt_time - subs_time_bfr,
                                               counterex_time = !SynthPrfTools.counterex_time - 
                                                                cx_time_bfr,
                                               prf_time = !SynthPrfTools.prf_time - prf_time_bfr
                                              })
                                  ::(!size_stats)
                *)
                        in
                          (oldconjs @ conjs', oldthrms @ thrms')
                          (* (cinfo_tab2, ctxt2, (oldconjs @ conjs', oldthrms @ thrms')) *)
                        end)
                    (constInfoTab, ctxt, ([], [])) (minsize upto max_size)
    in
      (* thrms have type (term * (thm, rst)) list) list, only interested in rst,
        so drop theorem representation (term is the term-rep of the theorem)  *)
      ((nw_cinfo_tab, new_ctxt), conjs, thrms)

     (*  (map (fn (trm,prfs) => (trm, map snd prfs)) conjs, 
        map (fn (trm, prfs) => (trm, map snd prfs)) thrms)) *)
    end;

*)


end (* local *)
end;

(* check signature *)
local structure CheckedConstrSynthesis : CONSTR_SYNTHESIS = ConstrSynthesis;
in val _ = (); end;
