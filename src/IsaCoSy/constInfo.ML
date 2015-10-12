(* Information IsaCoSy need to store about each constant it can use during synthesis *)

structure ConstInfo = 
struct

local open SynthNames in

(* FIXME: Sort out the Commute option, so that it is used properly. If a function is commutative, it
   should have exactly the same constraints on all its args, as order don't matter. Essentially, it 
   should be as if we also had generated constraints from the commuted constraint terms. 
    *) 

datatype T = CInfo of 
  { name : ConstantName.name,
    typ :  Trm.typ, (* most general type of const *) 
    args : (ArgName.name * Trm.typ) list, (* types of arguments to function *)
    arg_domains : (ConstantName.NSet.T) ArgName.NTab.T, (* arg number => allowed constants *)
    constrs : ThyConstr.T ConstraintName.NTab.T, (*All constraints *)
    arg_constrs : (ConstraintName.NSet.T) ArgName.NTab.T, (* Constraints, along paths from which args.*)
    commute_opt : Trm.T option, (* commutativity theorem as term *)
    weight : int (* A weight to be used by LPO for ordering equations *)    
   } 

(* Create and empty CInfo for constant cnm of type typ. *)
fun empty_cinfo (cnm,typ) = 
    let 
      val args = Library.map_index I (fst(Term.strip_type typ))
    in
         CInfo{name = ConstantName.mk cnm, 
              typ = typ,
              args = args,       
              arg_domains = List.foldl (fn ((arg,_),doms) => 
                                           ArgName.NTab.ins (arg, ConstantName.NSet.empty) doms) 
                                       ArgName.NTab.empty args, 
              constrs = ConstraintName.NTab.empty,
              arg_constrs = List.foldl (fn ((arg,_),argconstrs) => 
                                           ArgName.NTab.ins (arg, ConstraintName.NSet.empty) argconstrs) 
                                       ArgName.NTab.empty args, 
              commute_opt = NONE,
              weight = ~1}
       end;
    
(* ------------------------------------------------------------*)
(* Pretty print constant info. *)
(* ------------------------------------------------------------*)
fun pretty_opt f NONE = Pretty.str "NONE"
    | pretty_opt f (SOME x) = f x;

fun pretty_constinfo ctxt (CInfo rep) = 
      Pretty.chunks 
      [
       Pretty.block [Pretty.str "name:", ConstantName.pretty_name (#name rep)],
       Pretty.block [Pretty.str "typ:", Trm.pretty_typ ctxt (#typ rep)],
       Pretty.block [Pretty.str "args: ", 
                     Pretty.list "[" "]" 
                                 (map (fn (i,ty) => 
                                          Pretty.block 
                                            [(Pretty.str o Int.toString) i, 
                                            Trm.pretty_typ ctxt ty])
                                      (#args rep))],
       Pretty.block [Pretty.str "arg_domains: ", 
                     ArgName.NTab.pretty ConstantName.NSet.pretty (#arg_domains rep)],
       Pretty.block [Pretty.str "constrs: ", 
                     ConstraintName.NTab.pretty ThyConstr.pretty_constr (#constrs rep)],
       Pretty.block [Pretty.str "arg_constrs: ", 
                    ArgName.NTab.pretty ConstraintName.NSet.pretty (#arg_constrs rep)],
       Pretty.block [Pretty.str "commute_opt: ",   
                       pretty_opt (Trm.pretty ctxt) (#commute_opt rep)],
       Pretty.block [Pretty.str "LPO weight: ", (Pretty.str o Int.toString) (#weight rep)]
      ];

val print_constinfo = Pretty.writeln oo pretty_constinfo;  

(* ------------------------------------------------------------*)
(* Getting, setting, updating *)
(* ------------------------------------------------------------*)
fun get_name (CInfo info) = #name info;
fun get_arg_domains (CInfo info) = #arg_domains info;
fun get_typ (CInfo info) = (#typ info);
fun get_args (CInfo info) = (#args info);                     
fun get_argnms (CInfo info) = map fst (#args info);
fun get_constrs (CInfo info) = #constrs info;
fun get_arg_constrs (CInfo info) = #arg_constrs info;
fun get_commute_opt  (CInfo info) = (#commute_opt info);
fun get_weight (CInfo info) = #weight info;

fun update_arg_domains (CInfo cinfo) f = 
               CInfo {name = #name cinfo,  
               typ = #typ cinfo, args = #args cinfo, commute_opt = #commute_opt cinfo,
               arg_domains = f (#arg_domains cinfo), constrs = #constrs cinfo, 
               arg_constrs = #arg_constrs cinfo, weight = #weight cinfo};

fun update_constrs (CInfo cinfo) f = 
               CInfo {name = #name cinfo,  
               typ = #typ cinfo, args = #args cinfo, commute_opt = #commute_opt cinfo,
               arg_domains = #arg_domains cinfo, constrs = f (#constrs cinfo), 
               arg_constrs = #arg_constrs cinfo, weight = #weight cinfo};

fun update_arg_constrs (CInfo cinfo) f = 
               CInfo {name = #name cinfo,  
               typ = #typ cinfo, args = #args cinfo, commute_opt = #commute_opt cinfo,
               arg_domains = #arg_domains cinfo, constrs = #constrs cinfo, 
               arg_constrs = f (#arg_constrs cinfo), weight = #weight cinfo};

fun set_arg_domains cinfo nw_arg_domains = update_arg_domains cinfo (K nw_arg_domains);
fun set_constrs cinfo nw_constrs = update_constrs cinfo (K nw_constrs);
fun set_arg_constrs cinfo nw_arg_constrs = update_arg_constrs cinfo (K nw_arg_constrs);

fun set_commute_opt (CInfo cinfo) commute_opt = 
               CInfo {name = #name cinfo,
               typ = #typ cinfo, args = #args cinfo, commute_opt = commute_opt,
               arg_domains = #arg_domains cinfo, constrs = #constrs cinfo, 
               arg_constrs = #arg_constrs cinfo, weight = #weight cinfo};



fun set_weight (CInfo cinfo) nw_weight = 
              CInfo {name = #name cinfo,
               typ = #typ cinfo, args = #args cinfo, commute_opt = #commute_opt cinfo,
               arg_domains = #arg_domains cinfo, constrs = #constrs cinfo, 
               arg_constrs = #arg_constrs cinfo, weight = nw_weight};

fun insert_in_arg_dom cinfo (arg, dom_consts) =
      update_arg_domains cinfo 
                         (ArgName.NTab.map_entry (ConstantName.NSet.add_list dom_consts) arg);

fun del_from_arg_dom cinfo (arg, del_const) = 
      update_arg_domains cinfo
                        (ArgName.NTab.map_entry (ConstantName.NSet.delete del_const) arg);

fun del_from_all_arg_doms cinfo del_const = 
     List.foldl (fn ((arg,_), cinfo') => del_from_arg_dom cinfo' (arg,del_const)) 
                cinfo (get_args cinfo);
    
fun lookup_arg_domain cinfo arg =
    ArgName.NTab.get (get_arg_domains cinfo) arg;

fun lookup_arg_constrs cinfo arg = 
    ArgName.NTab.get (get_arg_constrs cinfo) arg;

fun lookup_constraint cinfo cnm =
    ConstraintName.NTab.get (get_constrs cinfo) cnm;

fun add_constr (nm,constr) cinfo = 
    let 
      val (cnm,nw_constrs) = ConstraintName.NTab.add (nm, constr) (get_constrs cinfo)
    in (cnm, set_constrs cinfo nw_constrs) end;

(* Add a new constraint  *)
fun add_constraint constr cinfo = 
    let 
      val (nw_cnm, cinfo') = 
                add_constr (ThyConstr.default_name, constr) cinfo

      val top_args_of_constr = ArgName.NSet.add_list (ThyConstr.top_args_of_constr constr) 
                               ArgName.NSet.empty
      in
        List.foldl (fn (arg, ci) =>
            update_arg_constrs ci (ArgName.NTab.map_entry (ConstraintName.NSet.add nw_cnm) arg))
            cinfo' (ArgName.NSet.list_of top_args_of_constr)
      end;

(* If we discover commutativity, we should share the constraints between arguments *)
fun update_commute_opt_and_constrs cinfo commutativity =
    let
      fun merge_domains domains merged_dom = 
            case domains of
              [] => merged_dom
            | (dom::ds) => merge_domains ds (ConstantName.NSet.intersect dom merged_dom)

      val merged_dom =
          case (ArgName.NTab.values (get_arg_domains cinfo)) of
            [] => raise ERROR ((ConstantName.dest (get_name cinfo)) ^ 
                        " can't be commutative, has no arguments.")
          | (d::ds) => merge_domains ds d

      (* Need to copy constraints on other args, then modify them so they apply
       to this arg. Might mean we get duplicate constraints, but don't think that
       matters very much apart from the clutter.

       1. figure out which constraints are not on this arg, but on some other.
       2. Modify this constraint to make a new one.
       3 attach to this arg.*)
    (*
      fun commute_constr (to_arg, from_arg) cnm =
          case (lookup_constraint cinfo cnm) of
            NotConst(arg',c) => NotConst(swap_arg (to_arg,from_arg) arg', c) 
          | UnEqual(args) => if (mem (ArgName.name_eq) to_arg args 
                                 andalso mem (ArgName.name_eq) from_arg args) 
                             then UnEqual(args)
                             else (UnEqual(map (swap_arg (to_arg,from_arg)) args))
          | Or(cs) => case (map_filter (commute_constr to_arg from_arg) cs) of 
                        (* FIXME: Figure out sensible stuff supposed to fit here *)
                      | cs' => Or(cs')

      fun copy_constrs arg otherargs =
          let
            val existing_constrs = lookup_arg_constrs cinfo arg 
            val other_constrs = map (lookup_arg_constrs cinfo) other_args
            val new_constrs = map commute_constr other_constrs

      val args = get_argnms cinfo
      val merged_constrs = ConstraintName.NTab (get_arg_constrs cinfo)                
     *)
    in 
      (* if commutative, all args have the same domain *)
      (update_arg_domains (set_commute_opt cinfo (SOME commutativity))
                         (ArgName.NTab.map_all (fn nm => fn d => merged_dom)))
        (* all args also should have the same constraints *)
        (* |>  FIXME: Clearly something missing here too.. *)
    end;



(* Check if a constant is of function type *)
fun is_fn cinfo = 
    let val (argtyps,_) = Term.strip_type (get_typ cinfo)
    in argtyps=[] end;

(* ------------------------------------------------------------*)
(* Creating constant information. *)
(* ------------------------------------------------------------*)

(* ienv must have both vars of ty1 and ty2 *)
  fun could_typ_unify (ty1, ty2) ienv = 
      let val unifs = SOME (TypUnify.unify (ty1,ty2) ienv)
            handle TUNIFY => NONE
            handle TYPE_MATCH => NONE       
      in is_some unifs end;
(* Note: Assumes nothing has been instantiated yet, so we only need
  to rename thigs so they aren't the same as in typ.*)
  fun typ_unify_check ctyp typ avoidenv = 
      if Term.is_TVar typ then true
      else let 
          val (_,finaltyp) = Term.strip_type typ
          val (_,finalctyp) =  Term.strip_type ctyp
          val (renaming, ctyp2) = InstEnv.rename_typ_tvars 
                                 (InstEnv.init_renaming avoidenv) finalctyp
        in
          could_typ_unify (finaltyp, ctyp2) (InstEnv.avoid_of_renaming renaming)
        end;

(* Initialise a constant information with no constraints yet, but with argument domains set. *)
fun mk_constinfo ctxt all_synth_consts (cname,typ) =          
    List.foldl (fn ((arg_ind,atyp), cinfo) =>
                insert_in_arg_dom cinfo 
                                  (arg_ind,
                                   map_filter (fn (cn,cty) => 
                                        if (typ_unify_check cty atyp (InstEnv.init ctxt)) 
                                        then SOME (ConstantName.mk cn) else NONE) 
                                    all_synth_consts)) 
              (empty_cinfo (cname,typ)) 
              (Library.map_index (fn (ind, ty) => (ind, ty)) 
                                 (fst(Term.strip_type typ)));  

(*Assumes the index represent LPO-precedence, and set weights accordingly. *)
fun mk_constinfo' ctxt all_synth_consts (index, (cname,typ)) =
      set_weight (mk_constinfo ctxt all_synth_consts (cname, typ)) (index+1);

end; (*local open *)
end; (* stuct *)

