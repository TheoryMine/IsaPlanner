(* Structure for keeping track of theory constraints, associated with constants. *)

structure TheoryConstraints = 
struct

local open SynthNames in

exception missing_constant of string

type T = ConstInfo.T ConstantName.NTab.T;
fun pretty ctxt = ConstantName.NTab.pretty (ConstInfo.pretty_constinfo ctxt);
val print = Pretty.writeln oo pretty;

fun lookup_const_opt thy_constrs const = 
      ConstantName.NTab.lookup thy_constrs const;
fun lookup_const thy_constrs const = the (lookup_const_opt thy_constrs const)
                  handle Option => raise missing_constant ("Constant "^(ConstantName.dest const)^ 
                                                           " does not have a constInfo entry.")
(* Update an entry for a constant in the theory constraints *)
fun update_thy_constrs nw_constInfo thy_constrs =
      ConstantName.NTab.update ((ConstInfo.get_name nw_constInfo), nw_constInfo) thy_constrs;

(* Check if this constant is of function type *)
fun is_fn thy_constrs const = ConstInfo.is_fn (lookup_const thy_constrs const);

(* Return the constants occuring in thyConstrs that match typ *)   
fun get_consts_of_typ typ thyConstrs = 
    if (Term.is_TVar typ) 
    then ConstantName.NTab.keys thyConstrs
    else map_filter (fn (cnm,cinfo) => if (Trm.eq_typ ((ConstInfo.get_typ cinfo), typ))
                                  then SOME cnm else NONE)
                    (ConstantName.NTab.list_of thyConstrs)



(* ------------------------------------------------------------*)
(* Initialising the theory constraints.   *)
(* ------------------------------------------------------------*)

          
  (* Constraints are only generated if t is an application, 
     otherwise the constraint term isn't considered interesting.
     Constraint generation does not support terms containing HO variables applied
     to arguments, e.g. things like ?F a b c. *)
fun mk_thy_constrs_from_trm t thy_constrs =
      case t of 
       (_$_) =>
        let
          val (hdtrm, _) = Term.strip_comb t
          in
          (case hdtrm of (Const(nm,_)) =>
            let 
              val c_nm = ConstantName.mk nm               
              val cinfo = lookup_const thy_constrs c_nm
              val uneq_constrs = ThyConstr.mk_UnEqual_constrs t
              val notConst_constrs = ThyConstr.mk_NotConst_constrs t
              val all_constrs = notConst_constrs @ uneq_constrs

              (* Remove cnm from all domains of any constants *)
              fun delete_from_domains del_cnm (_, cinfo) thy_constrs' = 
                update_thy_constrs (ConstInfo.del_from_all_arg_doms cinfo del_cnm) 
                                  thy_constrs'
              in
              (case all_constrs 
                  of [] => ConstantName.NTab.fold (delete_from_domains c_nm) thy_constrs thy_constrs
                    (* Just a single constraint, remove from domain if its a NotConst. *)
                     | [constr] =>
                       (case constr of 
                          ThyConstr.NotConst(p,c) => 
                          let val arg = the (ThyConstr.path_to_arg p)
                          in  
                            update_thy_constrs 
                              (ConstInfo.del_from_arg_dom cinfo (arg, c)) 
                              thy_constrs
                          end
                        | c => update_thy_constrs (ConstInfo.add_constraint c cinfo) thy_constrs
                       )
                     | (c::cs) => update_thy_constrs 
                                    (ConstInfo.add_constraint (ThyConstr.Or (c::cs)) cinfo)
                                    thy_constrs
               ) end
         | _ => raise ThyConstr.mk_constr_exp (t,
              "Does not support constraint generation from terms without a Const in head position.")
         ) end 
      | _ => thy_constrs (* No constraints to generate *)



(* Check if equation represents commutativity *)
(*fun try_mk_commutativity_constr (lhs,rhs) thy_constrs = 
    case tryget_commutative_symbol_of_term_eq (lhs,rhs) of
         SOME (const_nm,_) => 
         update_thy_constrs (ConstInfo.set_commute_opt 
                               (lookup_const thy_constrs (ConstantName.mk const_nm))
                               (SOME (HOLogic.mk_eq(lhs,rhs))))                                             
                            thy_constrs 
       | NONE => thy_constr;
*)
(* Set the commutativity option. Users responsibility to have checked this is a commuteativity thm *)
fun mk_thy_constrs_from_commutativity (const_nm,trm) thy_constrs =
    update_thy_constrs (ConstInfo.set_commute_opt 
                          (lookup_const thy_constrs (ConstantName.mk const_nm))
                          (SOME trm)) 
                       thy_constrs;

  (* Update constraints from a pair of terms corresponding to an equation/rewrite rule.
     It's the users responsibility to not pass in non-valid rw rules. *)
 fun mk_thy_constrs_from_eq  (lhs,rhs) thy_constrs =
     mk_thy_constrs_from_trm lhs thy_constrs
(*
      (case tryget_commutative_symbol_of_term_eq (lhs,rhs) of
         SOME (const_nm,_) => 
         update_thy_constrs (ConstInfo.set_commute_opt 
                               (lookup_const thy_constrs (ConstantName.mk const_nm))
                               (SOME (HOLogic.mk_eq(lhs,rhs))))                                             
                            thy_constrs 
       | NONE => mk_thy_constrs_from_trm lhs thy_constrs);
*)

 (* Also sets the LPO precedence in const-info. synth_consts are the constants
    IsaCoSy is allowed to use during synthesis (typically excluding for instance = 
    as we only want that on the top-level once). These must be a subset of all_consts. *)
  fun init' ctxt (all_consts,synth_consts, eqs, commute_funs, arb_trms, sort_constsf) =
      let 
        val constinfos = map_index (ConstInfo.mk_constinfo' ctxt synth_consts)
                                                     (sort_constsf all_consts)
      in  
      ConstantName.NTab.empty
          |> fold update_thy_constrs constinfos
          |> fold mk_thy_constrs_from_eq eqs
          |> fold mk_thy_constrs_from_trm arb_trms
          |> fold mk_thy_constrs_from_commutativity commute_funs

      end;

  fun init ctxt cparams =
      init' ctxt (Symtab.dest (ConstraintParams.get_cconsts cparams), 
                  Symtab.dest (ConstraintParams.get_consts cparams), 
                  ConstraintParams.get_termrws cparams,
                  ConstraintParams.get_commute_trms cparams,
                  ConstraintParams.get_constr_trms cparams,
                  ConstraintParams.get_sort_lpo_precf cparams);

end (* local open *)
end; (* struct *)
