(* This structure generates an ordering for LPO on the constants in a
theory. To use by IsaCoSy in order to avoid generating equations the
'wrong' way around and avoiding symmetric theorems when the physical size
of the LHS and RHS are the same. *) 

structure OrderTerms = 
struct  

(* To be used with Term_ord.term_lpo *)
fun constant_order thy_constrs (Const (const,_)) = 
     let 
       val const_info = TheoryConstraints.lookup_const thy_constrs 
                                                       (SynthNames.ConstantName.mk const)
     in (ConstInfo.get_weight const_info) end
  | constant_order _ (Var _) = 0
  | constant_order _ (Free _) = 0
  | constant_order _ (Bound _) = 0
  | constant_order _ _ = ~1 (* This shouldn't be called on _$_ or Abs *) 

   
  (* Call this to check if a theorem needs re-orientation. *)
 fun mk_valid_rw precedence thm  =
     case (ConstraintParams.termrw_of_thm thm) of
       SOME equality => 
       (case (Rpo.lpo precedence equality) of
          GREATER => SOME thm (* Valid rewrite rule *)
        | EQUAL => NONE (* Not a valid rewrite rule *)
        | LESS => (* Could be genuinly less, but also return this value for incomparable terms, so check again. *)
          let 
            (* Try swapping theorem around to see if lhs <-- rhs *)
            val sym_thm = thm RS (@{thm "sym"})                                         
          in 
            case (Rpo.lpo precedence 
                          (the (ConstraintParams.termrw_of_thm sym_thm))) of
              GREATER => SOME sym_thm
            | _ => NONE
          end)
     | NONE => NONE;

 fun is_valid_rw thy_constrs thm = 
     case (ConstraintParams.termrw_of_thm thm) of 
       SOME equality => 
       (case (Rpo.lpo (constant_order thy_constrs) equality) of
          GREATER => true (* Valid rewrite rule *)
        | _ => false) (* Not a valid rewrite rule *)
     | NONE => false

fun mk_valid_rw_trm precedence trm = 
     case (ConstraintParams.termrw_of_term trm) of
      SOME (l,r) => 
      (case (Rpo.lpo precedence (l,r)) of
         GREATER => SOME trm (* Valid rewrite rule *)
       | EQUAL => NONE (* Not a valid rewrite rule *)
       | LESS => (* Could be genuinly less, but also return this value for incomparable terms, so check again. *)
         case (Rpo.lpo precedence (r,l)) of
           GREATER => SOME (HOLogic.mk_eq (r,l))
         | _ => NONE
      )
    | NONE => NONE;

fun is_valid_rw_trm thy_constrs trm =
    case (ConstraintParams.termrw_of_term trm) of
      SOME eq =>  
       (case (Rpo.lpo (constant_order thy_constrs) eq) of
          GREATER => true (* Valid rewrite rule *)
        | _ => false) (* Not a valid rewrite rule *)
     | NONE => false

 (* Use IsaCoSy default precedence stored with the theory constraints for each constant *)
 fun mk_valid_rw_def_prec thy_constrs thm =
     mk_valid_rw (constant_order thy_constrs) thm;
 
(* Use IsaCoSy default precedence stored with the theory constraints for each constant *)
 fun mk_valid_rw_def_prec_trm thy_constrs trm =
     mk_valid_rw_trm (constant_order thy_constrs) trm;
                                              
end;
