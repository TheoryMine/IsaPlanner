(* This structure generates an ordering for LPO on the constants in a
theory. To use by IsaCoSy in order to avoid generating equations the
'wrong' way around and avoiding symmetric theorems when the physical size
of the LHS and RHS are the same. *) 

structure OrderTerms = 
struct  
  fun def_in_terms_of ((fnm,fnty),fdefs) =  
      let 
        val rh_sides = map (fn def => 
                               def |> Thm.concl_of
                                   |> Zipper.mktop
                                   |> Subst.move_to_rhs_of_eq
                                   |> Zipper.trm)
                           fdefs
      in ((fnm,fnty), rh_sides) end;
  
  (* FIXME : Make usable as the sort_const_lpo_precf in ConstraintParams,
             which takes a list of constants as input. *)

  (* Sort the constants in a theory. The datatype-constructors are less
  than the function symbols. The datatypes are ordered according to the
  number of arguments they take. The function symbols are ordered such
  that a function f defined in terms of another function g, then f >
  g. If neither (or both) function is defined in
  terms of the other, they are equal in the ordering *)
  
  (* This function returns a list sorted by LPO precedence, with datatype
  constructors are assumed smaller than function symbols. *)
  fun def_order (datatype_consts, fun_defs)  =
      let 
        fun arg_order ((_,t1), (_,t2)) = 
            let val (argtyps1,_) = Term.strip_type t1
                val (argtyps2,_) = Term.strip_type t2
            in int_ord (List.length argtyps1, List.length argtyps2) end;
      
        val sorted_dtyps = Library.sort arg_order datatype_consts
  
        fun fundef_order (((f1,_), rhss1), ((f2,_), rhss2)) =
            if 
              exists (fn rhs1 => 
                         Term.exists_Const (fn (cnm,_) => cnm = f2) rhs1) rhss1
             then 
              if exists (fn rhs2 =>
                            Term.exists_Const (fn (cnm,_) => cnm = f1) rhs2) rhss2
              then EQUAL (* Functions defined by mutual recursion.*)
              else GREATER
            else 
              if exists (fn rhs2 =>
                            Term.exists_Const (fn (cnm,_) => cnm = f1) rhs2) rhss2
              then LESS
              else EQUAL;
  
        val sorted_funs = 
            Library.sort fundef_order (map def_in_terms_of fun_defs);
       (* val num_of_dtyps = length sorted_dtyps *)
      in
        sorted_dtyps @ (map fst sorted_funs)
      (* map_index (fn (ind, (nm,_)) => (nm, ind)) (sorted_dtyps @ (map fst sorted_funs)) *)
      (*  (map_index (fn (ind,(dnm,_)) => (dnm,ind)) sorted_dtyps) 
        @
        (map_index (fn (ind,((fnm,_),_)) => (fnm,ind + num_of_dtyps)) sorted_funs) *)
      end;

  
(* To be used with Term_ord.term_lpo *)
fun constant_order thy_constrs (Const (const,_)) = 
     (case (Constraints.lookup_const thy_constrs (SynthNames.Constant.mk const))
      of NONE => ~1 | SOME const_info => Constraints.get_weight const_info)
  | constant_order _ (Var _) = 0
  | constant_order _ (Free _) = 0
  | constant_order _ (Bound _) = 0
  | constant_order _ _ = ~1 (* This shouldn't be called on _$_ or Abs *) 
  
         
  (* Call this to check if a theorem needs re-orientation. *)
 fun mk_valid_rw precedence thm  =
      case (Rpo.lpo precedence 
                              (ConstraintParams.termrw_of_thm thm)) of
        GREATER => SOME thm (* Valid rewrite rule *)
      | EQUAL => NONE (* Not a valid rewrite rule *)
      | LESS => (* Could be genuinly less, but also return this value for incomparable terms, so check again. *)
               let 
                 (* Try swapping theorem around to see if lhs <-- rhs *)
                 val sym_thm = thm RS (@{thm "sym"})                                         
                 in 
                 case (Rpo.lpo precedence 
                              (ConstraintParams.termrw_of_thm sym_thm)) of
                  GREATER => SOME sym_thm
                  | _ => NONE
                 end;

 (* Use IsaCoSy default precedence stored with the theory constraints for each constant *)
 fun mk_valid_rw_def_prec thy_constrs thm =
     mk_valid_rw (constant_order thy_constrs) thm;
                                        
end;
