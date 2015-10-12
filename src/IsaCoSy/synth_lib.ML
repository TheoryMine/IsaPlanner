(* Assorted library functions for IsaCoSy *) 

structure SynthLib = 
struct

(* Check if a hole is in the LHS of an equation *)
fun is_hole_in_lhs hole_nm trm =
    let 
      val z = Zipper.mktop trm 
    in
     case (Subst.opt_move_to_lhs_of_eq z) of
       SOME lhs =>
       lhs
         |> ZipperSearch.leaves_lr 
         |> Seq.list_of
         |> List.find (fn z => 
                          let val t = Zipper.trm z 
                          in 
                            if (Term.is_Var t) then 
                              fst (Term.dest_Var t) = hole_nm
                            else false
                          end)
         |> is_some
     | NONE => false
    end;

(* Check if a hole is in the RHS of an equation *)
fun is_hole_in_rhs hole_nm trm =
    let 
      val z = Zipper.mktop trm 
    in
     case (Subst.opt_move_to_rhs_of_eq z) of
       SOME rhs =>
       rhs
         |> ZipperSearch.leaves_lr 
         |> Seq.list_of
         |> List.find (fn z => 
                          let val t = Zipper.trm z 
                          in 
                            if (Term.is_Var t) then 
                              fst (Term.dest_Var t) = hole_nm
                            else false
                          end)
         |> is_some
     | NONE => false
    end;


(* Library function to separate a list, and map a function over one partition at the same time. *)
fun map_partition_aux _ [] (l1,l2) = (l1,l2)
  | map_partition_aux f (h::t) (l1,l2) =
    case (f h) of
      NONE => map_partition_aux f t (l1, h::l2)
    | SOME h' => map_partition_aux f t (h'::l1, l2);

fun map_partition f xs = map_partition_aux f xs ([],[]);



(* Check if this is a commutativity theorem for a binary function.*)
(* In the future, generalise this to cover commutativity in general.*)
fun tryget_commutative_symbol_of_term_eq (lhs,rhs) = 
      let val (lhs_f, lhs_args) = Term.strip_comb lhs
          val (rhs_f, rhs_args)  = Term.strip_comb rhs
      in if (Term.is_Const lhs_f andalso lhs_f = rhs_f) 
         then
           (case (lhs_args, rhs_args) of 
              ([a1, a2], [b1, b2]) => 
                 if (a1 = b2 andalso a2 = b1)
                 then SOME (fst (Term.dest_Const lhs_f)) else NONE
               | _ => NONE)
         else NONE
      end;

fun is_commutativity_trm t = 
    let 
      val z = Zipper.mktop t
      val lhs_t = (Subst.move_to_lhs_of_eq z) |> Zipper.trm
      val rhs_t = (Subst.move_to_rhs_of_eq z) |> Zipper.trm
      val commute_fun = tryget_commutative_symbol_of_term_eq (lhs_t,rhs_t)
    in
      case commute_fun of
        SOME const => SOME (const,t)
      | NONE => NONE
      end handle Eq_LData_HOL.bad_term_exp _ => NONE;

fun is_commutativity thm = 
    is_commutativity_trm (Thm.concl_of thm);
end;
