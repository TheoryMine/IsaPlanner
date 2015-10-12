(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/basic/dtac_rtechn.ML
    Author:     Moa Johansson, University of Edinburgh
                moa.johansson@ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:
    Reasoning technique wrappers for declarative tactics.
    
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

structure DTacRTechn =
struct

local
open RTechnEnv
in

(* ----------- Apply Auto ----------- *)
fun auto_dtac rst = IsaDTac.auto (RstPP.get_ctxt rst);
fun auto g rst = apply_dtac_to_g (auto_dtac rst) g rst;
fun multi_auto rst = apply_dtac (auto_dtac rst) rst;


(* ----------- Safe Auto ----------- *)
fun safe_dtac rst = IsaDTac.safe (RstPP.get_ctxt rst);
fun safe g rst = apply_dtac_to_g (safe_dtac rst) g rst;
fun multi_safe rst = apply_dtac (safe_dtac rst) rst;


(* --------- Apply simplification ----------*)     
fun simp_only thm g rst = 
    apply_dtac_to_g (IsaDTac.simp_only thm) g rst;

fun simp_asm_full g rst = 
    apply_dtac_to_g (IsaDTac.simp_asm_full (RstPP.get_ctxt rst)) g rst;
fun simp_noasm g rst = 
    apply_dtac_to_g (IsaDTac.simp_no_asm (RstPP.get_ctxt rst)) g rst;

fun simp_noasm_changes g rst = 
    apply_dtac_to_g (IsaDTac.simp_no_asm_changes (RstPP.get_ctxt rst)) g rst;

(* Use, but don't simplify assumptions *)
fun simp_no_asm_simp g rst = 
    apply_dtac_to_g (IsaDTac.simp_no_asm_simp (RstPP.get_ctxt rst)) g rst;

(* As above, also require simp to do something *)
fun simp_no_asm_simp_changes_dtac rst = 
    (IsaDTac.simp_no_asm_simp_changes (RstPP.get_ctxt rst)); 

fun simp_no_asm_simp_changes g rst = 
    apply_dtac_to_g (simp_no_asm_simp_changes_dtac rst) g rst; 

fun multi_simp_no_asm_simp_changes rst = 
    apply_dtac (simp_no_asm_simp_changes_dtac rst) rst;

 (* As above, but only local asumptions *)
(*  fun simp_no_asm_simp_changes_loc g rst = 
    apply_dtac_to_g (IsaDTac.simp_no_asm_simp_changes_loc
               (Simplifier.simpset_of (RstPP.get_theory rst))) g rst;
*)
              
(* Only give simp assumption that don't contain meta-variables. If they
do, it will believe they are universally quantified instead of existentially,
leading to to strong an assumption. This is an intermediate compromise. *)
 fun simp_use_asms_changes goal rst =
    let 
      val ppl = RState.get_pplan rst
     (* get asumptions, excluding ones with meta-vars *)
      (*val asms = map (fn g => 
                         Prf.get_assumed_lthm ppl g)
                     (List.filter 
                        (fn g => null (Term.term_vars 
                                         (RstPP.goal_concl rst g)))
                        (PPlan.get_aasms ppl goal))
       val simps = Simplifier.addsimps 
                    (Simplifier.simpset_of (RstPP.get_theory rst),
                     asms) *)
      val ctxt = RstPP.get_ctxt rst
      val res = (givename 
                 (RstName.str "Simplify using asms (without meta-vars)")
                 (apply_dtac_to_g (IsaDTac.simp_no_asm_simp_changes ctxt) goal)) rst

      (* Adding simplifiers seems to affect global simpset, so delete them afterwards *) 
    (*  val _ = Simplifier.delsimps (Simplifier.simpset_of (RstPP.get_theory rst),
                     asms) *)
    in
      res
    end;
end (*local*)  



end; (* struct *)




(*
fun simp_use_asms goal rst =  
    let 
      val ppl = RState.get_pplan rst
     (* get asumptions, excluding ones with meta-vars *)
      val asms = map (fn g => 
                         Prf.get_assumed_lthm ppl g)
                     (List.filter 
                        (fn g => null (Term.term_vars 
                                         (RstPP.goal_concl rst g)))
                        (PPlan.get_aasms ppl goal))

      (*val asms = map (fn g => 
                         Thm.assume (Thm.cterm_of (PPlan.get_theory ppl) 
                                   (RstPP.goal_concl rst g)))
                   (PPlan.get_aasms (RState.get_pplan rst) goal) *)
      val simps = Simplifier.addsimps 
                    (Simplifier.simpset_of (RstPP.get_theory rst),
                     asms)
    in
      apply_dtac_to_g (IsaDTac.simp_no_asm simps) goal rst
    end;

*)
