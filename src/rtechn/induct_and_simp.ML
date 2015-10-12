(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      induct_and_simp.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Reasoning Techniques - stuff working towards proof planning 
    with hi-proofs.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature INDUCT_AND_SIMP (* RIPPLE_RTECHN *)=
sig
  val simp_and_conj 
      : (PPlan.gname -> RTechn.T) (* technique to prove conjectures after simp *)
        -> RTechn.T
  val induct_and_simp : PPlan.gname -> RTechn.T
  val induct_and_simp_with_rule : PPlan.gname -> xstring -> RTechn.T
end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor InductAndSimpRTechnFUN(ConjRTechn : CONJ_RTECHN)
        : INDUCT_AND_SIMP
= struct
local open RTechnEnv; in

val induct_and_simpN = 
    RstName.str "Solve using Induction and Simplification.";
val induct_and_simp_with_ruleN = 
    RstName.str "Solve using Induction (custom rule) and Simplification.";

fun simp_and_conj lemma_techn = 
    map_then (ConjRTechn.conj_critic
                 lemma_techn
                 DTacRTechn.simp_asm_full);

fun induct_and_simp g rst = 
    refine induct_and_simpN
           (InductRTechn.induction_on_goal 
              g 
              (simp_and_conj induct_and_simp) 
              (simp_and_conj induct_and_simp) )
           rst; 

fun induct_and_simp_with_rule g rule rst = 
    (refine induct_and_simp_with_ruleN
           (InductRTechn.induction_on_goal_with 
              g
              (Proof_Context.get_thm (RState.get_ctxt rst) rule)
              (simp_and_conj induct_and_simp)
              (simp_and_conj induct_and_simp) ))
      rst; 

end; (* RTechnEnv local *) 
end; (* struct *)
