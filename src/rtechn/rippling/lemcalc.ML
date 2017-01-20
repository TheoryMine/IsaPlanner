signature RIPPLE_LEMCALC =
sig

structure BasicRipple : BASIC_RIPPLE

val induct_ripple_lemcalc : PPlan.gname -> RTechn.T
val induct_ripple_lemcalc_with_rule : PPlan.gname ->  xstring -> RTechn.T

end;


(* structure RippleLemCalc *)
functor RippleLemCalcFUN (structure BasicRipple : BASIC_RIPPLE) 
: RIPPLE_LEMCALC
= struct

structure BasicRipple = BasicRipple;
structure RippleCInfo = BasicRipple.RippleCInfo;

local 
  open RTechnEnv;
in



val induct_and_ripple_lemcalcN = 
    RstName.str "Solve using Induction, Rippling and Lemma Calculation.";
val induct_and_ripple_with_ruleN = 
    RstName.str "Solve using Induction (custom rule), Rippling and Lemma Calculation.";
val solved_by_ripplingN = 
    RstName.str "Rippling solves the goal directly";
val stepcase_by_ripplingN = 
    RstName.str "Solve the step case using rippling.";

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Induction and Rippling with Lemma Calc                             *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


fun simp_or_calc g = 
    (solve_or_nothing (DTacRTechn.simp_noasm g))
    try1_orelse 
    (ConjRTechn.prove_goal_by_lemma induct_ripple_lemcalc g)

and fert_calc g = 
    (BasicRipple.weak_fert_goal g)
     thenr (map_then simp_or_calc)

(* only with lemma calc *)
and endr_lemcalc rst = 
    rstif (null o RState.get_goalnames)
          (dummy RstName.solved_by_ripplingN)
          (split_then (RippleCInfo.success_chk rst) 
                      (map_then BasicRipple.strong_fert_goal)
                      (map_then fert_calc))              
      rst

and ripple_stepcase_lemcalc g rst = 
      (refine RstName.stepcase_by_ripplingN
              ((BasicRipple.startr_on_goal g)
                 thenr (BasicRipple.rsteps_on_goal g)
                 thenr endr_lemcalc))
               rst

and induct_ripple_lemcalc g rst = 
  (*  (CounterExCInfo.quickcheck_concl g rst)
      |> (if CounterExCInfo.has_counterex g rst 
          then fail
          else *)
            (refine (RstName.induct_ripple_lemcalcN g)
                    (InductRTechn.induction_on_goal g
                       (map_then (fn s => refine (RstName.basecaseN) 
		                     (ConjRTechn.conj_critic induct_ripple_lemcalc 
		                      BasicRipple.simplify_basecase s)))
                       (map_then ripple_stepcase_lemcalc))) rst;

(* given explicit rule for first induction *)
fun induct_ripple_lemcalc_with_rule g rule rst= 
    (refine induct_and_ripple_with_ruleN
           (InductRTechn.induction_on_goal_with g 
              (Proof_Context.get_thm (RState.get_ctxt rst) rule)
              (map_then (ConjRTechn.conj_critic induct_ripple_lemcalc 
                                     BasicRipple.simplify_basecase))
              (map_then induct_ripple_lemcalc))) 
           rst;   


end (* local *)

end; (* struct *)
