(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Multfert version of lemcalc.ML                                     *)
(*  Author: Daniel Raggi, Lucas Dixon, Moa Johansson                   *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature RIPPLE_MULTFERT_LEMCALC =
sig

structure RippleMultfert : RIPPLE_MULTFERT
  
val induct_ripple_multfert_lemcalc : PPlan.gname -> RTechn.T

end;

(* structure RippleLemCalc *)
functor RippleMultfertLemCalcFUN (structure RippleMultfert : RIPPLE_MULTFERT) 
: RIPPLE_MULTFERT_LEMCALC
= struct

structure RippleMultfert = RippleMultfert;
structure RippleCInfo = RippleMultfert.RippleCInfo;

local 
  open RTechnEnv; 
in

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Induction and Rippling with Lemma Calc                             *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* Interface for rippling *)
fun simp_or_calc g = 
    (solve_or_nothing (DTacRTechn.simp_noasm g))
    try1_orelse 
    (ConjRTechn.prove_goal_by_lemma induct_ripple_multfert_lemcalc g)

and multfert_calc g = 
    (RippleMultfert.weak_multfert_goal g)
     thenr (map_then simp_or_calc)

(* only with lemma calc *)
and endr_multfert_lemcalc rst = 
    rstif (null o RState.get_goalnames)
          (dummy RstName.solved_by_ripplingN)
          (split_then (RippleCInfo.success_chk rst) 
                      (map_then RippleMultfert.BasicRipple.strong_fert_goal)
                      (map_then multfert_calc))              
      rst

and ripple_stepcase_multfert_lemcalc g rst = 
      (refine RstName.stepcase_by_ripplingN
              ((RippleMultfert.BasicRipple.startr_on_goal g)
                 thenr (RippleMultfert.BasicRipple.rsteps_on_goal g)
                 thenr endr_multfert_lemcalc))
               rst

and induct_ripple_multfert_lemcalc g rst = 
    (refine (RstName.induct_ripple_lemcalcN g)
            (InductRTechn.induction_on_goal g
               (map_then (fn s => refine (RstName.basecaseN) 
                                    (ConjRTechn.conj_critic induct_ripple_multfert_lemcalc 
                                     RippleMultfert.BasicRipple.simplify_basecase s)
                         )
               )
               (map_then ripple_stepcase_multfert_lemcalc)
            )
     ) rst;

end (* local *)

end; (* struct *)