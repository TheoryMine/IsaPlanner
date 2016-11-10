
signature RSTATE_NAMES =
sig
  val basecase_str : string
  val basecase_simp_str : string
  val induct_and_ripple_str : string
  val induction_on_str : string
  val induct_and_ripple_with_rule_str : string
  val strong_fert_str : string
  val weak_fert_start_str : string
  val weak_fert_left_str : string
  val weak_fert_right_str : string
  val end_fert_str : string
  val start_rippling_str : string
  val update_step_str : string
  val end_rippling_str : string
  val solved_by_rippling_str : string
  val stepcase_by_rippling_str : string
  val induct_ripple_lemcalc_str : string
  val resolution_str : string
  val lemcalc_str : string
  val solved_str : string
  val simp_str : string
  val rippling_str : string
end;

structure RStateNames : RSTATE_NAMES =
struct
  val basecase_str = "Start base case"
  val basecase_simp_str = "Base case by simplification"
  val induct_and_ripple_str = "Solve using Induction and Rippling."
  val induction_on_str = "Induction on"
  val induct_and_ripple_with_rule_str = "Solve using Induction (custom rule) and Rippling."
  val strong_fert_str = "Strong fertilisation"
  val weak_fert_start_str = "Weak fertilisation start"
  val weak_fert_left_str = "Weak fertilisation left"
  val weak_fert_right_str = "Weak fertilisation right"
  val end_fert_str = "End fertilisation"
  val start_rippling_str = "Start Rippling"
  val update_step_str = "Ripple Step by"
  val solved_by_rippling_str = "Rippling solves the goal directly"
  val stepcase_by_rippling_str = "Solve the step case using rippling."
  val end_rippling_str = "End rippling"
  val induct_ripple_lemcalc_str = "Induct, Ripple and LemCalc"
  val resolution_str = "Resolution"
  val lemcalc_str = "Proving goal"
  val solved_str = "Solved!"
  val simp_str = "simp"
  val rippling_str = "End rippling on goal"
end;