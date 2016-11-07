(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      cinfo/htrace/rst_name.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    created:    30 Jun 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Little library for more easily naming reasoning states 

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature RST_NAME =
sig
type T
val str : string -> T
val pretty : Pretty.T -> T
val block : T list -> T
val chunks : T list -> T
val append_block : T -> T -> T
val prepend_block : T -> T -> T
val append_chunks : T -> T -> T 
val prepend_chunks : T -> T -> T 
(*val dmeth : DMethod.T -> T
val by_dmeth : DMethod.T -> T
*)
val dtac : DTac.T -> T
val by_dtac : DTac.T -> T
val term : Term.term -> T
val named_term : string -> Term.term -> T
val f : (RState.T -> Pretty.T) -> T
val apply : T -> RState.T -> Pretty.T

(* specific names *)
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

  val basecaseN : T
  val basecase_simpN : T
  val induct_and_rippleN : T
  val induction_onN : T
  val induct_and_ripple_with_ruleN : T
  val strong_fertN : T
  val weak_fert_startN : T
  val weak_fert_leftN : T
  val weak_fert_rightN : T
  val end_fertN : T
  val start_ripplingN : T
  val update_stepN : T
  val solved_by_ripplingN : T
  val stepcase_by_ripplingN : T
  val end_ripplingN : T
  val induct_ripple_lemcalcN : T
  val resolutionN : T
  val lemcalcN : T
  val solvedN : T
  val simpN : T
  val ripplingN : T
end;

structure RstName : RST_NAME =
struct
type T = RState.T -> Pretty.T

(* break up words *)
fun pretty_words s = 
    Pretty.block (map Pretty.str 
                      (Library.separate " " (space_explode " " s)));

(* note cunning trick to evalute pretty words directly but still
return a function. The idea is to use this function when writing
techniques as values, thus the prettifying of words is directly
evaluated at compile time instead of runtime. *)
fun str s = let val p = pretty_words s in (fn _ => p) end;
fun pretty p = K p;

fun block dl rst = Pretty.block (map (fn f => f rst) dl);
fun chunks dl rst = Pretty.chunks (map (fn f => f rst) dl);

fun append_block d' d rst = Pretty.block [d rst, d' rst];
fun prepend_block d' d rst = Pretty.block [d' rst, d rst];
fun append_chunks d' d rst = Pretty.block [d rst, d' rst];
fun prepend_chunks d' d rst = Pretty.block [d' rst, d rst];

(* prettying methods *)
(*fun dmeth dmeth rst =
    DMethod.pretty_of dmeth ((Proof.context_of o PPlan.top_pst_of o 
                              RState.get_pplan) rst);

fun by_dmeth m rst = 
    Pretty.block [Pretty.str " by ",
                  Pretty.enclose "(" ")" 
                                 [dmeth m rst]];
*)
fun dtac dtac rst =
    DTac.pretty dtac (RState.get_ctxt rst);

fun by_dtac dtac rst = 
    Pretty.block [Pretty.str " by ",
                  Pretty.enclose "(" ")" 
                                 [DTac.pretty dtac (RState.get_ctxt rst)]];
(* pretty function for the term in context of rst *)
fun term t rst = PPlan.pretty_term (RState.get_pplan rst) t;

fun named_term s t rst =
    Pretty.block [pretty_words s,
                  Pretty.quote (term t rst)];

val f = I;

fun apply pf rst = pf rst;

(* specific names, for universal id. Changing this may break NLProof *)
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


  val basecaseN = str basecase_str
  val basecase_simpN = str basecase_simp_str
  val induct_and_rippleN = str induct_and_ripple_str
  val induction_onN = str induction_on_str
  val induct_and_ripple_with_ruleN = str induct_and_ripple_with_rule_str
  val strong_fertN = str strong_fert_str
  val weak_fert_startN = str weak_fert_start_str
  val weak_fert_leftN = str weak_fert_left_str
  val weak_fert_rightN = str weak_fert_right_str
  val end_fertN = str end_fert_str
  val start_ripplingN = str start_rippling_str
  val update_stepN = str update_step_str
  val solved_by_ripplingN = str solved_by_rippling_str
  val stepcase_by_ripplingN = str stepcase_by_rippling_str
  val end_ripplingN = str end_rippling_str
  val induct_ripple_lemcalcN = str induct_ripple_lemcalc_str
  val resolutionN = str resolution_str
  val lemcalcN = str lemcalc_str
  val solvedN = str solved_str
  val simpN = str simp_str
  val ripplingN = str rippling_str
  
end;
