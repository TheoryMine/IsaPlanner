(*  Title:      util/isa_planner.ML
    ID:         $Id: isa_planner.ML,v 1.010 2009/06/12 19:07:00 omar Exp $
    Author:     Omar Montano Rivas, University of Edinburgh School of Informatics
    Copyright   University of Edinburgh 2009

This file provides a wrapper for the inductive prover IsaPlanner.
*)

signature ISA_PLANNER_WRAPPER =
sig
val rtechT_ref          : RState.rtechn option Unsynchronized.ref
end

structure DB_IsaP_Wrapper
(* : ISA_PLANNER_WRAPPER *)
= struct

(*val induction_schemes = Unsynchronized.ref ([]:string list)

fun induct_rules thy prop = 
    let
      val ind_frees = [] |> Term.add_frees prop
                         |> map snd
                         |> make_type_set
                         |> map_filter (fn ty => SOME (Term.dest_Type ty) handle TYPE _ => NONE)
                         |> map fst
                         |> make_string_set
                         |> map_filter (fn c => SOME (c ^ ".induct",(Global_Theory.get_thm thy (c ^ ".induct"))) handle ERROR _ => NONE)
                         |> map fst
      val ind_consts = [] |> Term.add_consts prop
                          |> map fst
                          |> make_string_set
                          |> map_filter (fn c => SOME (c ^ ".induct", Global_Theory.get_thm thy (c ^ ".induct")) handle ERROR _ => NONE)
                          |> map fst
    in
      (ind_frees,ind_consts)
    end*)


local open RTechnEnv in

(* simplify then safe then induct and ripple *)
fun proof_techn g = 
    ((DTacRTechn.simp_noasm g)
       try1_then 
       (rstif RstPP.solved_all_chk
              (dummy_str "Solved by Simp")
              (DTacRTechn.multi_safe 
                 try1_then 
                 (map_then RippleLemCalc.induct_ripple_lemcalc))))

fun induct_ripple_lemcalc_with_rules rules g =
    case rules of
      hrule :: trules => (tracing hrule;(RippleLemCalc.induct_ripple_lemcalc_with_rule g hrule)
                           try1_then
                           (rstif RstPP.solved_all_chk
                                  (dummy_str "Solved by Simp")
                                  (induct_ripple_lemcalc_with_rules trules g)))
    | _ => RTechnComb.fail

end

val wrule_add = Thm.declaration_attribute WRulesGCtxt.add_wrule_thm
val wrule_del = Thm.declaration_attribute WRulesGCtxt.del_wrule_thm

val wrule_modifiers' =
    [Args.add -- Args.colon >> K (I, wrule_add),
     Args.del -- Args.colon >> K (I, wrule_del)]

(* This part is supposed to parse a rtech *)
(* FIXME: parse different reasoning techniques *)
fun parse_proof_checks xs = 
(Args.$$$ "solved_all_chk" >> K RstPP.solved_all_chk
|| Args.$$$ "solved_focusgoals" >> K RstPP.solved_focusgoals) xs
fun parse_with_goal xs = 
(Args.$$$ "induct_ripple_lemcalc" >> K RippleLemCalc.induct_ripple_lemcalc
(*|| Args.$$$ "induct_ripple_lemcalc_rules" >> K (induct_ripple_lemcalc_with_rules (!induction_schemes))*)
|| Args.$$$ "auto" >> K DTacRTechn.auto
|| Args.$$$ "safe" >> K DTacRTechn.safe
|| Args.$$$ "simp_asm_full" >> K DTacRTechn.simp_asm_full
|| Args.$$$ "simp_noasm" >> K DTacRTechn.simp_noasm
|| Args.$$$ "simp_noasm_changes" >> K DTacRTechn.simp_noasm_changes
|| Args.$$$ "simp_no_asm_simp" >> K DTacRTechn.simp_no_asm_simp
|| Args.$$$ "simp_no_asm_simp_changes" >> K DTacRTechn.simp_no_asm_simp_changes
|| Args.$$$ "simp_use_asms_changes" >> K DTacRTechn.simp_use_asms_changes) xs
fun parse_basic xs = 
(Args.$$$ "multi_auto" >> K DTacRTechn.multi_auto
|| Args.$$$ "multi_safe" >> K DTacRTechn.multi_safe
|| Args.$$$ "multi_simp_no_asm_simp_changes" >> K DTacRTechn.multi_simp_no_asm_simp_changes
|| Args.$$$ "fail" >> K RTechnComb.fail
|| Args.$$$ "map_then" |-- parse_with_goal >> RTechnEnv.map_then
|| Args.$$$ "try_map_then" |-- parse_with_goal >> RTechnEnv.try_map_then
|| Args.$$$ "dummy_str" |-- Parse.string >> RTechnComb.dummy_str
|| Args.parens parse_ternary) xs
and parse_unary xs = 
(Args.$$$ "repeat" |-- parse_unary >> RTechnComb.repeat
|| Args.$$$ "solve_or_fail" |-- parse_unary >> RTechnComb.solve_or_fail
|| Args.$$$ "solve_or_nothing" |-- parse_unary >> RTechnComb.solve_or_nothing
|| parse_basic) xs
and parse_binary xs = 
(parse_unary --| Args.$$$ "branchfail_critic" -- parse_binary >> uncurry RTechnComb.branchfail_critic
|| parse_unary --| Args.$$$ "repeat_then" -- parse_binary >> uncurry RTechnComb.repeat_then
|| parse_unary --| Args.$$$ "orr" -- parse_binary >> RTechnComb.orr
|| parse_unary --| Args.$$$ "thenr" -- parse_binary >> RTechnComb.thenr
|| parse_unary --| Args.$$$ "try1_orelse" -- parse_binary >> RTechnComb.try1_orelse
|| parse_unary --| Args.$$$ "try1_then" -- parse_binary >> RTechnComb.try1_then
|| parse_unary) xs
and parse_ternary xs = 
(Args.$$$ "rstif" |-- parse_proof_checks -- parse_binary -- parse_ternary >> (fn ((chk,rt1),rt2) => RTechnComb.rstif chk rt1 rt2)
|| parse_binary) xs

val rtech_options =
 (Args.parens parse_ternary ||
(*  Scan.succeed (RippleLemCalc.induct_ripple_lemcalc "g")*)
Scan.succeed (RTechnEnv.map_then RippleLemCalc.induct_ripple_lemcalc))

(* ML support for RState.rtechn *)
val rtechT_ref = Unsynchronized.ref NONE : RState.rtechn option Unsynchronized.ref
fun rtechT_ml_parser (context,tok) = 
    (Scan.lift (Args.parens (Parse.position Args.name)) >> 
               (fn (txt,pos) => (ML_Context.eval_text_in 
                                  (SOME (Context.proof_of context)) false pos 
                                  ("IsaP_Wrapper.rtechT_ref := SOME (" ^ txt ^ ")"); the (!rtechT_ref))))
               (context,tok);

(* was: ML_Context.evaluate (Context.proof_of context) false ("IsaP_Wrapper.rtechT_ref",rtechT_ref) txt)) *)

(*val rtech_options =
 (Args.parens (Args.$$$ "induct_lemcalc") >> K (RippleLemCalc.induct_ripple_lemcalc "g") ||
  Scan.succeed (RippleLemCalc.induct_ripple_lemcalc "g"))*)

val strategy_options =
 (Args.parens (Args.$$$ "bfs") >> K PPInterface.breadth_fs ||
  Args.parens (Args.$$$ "dfs") >> K PPInterface.depth_fs ||
  Scan.succeed PPInterface.depth_fs)

fun ripple_tac ctxt rtech strategy (conjecture,i) = 
    let 
      val g = "g"
(*      val conjecture' = if Term.fastype_of conjecture = HOLogic.boolT then HOLogic.mk_Trueprop conjecture else conjecture*)
(*      val _ = induction_schemes := (op @) (induct_rules (ProofContext.theory_of ctxt) conjecture)*)
			val (init_goal,pp) = PPlan.conj_term_at_top (g,conjecture) (PPlan.init ctxt)
  in
  case
  (RState.init_from_pp pp)
	  |> RState.set_goalnames [init_goal]
    |> RState.set_rtechn (SOME rtech)
    |> strategy
    |> Seq.pull
  of 
  NONE => no_tac
  | SOME (rst, moreproofs) => simp_tac (HOL_basic_ss addsimps [RstPP.result_thm rst g]) i
  end

fun rippling_method meth =
(*  Args.bang_facts --*) (rtechT_ml_parser || Scan.lift rtech_options) -- Scan.lift strategy_options --|
    Method.sections wrule_modifiers' >>
    (fn (((*prems, *)rtech), strategy) => fn ctxt => METHOD (fn facts => meth ctxt ((*prems @ *)facts) (SUBGOAL (ripple_tac ctxt rtech strategy))))

val method_setup =
  Method.setup (Binding.name "rippling")
    (rippling_method (fn ctxt => fn facts => fn tac =>
      HEADGOAL (Method.insert_tac facts THEN' tac)))
    "rippling [(rtech_opt)] [(strategy_opt)] [add: rules] [del: rules]"

(* theory setup *)

val _ = Context.>> (Context.map_theory method_setup)

end

structure IsaP_Wrapper : ISA_PLANNER_WRAPPER = DB_IsaP_Wrapper
