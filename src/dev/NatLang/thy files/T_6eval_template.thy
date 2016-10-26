theory T_6
imports IsaP 
uses "../myrippling.ML"
begin

datatype "T_6" =  "C_12" "T_6" "HOL.bool"  | "C_11" "HOL.bool" "HOL.bool"  
declare nat.inject[wrule]
declare T_6.inject[wrule]

fun f_0 :: "T_6 => nat => nat" where
  "f_0 (C_11 a b) c = c"
| "f_0 (C_12 a b) c = Suc (f_0 a c)"

fun f_1 :: "T_6 => nat => nat" where
  "f_1 (C_11 a b) c = Suc c"
| "f_1 (C_12 a b) c = Suc (Suc (f_1 a (Suc c)))"

fun f_2 :: "T_6 => nat => nat" where
  "f_2 (C_11 a b) c = Suc (Suc c)"
| "f_2 (C_12 a b) c = Suc (f_2 a (Suc (f_2 a c)))"

fun f_3 :: "T_6 => nat => nat" where
  "f_3 (C_11 a b) c = Suc (Suc (Suc c))"
| "f_3 (C_12 a b) c = Suc (Suc (f_3 a (f_3 a (Suc c))))"

fun f_4 :: "T_6 => nat => nat" where
  "f_4 (C_11 a b) c = Suc (Suc (Suc (Suc (Suc c))))"
| "f_4 (C_12 a b) c = f_4 a (f_4 a (Suc c))"

fun f_5 :: "T_6 => nat => nat" where
  "f_5 (C_11 a b) c = Suc (Suc (Suc (Suc (Suc (Suc c)))))"
| "f_5 (C_12 a b) c = f_5 a (Suc (Suc (f_5 a (Suc c))))"

fun f_6 :: "T_6 => nat => nat" where
  "f_6 (C_11 a b) c = Suc (Suc (Suc (Suc (Suc (Suc (Suc c))))))"
| "f_6 (C_12 a b) c = Suc (f_6 a (Suc c))"

declare f_0.simps[wrule]
declare f_1.simps[wrule]
declare f_2.simps[wrule]
declare f_3.simps[wrule]
declare f_4.simps[wrule]
declare f_5.simps[wrule]
declare f_6.simps[wrule]

ML{*
val openconjs = [
 (* lemmas proven without my work: *)
"f_0 a (f_0 b c) = f_0 b (f_0 a c)",
"f_0 a (Suc b) = Suc (f_0 a b)",
"Suc (f_0 a b) = f_0 a (Suc b)",
"f_1 a (Suc b) = Suc (f_1 a b)",
"Suc (f_1 a b) = f_1 a (Suc b)",
"f_6 a (Suc b) = Suc (f_6 a b)",
"Suc (f_6 a b) = f_6 a (Suc b)",

 (* open conjectures for function: f_1*)
"f_1 a (f_1 b c) = f_1 b (f_1 a c)",
"f_1 a (Suc 0) = Suc (f_1 a 0)",

 (* open conjectures for function: f_2*)
"f_2 a (f_2 b c) = f_2 b (f_2 a c)",
"f_2 a (f_2 b 0) = f_2 b (f_2 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))",(*mult fert; breadth first needed to prevent inf lemma conj*)
"Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))",(*gen; success will lead to mult fert. Another path leads to a failure to fertilise*)
"Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))",(*gen; success leads to mult fert. Another path leads to mult fert; this means that breadth first might be helpful*)
"f_2 a (Suc b) = Suc (f_2 a b)",(*failure to fertilise; success will lead to mult fert*)
"f_2 a (Suc 0) = Suc (f_2 a 0)",(*failure to fertilise; success will lead to mult fert*)


 (* open conjectures for function: f_3*)
"f_3 a (f_3 b c) = f_3 b (f_3 a c)",(*mult fert*)
"f_3 a (f_3 b 0) = f_3 b (f_3 a 0)",(*doesn't ripple*)
"Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))",(*case in which a 'borrowing fertilisation' (multiple) would solve the problem; otherwise it leads to inf lemma calc *) 
"Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"f_3 a (Suc b) = Suc (f_3 a b)",(*mult fert*)
"f_3 a (Suc 0) = Suc (f_3 a 0)",(*doesn't ripple*)

 (* open conjectures for function: f_4*)
"f_4 a (f_4 b c) = f_4 b (f_4 a c)",(*mult fert*)
"f_4 a (f_4 b 0) = f_4 b (f_4 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"f_4 a (Suc b) = Suc (f_4 a b)",(*mult fert*)
"f_4 a (Suc 0) = Suc (f_4 a 0)",(*gen; success will lead to mult fert*)

 (* open conjectures for function: f_5*)
"f_5 a (f_5 b c) = f_5 b (f_5 a c)",(*mult fert*)
"f_5 a (f_5 b 0) = f_5 b (f_5 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"f_5 a (Suc b) = Suc (f_5 a b)",(*fails to fertilise; success would lead to mult fert*)
"f_5 a (Suc 0) = Suc (f_5 a 0)",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)


 (* open conjectures for function: f_6*)
"f_6 a (f_6 b c) = f_6 b (f_6 a c)",(*lemma spec. We are trying to prove "Suc (f_6 d (Suc (f_6 e f))) = f_6 e (Suc (f_6 d (Suc f)))" and the usual rule would be helpful, and it is actually proved*)
"f_6 a (f_6 b 0) = f_6 b (f_6 a 0)",(*fails to ripple*)
"f_6 a (Suc 0) = Suc (f_6 a 0)"(*fails to ripple, but is a particular case of the usual rule*)
(*all in all, it is clear that some more simplification should happen at the beginning and in steps (like before a lemma calculation), using already proved lemmas, and stuff like that*)
];

val newopenconjs = top_level_updt_ctx_end @{context} [] openconjs;
*}

ML{*
fun printlist [] = []
  | printlist l =
  let val h::t = l
      val _ = TextIO.print(h) 
      val _ = TextIO.print("\n")
  in printlist t
  end;

fun printlist_annthms [] = []
  | printlist_annthms l =
  let val h::t = l
      val (ann,thm) = h
      val _ = TextIO.print(ann)
      val _ = textIO.print("\<rightarrow> ")
      val _ = TextIO.print(thm)
      val _ = TextIO.print("\n")
  in printlist t
  end;

TextIO.print("openconjs:");
TextIO.print("\n");
printlist openconjs;
TextIO.print("lenght of openconjs: ");
TextIO.print(Int.toString(length openconjs));
TextIO.print("\n\n");

TextIO.print("newopenconjs:");
TextIO.print("\n");
val (x,_) = newopenconjs;
printlist x;
TextIO.print("lenght of newopenconjs: ");
TextIO.print(Int.toString(length x));
TextIO.print("\n\n");

TextIO.print("Proved: ");
TextIO.print("\n");
val (_,y) = newopenconjs;
printlist y;
TextIO.print("lenght of proved conjectures: ");
TextIO.print(Int.toString(length y));
TextIO.print("\n\n");
*}




(* Not updating the context, given 30 seconds for each conjecture: 44 conjs, 27 openconjs *)
(* Each conjecture is tried to be proved without updating the context for the first step, given 3 seconds for each conjecture: 44 conjs, 30 openconjs*)
(* Each conjecture is tried to be proved without updating the context for the first step, given 5 seconds for each conjecture: 44 conjs, 27 openconjs (but new things are proved!, which means that updating the context does pay)*)
(* Each conjecture is tried to be proved without updating the context for the first step, given 5 or 30 seconds each, but depth first search: 44 conjs, 32 opencons*)
(* Each conjecture is tried to be proved without updating the context for the first step, given 30 seconds each: 33 conjs (removing conjs from functions f_5 and f_6, which aren't fertilised or rippled anyway and weren't proved anyway), 16 openconjs*)
(* Each conjecture is tried to be proved without updating the context for the first step, given 30 seconds each: 25 conjs (removing conjs from functions f_4, f_5, f_6, which aren't fertilised or rippled anyway and weren't proved anyway), 8 openconjs*)
(* Each conjecture is tried to be proved without updating the context for the first step, given 30 seconds each: 25 conjs (removing conjs from functions f_4, f_5, f_6, which aren't fertilised or rippled anyway and weren't proved anyway), 10 openconjs*)
(* top_level_updt_ctx_end, 10 seconds for each: openconjs=44, newopenconjs=25*)




ML{*
val openconjs2 = [
 (* lemmas proven without my work: *)
"f_0 a (f_0 b c) = f_0 b (f_0 a c)",
"f_0 a (Suc b) = Suc (f_0 a b)",
"Suc (f_0 a b) = f_0 a (Suc b)",
"f_1 a (Suc b) = Suc (f_1 a b)",
"Suc (f_1 a b) = f_1 a (Suc b)",
"f_6 a (Suc b) = Suc (f_6 a b)",
"Suc (f_6 a b) = f_6 a (Suc b)",

 (* open conjectures for function: f_1*)
"f_1 a (f_1 b c) = f_1 b (f_1 a c)",
"f_1 a (Suc 0) = Suc (f_1 a 0)",

 (* open conjectures for function: f_2*)
"f_2 a (f_2 b c) = f_2 b (f_2 a c)",
"f_2 a (f_2 b 0) = f_2 b (f_2 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))",(*mult fert; breadth first needed to prevent inf lemma conj*)
"Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))",(*gen; success will lead to mult fert. Another path leads to a failure to fertilise*)
"Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))",(*gen; success leads to mult fert. Another path leads to mult fert; this means that breadth first might be helpful*)
"f_2 a (Suc b) = Suc (f_2 a b)",(*failure to fertilise; success will lead to mult fert*)
"f_2 a (Suc 0) = Suc (f_2 a 0)",(*failure to fertilise; success will lead to mult fert*)


 (* open conjectures for function: f_3*)
"f_3 a (f_3 b c) = f_3 b (f_3 a c)",(*mult fert*)
"f_3 a (f_3 b 0) = f_3 b (f_3 a 0)",(*doesn't ripple*)
"Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))",(*case in which a 'borrowing fertilisation' (multiple) would solve the problem; otherwise it leads to inf lemma calc *) 
"Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"f_3 a (Suc b) = Suc (f_3 a b)",(*mult fert*)
"f_3 a (Suc 0) = Suc (f_3 a 0)",(*doesn't ripple*)


 (* open conjectures for function: f_4*)
"f_4 a (f_4 b c) = f_4 b (f_4 a c)",(*mult fert*)
"f_4 a (f_4 b 0) = f_4 b (f_4 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"f_4 a (Suc b) = Suc (f_4 a b)",(*mult fert*)
"f_4 a (Suc 0) = Suc (f_4 a 0)",(*gen; success will lead to mult fert*)


 (* open conjectures for function: f_5*)
"f_5 a (f_5 b c) = f_5 b (f_5 a c)",(*mult fert*)
"f_5 a (f_5 b 0) = f_5 b (f_5 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"f_5 a (Suc b) = Suc (f_5 a b)",(*fails to fertilise; success would lead to mult fert*)
"f_5 a (Suc 0) = Suc (f_5 a 0)",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)


 (* open conjectures for function: f_6*)
"f_6 a (f_6 b c) = f_6 b (f_6 a c)",(*lemma spec. We are trying to prove "Suc (f_6 d (Suc (f_6 e f))) = f_6 e (Suc (f_6 d (Suc f)))" and the usual rule would be helpful, and it is actually proved*)
"f_6 a (f_6 b 0) = f_6 b (f_6 a 0)",(*fails to ripple*)
"f_6 a (Suc 0) = Suc (f_6 a 0)"(*fails to ripple, but is a particular case of the usual rule*)
(*all in all, it is clear that some more simplification should happen at the beginning and in steps (like before a lemma calculation), using already proved lemmas, and stuff like that*)
];

val newopenconjs2 = top_level_updt_ctx_end @{context} openconjs;
*}




ML{*
val openconjs = [
 (* open conjectures for function: f_1*)
"f_1 a (f_1 b c) = f_1 b (f_1 a c)",
"f_1 a (f_1 b 0) = f_1 b (f_1 a 0)",
"f_1 a (Suc 0) = Suc (f_1 a 0)",

 (* open conjectures for function: f_2*)
"f_2 a (f_2 b c) = f_2 b (f_2 a c)",
"f_2 a (f_2 b 0) = f_2 b (f_2 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))",(*mult fert; breadth first needed to prevent inf lemma conj*)
"Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))",(*gen; success will lead to mult fert. Another path leads to a failure to fertilise*)
"Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))",(*mult fert*)];
"Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))",(*gen; success leads to mult fert. Another path leads to mult fert; this means that breadth first might be helpful*)
"f_2 a (Suc b) = Suc (f_2 a b)",(*failure to fertilise; success will lead to mult fert*)
"f_2 a (Suc 0) = Suc (f_2 a 0)",(*failure to fertilise; success will lead to mult fert*)


 (* open conjectures for function: f_3*)
"f_3 a (f_3 b c) = f_3 b (f_3 a c)",(*mult fert*)
"f_3 a (f_3 b 0) = f_3 b (f_3 a 0)",(*doesn't ripple*)
"Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))",(*case in which a 'borrowing fertilisation' (multiple) would solve the problem; otherwise it leads to inf lemma calc *) 
"Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"f_3 a (Suc b) = Suc (f_3 a b)",(*mult fert*)
"f_3 a (Suc 0) = Suc (f_3 a 0)",(*doesn't ripple*)


 (* open conjectures for function: f_4*)
"f_4 a (f_4 b c) = f_4 b (f_4 a c)",(*mult fert*)
"f_4 a (f_4 b 0) = f_4 b (f_4 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"f_4 a (Suc b) = Suc (f_4 a b)",(*mult fert*)
"f_4 a (Suc 0) = Suc (f_4 a 0)",(*gen; success will lead to mult fert*)


 (* open conjectures for function: f_5*)
"f_5 a (f_5 b c) = f_5 b (f_5 a c)",(*mult fert*)
"f_5 a (f_5 b 0) = f_5 b (f_5 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"f_5 a (Suc b) = Suc (f_5 a b)",(*fails to fertilise; success would lead to mult fert*)
"f_5 a (Suc 0) = Suc (f_5 a 0)",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)


 (* open conjectures for function: f_6*)
"f_6 a (f_6 b c) = f_6 b (f_6 a c)",(*lemma spec. We are trying to prove "Suc (f_6 d (Suc (f_6 e f))) = f_6 e (Suc (f_6 d (Suc f)))" and the usual rule would be helpful, and it is actually proved*)
"f_6 a (f_6 b 0) = f_6 b (f_6 a 0)",(*fails to ripple*)
"f_6 a (Suc 0) = Suc (f_6 a 0)"(*fails to ripple, but is a particular case of the usual rule*)
(*all in all, it is clear that some more simplification should happen at the beginning and in steps (like before a lemma calculation), using already proved lemmas, and stuff like that*)

]
val newopenconjs = top_level @{context} openconjs

*}

ML{* val thm = a_rippling_one_goal_timeout @{context} "f_3 a (Suc b) = Suc (f_3 a b)"*}

ML{* val thm = a_rippling_one_goal_timeout @{context} "Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))"*}

ML{*
val (rst,lem) = rsts;
  RState.print rst ;
  val thethm = SynthPrfTools.name_thrm_from_rst "g1" rst;
  val myctx = RState.get_ctxt rst;
  val newctx = SynthPrfTools.add_to_wrules thethm myctx;
*}


ML{* my_rippling @{context} ["f_6 a (f_6 b c) = f_6 b (f_6 a c)",

 (* open conjectures for function: f_0*)
(*

 (* open conjectures for function: f_1*)
"f_1 a (f_1 b c) = f_1 b (f_1 a c)",(*lemma spec; again, the lemma needed is "f_1 a (Suc b) = Suc (f_1 a b)", which is actually proved*)
"f_1 a (f_1 b 0) = f_1 b (f_1 a 0)",(*doesn't ripple*)
"f_1 a (Suc 0) = Suc (f_1 a 0)",(*doesn't ripple; this is a particular case of a proved lemma*)


 (* open conjectures for function: f_2*)
"f_2 a (f_2 b c) = f_2 b (f_2 a c)",(*mult fert*)
"f_2 a (f_2 b 0) = f_2 b (f_2 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_2 a (Suc b)) = f_2 a (Suc (Suc b))",(*mult fert; breadth first needed to prevent inf lemma conj*)
"Suc (f_2 a (Suc 0)) = f_2 a (Suc (Suc 0))",(*gen; success will lead to mult fert. Another path leads to a failure to fertilise*)
"Suc (Suc (f_2 a b)) = f_2 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_2 a 0)) = f_2 a (Suc (Suc 0))",(*gen; success leads to mult fert. Another path leads to mult fert; this means that breadth first might be helpful*)
"f_2 a (Suc b) = Suc (f_2 a b)",(*failure to fertilise; success will lead to mult fert*)
"f_2 a (Suc 0) = Suc (f_2 a 0)",(*failure to fertilise; success will lead to mult fert*)
*)

 (* open conjectures for function: f_3*)
"f_3 a (f_3 b c) = f_3 b (f_3 a c)",(*mult fert*)
"f_3 a (f_3 b 0) = f_3 b (f_3 a 0)",(*doesn't ripple*)
"Suc (f_3 a (Suc b)) = f_3 a (Suc (Suc b))",(*case in which a 'borrowing fertilisation' (multiple) would solve the problem; otherwise it leads to inf lemma calc *) 
"Suc (f_3 a (Suc 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"Suc (Suc (f_3 a b)) = f_3 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_3 a 0)) = f_3 a (Suc (Suc 0))",(*doesn't ripple*)
"f_3 a (Suc b) = Suc (f_3 a b)",(*mult fert*)
"f_3 a (Suc 0) = Suc (f_3 a 0)",(*doesn't ripple*)


 (* open conjectures for function: f_4*)
"f_4 a (f_4 b c) = f_4 b (f_4 a c)",(*mult fert*)
"f_4 a (f_4 b 0) = f_4 b (f_4 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_4 a (Suc b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (f_4 a (Suc 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"Suc (Suc (f_4 a b)) = f_4 a (Suc (Suc b))",(*mult fert*)
"Suc (Suc (f_4 a 0)) = f_4 a (Suc (Suc 0))",(*gen; success will lead to mult fert*)
"f_4 a (Suc b) = Suc (f_4 a b)",(*mult fert*)
"f_4 a (Suc 0) = Suc (f_4 a 0)",(*gen; success will lead to mult fert*)


 (* open conjectures for function: f_5*)
"f_5 a (f_5 b c) = f_5 b (f_5 a c)",(*mult fert*)
"f_5 a (f_5 b 0) = f_5 b (f_5 a 0)",(*gen; success will lead to mult fert*)
"Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))",(*fails to fertilise; success would lead to mult fert*)
"Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)
"f_5 a (Suc b) = Suc (f_5 a b)",(*fails to fertilise; success would lead to mult fert*)
"f_5 a (Suc 0) = Suc (f_5 a 0)",(*gen; success will lead to failure to fertilise, which will lead to mult fert*)


 (* open conjectures for function: f_6*)
"f_6 a (f_6 b c) = f_6 b (f_6 a c)",(*lemma spec. We are trying to prove "Suc (f_6 d (Suc (f_6 e f))) = f_6 e (Suc (f_6 d (Suc f)))" and the usual rule would be helpful, and it is actually proved*)
"f_6 a (f_6 b 0) = f_6 b (f_6 a 0)",(*fails to ripple*)
"f_6 a (Suc 0) = Suc (f_6 a 0)",(*fails to ripple, but is a particular case of the usual rule*)
(*all in all, it is clear that some more simplification should happen at the beginning and in steps (like before a lemma calculation), using already proved lemmas, and stuff like that*)

end