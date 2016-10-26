theory T_1
imports IsaP 
uses "../myrippling.ML"
begin

datatype "T_1" =  "C_2" "T_1" "Nat.nat"  | "C_1" "Nat.nat" "Nat.nat"  
declare nat.inject[wrule]
declare T_1.inject[wrule]

fun f_0 :: "T_1 => nat => nat" where
  "f_0 (C_1 a b) c = c"
| "f_0 (C_2 a b) c = Suc (Suc (f_0 a b))"

fun f_1 :: "T_1 => nat => nat" where
  "f_1 (C_1 a b) c = Suc c"
| "f_1 (C_2 a b) c = f_1 a (Suc (f_1 a (f_1 a 0)))"

fun f_2 :: "T_1 => nat => nat" where
  "f_2 (C_1 a b) c = Suc (Suc c)"
| "f_2 (C_2 a b) c = Suc (f_2 a (Suc (f_2 a 0)))"

fun f_3 :: "T_1 => nat => nat" where
  "f_3 (C_1 a b) c = Suc (Suc (Suc c))"
| "f_3 (C_2 a b) c = f_3 a (Suc (f_3 a (Suc (Suc b))))"

fun f_4 :: "T_1 => nat => nat" where
  "f_4 (C_1 a b) c = Suc (Suc (Suc (Suc c)))"
| "f_4 (C_2 a b) c = Suc (f_4 a (Suc (Suc (Suc b))))"

fun f_5 :: "T_1 => nat => nat" where
  "f_5 (C_1 a b) c = Suc (Suc (Suc (Suc (Suc c))))"
| "f_5 (C_2 a b) c = f_5 a (Suc (Suc (f_5 a (Suc c))))"

fun f_6 :: "T_1 => nat => nat" where
  "f_6 (C_1 a b) c = Suc (Suc (Suc (Suc (Suc (Suc c)))))"
| "f_6 (C_2 a b) c = Suc (Suc (f_6 a (f_6 a c)))"

fun f_7 :: "T_1 => nat => nat" where
  "f_7 (C_1 a b) c = Suc (Suc (Suc (Suc (Suc (Suc (Suc c))))))"
| "f_7 (C_2 a b) c = f_7 a (Suc (Suc (Suc (Suc (Suc 0)))))"

declare f_0.simps[wrule]
declare f_1.simps[wrule]
declare f_2.simps[wrule]
declare f_3.simps[wrule]
declare f_4.simps[wrule]
declare f_5.simps[wrule]
declare f_6.simps[wrule]
declare f_7.simps[wrule]

ML{*
val conjectures = [
(* PROVED WITHOUT MY WORK *)
"f_1 (C_2 t n) (Suc (Suc p)) = f_1 t (Suc (Suc (Suc 0)))",
"f_1 a (f_1 a b) = f_1 a (Suc b)",
"f_1 t (Suc (f_1 t (f_1 t 0))) = f_1 t (Suc (f_1 t (Suc 0)))",
"f_1 t (Suc (f_1 t (f_1 t 0))) = f_1 t (Suc (Suc (Suc 0)))",
"f_1 a (Suc (f_1 a b)) = f_1 a (Suc (Suc b))",

(* OPEN CONJECTURES *)

 (* open conjectures for function: f_0*)
"f_0 a (f_0 a (f_0 a 0)) = f_0 a 0",
"f_0 a (f_0 a (f_0 a b)) = f_0 a b",
"f_0 a (f_0 a (Suc 0)) = f_0 a (Suc 0)",
"f_0 a (f_0 a (Suc b)) = f_0 a (Suc b)",
"f_0 a (Suc (f_0 a 0)) = f_0 a (Suc 0)",
"f_0 a (Suc (f_0 a b)) = f_0 a (Suc b)",
"f_0 a (f_0 a 0) = f_0 a 0",
"f_0 a (f_0 a b) = f_0 a b",


 (* open conjectures for function: f_1*)


 (* open conjectures for function: f_2*)
"f_2 a (f_2 a 0) = f_2 a (Suc (Suc 0))",
"f_2 a (f_2 a b) = f_2 a (Suc (Suc b))",
"f_2 a (Suc (Suc 0)) = f_2 a (f_2 a 0)",
"f_2 a (Suc (Suc b)) = f_2 a (f_2 a b)",


 (* open conjectures for function: f_3*)


 (* open conjectures for function: f_4*)


 (* open conjectures for function: f_5*)
"f_5 a (f_5 b 0) = f_5 b (f_5 a 0)",
"f_5 a (f_5 b c) = f_5 b (f_5 a c)",
"f_5 a (Suc (Suc 0)) = Suc (f_5 a (Suc 0))",
"f_5 a (Suc (Suc 0)) = Suc (Suc (f_5 a 0))",
"f_5 a (Suc (Suc b)) = Suc (f_5 a (Suc b))",
"f_5 a (Suc (Suc b)) = Suc (Suc (f_5 a b))",
"Suc (f_5 a (Suc 0)) = f_5 a (Suc (Suc 0))",
"Suc (f_5 a (Suc b)) = f_5 a (Suc (Suc b))",
"Suc (Suc (f_5 a 0)) = f_5 a (Suc (Suc 0))",
"Suc (Suc (f_5 a b)) = f_5 a (Suc (Suc b))",
"f_5 a (Suc 0) = Suc (f_5 a 0)",
"f_5 a (Suc b) = Suc (f_5 a b)",
"Suc (f_5 a 0) = f_5 a (Suc 0)",
"Suc (f_5 a b) = f_5 a (Suc b)",


 (* open conjectures for function: f_6*)
"f_6 a (f_6 b 0) = f_6 b (f_6 a 0)",
"f_6 a (f_6 b c) = f_6 b (f_6 a c)",
"f_6 a (Suc (Suc 0)) = Suc (f_6 a (Suc 0))",
"f_6 a (Suc (Suc 0)) = Suc (Suc (f_6 a 0))",
"f_6 a (Suc (Suc b)) = Suc (f_6 a (Suc b))",
"f_6 a (Suc (Suc b)) = Suc (Suc (f_6 a b))",
"Suc (f_6 a (Suc 0)) = f_6 a (Suc (Suc 0))",
"Suc (f_6 a (Suc b)) = f_6 a (Suc (Suc b))",
"Suc (Suc (f_6 a 0)) = f_6 a (Suc (Suc 0))",
"Suc (Suc (f_6 a b)) = f_6 a (Suc (Suc b))",
"f_6 a (Suc 0) = Suc (f_6 a 0)",
"f_6 a (Suc b) = Suc (f_6 a b)",
"Suc (f_6 a 0) = f_6 a (Suc 0)",
"Suc (f_6 a b) = f_6 a (Suc b)"


 (* open conjectures for function: f_7*)
]

val (openconjs, theorems) = top_level_updt_ctx_end @{context} [] conjectures;
*}

ML{*
fun pretty_thm ctxt thm =
  Syntax.pretty_term ctxt (prop_of thm);

fun printlist [] = ()
  | printlist (h::t) =
    let
      val _ = TextIO.print(h ^ "\n")
  in printlist t
  end;

fun printlist_annthms [] = ()
  | printlist_annthms (h::t) =
    let
      val (ann,thm) = h
      val _ = PolyML.print(ann ^ "-> " ^ (Display.string_of_thm @{context} thm))
      val _ = TextIO.print("\n")
  in printlist_annthms t
  end;

TextIO.print("Conjectures:\n");
printlist conjectures;
TextIO.print("\n\n");

TextIO.print("New open conjectures:\n");
printlist openconjs;
TextIO.print("\n\n");

TextIO.print("Proved:\n");
printlist_annthms theorems;
TextIO.print("\n\n");

TextIO.print("lenght of openconjs:" ^ Int.toString(length conjectures) ^ "\n");
TextIO.print("lenght of newopenconjs: " ^ Int.toString(length openconjs) ^ "\n");
TextIO.print("lenght of proved conjectures: " ^ Int.toString(length theorems) ^ "\n");
*}

end