val s = 
Abs("nn",Type("nat", []), 
  Abs("a",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("b",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("a1",Type("List.list", [TFree("'a", ["HOL.type"])]), 
  Abs("a2",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("c",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("no",Type("nat", []), 
  (((Const("List.foldl", Type("fun", [Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])]), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])]))) $
 (Abs("",Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), 
  (((Var( ("f",2), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])])]))) $
 (Bound(4))) $
 (Bound(0))) $
 (((Const("List.append", Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])]))) $
 (Bound(2))) $
 (Bound(3)))))) $
 ((((Const("List.foldl", Type("fun", [Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])]), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])]))) $
 (Abs("",Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), 
  (((Var( ("f",2), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])])]))) $
 (Bound(4))) $
 (Bound(0))) $
 (((Const("List.append", Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])]))) $
 (Bound(2))) $
 (Bound(3)))))) $
 (((Var( ("a",2), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])]))) $
 (Bound(3))) $
 (((Const("List.append", Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])]))) $
 (Bound(1))) $
 (Bound(2))))) $
 (Bound(1)))) $
 (Bound(2)))))))));

val t = 
Abs("nn",Type("nat", []), 
  Abs("a",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("b",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("a1",Type("List.list", [TFree("'a", ["HOL.type"])]), 
  Abs("a2",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("c",Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), 
  Abs("no",Type("nat", []), 
  (((Const("List.foldl", Type("fun", [Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [TVar( ("'b_1", 0), ["HOL.type"]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])]), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [Type("List.list", [TVar( ("'b_1", 0), ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])]))) $
 ((((((((Var( ("f",0), Type("fun", [Type("nat", []), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [TVar( ("'b_1", 0), ["HOL.type"]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])])])])])])])]))) $
 (Bound(6))) $
 (Bound(5))) $
 (Bound(4))) $
 (Bound(3))) $
 (Bound(2))) $
 (Bound(1))) $
 (Bound(0)))) $
 ((((((((((Var( ("f",0), Type("fun", [Type("nat", []), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("fun", [Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])]), Type("fun", [TVar( ("'b_1", 0), ["HOL.type"]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])])])])])])])]))) $
 (Bound(6))) $
 (Bound(5))) $
 (Bound(4))) $
 (Bound(3))) $
 (Bound(2))) $
 (Bound(1))) $
 (Bound(0))) $
 ((((((((Var( ("a",0), Type("fun", [Type("nat", []), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])])])])])])])])])])])]))) $
 (Bound(6))) $
 (Bound(5))) $
 (Bound(4))) $
 (Bound(3))) $
 (Bound(2))) $
 (Bound(1))) $
 (Bound(0)))) $
 ((((((((Var( ("x",0), Type("fun", [Type("nat", []), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), TVar( ("'b_1", 0), ["HOL.type"])])])])])])])]))) $
 (Bound(6))) $
 (Bound(5))) $
 (Bound(4))) $
 (Bound(3))) $
 (Bound(2))) $
 (Bound(1))) $
 (Bound(0))))) $
 ((((((((Var( ("xs",0), Type("fun", [Type("nat", []), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("List.list", [Type("List.list", [TFree("'a", ["HOL.type"])])]), Type("fun", [Type("nat", []), Type("List.list", [TVar( ("'b_1", 0), ["HOL.type"])])])])])])])])]))) $
 (Bound(6))) $
 (Bound(5))) $
 (Bound(4))) $
 (Bound(3))) $
 (Bound(2))) $
 (Bound(1))) $
 (Bound(0))))))))));

val thry = the_context();
val ct = Thm.cterm_of thry t;
val cs = Thm.cterm_of thry s;

Thm.trivial (Thm.cterm_of thry (Logic.mk_equals (t,s)));

(* 
These raise a type exception:
Seq.list_of (Unify.unifiers (thry, Envir.empty 0, [(t,s)]));
Seq.list_of (Unify.unifiers (thry, Envir.empty 1, [(t,s)]));

Exception-
   TYPE
      ("Variable \"?f2\" has two distinct types",
         ["'a List.list
             => ('a List.list List.list
              => 'a List.list List.list => nat => 'a List.list List.list)
             => 'a List.list List.list
             => 'a List.list
             => 'a List.list List.list
             => 'a List.list List.list => nat => 'a List.list List.list",
            "'a List.list
             => ('a List.list List.list
              => 'a List.list List.list => nat => 'a List.list List.list)
             => 'a List.list List.list
             => ?'b_1.0
             => 'a List.list List.list
             => 'a List.list List.list => nat => nat"],
         []) raised

This seems to loop forever:
Seq.list_of (Unify.unifiers (thry, Envir.empty 2, [(t,s)]));

*)

(* My version raises a TYPE exception *)
(* Seq.list_of (MyUnify.unifiers thry (InstEnv.init thry, [(t,s)]));  *)
