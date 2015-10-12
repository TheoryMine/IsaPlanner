theory IsaCoSyLemmas
imports IsaP
begin

(* This file is for experiments for the ITP paper.
   The ML commands start IsaPlanner on the theorems, loading
  a theory containing extra lemmas found by IsaCoSy. Note that you
   will have to switch to the isabelle buffer to see IsaPlanner's
  interactive top-level. Press "go" in the isabelle buffer
  and all proof should be completed autoamtically.*)
ML {*
use_thy "src/benchmarks/lemspec_theories/HOLemSpecSynth";

*}

ML{*
val thry = theory "HOLemSpecSynth";
val rippling = RippleLemCalc.induct_ripple_lemcalc;
*}
ML{*
val thm1 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "x + (Suc x) = Suc(x + x)")) ();
*}
ML{*
val thm2 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "even(x + x)")) ();
*}
ML{*
(* This is the theorem that fails, IsaCosy hasn't got the right lemma,
  namely distributivity of len over @ *)
val thm3 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "even(len(l@l))")) ();
*}
ML{*
val thm4 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "rev((rev l) @ m) = (rev m) @ l")) ();
*}
ML{*
val thm5 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "rev(rev(l@m)) = (rev(rev l)) @ (rev(rev m))")) ();
*}
ML{*
val thm6 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "rev(rev l) @ m = rev(rev(l@m))")) ();
*}
ML{*
val thm7 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") 
  ("a", "rotate (len l) (l @ m) = m @ l")) ();
*}

ML{*
val thm8 = PrintMode.setmp [] (fn () => 
  PPInterface.ipp thry (rippling "a")
  ("a", "rev(concat l) = concat(map rev (rev l))")) ();
*}

ML{*
(* This one also miss the same lemma as thm3. *)
val thm9 = PrintMode.setmp [] (fn () =>
  PPInterface.ipp thry (rippling "a") 
  ("a", "len(concat (map f l)) = len(maps f l)")) ();
*}

ML{*
val thm10 = PrintMode.setmp [] (fn () =>
  PPInterface.ipp thry (rippling "a")
  ("a", "foldl (%x y. y +x) nn ((rev l1) @ l2) =foldl (%x y. y +x) nn (l2 @ l1)")) ();
*}

ML{*
val thm11 =PrintMode.setmp [] (fn () =>
  PPInterface.ipp thry (rippling "a") 
  ("a", "foldl (%x y. x + len y) nn ((rev l1) @ l2) =foldl (%x y. x + len y) nn (l2 @ l1)")) ();
*}

ML{*
val thm12 = PrintMode.setmp [] (fn () => 
PPInterface.ipp thry (rippling "a") ("a", "x leq (x + y)")) ();
*}


end