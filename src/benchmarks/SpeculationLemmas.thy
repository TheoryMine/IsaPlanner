theory SpeculationLemmas
imports IsaP
begin

(* This file is for experiments for the ITP paper.
   The ML commands start IsaPlanner on the theorems, loading
  a theory with just the relevant function definitions.
  IsaPlanne is set to use lemma speculation to attempt the proofs.*)
ML {*
use_thy "src/benchmarks/lemspec_theories/HOLemSpec";
use_thy "src/benchmarks/lemspec_theories/Ireland";
use_thy "src/benchmarks/lemspec_theories/Ineq";
*}

ML{*
val HOthy = theory "HOLemSpec";
val Irethy = theory "Ireland";
val Ineqthy = theory "Ineq";
val rippling = RippleLemSpec.induct_ripple_lemspec;
*}
ML{*
val thm1 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "x + (suc x) = suc(x + x)")) ();
*}
ML{*
val thm2 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "even(x + x)")) ();
*}
ML{*
(* This is the theorem that fails, IsaCosy hasn't got the right lemma,
  namely distributivity of len over @ *)
val thm3 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "even(len(l@l))")) ();
*}
ML{*
val thm4 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "rev((rev l) @ m) = (rev m) @ l")) ();
*}
ML{*
val thm5 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "rev(rev(l@m)) = (rev(rev l)) @ (rev(rev m))")) ();
*}
ML{*
val thm6 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "rev(rev l) @ m = rev(rev(l@m))")) ();
*}
ML{*
val thm7 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Irethy (rippling "a") 
  ("a", "rotate (len l) (l @ m) = m @ l")) ();
*}

ML{*
val thm8 = PrintMode.setmp [] (fn () => 
  PPInterface.ipp HOthy (rippling "a")
  ("a", "rev(concat l) = concat(map rev (rev l))")) ();
*}

ML{*
(* This one also miss the same lemma as thm3. *)
val thm9 = PrintMode.setmp [] (fn () =>
  PPInterface.ipp HOthy (rippling "a") 
  ("a", "len(concat (map f l)) = len(maps f l)")) ();
*}

ML{*
val thm10 = PrintMode.setmp [] (fn () =>
  PPInterface.ipp HOthy (rippling "a")
  ("a", "foldl (%x y. y +x) nn ((rev l1) @ l2) =foldl (%x y. y +x) nn (l2 @ l1)")) ();
*}

ML{*
val thm11 =PrintMode.setmp [] (fn () =>
  PPInterface.ipp HOthy (rippling "a") 
  ("a", "foldl (%x y. x + len y) nn ((rev l1) @ l2) =foldl (%x y. x + len y) nn (l2 @ l1)")) ();
*}

ML{*
val thm12 = PrintMode.setmp [] (fn () => 
PPInterface.ipp Ineqthy (rippling "a") ("a", "x leq (x + y)")) ();
*}


end