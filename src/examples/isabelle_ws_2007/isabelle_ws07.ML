use "ROOT.ML";

use_thy "examples/isabelle_ws_2007/critics_isabelleWS07";
use_thy "benchmarks/lemspec_theories/HOLemSpec";
use_thy "benchmarks/lemspec_theories/Tree";
Trm.drop_var_args_flag := false;

val thy = theory "critics_isabelleWS07";




val thy = theory "Tree";
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then RippleLemSpec_flow.induct_ripple_lemspec);

val ripple =  PPInterface.ipp thy (RTechnEnv.map_then RippleLemSpec_dsum.induct_ripple_lemspec);

(* These can be solved by lemma speculation *)

(*Works *)

(* T15 *) ripple ("a", "x + suc(x) = suc(x+x)"); (* works again! *)
(* T16 *) ripple ("a", "evenR(x + x)");  (* have T15 as lemma, which is OK if allowed speculation *)
(* T17 *) ripple("a", "rev(rev(x@y)) = rev(rev x) @ rev(rev y)"); (* fail with dsum *)
(* T18 *) ripple ("a","rev(rev(x) @ y) = rev(y) @ x"); (*  ok with dsum *)
(* T19 *) ripple("a", "rev(rev x) @ y = rev(rev(x@y))"); (* fail with dsum *)
(* T20 *) ripple("a", "evenR(len(x@x))"); (* did this ever work? Massive lemma calculation going on in
                                             proof of lemma.*)


(* Our critic fails because there's no middle-out steps. *)
(* T21 *) ripple("a", "rotate (len x) (x @ y) = y @ x");

(* Need implication lemma *)
(* T14 *) ripple("a", "ordered(isort l)");

(* ------------------------------------------------------- *)
(* Higer order test *)
(* ------------------------------------------------------- *)
structure RippleCalc = RippleLemCalcFUN(structure BasicRipple = RippleCaseSplit);
structure Ripple = RippleLemSpecFUN(structure RippleLemCalc = RippleCalc
            structure MidOutRCInfo = MidOutCInfo_g_dsum);
use_thy "benchmarks/Trees";
Trm.drop_var_args_flag := false;
val thy = theory "Trees";

val ripple =  PPInterface.ipp2 (the_context()) (RTechnEnv.map_then Ripple.induct_ripple_lemspec);
val ripple =  PPInterface.ipp (the_context()) (RTechnEnv.map_then Ripple.induct_ripple_lemspec);

(*  Warning! Counter-example checker falls over
   if any of the variables becomes called `o', it thinks it means fucntion composition *)

(* ----------------------------------------------------------------------*)
(* Can't find lemma because it needs to go straingt to fertilisation. *)
(* ----------------------------------------------------------------------*)

(* Needs:  "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"
   and     "foldr f (xs @ ys) a = foldr f xs (foldr f ys a)" *)
ripple ("a", "foldl (%a. %l.  a + (len l)) n (in_ord t)  = foldl (%a. %l. a + (len l)) n (postord t)");
ripple ("a", "foldr (%l. op + (len l)) (in_ord t) n = foldr (%l. op + (len l)) (postord t) n");
ripple ("a", "foldl (%a. %l.  a + (len l)) nn (lr_ord t) = foldl (%a. %l. a + (len l)) nn (rl_ord t)");
ripple ("a","foldl (%a l. a + len l) nn (lr_ord t) = foldl (%a l. a + len l) nn (rev (lr_ord t))");

ripple ("a","foldl (%a l. a + len l) nn (lr_ord t) = nn + len (concat (lr_ord t))");
ripple("a", "rev(concat l) = concat(map rev (rev l))");


(* ----------------------------------------------------------------------*)
(* Works, as long as fold-append isn't a wave-rule, then get ho-unify problems.
   These also have gigantuan search spaces and no raise a TERM exception if let
   loose.                                                                *)
(* ----------------------------------------------------------------------*)
ripple ("a", "foldl (%a. %l.  a + (len l)) nn ((rev a) @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)");
ripple ("a", "foldl (%x y. y+x) (nn :: nat) ((rev a) @ b) = foldl (%x y. y+x) nn (b @ a)");

(* ----------------------------------------------------------------------*)
(*REALLY slow but works!!! .*)
ripple ("a", "foldl f ((rev a) @ b) = foldl f (rev ((rev b) @ a))");


(* more that fails *)
ripple ("a", "maps f (rev l) = rev maps f l"); (* fail *)
ripple ("a","postord (mirror t) = rev (pre_ord t)"); (* fail *)

(* ----------------------------------------------------------------------*)
(* Calculation fails (over generalisation?), donesn't try spec, but that 
   would probably not work either... *)
(* ----------------------------------------------------------------------*)
ripple ("a", "foldl (%a. %l.  a + (len l)) nn  (a @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)");
(* This should be a lemma from ThmA, but it fails *)
ripple ("a", "foldl (%a. %l.  a + (len l)) (foldl (%a. %l.  a + (len l)) nn l) (lr_ord t2) 
             = foldl (%a. %l. a + (len l)) nn ((rl_ord t2) @ l)");

ripple ("a", "foldl (%a. %l.  a + (len l)) (foldl (%a. %l.  a + (len l)) nn k) (lr_ord t2) = 
              foldl (%a. %l.  a + (len l)) (foldl (%a. %l.  a + (len l)) nn (rl_ord t2)) k");

ripple ("a", "foldl (%a l. a + len l) (foldl (%a l. a + len l) nn l) k = foldl (%a l. a + len l) nn (k @ l)");



(* ----------------------------------------------------------------------*)
(* Simple examples IsaPlanner can do with calc or strong fert.           *)
(* ----------------------------------------------------------------------*)
(* from Isabelle List.foldl_foldr. *)
ripple ("a","foldl f a xs = foldr (%x y. f y x) (rev xs) a");
ripple ("a", "foldl (%a l. a + len l) a (xs @ ys) = 
              foldl (%a l. a + len l) (foldl (%a l. a + len l) a xs) ys");
ripple ("a", "foldl op + a xs = a + foldr op + xs (0::nat)");
ripple ("a", "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys");



(* fail spec?*)
ripple ("a", "map f ((rev a) @ b) = map f (rev ((rev b) @ a))");


(* Seem to do lemma calculation forever...*)
ripple ("a", "(rl_ord t) @ a = treefold2 (%lf x. lf#x) a t");
ripple ("a", "a @ (lr_ord t) = treefold2 (%lf. %x. x @ [lf]) a t");
ripple("a", "foldl (op +) x (lr_ord t) = treefold2 ( op +) (x::nat) t");
ripple("a", "foldl (op +) x (rl_ord t) = treefold2 ( op +) (x::nat) t");


(* ------------------------------------------------------- *)
PolyML.exception_trace (fn () => ripple ("a", "foldl (%a. %l.  a + (len l)) nn ((rev a) @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)"));


(* Mutual recursion example. NOTE, make sure rippling uses that update function! *)
ripple_2step ("a", "evenM(n) \/ oddM(n)");

(* Can't do, lemma from T19 and T17 although should be easily solved by simp
  without induction provided the lemma rev(rev x)) = x. *)
(* L1 *)  ripple("a", "rev(rev (h#t)) = h#(rev rev t)");

(* can't do variant either, but it could if `rev t' was generalised as it should
   when given to the conjecturing technique. L1 does one of the funny little loops
   when the rev rule gets applied once in each direction. Otherwise we'd get this
   lemma and it would be OK. *)
 ripple("a", "rev((rev t) @ [h]) = h#(rev rev t)");

(* This alternative lemma for T17 could however be solved, but then the reminder after weak fertilisation requires the lemma L1 above.... *)
 ripple("a","rev (l @ [a]) = a # rev l");
