
use_thy "benchmarks/CaseAnalysis_L2";
val thy = theory "CaseAnalysis_L2";
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then RippleLemCalc_flow.induct_ripple_lemcalc);
ripple ("a", "(i minus j) minus k = (i minus k) minus j"); 
ripple ("a","x mem l@[x]"); (*OK -split if *)

structure Ripple = RippleCaseSplitCalcFUN(structure BasicRipple = RippleRTechn_flow);
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then Ripple.induct_ripple_lemcalc);
ripple ("a", "max a (max b c) = max (max a b) c");  
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then RippleLemCalc_flow2.induct_ripple_lemcalc);

val simp = PPInterface.ipp thy (RTechnEnv.map_then InductAndSimp.induct_and_simp);
simp ("a", "butlast (xs @ [x]) =xs");
ripple ("a", "butlast (xs @ [x]) =xs");

use_thy "benchmarks/synth_theories/Tree_size_height";
val thy = theory "Tree_size_height";
structure Ripple = RippleLemCalc;
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then Ripple.induct_ripple_lemcalc);
ripple ("a", "max a b = max b a");
ripple ("a", "max (max a b) c = max a (max b c)");
ripple ("a", "min (min a b) c = min a (min b c)");

ripple ("a","x mem [x]@l");
ripple ("a","x mem l@[x]"); (*OK -split if *)
ripple ("a","x mem (ins x l)"); (*OK -split if *)
ripple ("a","x mem (ins(x,l)) = True"); (*OK -split if *)
ripple ("a", "x mem l --> x mem (l@t)"); (* OK, not solvable if using ==> *)
ripple ("a","x mem t --> x mem (l@t)"); (*OK -split if *)
ripple ("a", "~(x=y) ==> ((x mem (ins y l)) = x mem l)"); (* fail *)
ripple ("a", "(x less y) ==> ((x mem (ins y l)) = x mem l)"); (* fail *)

(* Lists as sets *)
ripple ("a","~(x=y) ==> (x mem (ins_1 y l) = x mem l)"); (* *)
ripple ("a","~(y=x) ==> (x mem (ins_1 y l) = x mem l)"); (*also fails, get a~=z |- aa~=z *)

ripple ("a","x=y ==> (x mem (ins_1 y l ) = True)"); (* fail *)
ripple ("a", "x=y ==> x mem (ins_1 y l)"); (* fail *)
ripple ("a", "x mem (ins_1 x l )"); (*ok*)
ripple ("a","x mem (ins_1 x l) = True"); (* ok *)
(* 8/11 solved *) 

(* delete *)
ripple ("a", "~(x mem (delete x l))"); (* ok *)
ripple ("a", "(len (delete x l)) leq (len l)"); (* fail, lemma-spec candidate *)(* This would need a lemma, x leq y ==> x leq Suc y, which can't even be proved itself! *)
(* 0/2 *)


(* Filter *)
(* filter_append: *)
ripple ("a", "filter P (xs @ ys) = filter P xs @ filter P ys"); (* Exception - UNDEF*)
(* rev_filter: *)
ripple ("a", "rev (filter P xs) = filter P (rev xs)"); (*ok *)
(* length_filter_le: *)
ripple ("a", "(len (filter P xs)) leq (len xs)"); (* fail - EXCEPTION : UNDEF( *)
(* filter_map: *)
ripple ("a", "filter P (map f xs) = map f (filter (P o f) xs)"); (*fail*)
(* length_filter_map: *)
ripple ("a", "len (filter P (map f xs)) = len (filter (P o f) xs)"); (* fail*)
(* 1/5 solved *)

(* last and butlast *)
(* last_snoc: *)
ripple ("a", "last (xs @ [x]) = x"); (* OK *)
(* butlast_snoc: *)
ripple ("a", "butlast (xs @ [x]) = xs"); (* OK *)
(* last_ConsL:*)
ripple ("a", "xs = [] --> (last (x # xs) = x)"); (* ok *)
ripple ("a", "xs = [] ==> (last (x # xs) = x)"); (*ok,*)
(* last_ConsR: *)
ripple ("a", "~(xs = []) --> (last (x # xs) = last xs)"); (* fail *)
(* last_append: *)
ripple ("a", "last (xs @ ys) = (if ys = [] then last xs else last ys)"); (* OK *)
(* length_butlast: *)
ripple ("a", "length (butlast xs) = length xs - (suc 0)"); (* fail *)
(* butlast_append: *)
 ripple ("a", "butlast (xs @ ys) = (if ys = [] then butlast xs else xs @ butlast ys)"); (**)
(* last_drop: *)
ripple ("a", "(n less length xs) --> (last (drop n xs) = last xs)") (* fail *)
(* butlast_conv_take: *)
ripple ("a", "butlast xs = take (length xs - 1) xs"); (* fail *)
(* 4/9 *)

(* takeWhile and dropWhile *)
(* takeWhile_dropWhile_id: *)
ripple ("a", "takeWhile P xs @ dropWhile P xs = xs"); (* OK *)
ripple ("a", "takeWhile (%x. True) xs = xs"); (* OK, *) 
ripple ("a", "dropWhile (%x. False) xs = xs"); (* OK (no use of IH, simp solves both cases. *)
ripple ("a", "takeWhile (%x. True) xs = dropWhile (%x. False) xs"); (* works *)
(*3/4*)

(* Count *) 
ripple ("a", "(count n l) + (count n m) = count n (l @ m)"); (* ok *)
ripple ("a", "count n l = count n (rev l)"); (* fail *)
ripple ("a", "count (f n) (map f l) = count n l"); (* *)
ripple ("a", "(count n l) leq (count n (l@m))"); (*  *)
ripple ("a", "1 + (count n l) = count n (n#l)"); (*gigantuan search space but OK! *)
ripple ("a", "(n = x) ==> (1 + (count n l) = count n (x#l))"); (*  *)
(*from Sean *)
ripple ("a", "count n (x @ [n]) = Suc (count n x)"); (*  *)
ripple ("a", "~(n=h) ==> count n (x @ [h]) = count n x"); (*  *)
ripple ("a", "count n t + count n [h] = count n (h#t)"); (* ok *)
ripple ("a", "count n [h] + count n t = count n (h#t)"); (* ok *)

(* Sorting *)
ripple ("a","count x l = count x (sort l)"); (* fail *)
ripple ("a","sorted (sort l)"); (* fail *)
ripple ("a", "sorted l ==> sorted (insort x l)"); (* fail *)

(* Things that use case *)
(* zip *)
(* zip_Nil: *)
ripple ("a", "zip [] ys = []"); (* ok *)
(* zip_Cons_Cons: *)
ripple ("a", "zip (x # xs) (y # ys) = (x, y) # zip xs ys"); (* ok *)
(* lemma zip_Cons1: *)
ripple ("a", "zip (x # xs) ys = (case ys of [] => [] | y # ys => (x, y) # zip xs ys)"); (* OK, not inductive though. *)
(* take_zip *)
ripple ("a", "take n (zip xs ys) = zip (take n xs) (take n ys)"); (* fail *)
(* drop_zip *)
ripple ("a", "drop n (zip xs ys) = zip (drop n xs) (drop n ys)"); (* fail*)
(* 3/5 *)

(* take and drop *)
(* take_0*)
ripple ("a", "take 0 xs = []"); (* ok*)
(* drop_0 *)
ripple ("a", "drop 0 xs = xs"); (* ok *)
(*take_Suc_Cons: *) 
ripple ("a", "take (Suc n) (x # xs) = x # take n xs"); (*works! *)
(* drop_Suc_Cons*) 
ripple ("a","drop (Suc n) (x # xs) = drop n xs"); (* ok *)
(*2/4*)


use_thy "benchmarks/CaseAnalysis";
val thy = theory "CaseAnalysis";
structure Ripple = RippleLemCalcFUN(structure BasicRipple = RippleCaseSplit);
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then Ripple.induct_ripple_lemcalc);

(* Theorems about minus from Isabelle. I use different def. not Isabelle's. *)
(* diff_self_eq_0 *) 
ripple ("a","(m::nat) minus m = 0"); (* OK*)
(* diff_diff_left, need induct on both i & j *) 
ripple ("a", "((i::nat) minus j) minus k = i minus (j + k)"); (*ok *)
(* Suc_diff_diff (simp), need lemma diff_diff_left *)
ripple ("a", "((Suc m) minus n) minus Suc k = (m minus n) minus k"); (* fail *)
(* diff_commute, need lemmas diff_diff_left, add_commute *)
ripple ("a", "((i::nat) minus j) minus k = (i minus k) minus j");  (* fail *)
(* diff_add_inverse *)
ripple ("a", "(n + m) minus n = (m::nat)"); (* ok *)
(* diff_add_inverse2, need lemma diff_add_inverse 2 *)
ripple ("a", "(m + n) minus n = (m::nat)"); (* ok *)
(* diff_cancel *)
ripple ("a", "(k + m) minus (k + n) = m minus (n::nat)"); (* OK, *)
(* diff_cancel2, need diff_cancel, add_commute *)
ripple ("a", "(m + k) minus (n + k) = m minus (n::nat)"); (* OK, no split  *)
(* diff_add_0 *)
ripple ("a", "n minus (n + m) = (0::nat)"); (* OK *)
(*diff_mult_distrib, need induct on m & n, lemma diff_cancel *)
ripple ("a", "((m::nat) minus n) * k = (m * k) minus (n * k)"); (* fail *)
(* diff_mult_distrib2, need diff_mult_distrib, mult_commute *)
ripple ("a", "k * ((m::nat) minus n) = (k * m) minus (k * n)"); (* fail, large search sp. 
                                                                   lemma spec same lemma lots of 
                                                                   times ??? *)

(* 6/11 solved *)

(* ---------------------------------------------------------------- *)

(* Theorems about orders, from Isabelle *)

(* le_0_eq [iff] *) 
ripple ("a", "(n::nat) leq 0 <-> n = 0"); (* OK *)
(* le_SucI,  *) 
ripple ("a","m leq n ==> m leq Suc n"); (* fail *)
(* le_add2:*) 
ripple ("a", "n leq ((m + n)::nat)"); (* fail *)
(*le_add1: *) 
ripple ("a","n leq ((n + m)::nat)"); (* ok *)
(* less_add_Suc1: *) 
ripple ("a","i less Suc (i + m)"); (* ok *)
(* less_add_Suc2: *)
ripple ("a","i less Suc (m + i)"); (* ok , actually calculates a lemma with a case statement*)
(* add_diff_inverse: *)
ripple ("a", "~  m less n ==> n + (m minus n) = (m::nat)"); (* fail *)
(*le_add_diff_inverse [simp]: *) 
ripple ("a","n leq m --> n + (m minus n) = (m::nat)"); (* fail *)
(*le_add_diff_inverse2 [simp]:*)
ripple ("a", "n leq m --> (m minus n) + n = (m::nat)"); (* fail *)
(*Suc_diff_le:*) 
ripple ("a","n leq m --> Suc m minus n = Suc (m minus n)"); (* fail *)
(* diff_less_Suc: *) 
ripple ("a","(m minus n) less (Suc m)"); (* fail *)
(* diff_le_self [simp]: *)
ripple ("a","(m minus n) leq (m::nat)"); (* fail *)
(* diff_add_assoc: *)
ripple ("a","(k leq (j::nat)) --> (i + j) minus k = i + (j minus k)"); (* fail *)
(* diff_add_assoc2: *)
ripple ("a","k leq (j::nat) --> (j + i) minus k = (j minus k) + i"); (* fail *)
(* le_imp_diff_is_add: *)
ripple ("a","i leq (j::nat) --> (j minus i = k) = (j = k + i)"); (* fail *)
(* diff_is_0_eq [simp]: *)
ripple ("a","((m::nat) minus n = 0) = (m leq n)");  (* fail *)
(* zero_less_diff [simp]: *)
ripple ("a","(0 less (n minus (m::nat))) = (m less n)"); (* fail *)
(* less_diff_conv: *)
ripple ("a",  "(i less (j minus k)) = ((i + k) less j)"); (* fail *)
(*le_diff_conv:*)
ripple ("a",  "((j minus k) leq i) = (j leq (i + k))"); (* fail *)
(*lemma diff_diff_right:*)
ripple ("a",  "(k leq j) --> i minus (j minus k) = i + k minus j"); (* fail *)

(* / 20 *)

(* ---------------------------------------------------------------- *)

(* with case-split, calculation + speculation *)
structure RippleSpec =  RippleLemSpecFUN(structure RippleLemCalc = Ripple
            structure MidOutRCInfo = MidOutCInfo_g_dsum);
Trm.drop_var_args_flag := false;
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then RippleSpec.induct_ripple_lemspec);



(* 
(* Up-to, Can't use Isabelle's def, clashing less-eq definition *)
(* upt_rec: *)
ripple ("a", "[i..<j] = (if i < j then i # [Suc i..<j] else [])"); (* fail, eager if-split *)
(* upt_eq_Nil_conv:*)
ripple ("a", "([i..<j] = []) = ((j = 0) | (j leq i))"); (* fail *)
(*upt_eq_Cons_conv: *)
ripple ("a", "([i..<j] = x # xs) = ((i less j) & (i = x) & ([i + 1..<j] = xs))"); (* fail *)
(* upt_Suc_append: *)
ripple ("a", "(i leq j) --> ([i..<Suc j] = [i..<j] @ [j])"); (* fail, slow *)
(* upt_conv_Cons: *)
ripple ("a", "(i less j) --> ([i..<j] = i # [Suc i..<j])"); (* fail *)
(* length_upt: *)
ripple ("a", "len [i..<j] = (j minus i)"); 

*)
