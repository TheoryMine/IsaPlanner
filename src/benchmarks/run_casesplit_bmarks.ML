(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* Test on Peano Arithmetic benchmarks for lemma speculation using     *)
(* different combinations of definitions of plus, multiplication and   *)
(* exponentiation.                                                     *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*   PEANO ARITHMETIC THEORIES                                         *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* 
use_thy "benchmarks/CaseAnalysis_L";        
use_thy "benchmarks/synth_theories/Tree_size_height";
 *)

(* own defs of nat/list which don't use Isabelles definitions*)
use_thy "benchmarks/CaseAnalysis_L2";        
use_thy "benchmarks/Tree_size_height2";

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* different theories *)
(*val thy = theory "CaseAnalysis_L";
val thy2 = theory "Tree_size_height";
*)
(* own defs of nat/list which don't use Isabelles definitions*)
val thy = theory "CaseAnalysis_L2";
val thy2 = theory "Tree_size_height2";

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Different versions of rippling *)
val technique1 = 
("simp", InductAndSimp.induct_and_simp);

val technique2 = 
("rippling", RippleLemCalc_flow.induct_ripple_lemcalc);

structure RippleCaseSplitCalc = RippleCaseSplitCalcFUN(structure BasicRipple = RippleRTechn_flow);
val technique3 = 
("ripple_calc", RippleCaseSplitCalc.induct_ripple_lemcalc);

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Peano Arithmetic Theorems *)
val L_mem_del_thrms = [
(* ("mem_app_single_l", "x mem [x]@l"), not an inductive proof *)
("mem_app_single_r", "x mem l@[x]"),
("mem_ins","x mem (ins x l)"),
("mem_app_l", "x mem l --> x mem (l@t)"),
("mem_app_r", "x mem t --> x mem (l@t)"),
("mem_ins_noteq", "~(x=y) ==> ((x mem (ins y l)) = x mem l)"),
("mem_ins_less", "(x less y) ==> ((x mem (ins y l)) = x mem l)"),
("mem_ins1", "x mem (ins_1 x l )"),
("ins_len", "len(ins x l) = suc(len l)"),
("not_mem_del", "~(x mem (delete x l))"),
("length_del_leq", "(len (delete x l)) leq (len l)")
] (* 10 thrms with if *)

val L_filter_thrms = [
("filter_append", "filter P (xs @ ys) = filter P xs @ filter P ys"),
("rev_filter", "rev (filter P xs) = filter P (rev xs)"),
("len_filter_le", "(len (filter P xs)) leq (len xs)")
]; (*3 theorems (if) *)

val L_last_thrms = [
("last_snoc", "last (xs @ [x]) = x"),
("butlast_snoc", "butlast (xs @ [x]) = xs"),
("last_ConsL", "xs = [] ==> (last (x # xs) = x)"),
("last_ConsR", "~(xs = []) ==> (last (x # xs) = last xs)"),
("last_append", "last (xs @ ys) = (if ys = [] then last xs else last ys)"),
("last_appendL", "ys = [] ==> last (xs @ ys) = last xs"),
("last_appendR", "~(ys = []) ==> last (xs @ ys) = last ys"),
("length_butlast", "len (butlast xs) = (len xs) minus (suc 0)"),
("butlast_append", "butlast (xs @ ys) = (if ys = [] then butlast xs else xs @ butlast ys)"), 
("append_butlast_last_id", "~(xs = []) ==> butlast xs @ [last xs] = xs"),
("last_drop", "(n less (len xs)) ==> (last (drop n xs) = last xs)"),
("butlast_conv_take", "butlast xs = take ((len xs) minus (suc 0)) xs")
]; (* 12 thrms (if) *)

val L_takeWhile_dropWhile = [
("takeWhile_dropWhile_id", "takeWhile P xs @ dropWhile P xs = xs"),
("my_take_all", "takeWhile (%x. True) xs = xs"),
("my_drop_none", "dropWhile (%x. False) xs = xs")
]; (* 3 thrms (if) *)

val L_count = [ (* These are not from Isabelle *)
("count_append", "(count n l) + (count n m) = count n (l @ m)"),
("count_rev", "count n l = count n (rev l)"),
("count_leq_append", "(count n l) leq (count n (l@m))"),
("count_plus1_cons", "(suc 0) + (count n l) = count n (n#l)"),
("count_plus1_consx", "(n = x) ==> ((suc 0) + (count n l) = count n (x#l))"),
("sean_count1", "count n (x @ [n]) = suc (count n x)"),
("sean_count2", "~(n=h) ==> count n (x @ [h]) = count n x"), (*fert fail*)
("sean_count3", "count n t + count n [h] = count n (h#t)"),
("sean_count4", "count n [h] + count n t = count n (h#t)")
]; (* 9 theorems (if) *)

val L_sort = [ (* Not from Isabelle *)
("count_sort","count x l = count x (sort l)"),
("sorted_sort","sorted (sort l)"),
("sorted_insort", "sorted l ==> sorted (insort x l)"),
("len_sort", "len(sort l) = len l")
]; (* 4 thrms (if) *)

val L_zip_thrms = [
("zip_Nil", "zip [] ys = []"),
("zip_Cons_Cons", "zip (x # xs) (y # ys) = (x, y) # zip xs ys"),
("zip_Cons1", "zip (x # xs) ys = (case ys of [] => [] | y # ys => (x, y) # zip xs ys)"), (* OK, not inductive though. *)
("zip_append1", "zip (xs @ ys) zs = zip xs (take (len xs) zs) @ zip ys (drop (len xs) zs)"),
("zip_append2", "zip xs (ys @ zs) = zip (take (length ys) xs) ys @ zip (drop (length ys) xs) zs"),
("zip_rev", "len xs = len ys ==> zip (rev xs) (rev ys) = rev (zip xs ys)"),
("take_zip", "take n (zip xs ys) = zip (take n xs) (take n ys)"),
("drop_zip", "drop n (zip xs ys) = zip (drop n xs) (drop n ys)")
]; (* 8 theorems (case) *)

val L_take_drop = [
("take_0", "take 0 xs = []"),
("drop_0", "drop 0 xs = xs"), 
("take_suc_Cons", "take (suc n) (x # xs) = x # take n xs"), 
("drop_suc_Cons","drop (suc n) (x # xs) = drop n xs"),
("length_drop", "len (drop n xs) = ((len xs) minus n)"),
("take_append", "take n (xs @ ys) = (take n xs @ take (n minus (len xs)) ys)"),
("drop_append", "drop n (xs @ ys) = drop n xs @ drop (n minus (len xs)) ys"),
("drop_drop", "drop n (drop m xs) = drop (n + m) xs"),
("take_drop", "take n (drop m xs) = drop m (take (n + m) xs)"),
("drop_take", "drop n (take m xs) = take (m minus n) (drop n xs)"),
("append_take_drop_id", "take n xs @ drop n xs = xs"),
("take_map", "take n (map f xs) = map f (take n xs)"),
("drop_map", "drop n (map f xs) = map f (drop n xs)"),
("rev_take", "rev (take i xs) = drop ((len xs) minus i) (rev xs)"),
("rev_drop", "rev (drop i xs) = take ((len xs) minus i) (rev xs)")
]; (* 15 thrms (case) *)

 val nat_thrms = [
("diff_self_eq_0","m minus m = 0"),
("diff_diff_left", "(i minus j) minus k = i minus (j + k)"),
("suc_diff_diff", "((suc m) minus n) minus (suc k) = (m minus n) minus k"),
("diff_add_inverse", "(n + m) minus n = (m)"),
("diff_add_inverse2", "(m + n) minus n = (m)"),
("diff_cancel", "(k + m) minus (k + n) = m minus (n)"),
("diff_add_0", "n minus (n + m) = 0"),
("diff_comute", "(i minus j) minus k = i minus (k minus j)"),
("le_0_eq", "n leq 0 <-> n = 0"),
("le_sucI","m leq n ==> m leq (suc n)"),
("leq_add2", "n leq ((m + n))"),
("leq_add1","n leq ((n + m))"),
("le_add_suc1","i less (suc (i + m))"),
("le_add_suc2","i less (suc (m + i))")
]; (* 14 thrms (case) *)

val max_min_thrms = [
("max_commute", "max a b = max b a"),
("min_commute", "min a b = min b a"),
("max_assoc", "max (max a b) c = max a (max b c)"),
("min_assoc", "min (min a b) c = min a (min b c)"),
("min_leq1", "((min a b) = a) <-> a leq b"),
("max_leq1", "((max a b) = a) <-> b leq a"),
("min_leq2", "((min a b) = b) <-> b leq a"),
("max_leq2", "((max a b) = b) <-> a leq b")
]; (* 8 theorems *)

val tree_thrms = [
("height_mirror", "height (mirror a) = height a")
]; (* 1 theorems *)

(* Total 88 theorems *)
val all_L_nat_problems = L_mem_del_thrms @ L_filter_thrms @ L_last_thrms @
                   L_takeWhile_dropWhile @ L_count @ L_sort @ L_zip_thrms @
                   L_take_drop @ nat_thrms @ max_min_thrms; 

(* Max 3 minutes per problem *)
fun bmarkit srchf problems (thry,(technname,techn)) = 
    IsaPBenchmarksSql.benchmark_problems 
      (Time.fromSeconds 30) srchf (technname,techn) 
      (IsaPBenchmarksSql.mk_problems (theory thry) problems);


(* create all possible pairs with fst element from the first list
and snd element from teh second list *)
fun all_pairs xs ys = 
    let 
      fun all_pairs_aux yss [] _ acc = acc
        | all_pairs_aux yss (x::xs) [] acc = 
          all_pairs_aux yss xs yss acc
        | all_pairs_aux yss (xs as (x1::x1s)) (y::ys) acc = 
          all_pairs_aux yss xs ys ((x1,y)::acc)
    in
      all_pairs_aux ys xs ys []
    end;

(* Benchmark the case-split problems *)
bmarkit PPInterface.depth_fs all_L_nat_problems ("CaseAnalysis_L2", technique1) ;
bmarkit PPInterface.depth_fs tree_thrms ("Tree_size_height2", technique1) ;

bmarkit PPInterface.depth_fs all_L_nat_problems ("CaseAnalysis_L2", technique2) ;
bmarkit PPInterface.depth_fs tree_thrms ("Tree_size_height2", technique2) ;

bmarkit PPInterface.depth_fs all_L_nat_problems ("CaseAnalysis_L2", technique3) ;
bmarkit PPInterface.depth_fs tree_thrms ("Tree_size_height2", technique3) ;

exit 0;
