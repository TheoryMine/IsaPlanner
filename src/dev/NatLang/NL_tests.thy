theory NL_tests
imports Main IsaP
begin

ML_file "nlproof.ML"  
ML_file "rippling-interface.ML"

datatype "T" = "C_1" "HOL.bool" "HOL.bool" | "C_2" "T"
declare bool.simps[wrule]

fun f_1 :: "T => T => T" where
  "f_1 (C_1 x y) z = z"
| "f_1 (C_2 x) y = C_2 (f_1 x y)"

declare f_1.simps[wrule]

ML{*  val rst = a_rippling_rst @{context} "f_1 b (f_1 a c) = f_1 a (f_1 b c) " *}
  
ML{*
 val k = NLProof.nlproof_init rst "f_1"
 val _ = NLProof.print @{context} "f_1" k
 *}


 
ML{* val prf = PPlan.get_prf (RState.get_pplan rst) *}
ML{* val _ = Pretty.writeln (APrf.pretty prf) *}
ML{* 
val prf_is_complete = null (RState.get_goalnames rst)
    val fs = if prf_is_complete then fst else 
              (fn x => case (snd x) of NONE => [] 
              | SOME t => (t |> HTraceCInfo.get_from_trace |> fst))
    val htr = rst |> RState.get_cinfo 
                  |> HTraceCInfo.I.get_from_cinfo 
                  |> HTraceCInfo.get_from_trace
                  |> fs |> hd 
    val ccc = HTraceCInfo.pretty (HTraceCInfo.I.get_from_cinfo (RState.get_cinfo rst))
    val x = Pretty.writeln ccc
*}
 
datatype T_14 = "C_1" "bool" | "C_2" "T_14" "bool"
declare bool.simps[wrule]
declare nat.inject[wrule]
declare T_14.inject[wrule]

fun f_2 :: "T_14 \<Rightarrow> nat \<Rightarrow> nat" where
 "f_2 (C_1 a) b = b"
| "f_2 (C_2 a b) c = f_2 a (Suc c)"

declare f_2.simps[wrule]

ML{*  val rst = a_rippling_rst @{context} "f_2 a (f_2 b c) = f_2 b (f_2 a c)" *}
ML{* val prf = PPlan.get_prf (RState.get_pplan rst) *}
ML{* val _ = Pretty.writeln (APrf.pretty prf) *}
ML{* 
val prf_is_complete = null (RState.get_goalnames rst)
    val fs = if prf_is_complete then fst else 
              (fn x => case (snd x) of NONE => [] 
              | SOME t => (t |> HTraceCInfo.get_from_trace |> fst))
    val htr = rst |> RState.get_cinfo 
                  |> HTraceCInfo.I.get_from_cinfo 
                  |> HTraceCInfo.get_from_trace
                  |> fs |> hd 
    val ccc = HTraceCInfo.pretty (HTraceCInfo.I.get_from_cinfo (RState.get_cinfo rst))
    val x = Pretty.writeln ccc
*}
ML{*
 val k = NLProof.nlproof_init rst "f_2"
 val _ = NLProof.print @{context} "f_2" k
 *}

(*
f<sub>&omicron;</sub> : T<sub>14</sub> &times;  &#8469; &#8594; &#8469;
</td></tr></table>
<table>
<tr><td width="48%" align="right">
  f<sub>&omicron;</sub>(C<sub>z</sub>(a), b)
</td><td width="4%" align="center">=</td><td width="48%" align="left">
  b
</td></tr>
<tr><td width="48%" align="right">
  f<sub>&omicron;</sub>(C<sub>y</sub>(a, b), c)
</td><td width="4%" align="center">=</td><td width="48%" align="left">
  f<sub>&omicron;</sub>(a, Suc(c))
</td></tr>
</table>

';

$theorems = array();
array_push($theorems,
           array('proof' => 'induction and rippling',
                 'statement' => 'f<sub>&omicron;</sub>(a, f<sub>&omicron;</sub>(b, c)) = f<sub>&omicron;</sub>(b, f<sub>&omicron;</sub>(a, c))'));
array_push($theorems,
           array('proof' => 'induction and rippling',
                 'statement' => 'f<sub>&omicron;</sub>(a, Suc(b)) = Suc(f<sub>&omicron;</sub>(a, b))'));
array_push($theorems,
           array('proof' => 'induction and rippling',
                 'statement' => 'Suc(f<sub>&omicron;</sub>(a, b)) = f<sub>&omicron;</sub>(a, Suc(b))'));

*)
datatype "T_6" =  "C_12" "T_6" "HOL.bool"  | "C_11" "HOL.bool" "HOL.bool" 

declare bool.simps[wrule]
declare nat.inject[wrule]
declare T_6.inject[wrule]

fun f_3 :: "T_6 => nat => nat" where
  "f_3 (C_11 a b) c = Suc (Suc c)"
| "f_3 (C_12 a b) c = Suc (f_3 a (Suc (f_3 a c)))"

declare f_3.simps[wrule]

ML{*  val rst = a_rippling_rst @{context} "f_3 a (f_3 b c) = f_3 b (f_3 a c)" *}
  
ML{*
 val k = NLProof.nlproof_init rst "f_3"
 val _ = NLProof.print @{context} "f_3" k
 *}



end