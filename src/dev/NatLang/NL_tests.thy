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
 
 
 
 
ML{* val tree = let val (x::t,_) = (HTraceCInfo.get_from_trace new_htrace) in x end *}
ML{* val from_tree = HTraceCInfo.get_from_tree tree *}
ML{* val rst = let val ((_,x),_) = from_tree in x end*}
ML{* DescripCInfo.string_of_rst rst *}



datatype "T_6" =  "C_12" "T_6" "HOL.bool"  | "C_11" "HOL.bool" "HOL.bool" 

declare nat.inject[wrule]
declare T_6.inject[wrule]

fun f_2 :: "T_6 => nat => nat" where
  "f_2 (C_11 a b) c = Suc (Suc c)"
| "f_2 (C_12 a b) c = Suc (f_2 a (Suc (f_2 a c)))"

declare f_2.simps[wrule]


ML{*  
use "~/IsaPlanner/src/dev/NatLang/rippling-interface.ML";

fun a_rippling_test ctx goal = 
    let
      val rsts_opt = 
        PPInterface.init_rst_of_strings ctx [goal]
         |> RState.set_rtechn (SOME (RTechnEnv.map_then MyRippling.induct_ripple_lemcalc))
         |> GSearch.breadth_fs (fn rst => is_none (RState.get_rtechn rst)) RState.unfold 
         |> Seq.filter RstPP.solved_all_chk
         |> Seq.pull;
      val rst_opt =
            case rsts_opt of 
              NONE => NONE
            | SOME (rst,altrsts) => SOME rst
    in rst_opt end;


val rst_opt = a_rippling_rst @{context} "f_2 a (f_2 b c) = f_2 b (f_2 a c)";

*}

(*val pplan_opt = case rst_opt of NONE => NONE | SOME x => SOME (RState.get_pplan x)
val prf_opt = case pplan_opt of NONE => NONE | SOME x => SOME (PPlan.get_prf x)

val _ = case rst_opt of NONE => NONE | SOME rst => SOME (Pretty.writeln (HTraceCInfo.pretty_rst rst))
val cinfo_opt = case rst_opt of NONE => NONE | SOME x => SOME (RState.get_cinfo x) 
val htrace_opt = case cinfo_opt of NONE => NONE | SOME x => SOME (HTraceCInfo.I.get_from_cinfo x) 
val t_opt = case htrace_opt of NONE => NONE | SOME x => SOME (HTraceCInfo.get_from_trace x) 
val trees_opt = case t_opt of NONE => NONE | SOME (x,_) => SOME x 


local open HTraceCInfo in
datatype tr = Tr of (string * tr list)

fun uton (Tree ((_,rst),ch)) = Tr (DescripCInfo.string_of_rst rst, map uton ch)

val tree_opt = case trees_opt of NONE => NONE | SOME (h::t) => SOME (uton h)

end; 

val x_opt = case t_opt of NONE => NONE | SOME (h::t) => SOME h 
val t_opt = case tree_opt of NONE => NONE | SOME (x::_,_) => SOME (HTraceCInfo.get_from_tree x) 
val x_opt = case t_opt of NONE => NONE | SOME ((_,x),_) => SOME (PolyML.print (DescripCInfo.I.get_from_rst x)) 
val x_opt = case t_opt of NONE => NONE | SOME ((_,x),_) => SOME (DescripCInfo.string_of_rst x) 

*)


ML{*
val x = my_r ippling @{context}  ["f_2 a (f_2 b c) = f_2 b (f_2 a c)"] 
*}

ML{*
val _ = NLProof.print 
*}

end