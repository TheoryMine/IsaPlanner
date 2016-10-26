theory T_2
imports IsaP 
uses "../myrippling.ML" "../nlproof.ML"
begin

datatype "T_2" =  "C_4" "T_2" "HOL.bool"  | "C_3" "Nat.nat" "Nat.nat" 
declare nat.inject[wrule]

fun f_0 :: "T_2 => nat => nat" where
  "f_0 (C_3 a b) c = c"
| "f_0 (C_4 a b) c = Suc (f_0 a (Suc (f_0 a (Suc c))))"


declare f_0.simps[wrule]

ML{* 
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
            | SOME (rst,altrsts) => 
              SOME rst
    in
      rst_opt
    end;

val rst_opt = a_rippling_test @{context} "Suc (f_0 a (Suc b)) = f_0 a (Suc (Suc b))"
val pplan_opt = case rst_opt of NONE => NONE | SOME x => SOME (RState.get_pplan x)
val prf_opt = case pplan_opt of NONE => NONE | SOME x => SOME (PPlan.get_prf x)

*}
ML{* val _ = case rst_opt of NONE => NONE | SOME rst => SOME (Pretty.writeln (HTraceCInfo.pretty_rst rst)) *}
ML{* val cinfo_opt = case rst_opt of NONE => NONE | SOME x => SOME (RState.get_cinfo x) *}
ML{* val htrace_opt = case cinfo_opt of NONE => NONE | SOME x => SOME (HTraceCInfo.I.get_from_cinfo x) *}
ML{* val t_opt = case htrace_opt of NONE => NONE | SOME x => SOME (HTraceCInfo.get_from_trace x) *}
ML{* val trees_opt = case t_opt of NONE => NONE | SOME (x,_) => SOME x *}
ML{*

local open HTraceCInfo in
datatype tr = Tr of (string * tr list)

fun uton (Tree ((_,rst),ch)) = Tr (DescripCInfo.string_of_rst rst, map uton ch)

val tree_opt = case trees_opt of NONE => NONE | SOME (h::t) => SOME (uton h)

end;
 *}

ML{* val x_opt = case t_opt of NONE => NONE | SOME (h::t) => SOME h *}
ML{* val t_opt = case tree_opt of NONE => NONE | SOME (x::_,_) => SOME (HTraceCInfo.get_from_tree x) *}
ML{* val x_opt = case t_opt of NONE => NONE | SOME ((_,x),_) => SOME (PolyML.print (DescripCInfo.I.get_from_rst x)) *}
ML{* val x_opt = case t_opt of NONE => NONE | SOME ((_,x),_) => SOME (DescripCInfo.string_of_rst x) *}


ML{*
fun go_to id tree (gives entry of id from the tree)

fun t_t id tree copy = 
    if (go_to id tree) = []
    then
      
    else

 *}

ML{* case rst_opt of NONE => NONE | SOME x => SOME (Pretty.writeln (HTraceCInfo.pretty_cmp_rst x)) *}
ML{* case rst_opt of NONE => NONE | SOME x => SOME (Pretty.writeln (PPInterface.pretty_rst x)) *}
ML{* case pplan_opt of NONE => NONE | SOME x => SOME (PPlan.print x) *}
ML{* case prf_opt of NONE => NONE | SOME x => SOME x *}

ML{* my_rippling @{context} ["Suc (f_0 a (Suc b)) = f_0 a (Suc (Suc b))"] *}
