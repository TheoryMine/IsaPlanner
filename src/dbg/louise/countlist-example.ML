use_thy "/Users/lad/Systems/IsaPlanner/IsaPlanner/src/dbg/louise/count_list";
val thry = theory "count_list";
val rippling = RippleLemCalc.induct_ripple_lemcalc;
  
(* theorem memlem: "[| x mem l; ~ aa mem l |] ==> ~x = aa" *)

(*theorem count_list_not_mem: "~(x mem list) ==> count_list x list = 0"*)

val rst = PPInterface.ipp thry (rippling "g") ("g","~(x mem list) ==> count_list x list = 0");

fun just_rst g rst = 
    let
      val ((ihc, ihhs), rst2) = (lift_hyp g rst);
    in
      rst2
    end;


fun ripple_then_lift_hyp g rst =
    rst |>  rippling g
        |> just_rst g;
 
val goal = "aa";

val ihs_aa = get_ihs goal rst;
(* val ihs_ae = get_ihs rst "ae"; *)

val ((ihc, ihh2s), rst2) = lift_hyp goal rst;

val cex_goal_list = pick_res_goals rst2;

val ihs as (ih::_) = get_ihs rst goal;


val rst_triples as (((rst3::_), gc, ih)::_) = rstates_can_be_fertilised goal (RState.get_goalnames rst) rst;

val (seq, hyp) =  (try_forward_rippling thry rst3);
val rst4s as (rst4::_) = Seq.list_of seq;

val (rst5s as rst5::_) = Seq.list_of (RippleRTechn.rsteps_on_goal hyp rst4 );
val (rst6s as rst6::_) = Seq.list_of (RippleRTechn.rsteps_on_goal "not_eq_or_mem_cons_lisw" rst5 );

(*
val rst = PPInterface.ipp thry (rippling "g") ("g","~(x mem list) ==> count_list x list = 0")

val cl1rst = PPInterface.ipp thry (rippling "g") ("g","count_list x (l1 @ l2) = (count_list x l1) + (count_list x l2)");

val slrst = PPInterface.ipp thry (rippling "g") ("g", "sub_list l1 l2 ==> sub_list (tl l1) l2");

val sl2rst = PPInterface.ipp thry (rippling "g") ("g", "sub_list l1 (tl l2) ==> sub_list l1 l2");

val sl3rst = PPInterface.ipp thry (rippling "g") ("g", "sub_list l1 l2 ==> sub_list (tl l1) (tl l2)");

val sl4rst = PPInterface.ipp thry (rippling "g") ("g", "[| ~((hd l1) = (hd l2)); (sub_list l1 l2) |] ==> sub_list l1 (tl l2)");

val sl5rst = PPInterface.ipp thry (rippling "g") ("g", "[| sub_list l1 l2; sub_list l2 l3 |] ==> sub_list l1 l3");

val sl6rst = PPInterface.ipp thry (rippling "g") ("g", "sub_list l1 l2 ==> sub_list l1 (l2 @ l3)");

val sl7rst = PPInterface.ipp thry (rippling "g") ("g", "sub_list l1 l2 ==> sub_list l1 (l3 @ l2)");

val sl8rst = PPInterface.ipp thry (rippling "g") ("g", "[|sub_list l1 l2; sub_list l3 l4|] ==> sub_list (l1@l3) (l2 @ l4)");

*)

val big_imp_s = mk_big_imp rst2 "IsaP_split_is";

val big_imp_q = mk_big_imp rst2 "IsaP_split_iq";

val cex_s =  CounterExCInfo.quickcheck_term (RstPP.get_theory rst2) (CounterExCInfo_DB.codegen_params, []) (big_imp_s);

val cex_q =  CounterExCInfo.quickcheck_term (RstPP.get_theory rst2) (CounterExCInfo_DB.codegen_params, []) (big_imp_q); 

val glist = RState.get_goalnames rst2;

