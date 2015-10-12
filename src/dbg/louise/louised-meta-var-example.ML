Trm.drop_var_args_flag := false;

use_thy "examples/isabelle_ws_2007/critics_isabelleWS07";
val thry = theory "critics_isabelleWS07";
val rst0 = RstPP.init thry;

set show_types;

(* induction on Z *)
val (bc,rst0) = 
    rst0 |> RstPP.new_conj_of_str
         ("base case", 
          "Trueprop (X @ (Y#[]) = ((?G::'a List => 'a => 'a List => 'a List) X Y []) @ [])");
val (sc,rst0) = 
    rst0 |> RstPP.new_conj_of_str
         ("step case", 
          "(!! X Y. (X @ (Y#t) = ((?G::'a List => 'a => 'a List => 'a List) X Y t) @ t)) ==> (X @ (Y#(h#t)) = (?G X Y (h#t)) @ (h#t))");

(* val (bc,rst) = 
    rst |> RstPP.new_conj 
        ("base case", 
         RstPP.read_top_term rst "Trueprop ([] @ (Y#Z) = (?G [] Y Z) @ Z)");
val (sc,rst) = 
    rst |>  RstPP.new_conj 
        ("step case", 
         RstPP.read_top_term rst "(!! Y Z. (t @ (Y#Z) = (?G t Y Z) @ Z)) ==> ((h#t) @ (Y#Z) = (?G (h#t) Y Z) @ Z)");
*)

val rst = rst0;

reset show_types;

val (rsts as (rst::_)) = Seq.list_of (RippleLemSpec.BasicRipple.startr_on_goal sc rst);
val oldskels = RippleLemSpec.BasicRCInfo.all_skels_of rst sc;
val (rsts as (rst::_)) = Seq.list_of (RippleLemSpec.init_midout_cinfos oldskels sc rst); 
val _ = Pretty.writeln (RippleCInfo.pretty rst sc); 

val L1 = Seq.list_of (Seq.maps (RippleLemSpec.do_midout_ripple_step sc) (Seq.of_list rsts));

val L2 = Seq.list_of (MiddleOutRW.midout_rw sc rst);


raise ERROR "stop";


PolyML.exception_trace (fn ()           );

