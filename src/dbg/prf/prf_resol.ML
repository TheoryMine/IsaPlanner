(* use "ROOT.ML"; *)

Trm.drop_var_args_flag := false;

ML_Context.set_context (SOME (Context.Theory (theory "Main")));
val thry = (theory "Main");
val p = Prf.init (the_context());
val t =  
    Prf.read_top_term 
      p "!! x. ((!! x. R x x) ==> (!! x y. R x y ==> Q x y y) ==> (!!y. Q x (?z x) y ==> P x y (?z x)) ==> P x (?z x) (?w x))";
val p = Prf.init (the_context());
val t =  
    Prf.read_top_term 
      p "!! x. ((!! y. R y y) ==> (!! z y. R z y ==> Q z y y) ==> (!!y. Q x (?v x) y ==> P x y (?v x)) ==> P x (?v x) (?v2 x))";

val (g,p) = p |> Prf.conj_top_term "g" t;

val (nnd,(cxn,cx)) = APrf.get_result (Prf.get_aprf p) "j";
Cx.print thry cx;

Prf.print_script p;

val [([g2],p2)] =  Seq.list_of (Prf.apply_resol_bck "k" "g" p);
 
Prf.print_script p2;

val [([g2],p2)] = Seq.list_of (Prf.apply_resol_bck "i" "m" p2);

Prf.print_script p2;

val [([],p2)] = Seq.list_of (Prf.apply_resol_bck "h" "n" p2);

Prf.print_script p2;

writeln "DONE!!!";

(* 
open DB_APrf;

val r_name = "k";
val goal_name = "l";

APrf.print_full_node p "g";
APrf.print_full_node p "h";
APrf.print_full_node p "i";
APrf.print_full_node p "j";
*)
