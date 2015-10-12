(* use "ROOT.ML"; *)

Trm.drop_var_args_flag := false;

context (theory "Main");
val thry = (theory "Main");
val p = Prf.init (the_context());
val t =  
    Prf.read_top_term 
      p "!! x. ((!! x. R x x) ==> (!! x y. R x y ==> Q x y y) ==> (!!y. Q x (?z x) y ==> P x y (?z x)) ==> P x (?z x) (?w x))";

val suggested_name = "g";

val (g,p) = p |> Prf.conj_top_term "g" t;
Prf.print_script p;


val p = Prf.get_aprf p;
open DB_APrf;
      val top_cxname = get_top_cxname p
      val cxtab = fold add_r_to_cxtab 
                       (map (get_result p) (GoalNTab.keys (get_goals p)))
                       CxNTab.empty;

CxNTab.print (fn (cx,l) => 
                 Pretty.block [Pretty.str "in: ", (Cx.pretty_cx_ancestors cx),
                               Pretty.str " results: ",
                               Pretty.list "[" "]" (map (Pretty.str o fst) l)]) 
             cxtab;



Prf.print_open p;
Prf.print_full p;
Prf.print_script p;

val [([g2],p2)] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (Prf.apply_res "h" "g" p)
);
 
Prf.print_full p2;

val [([g2],p2)] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (Prf.apply_res "j" "m" p2)
);


Prf.print_full p2;

val [([],p2)] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (Prf.apply_res "l" "n" p2)
);

Prf.print_full p2;

writeln "PROVED!!!";

(* 
open DB_APrf;

val r_name = "k";
val goal_name = "l";

APrf.print_full_node p "g";
APrf.print_full_node p "h";
APrf.print_full_node p "i";
APrf.print_full_node p "j";
*)