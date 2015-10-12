(* 
   use_thy "InductiveSetsDefs"; 
*)
Trm.drop_var_args_flag := false;
context (theory "Main");
val thry = (theory "Main");
val p = Prf.init (the_context());
val t = 
    Prf.read_top_term 
      p "g = f ==> EX x. f x ==> (EX y. g y)";
val (g,p) = p |> Prf.conj_top_term "g" t;

(* backward proof method *)
val premeth_p = p;
val p = Prf.prep_bck_subprf "g" p;
val (exi_name, p) = p |> Prf.insert_thm (thm "exE");

val [([g2,g3],p2)] = 
  Seq.list_of (Prf.apply_res exi_name "g" p);

val [(gs,p3)] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (Prf.apply_res "HOL.exEf" "HOL.exEe" p2)
);

raise ERROR "--- DONE ---";

(* enter goal_resol *)
val r_name = exi_name;
val g_name = "g";
val flexes = Trm.mk_flexes (Prf.get_ffs p);
val p = Prf.get_aprf p;

open DB_APrf;

(* ... *)
val Meth(MOpen, gavoid) = nd_get_meth g_nd ;
(* ... *)
val [(new_vars, (all_vars, ((rienv, pienv), flexes)))] =
    Seq.list_of unifs;

InstEnv.print thry result_ienv;
InstEnv.print thry goal_ienv;


APrf.print_full p;




 
Prf.print_full p2;

val [([g2],p2)] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (Prf.apply_res "i" "m" p2)
);

(* RAISES EXCEPTION *)

val ap = Prf.get_aprf p;
val flexes = Trm.mk_flexes (map (pair "") (Prf.get_ffs p2));

APrf.print_full ap;

val [([g2],(flexes,ap))] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (APrf.apply_goal_resol "i" "m" (flexes,ap))
);



writeln "DONE!!!";


(* 
val [([],(flexes,p2))] = 
PolyML.exception_trace (fn () => 
  Seq.list_of (APrf.apply_resol "g" "n" (flexes,p2))
);

APrf.print_full p2;

writeln "PROVED!!!";

 *)

(* 
open DB_APrf;

val r_name = "k";
val goal_name = "l";

APrf.print_full_node p "g";
APrf.print_full_node p "h";
APrf.print_full_node p "i";
APrf.print_full_node p "j";
*)