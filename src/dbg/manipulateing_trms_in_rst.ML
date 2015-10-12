Trm.drop_var_args_flag := false;

val thry = theory "Main";
val rst0 = RstPP.init thry;

set show_types;

val rst = rst0;
(* induction on Z *)
val (an,rst) = rst |> RstPP.new_conj_of_str ("a", "Trueprop Q");
(* induction on Z *)
val (bn,rst) = rst |> RstPP.new_conj_of_str ("b", "Trueprop P");

val t1 = RstPP.goal_concl rst an;
val t2 = RstPP.goal_concl rst bn;

val t3 = Logic.mk_implies (t1, t2);

TermDbg.writeterm t3; 

val (cn,rst) = rst |> RstPP.new_conj ("c", t3);

raise ERROR "stop";
