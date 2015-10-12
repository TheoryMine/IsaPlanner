Trm.drop_var_args_flag := false;
use_thy "examples/N";
ML_Context.set_context (SOME (Context.Theory (theory "N")));
val thry = (theory "N");

val rippling = RippleRTechn.induct_ripple_conj;

val rsts = 
PolyML.exception_trace (fn () => 
    (PPInterface.prep_rst rippling ("g", "(a * b) *c = a * (b * (c::N))")) 
      |> RState.search (MSearch.depthfs ())
      |> Seq.list_of);


val SOME (thry, ienv, flexes, t) = 
    ((PPInterface.prep_rst rippling ("g", "(a * b) *c = a * (b * (c::N))")) 
       |> RState.search (MSearch.depthfs ())
       |> Seq.list_of; NONE)
    handle LemmaConjLib.try_mk_eq_conj_exp x => SOME x;


raise ERROR "done!";

open DB_LemmaConjLib;

open DB_APrf;



(* 
val SOME (r_name, g_r, z, flexes, p) = 
    ((PPInterface.prep_rst rippling ("g", "(a * b) *c = a * (b * (c::N))")) 
       |> RState.search (MSearch.depthfs ())
       |> Seq.list_of; NONE)
    handle APrf.subst_exp x => SOME x;


val rsts = 
PolyML.exception_trace (fn () => 
    (PPInterface.prep_rst rippling ("g", "(a * b) *c = a * (b * (c::N))")) 
      |> RState.search (MSearch.depthfs ())
      |> Seq.list_of);
*)