use_thy "examples/isabelle_ws_2007/critics_isabelleWS07";
Trm.drop_var_args_flag := false;
val thry = theory "critics_isabelleWS07";
val rippling = RippleLemSpec.induct_ripple_lemspec;

(* should be provable by lemma spec *)
val myrst = PPInterface.ipp thry (rippling "a") ("a","rev(rev(x) @ y) = rev(y) @ x");

PolyML.exception_trace (fn () =>
  PPInterface.ipp thry (rippling "a") ("a","rev(rev(x) @ y) = rev(y) @ x")
);

(* not provable by lemma spec *)
val myrst = PPInterface.ipp thry (rippling "a") ("a", "rotate (len x) (x @ y) = y @ x"); 

val rst = the (!PPInterface.last_rst);

PolyML.exception_trace (fn () => 
  PPInterface.ipp thry (rippling "a") ("a","rev(rev(x) @ y) = rev(y) @ x")
);

 PolyML.exception_trace (fn () =>  Seq.pull(RState.unfold rst)  );

val SOME (embeddings, goal) = 
    (PPInterface.ipp thry (rippling "a") ("a", "rotate (len x) (x @ y) = y @ x"); NONE) 
    handle LemmaSpec.lemmaspec2_exp x => SOME x;

val SOME (goal_params, e) = 
    (PPInterface.ipp thry (rippling "a") ("a", "rotate (len x) (x @ y) = y @ x"); NONE) 
    handle LemmaSpec.mk_lemma_exp x => SOME x;
