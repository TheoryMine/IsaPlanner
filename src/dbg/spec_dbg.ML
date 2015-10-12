
(* Bug chase: after new ripple measure introduced *)
use_thy "examples/isabelle_ws_2007/critics_isabelleWS07";
Trm.drop_var_args_flag := false;
val thy = theory "critics_isabelleWS07";
val ctxt = ProofContext.init thy;
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then RippleLemSpec.induct_ripple_lemspec);

val SOME (params, e) = (ripple ("a", "evenR(x + x)"); NONE)
                       handle LemmaSpec.mk_lemma_exp x => SOME x;
val lhs = (Embed.tgt e) 
val rhs = (Embed.src e);
Trm.print ctxt lhs; Trm.print ctxt rhs; 
Thm.cterm_of thy lhs;
val mvar_rhs = snd (MetaVarLib.insert_metavars_embedding 
                              params e);
Trm.print ctxt mvar_rhs; 


(* hounifiers_exp *)
structure RippleCalc = RippleLemCalcFUN(structure BasicRipple = RippleCaseSplit);
structure Ripple = RippleLemSpecFUN(structure RippleLemCalc = RippleCalc
                   structure MidOutRCInfo = MidOutCInfo_g_dsum);
use_thy "benchmarks/Trees";
Trm.drop_var_args_flag := false;
val ripple =  PPInterface.ipp (the_context()) (RTechnEnv.map_then Ripple.induct_ripple_lemspec);

PolyML.exception_trace (fn () =>
ripple ("a", "foldl (%a. %l.  a + (len l)) nn ((rev a) @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)")
);

(* ho-unification exp *)
PolyML.exception_trace (fn () =>
ripple ("a", "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"));
val SOME (rz, gz, ppl, rule_nm) = 
    (ripple ("a", "foldl f a (xs @ ys) = foldl f (foldl f a xs) ys"); NONE) 
    handle MiddleOutRW.my_exp x => SOME x;

my_exp of (Zipper.T  * Zipper.T* DB_Prf.T * DB_Prf.gname)


val SOME (s,(r_name, g_r, z, flexes, p)) = 
    (ripple ("a", "foldl (%a. %l.  a + (len l)) nn ((rev a) @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)"); NONE)
    handle APrf.subst_exp x => SOME x;

    handle DB_RippleWRules.ripple_wrulesdb_apply_exp x => SOME x;

val thm = (RippleWRules.rule_of_wrule wrule);
val sym = false;
val ffp = prf;

open DB_Subst;

    handle RippleCInfo.lookup_arules_exp x => SOME x;

open RippleWRules;

open RippleCInfo;

PolyML.exception_trace (fn () =>
Seq.list_of eqs );


val prf = pplan;
val z = (Zipper.mktop t);

Seq.maps (WRNet.matchings (get_eqrule_net db) prf gname)
             ((get_searchf db) z);

val zlist = Seq.list_of ((get_searchf db) z);



use "ROOT.ML";
use_thy "critics/ctest";
Trm.drop_var_args_flag := false;
val ripple =  PPInterface.ipp (RTechnEnv.map_then RippleLemSpec.induct_ripple_lemspec);

PolyML.exception_trace (fn () => ripple ("a","rev((rev x)) @ y = rev(rev (x@y))"));
val (rz, (n,ty), gz, ppl) = the ((ripple ("a","rev((rev x)) @ y = rev(rev (x@y))"); NONE) handle MiddleOutRW.inst_mvar_exp x => SOME x);
val (zip,ppl,rulenm) = the ((ripple ("a","rev((rev x)) @ y = rev(rev (x@y))"); NONE) handle MiddleOutRW.my_exp x => SOME x);

val ts = the ((ripple ("a","rev((rev x)) @ y = rev(rev (x@y))"); NONE) handle LemmaSpec.my_ex x => SOME x);

 val (ppl,t) = the ((Seq.list_of(MiddleOutRW.midout_rw "n" rst2);NONE ) handle APrf.term_is_not_valid_exp x => SOME x);
use_thy "examples/N";
val env = the ((ripple ("a","x+suc(x) = suc(x+x)"); NONE) handle InstEnv.bad_ienv_exp x => SOME x); 
val (str,env) = the ((ripple ("a", "foldl (%a. %l.  a + (len l)) nn ((rev a) @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)"); NONE) handle InstEnv.bad_ienv_exp x => SOME x);

val (t1,t2) = the ((ripple ("a", "foldl (%a. %l.  a + (len l)) nn ((rev a) @ b) = foldl (%a. %l. a + (len l)) nn (b @ a)"); NONE) handle DB_EmbeddingLib.embedding_term_exp x => SOME x);

Trm.print (ProofContext.init (the_context())) t;

(* Error term
foldl (%a l. a + len l) no ((rev a2 @ [a1]) @ c) =
foldl (%a l. a + len l) no
 (foldl (%a. ?f2 a1 a (c @ a2)) (?a2 a1 (c @ a2))
   (?xs2 a1 (c @ a2) @ ?ys2 a1 (c @ a2)) a2 c no) 

Error env: 
 InstEnv.print (the_context()) env;
TVars: ['b : type == 'a]
Vars: [xs2 : 'a list
             => 'a list list => 'a list == %argabs1 argabs0. argabs1,
        f2 : 'a list
             => ('a list list => 'a list list => nat => 'a list list)
                => 'a list list
                   => 'a => 'a list list
                            => 'a list list
                               => nat
                                  => 'a list list == %argabs6 argabs5
                  argabs4 argabs3 argabs2 argabs1 argabs0. argabs4,
        a2 : 'a list
             => 'a list list
                => 'a list list
                   => 'a list list
                      => nat
                         => 'a list list == %argabs4 argabs3 argabs2 argabs1
         argabs0. argabs3]
*)



val (s,tys,trms) = the ((ripple ("a","rev(rev(x) @ y) = rev(y) @ x"); NONE) handle TYPE (s,tys,trms) => SOME (s,tys,trms));


(* Exception *)
use_thy "examples/critics_isabelleWS07";
val (thry, (ienv, [(t1,t2)])) = the ((ripple("a", "evenR(len(x@x))"); NONE) handle MyUnify.hounifiers_exp (thry, (ienv, [(t1,t2)]))  => SOME (thry, (ienv, [(t1,t2)])));

val (thry, trms, ienv)  = the ((ripple("a", "rotate (len x) (x @ y) = y @ x"); NONE) handle TypUnify.unify_typsof_terms_exp (thry, trms, ienv) => SOME (thry, trms, ienv));

val (thry, trms, ienv)  = the ((ripple("a", "foldl (%a. %l.  a + (len l)) n (in_ord t)  = foldl (%a. %l. a + (len l)) n (postord t)"); NONE) handle TypUnify.unify_typsof_terms_exp (thry, trms, ienv) => SOME (thry, trms, ienv));

(* Trying to ripple a goal containing a meta-variable *)
PolyML.exception_trace (fn () => ripple ("a", "rev(x) @ (h#t) = ?F(rev(x)) @ t")); 


 val (ppl,t) = the ((ripple ("a","rev((rev x)) @ y = rev(rev (x@y))");NONE ) handle APrf.term_is_not_valid_exp x => SOME x);
