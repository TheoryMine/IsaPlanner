use_thy "benchmarks/CaseAnalysis_L";
val thy = theory "CaseAnalysis_L";

val ectxt = Ectxt.init (InstEnv.init thy) ParamRGraph.empty;

val s2 = (((Const("CaseAnalysis_L.zip", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])])]))) $
 (Const("List.list.Nil", Type("List.list", [TFree("'a", ["HOL.type"])])))) $
 (Free("yt", Type("List.list", [TFree("'a", ["HOL.type"])]))));

val t2 = ((((Const("List.list.list_case", Type("fun", [Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])]), Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])])])]))) $
 (Const("List.list.Nil", Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])))) $
 (Abs("z",TFree("'a", ["HOL.type"]), 
  Abs("zs",Type("List.list", [TFree("'a", ["HOL.type"])]), 
  ((Const("List.list.Cons", Type("fun", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])]), Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])])]))) $
 (((Const("Product_Type.Pair", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", [TFree("'a", ["HOL.type"]), Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])]))) $
 (Bound(1))) $
 (Free("a", TFree("'a", ["HOL.type"]))))) $
 (((Const("CaseAnalysis_L.zip", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [Type("*", [TFree("'a", ["HOL.type"]), TFree("'a", ["HOL.type"])])])])]))) $
 (Bound(0))) $
 (Free("yt", Type("List.list", [TFree("'a", ["HOL.type"])])))))))) $
 (Const("List.list.Nil", Type("List.list", [TFree("'a", ["HOL.type"])]))));

val ctxt = ProofContext.init thy;

Trm.print ctxt s2;
Trm.print ctxt t2;

(* PolyML.Debug.clearIn "DB_Embed.embed"; *)
(* PolyML.Debug.breakIn "DB_Ectxt.lookup_bnd_wf";
PolyML.Debug.up();
PolyML.Debug.down();
PolyML.Debug.variables();
PolyML.Debug.continue();
PolyML.Debug.clearIn "DB_Ectxt.lookup_bnd_wf"; *)
(* PolyML.Debug.breakIn "DB_Embed.embed_into_some_subpos"; *)
PolyML.Debug.breakIn "DB_Embed.solve_bnd_embedding_agenda";

(* PolyML.Debug.continue();

*)


PolyML.Debug.trace true;

PolyML.exception_trace (fn () =>  
Seq.list_of (DB_Embed.embed ectxt s2 t2)
);

(* 
open DB_Embed;

val (SOME ((n,(wfn,t)), a2)) = Em.NTab.pull_elem (get_agenda e);
val wf = Wf.NTab.get (get_wfs e) wfn;

*)

(* 
Embed.app_embeddings 
  ectxt
  (Term.strip_comb (Pattern.eta_long [] s))
  (Term.strip_comb (Pattern.eta_long [] t));
*) 

(*
use_thy "benchmarks/CaseAnalysis_L";
val thy = theory "CaseAnalysis_L";
structure Ripple = RippleLemCalc;
val ripple =  PPInterface.ipp thy (RTechnEnv.map_then Ripple.induct_ripple_lemcalc);

val SOME e = 
    (ripple ("a", "filter P (xs @ ys) = filter P xs @ filter P ys"); NONE)
    handle DB_Embed.embed_pretty_exp e => SOME e;

PolyML.exception_trace (fn () =>   
ripple ("a", "filter P (xs @ ys) = filter P xs @ filter P ys")
 );

PolyML.exception_trace (fn () =>   
(mk_prettyterm e));


*)

val t1 = ((((Const("HOL.If", Type("fun", [Type("HOL.bool", []), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])])]))) $
 ((Free("Pa", Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Free("a", TFree("'a", ["HOL.type"]))))) $
 (((Const("List.list.Cons", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Free("a", TFree("'a", ["HOL.type"])))) $
 (((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Free("Pa", Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0))))) $
 (((Const("List.append", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Free("xt", Type("List.list", [TFree("'a", ["HOL.type"])])))) $
 (Free("yt", Type("List.list", [TFree("'a", ["HOL.type"])]))))))) $
 (((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Free("Pa", Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0))))) $
 (((Const("List.append", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Free("xt", Type("List.list", [TFree("'a", ["HOL.type"])])))) $
 (Free("yt", Type("List.list", [TFree("'a", ["HOL.type"])]))))));

val t2 = (((Const("List.append", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (
((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Free("Pa", Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0)))))
 $
 (((Const("List.list.Cons", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Free("a", TFree("'a", ["HOL.type"])))) $
 (Free("xt", Type("List.list", [TFree("'a", ["HOL.type"])])))))) $
 (((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Free("Pa", Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0))))) $
 (Free("yt", Type("List.list", [TFree("'a", ["HOL.type"])])))));



val t = ((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Free("Pa", Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0)))));




val s2 = ((Const("List.append", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Var( ("Pb",0), Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0))))) $
 (Free("xt", Type("List.list", [TFree("'a", ["HOL.type"])]))))) $
 (((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Var( ("Pb",0), Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0))))) $
 (Var( ("yu",0), Type("List.list", [TFree("'a", ["HOL.type"])]))));

val s1 = (((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Var( ("Pb",0), Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0))))) $
 (((Const("List.append", Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Free("xt", Type("List.list", [TFree("'a", ["HOL.type"])])))) $
 (Var( ("yu",0), Type("List.list", [TFree("'a", ["HOL.type"])])))));


val s = ((Const("List.filter", Type("fun", [Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]), Type("fun", [Type("List.list", [TFree("'a", ["HOL.type"])]), Type("List.list", [TFree("'a", ["HOL.type"])])])]))) $
 (Abs("x",TFree("'a", ["HOL.type"]), 
  (Var( ("Pb",0), Type("fun", [TFree("'a", ["HOL.type"]), Type("HOL.bool", [])]))) $
 (Bound(0)))));


val ctxt = ProofContext.init thy;
val ectxt = Ectxt.init (InstEnv.init thy) ParamRGraph.empty;


PolyML.exception_trace (fn () =>  
map DB_Embed.mk_prettyterm (Seq.list_of (DB_Embed.embed ectxt s t))
);

val (e::_) = Seq.list_of (DB_Embed.embed ectxt s t);
DB_Embed.print e;
val et = DB_Embed.get_eterm e;
