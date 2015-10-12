use "ROOT.ML";
use_thy "examples/N";
(* val myrst = PPInterface.ipp rippling ("g", "a + b = b + (a::N)"); *)

val thry = (theory "N");
ML_Context.set_context (SOME (Context.Theory thry));
val p = Prf.init thry;
val t = Prf.read_top_term p "Trueprop (a + b = b + (a::N))";
val (g,p) = p |> Prf.conj_top_term "g" t;

val rippling = RippleRTechn.induct_ripple_conj;

val rst = 
    (PPInterface.prep_rst rippling ("g", "a + b = b + (a::N)")) 
      |> RState.search (MSearch.depthfs ())
      |> Seq.hd;

Conjdb_CtxtInfo.print_rst rst;

raise ERROR "done!";
val rst = PPInterface.ipp rippling ("g", "a + b = b + (a::N)");
val gname = "r_e";
val (appinfo, (ptab2,t)) = Seq.hd (ConjRTechn.conj_from_gname rst gname);
val (prfs,status) = Conjdb_CtxtInfo.lookup_rst rst t;
val (n,(th,_)) = hd prfs; 
val dthm = (LemmaConjLib.mk_dthm (RstPP.get_theory rst) appinfo (n,th));

val ppl = RState.get_pplan rst;
val gname = "r_e";
val [(appinfo,(ptab,t))] = Seq.list_of (ConjRTechn.conj_from_gname rst gname);

         val ptab = Cx.get_fixed_trm_ps (RstPP.get_cx rst gname);
        val sgterm = RstPP.goal_concl rst gname;
        val thy = RstPP.get_theory rst;

open LemmaConjLib;

    val thry = Prf.get_theory ppl;
    val ienv = Prf.get_ienv ppl;
    val flexes = Prf.get_flexes ppl;

val t = MinimalRenameLib.rename_term sgterm;
val (d,lt2) = try_mk_eq_conj thry ienv flexes t;
(* in try_mk_eq_conj *)
Data.dest_eq_term t



val p = Prf.get_aprf ffp;


APrf.mk_thm p gname;

val ppl = RState.get_pplan rst;
val thry = Prf.get_theory ppl;
val p = Prf.get_aprf ppl;
val gname = "r_r";

open DB_APrf;

val (r as ((gname,nd),rncx as (rcxn,rcx))) = (get_result p gname);
val Meth(MClosed(MKindPrf (mname,subprf),subgoals),_) = nd_get_meth nd;



(* enter: mk_result_thm *);

val super_cx = (snd (get_top_ncx p));
val (r as ((gname,nd),rncx as (rcxn,rcx))) = (get_result p gname);

val Meth(MClosed(MKindPrf (mname,subprf),subgoals),_) = nd_get_meth nd;
val p = subprf;
val Meth(MClosed(MKindRes gname2,subgoals),_) = nd_get_meth nd;
val gname = gname2;
val Meth(MClosed(MKindThm th,subgoals),_) = nd_get_meth nd;



val rst = PPInterface.ipp rippling ("g", "a + b = b + (a::N)");


val SOME (gname,ffp) = (PPInterface.ipp rippling ("g", "a + b = b + (a::N)"); NONE) 
    handle Prf.mk_thm_exp x => SOME x;

val p = (Prf.get_aprf ffp);

open DB_APrf;

Seq.hd (mk_thm p gname);

val Meth(MClosed(MKindPrf (mname,subprf),subgoals),_) = nd_get_meth nd;
val p = subprf;
val Meth(MClosed(MKindRes gname2,subgoals),_) = nd_get_meth nd;
val gname = gname2;
val Meth(MClosed(MKindThm th,subgoals),_) = nd_get_meth nd;



raise ERROR "done!";

PolyML.exception_trace (fn () => PPInterface.ipp rippling ("g", "a + b = b + (a::N)"));


Trm.drop_var_args_flag := false;
ML_Context.set_context (SOME (Context.Theory (theory "Main")));
val thry = (theory "Main");
val p = Prf.init (the_context());
val t = 
    Prf.read_top_term 
      p "(!! z. g z = f z) ==> (EX x. f x) ==> (ALL y. f y)==> (EX y. g y)";
val (g,p) = p |> Prf.conj_top_term "g" t;

val [(gs,p)] = 
  Seq.list_of (Prf.apply_erule_thm (thm "exE") "i" "g" p);

