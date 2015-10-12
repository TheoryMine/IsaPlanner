use "ROOT.ML";

fun print_full rst = Prf.print_full (PPlan.get_prf (RState.get_pplan rst));

set quick_and_dirty;
use_thy "examples/N";

val thry = (the_context());

(* induction *)
val rst = PPInterface.init_rst (the_context()) "(a + ?b) + c = a + ((?b ::N) + c)";
val rsts = Seq.list_of (InductRTechn.just_induction rst);
val rst = hd rsts;
PPInterface.print_rst rst;
print_full rst;


PPInterface.ipp RippleRTechn.induct_and_ripple "(a + ?b) + c = a + ((?b ::N) + c)";

val goal = "c";
val ppl = RState.get_pplan rst;
val skels = PPlan.get_asmtrms ppl goal;
val rsts2 = (RippleCInfo.start_rst skels) rst;
val s = snd (hd skels);
val t = RstPP.goal_concl rst "c";

RippleSkel.init {skelterm=s, skelname="d", target=t};


val [e] = Seq.list_of (EmbeddingLib.embed s t);
val eterm = EmbeddingLib.eterm_of_embedding e;
RippleSkel.RippleMeasure.of_eterm eterm;

RippleATerms.u_aterms_of_eterm eterm;
RippleATerms.r_aterms_of_eterm eterm;
RippleATerms.cu_aterms_of_eterm eterm;
RippleATerms.cr_aterms_of_eterm eterm;



val g = "d";
val ffp = PPlan.get_prf (RState.get_pplan rst);
Prf.get_local_asm_thm ffp "d";
val (vtab, t) = Prf.get_local_asm_trm ffp "d";
Thm.cterm_of thry t;


(* simp base case trm *)
val rsts = Seq.list_of (RTechnEnv.apply_to_goals 
                       ["b"] RippleRTechn.simplify_basecase rst);
val rst = hd rsts;
PPInterface.print_rst rst;
print_full rst;

val rsts = Seq.list_of (RippleRTechn.startr rst);

val goal = "d";
            val ppl = RState.get_pplan rst;
            val skels = (*Skels is a lsit of (gname,term) pairs *)
                          map (fn (g,_) => 
                                  (g, Thm.concl_of (PPlan.get_local_asm_thm ppl g)))
                          (PPlan.get_asms ppl goal);
Seq.list_of ((RippleCInfo.start_rst skels) rst);

val g = "d";
val ffp = PPlan.get_prf (RState.get_pplan rst);
Prf.get_local_result_thm ffp "d";

(get_alled_goal_thm ffp g);

open Prf;


PPlan.has_asm (RState.get_pplan rst) "h";
PPlan.has_asm (RState.get_pplan rst) "i";


val rst2 = hd (Seq.list_of( RState.unfold rst));
print_full rst2;

val rst3 = hd (Seq.list_of( RState.unfold rst2));
val rst4 = hd (Seq.list_of( RState.unfold rst3));
print_full rst4;
val rst5 = hd (Seq.list_of( RState.unfold rst4));
print_full rst5;
val rst6 = hd (Seq.list_of( RState.unfold rst5));


val dtacs = RippleCInfo.lookup_arules_goal rst4 "i";
val [rst5] = Seq.list_of (RTechnEnv.apply_dtac_to (hd dtacs) "i" rst4);



(* entering RippleCInfo.update ... *)
 val old_skels = RippleCInfo_dsum.all_skels_of_goal rst4 "i";
val rst = rst5;
(RState.get_goalnames rst);
val goal = "k";
val (newgoalthm, newgoalterm, vtab, ctxt) = 
    (snd (RstPP.goal_thm_winst rst goal),
     (RstPP.goal_concl rst goal),
     (RstPP.vtab_of_pplan rst),
     (RstPP.get_ctxt rst));

raise ERROR "done!";
structure RippleSkel = RippleSkel_dsum;
structure RippleCInfo = RippleCInfo_dsum;

(* something inside RippleCInfo.update *)
val newskels = 
(Library.map_filter 
                             (* filter: keep only mes decreasing skels *)
                             (fn s => case RippleSkel.mk_next newgoalterm s
                                       of [] => NONE
                                        | (l as _::_ ) => 
                                          SOME (map (fn e =>
                                          (RippleSkel.named_skel_term_of e,
                                           SOME e)) l))
                             (map (the o snd) old_skels));


print_full rst5;
val [rst5] = Seq.list_of (RTechnEnv.apply_dtac_to (hd (tl dtacs)) "i" rst4);
print_full rst5;

Seq.list_of (RTechnEnv.apply_dtacs_to dtacs "i" rst4);


print_full rst4;
PolyML.exception_trace (fn () =>hd (Seq.list_of( RState.unfold rst4)) ); 
print_full it;


RstPP.goal_thm_winst rst4 "i";
val prf = PPlan.get_prf (RState.get_pplan rst4);
Prf.print_full prf;
Seq.list_of (Prf.apply_dtac_to_fixedthm (hd dtacs) "i" prf);

val (vs, th) = Prf.get_fixed_goal_thm_winst prf "i";
val vtab = Trm.vtab_of (Thm.prop_of th);


val wruledb = RippleThyInfo.wrules_of_theory thry;
val wrules_out = Seq.list_of (RippleWRulesDB.eqrule_concl_lookup wruledb vtab th);
val (dthm, rule, (m as (prematch, (ruleinst, goalinst)))) = hd wrules_out;
val thms = Seq.list_of (IsaDTac.Subst.direct_rw_tac m rule th);
val stuff = (DTac.strip_insts InstEnv.empty vs) (hd thms);



val tvar_insts = InstEnv.tvar_insts tvars;
val var_insts = InstEnv.var_insts vars;
val (nm, nm',t) = RippleWRulesDB.WREvalNet.rw_matchinfo_of prematch;
val t2 = InstEnv.inst_trm ruleinst t;


InstEnv.print thry rienv;
InstEnv.print thry gienv;



fun term_of_str s =
   let  in
     (Sign.read_term thry s) end;

val t = term_of_str "a+?b=?b+(a::nat)";

val vtab = Trm.vtab_of t;
val (rntab, t2) =
    TrmRename.rename_trm
      TrmRename.ignore_none
      (TrmRename.init vtab) t;

TrmRename.renamings_of rntab; 


val rst = PPInterface.init_rst (the_context()) "a + b = b + (a :: nat)";
PPInterface.print_rst rst;

val rsts = Seq.list_of (InductRTechn.just_induction rst);
val rst = hd rsts;
PPInterface.print_rst rst;
val prf = PPlan.get_prf (RState.get_pplan rst);
Prf.print_full prf;

(* Issue: Induction tactic now works on params, so we need to change
the induction techinque to include searching over meta-level params *)


val prf = PPlan.get_prf (RState.get_pplan rst);
val th = Prf.get_goal_thm prf "g";
val goalthm = th;

open InductDTac;
val vars = ["a"];
val thry = PPlan.get_theory (RState.get_pplan rst);
      val ctxt = ProofContext.init thry;
      val ithings = inductable_things_in_sg 1 goalthm;
      val (otherfrees, inductfrees) = mk_induct_insts ithings vars;
      val insts = [map (fn NONE => NONE | SOME v => SOME (NONE : string option ,Free v)) 
                         inductfrees];

InductMethod.induct_tac ctxt false insts [] [] NONE [] 1 goalthm;
InductMethod.induct_tac ctxt false insts [otherfrees] [] NONE [] 1 (topthm());

RState.get_goalnames rst;
val rst = rst |> RState.set_rtechn (SOME InductRTechn.just_induction);


InductRTechn.inductable_things_of "g" rst;



InductDTac.inductable_things_in_term


val inductables = InductRTechn.inductable_things_of "g" rst;



InductDTac.inductable_things_in_sg 1 goalthm;
      val ithings = inductable_things_in_sg 1 goalthm;
      val (otherfrees, inductfrees) = mk_induct_insts ithings vars;

      val insts = [map (fn NONE => NONE | SOME v => SOME (Free v)) 
                         inductfrees];

RTechnEnv.apply_dtacs_to [InductDTac.induct thry ["a"]] "g" rst;
