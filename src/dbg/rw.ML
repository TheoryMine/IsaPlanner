(* digging: 
rst
pplan
RippleWRulesDB
RippleWRulesDB.searchf_of
RuleNet.trm_unifier
InstEnv.unify
*)

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

val dtacs = RippleCInfo.lookup_arules_goal rst "c";
map DTac.print dtacs;

(* 
val rsts2 = Seq.list_of (RTechnEnv.apply_dtac_to (List.nth (dtacs, 0)) "c" rst);
map PPInterface.print_rst rsts2;

val rsts2 = Seq.list_of (RTechnEnv.apply_dtac_to (List.nth (dtacs, 1)) "c" rst);
map PPInterface.print_rst rsts2; 
*)

val gthm = (snd (RstPP.goal_thm_winst rst "c"));

val vtab = (RstPP.vtab_of_pplan rst);
val ctxt = (RstPP.get_ctxt rst);
val db = RippleThyInfo.wrules_of_pctxt ctxt;
val (wrlseq,rlseq) = (RippleWRulesDB.lookup_concl db vtab gthm);

val wrls = Seq.list_of wrlseq;
val rls = Seq.list_of rlseq;

val (wrdthm,wrth,(prematch,(inst1,inst2))) = (List.nth (wrls, 1));

InstEnv.print thry inst1;
InstEnv.print thry inst2;
val gth = gthm;

val z =  gth
                 |> Thm.prop_of
                 |> Zipper.mktop (* now above: ==> $ prem $ concl *)
                 |> Zipper.move_down_left (* now above: ==> $ prem *)
                 |> Zipper.move_down_right; (* now above: Trueprop $ p *) 

val searchf = RippleWRulesDB.searchf_of db;
val rulenet = RippleWRulesDB.get_eqrulenet db;

val m = List.nth (Seq.list_of (searchf thry vtab z rulenet), 1);
val rep_m = RippleWRulesDB.WREvalNet.rep_of_match m;
val (p,t) = #from rep_m;

Trm.print_vtab vtab;

(* from RuleNet.trm_unifier *)
           val rule_vtab = RippleWRulesDB.RuleData.vars_of (#data rep_m);
Trm.print_vtab rule_vtab;
            val (renaming, pat2) =  
                TrmRename.rename_trm 
                  TrmRename.ignore_none
                  (Trm.rename_vtab rule_vtab (TrmRename.init vtab))
                  p;
            val rn_instenv = InstEnv.of_renaming renaming;
            val vars2 = Trm.vars_of_renamings renaming;
Trm.print_vtab vars2;
val unifseq = InstEnv.unify thry (vtab, vars2) Trm.empty_flexes [("c",(p,t))];
val [(newvars,(allvars,((ruleinsts, goalinsts),instflexes)))] = Seq.list_of unifseq;

InstEnv.print thry ruleinsts;
InstEnv.print thry goalinsts;

raise ERROR "DONE!";


val rsts2 = Seq.list_of (RTechnEnv.apply_dtac_to (List.nth (dtacs, 0)) "c" rst);
map PPInterface.print_rst rsts2;

val rsts2 = Seq.list_of (RTechnEnv.apply_dtac_to (List.nth (dtacs, 0)) "c" rst);
map PPInterface.print_rst rsts2;



val goal = "c";
val ppl = RState.get_pplan rst;
val skels = PPlan.get_asmtrms ppl goal;
val rsts2 = (RippleCInfo.start_rst skels) rst;
val s = snd (hd skels);
val t = RstPP.goal_concl rst "c";

