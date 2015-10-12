context (theory "Main");
val thry = the_context();

(* use "testing/mydtacs.ML"; *)
use "gproof/testing/mydtacs.ML";
fun term_of_str s = 
    let val thry = (the_context()) in
      (Sign.read_term thry s) end;

(* set the theory to work in *)
(* set an initial goal *)
val p = (Prf.init thry);
val (g0, p) = p |> Prf.add_topgoal_trm (term_of_str "Trueprop (a + b = ?n + (a :: nat))");


val p = (Prf.init thry);
val (g0, p) = p |> Prf.add_topgoal_trm (term_of_str "Trueprop (a + b = a + (b :: nat))");


Prf.print_full p;
Prf.print p;

val plist = p |> Prf.apply_dtac (induct_dtac "a") "g" |> Seq.list_of;
raise ERROR_MESSAGE "ok so far!";

(* apply_dtac *)
val dtac = induct_dtac "a";
val gname = "g";
val ffp = p;

open Prf;

        val nd = get_nd ffp gname;
        val cx = get_nd_cx ffp nd;

val ths = Seq.list_of 
            (DTac.apply_winst 
               dtac 
               (get_theory ffp, Prf.get_vars ffp, (snd (Cx.get_fixes cx)))
               (get_nd_goal_thm ffp nd));

(* DTac.apply_winst *) 
open DB_DTac;
val th = (get_nd_goal_thm ffp nd);
val (thy,vars,params) = (get_theory ffp, Prf.get_vars ffp, (snd (Cx.get_fixes cx)));

val ths = Seq.list_of (apply dtac (thy,vars,params) prep_th);
val th = hd ths;
val ienv = InstEnv.empty;
val vs = vs;

PolyML.exception_trace (fn () => 
Seq.list_of 
            (DTac.apply_winst 
               dtac 
               (get_theory ffp, Prf.get_vars ffp, (snd (Cx.get_fixes cx)))
               (get_nd_goal_thm ffp nd)));

(* dtac_inc  *)
val [x1,x2,x3,x4] = ths;
val goalconcl = Nd.get_goal_concl nd;

(* Prf.subgoals_of_instth *)
val (inst,th) = x1;

        val thry = Thm.theory_of_thm th;
        val rename_env = 
            InstEnv.mk_invert_var_renamings inst;
        val th2 = InstEnv.inst_thm rename_env thry th;
        val prf_env = InstEnv.correct_var_renamings rename_env inst;

        val ptab = Cx.get_fixes cx
        val goalconcl = Nd.get_goal_concl nd
        val cxname = Nd.get_cx_name nd;
        val usedby = Nd.get_usedby nd;

val ts = (Thm.prems_of th2);
val t = 

val (t,(ns,(FFPrf (ffs,p1)))) = 


raise ERROR_MESSAGE "ok so far!";

(* 

(* APrf.add_goalnode *)
val (cx_name, usedby) = (Nd.get_cx_name nd, GNTab.addnew gname (Nd.get_usedby nd));
val (ns,(FFPrf (ffs,p1))) = ([],ffp);
val [t_b,t_sc] = (Thm.prems_of th2);
val alledt = t_sc;
open APrf;
val (Proof rep) = p1;




val oldctxt = Goal.NTab.get (#ctxts rep) cx_name;
val (oldftvs, oldfvs) = Cx.get_fixes oldctxt;
D.Trm.plist_of_ptab oldfvs;

(* Trm.refix_params *)
open Trm;
val (tab as (i,L,_)) = oldfvs;





val plist = p |> Prf.apply_dtac (induct_dtac "a") "g" |> Seq.list_of;

raise ERROR;

PolyML.exception_trace (fn () => 
p |> Prf.apply_dtac (induct_dtac "a") "g" |> Seq.list_of );



(* PStep.bck_res_thm (thm "add_Suc") "g" p; *)

(* P.print_gs p; *)


(* applying a dtac *)
raise ERROR; 

val r1_dtac = DTac.mk (Pretty.str "res", rtac (thm "add_commute") 1);
val r2_dtac = 
    DTac.mk (Pretty.str "res", 
             rtac ((thm "add_commute") RS (thm "subst")) 1);

val plist = p |> Prf.apply_dtac (induct_dtac "a") "g" |> Seq.list_of;

raise ERROR; 

val plist = p |> Prf.apply_dtac r1_dtac "g" |> Seq.list_of;

PolyML.exception_trace (fn () => 
p |> Prf.apply_dtac r2_dtac "g" |> Seq.list_of);

