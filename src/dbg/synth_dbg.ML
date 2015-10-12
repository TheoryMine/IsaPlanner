structure Synthesis = ConstrSynthesis;


val SOME (const, trm, thm) = 
    ((Constraints.mk_const_infos2 thy); NONE) 
    handle Constraints.my_exp2 x => SOME x;

val SOME (ts, ienv) = 
    ((Synthesis.synthesise_eq_terms 5 thy); NONE)
    handle TypUnify.unify_typsof_terms_exp x => SOME x;

(* 
use_thy "Synthesis";
val thy = theory "Synthesis";
*)

use_thy "benchmarks/synth_theories/N_plus_mult";
val thy = theory "N_plus_mult";
val (cs, thy) = Constraints.mk_const_infos_ac thy; 


val (cs, cty) = Constraints.mk_const_infos thy;
val t1 = Sign.read_term thy "height(mirror t) = height t";
val t2 = Sign.read_term thy "max a b = max b a";
val t3 = Sign.read_term thy "max (nodes a) (height a) = nodes a";
val t4 = Sign.read_term thy "max (height a) (nodes a) = nodes a";

val ci2 = foldl (fn (t,ci) => Constraints.update_constraints_term t ci) constinfos [t1,t2,t3,t4];
Synthesis.synth_w_stats (3, 6) 2 thy ci2;
val SOME (ifthen_nm, sub_constr,  
          (hc_tab, c_tab, cd_tab)) =
    (Synthesis.synth_w_stats (10, 10) 3 thy ci; NONE) 
    handle Synthesis.IfThen_exp x => SOME x;

val max_i = the (Constraints.lookup_const ci (Constraints.Constant.mk "Tree_size_height.max"));
val cstr =  Constraints.Constraint.NTab.list_of (Constraints.get_constrTab max_i); 

val (constinfos, ctylist) = Constraints.mk_const_infos thy;
val s0 = Synthesis.init_sterm thy constinfos 3 2 HOLogic.boolT;
Synthesis.print_sterm s0;


use_thy "benchmarks/synth_theories/List_fold";
val thy0 = theory "List_fold"; 
val (cs, thy) = Constraints.mk_const_infos_ac thy0; 

val rst0 = RstPP.init thy;
val t = "foldl f (foldl f a l) l2 = foldl f a (l @ l2)"
          |> RstPP.read_top_term rst0
          |> Trm.change_frees_to_fresh_vars;
          
(* t to make synth term to match *)
(* val t = Trm.change_frees_to_fresh_vars
          (RstPP.read_top_term rst0 ("x = y")); *)
val tpset = Trm.TypParams.get_pnames (Trm.tparams_of t)
val pset = Trm.TrmParams.get_pnames (Trm.params_of t)
val tvtab = TVar.NTab.empty;
val vtab = Var.NTab.empty;
val (_,t') = Trm.change_vars_to_fresh_frees' ((tpset,tvtab),(pset,vtab)) t;
Term.size_of_term t';

(* init sterm *)
val s0 = Synthesis.init_any_sterm thy cs 14 4;
val SOME s1 = Synthesis.is_instance_of_term thy (t',pset) s0;
Synthesis.print_sterm s1;


val SOME (x,xs) = Seq.pull (Synthesis.synthesise_upto_given_term 
            thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0);

Synthesis.print_sterm x;


(* in Synthesis.synthesise_1step *)
val (var_allowed_fn, cinfoTab, sterm) = 
    (Synthesis.VarAllowed.is_hole_in_lhs, cs, s1);

val (Synthesis.ProgressSynth sterms) = 
    Synthesis.synthesise_1step thy var_allowed_fn cinfoTab sterm;

val sterms2 = map_filter 
                 (Synthesis.is_instance_of_term thy (t',pset))
                 (Seq.list_of sterms);

val (sterm :: sterms) = sterms2;

Synthesis.synthesise_1step thy var_allowed_fn cinfoTab sterm;
Synthesis.is_instance_of_term thy (t',pset) sterm;


open Synthesis;


val (Synthesis.ProgressSynth sterms) = 
    Synthesis.synthesise_1step thy var_allowed_fn cinfoTab sterm;
 

length sterms2;
val sterm2 = hd sterms2;
 Synthesis.synthesise_1step thy var_allowed_fn cinfoTab sterm2;




val (hole::hs) = (get_holes_agenda sterm);

(* in Synthesis.inst_hole_with_const *)
val strm1 = sterm; 
val (const_info::_) = const_infos;




val SOME (sterm,sterms) = (Seq.pull sterms);
Synthesis.print_sterm sterm;

val x = Seq.pull (Synthesis.synthesise_upto_given_term 
            thy Synthesis.VarAllowed.is_hole_in_lhs cs t s0);


print_depth 30;
use "synthesis/synth_prf_tools.ML";
use "synthesis/constInfo.ML";
use "synthesis/synthesise.ML";

use "synthesis/naive_synth.ML";
use_thy "benchmarks/synth_theories/List_rev_app";
val thy = theory "List_rev_app";
NaiveSynth.synthesise_eq_terms 11 thy;

(* Try to check *)
use_thy "benchmarks/synth_theories/List_fold";
val thy0 = theory "List_fold";
val (cs, thy) = Constraints.mk_const_infos_ac thy0;

val thrm_strs = [
"rev (a @ [[], []]) = [] # [] # rev a",
"rev (a @ [[], b]) = b # [] # rev a",
"rev (a @ [b, []]) = [] # b # rev a",
"rev (a @ [b, b]) = b # b # rev a",
"rev (a @ (b @ [[]])) = [] # rev (a @ b)",
"rev a @ ([] # rev b) = rev (b @ ([] # a))",
"rev (a @ ([] # rev b)) = b @ ([] # rev a)",
"rev (rev a @ [b]) = b # a",
"rev (a @ [[]]) = [] # rev a",
"rev (a @ [b]) = b # rev a",
"rev (rev a @ rev b) = b @ a",
"rev a @ rev b = rev (b @ a)",
"rev (a @ rev b) = b @ rev a",
"len (a @ b) = len (b @ a)",
"len (rev a) = len a",
"a @ [] = a",
"rev rev a = a"
];
val thms = map (fn thm_str => 
                   Thm.trivial 
                     (Thm.cterm_of thy 
                                   (Sign.read_term thy 
                                                   ("Trueprop("^thm_str^")"))))
               (rev thrm_strs);
val cs2 = foldl Constraints.update_constraints cs thms;

val ((cs,thy), _) = 
    PolyML.exception_trace (fn () => 
                               Synthesis.synth_w_stats (16,16) 2 thy cs2);

val SOME ((hole, init_cnm, (init_ctab, init_cdtab)), (bad_cnm, (bad_ctab, bad_cdtab))) =
      (Synthesis.synth_w_stats (14,14) 3 thy cs; NONE) 
    handle Synthesis.prop_var_exp x => SOME x;
val SOME  ((hole, (var,ty)), 
           (hc_tab, c_tab, a_tab, cd_tab)) =
      (Synthesis.synth_w_stats (14,14) 3 thy cs; NONE) 
    handle Synthesis.update_constr_exp3 x => SOME x;

val SOME ((arg, nw_nm), old_cnm, c_tab, cd_tab) =
      (Synthesis.synth_w_stats (14,14) 3 thy cs; NONE) 
    handle Synthesis.rnm_in_parents_exp x => SOME x;

val SOME (constr, (hc_tab, c_tab, a_tab, cd_tab)) = 
    (Synthesis.synth_w_stats (11,11) 2 thy cs; NONE) 
    handle Synthesis.not_allowed_exp x => SOME x;

val SOME  ((hole, const_nm), new_hole_nms, (bad_arg, bad_constr), 
           (hc_tab, c_tab, a_tab, cd_tab)) =
      (Synthesis.synth_w_stats (10,10) 3 thy ci; NONE) 
    handle Synthesis.update_constr_exp4 x => SOME x;

Constraints.Constraint.NTab.list_of c_tab;
Constraints.Constraint.NTab.list_of cd_tab;                
Synthesis.Hole.NTab.dest hc_tab;

val constr = Synthesis.Constraint.mk ("C", 19);
val (hctab2, ctab2, atab2, cdtab2) = Synthesis.update_constr_of_hole (hole, const_nm) new_hole_nms (hc_tab, c_tab, a_tab, cd_tab) constr;
Constraints.Constraint.NTab.dest ctab2;
Constraints.Constraint.NTab.dest cdtab2;
(* ---------------------------------------------------------------*)
use "synthesis/naive_synth.ML";
use_thy "dbg/SynthN";
val thy = theory "SynthN";
NaiveSynth.synthesise_eq_terms 4 thy;

val (cs, thy) = Constraints.mk_const_infos_ac thy0;
val cs = Constraints.mk_const_infos_no_ac thy;
val ctxt = ProofContext.init thy2
val ((cs,thy), _) = Synthesis.synth_w_stats (3,3) 3 thy cs;

val (cinfo,thrms) =   PolyML.exception_trace (fn () => 
                                         Synthesis.synthesise_eq_terms 5 thy cs);
val (conjectures, theorems) = (List.partition (fn (t, prfs) => null prfs) thrms)

(* --- *)
(* List test *)
print_depth 30;
use "synthesis/synth_prf_tools.ML";
use "synthesis/constInfo.ML";
use "synthesis/synthesise.ML";
use "synthesis/synthesise2.ML";
use_thy "dbg/SynthL";
val thy = theory "SynthL";
use_thy "dbg/SynthTree";
val thy = theory "SynthTree";
val rippling = RippleLemCalc.induct_ripple_lemcalc;
val myrst = PPInterface.ipp thy (rippling "g") ("g","mirror(mirror t) = t");

val ctxt = ProofContext.init thy
val (cs,thy') = Constraints.mk_const_infos_ac thy;
val ((cs2,thy2),(conjs,thrms)) = Synthesis.synth_w_stats (3,8) 2 thy' cs;

val (cinfo,thrms) =   PolyML.exception_trace (fn () => 
                      Synthesis.synthesise_eq_terms 8 2 thy' cs);

val cs = PolyML.exception_trace (fn () => Constraints.mk_const_infos_no_ac thy);
val _ = Synthesis2.synth_w_stats 10 3 thy [] cs;
val _ = Synthesis2.synth_w_stats 10 3 thy [Constraints.Constant.mk "SynthL.rev", Constraints.Constant.mk "SynthL.append"] cs;
val ((cinfo, thy2), (conjs, thrms)) = 
          Synthesis2.synth_single_consts 10 3 thy cs;

val simpset = Simplifier.simpset_of thy'
val app_assoc = StrNameTab.get (!SynthPrfTools.thm_nm_tab) "synth_thm_a";
val app_nil2 = StrNameTab.get (!SynthPrfTools.thm_nm_tab) "synth_thm_c";
val simpset2 = Simplifier.addsimps simpset [app_assoc];
val thy2 = Simplifier.map_simpset (fn sset => 
                                       Simplifier.addsimps (sset, [app_assoc])) thy';
val thy2' = Simplifier.map_simpset (fn sset => 
                             Simplifier.addsimps (sset, [app_nil2])) thy2;
(* --- *)
use_thy "dbg/SynthL2";
val thy = theory "SynthL2";
val (cs, thy2) = Constraints.mk_const_infos_ac thy;
val ((cs2,thy3),(conjs,thrms)) = Synthesis.synth_w_stats 10 2 thy2 cs;
val wruledb = RippleThyInfo.wrule_of_theory thy2;
WRules.print wruledb;
val qrev_gen_thm = StrNameTab.get (!SynthPrfTools.thm_nm_tab) "synth_thm_e"

val (cinfo,thrms) = PolyML.exception_trace (fn () => 
                                         Synthesis.synthesise_eq_terms 5 thy cs);
val SOME trm = (Synthesis.synthesise_eq_terms 10 thy cs; NONE)
    handle Synthesis.synth_error x => SOME x;

(* Path bug *)
val ((cs,thy), _) = Synthesis.synth_w_stats (3,10) 3 thry cs;
val SOME (rename_map, const_constr_tab, constr_tab, old_constr_nm) =
    (Synthesis.synth_w_stats (12,12) 12 thy cs; NONE)
    handle Synthesis.rename_exp x => SOME x;
val assoc1 = Thm.trivial (Thm.cterm_of thy 
              (Sign.read_term thy "Trueprop(a+b+c = b+c+a)"));
val assoc2 = Thm.trivial (Thm.cterm_of thy 
              (Sign.read_term thy "Trueprop(a+b+c = b+a+c)"));
val assoc3 = Thm.trivial (Thm.cterm_of thy 
              (Sign.read_term thy "Trueprop(a + b + b = b + a + b)"));
val cs2 = Constraints.update_constraints (assoc3, cs);

(* --- *)
val add_i = the ( Constraints.lookup_const cinfo (Constraints.Constant.mk "SynthN.add"));
val allow =  Constraints.ArgPos.NTab.dest(Constraints.get_allowedTab add_i);
val suc_i = the ( Constraints.lookup_const cinfo (Constraints.Constant.mk "SynthN.N.suc"));
val allow =  Constraints.ArgPos.NTab.dest(Constraints.get_allowedTab suc_i);
val cstr =  Constraints.Constraint.NTab.list_of(Constraints.get_constrTab add_i);;
val argcstr =  StrIntNameTab.dest(Constraints.get_argConstrs add_i);;


val suc_inj = Thm.trivial (Thm.cterm_of thy 
              (Sign.read_term thy "Trueprop( (suc ?n = suc ?m) = (?n =?m) )"));

val reflex = Thm.trivial (Thm.cterm_of thy 
              (Sign.read_term thy "Trueprop( (?x=?x) =True)"));
val my_test = Thm.trivial (Thm.cterm_of thy
                           (Sign.read_term thy "Trueprop( (?a + ?b) * (?b + (?c + ?b)) = (?a + ?b) * ((?b + ?c) + ?b))"));
val add_commute = Thm.trivial (Thm.cterm_of thy 
                               (Sign.read_term thy "Trueprop(?a+?b = ?b+?a)"));
val cs2 = Constraints.update_constraints (add_commute, cs);
val add_i = the (Constraints.lookup_const cs2 (Constraints.Constant.mk "SynthN.add"));
val allow =  Constraints.ArgPos.NTab.dest(Constraints.get_allowedTab add_i);
val cstr =  Constraints.Constraint.NTab.dest(Constraints.get_constrTab add_i);;


val cs2 = Constraints.update_constraints (suc_inj, cs);
val cs3 = Constraints.update_constraints (reflex, cs2);

val cs4 = Constraints.update_constraints (my_test, cs);

val eq_i = the (Constraints.lookup_const cs (Constraints.Constant.mk "HOL.eq"));
val allow =  Constraints.ArgPos.NTab.dest(Constraints.get_allowedTab eq_i);
val cstr =  Constraints.Constraint.NTab.dest(Constraints.get_constrTab eq_i);;
val argcstr =  StrIntNameTab.dest(Constraints.get_argConstrs eq_i);;

val cs = Constraints.mk_const_infos thy;
val my_test = Thm.trivial (Thm.cterm_of thy
                           (Sign.read_term thy "Trueprop( (?a + ?b) * (?b + (?c + ?b)) = (?a + ?b) * ((?b + ?c) + ?b))"));val cs4 = Constraints.update_constraints (my_test, cs);



val mult_i = the (Constraints.lookup_const cs4 (Constraints.Constant.mk "BestF_L.mult"));
val cstr =  Constraints.Constraint.NTab.dest(Constraints.get_constrTab mult_i);
val top_cstr = Constraints.get_start_constrs mult_i;
val mult_cstrs = (Constraints.get_constrTab mult_i);

 val (init_trm, init_holes, ienv, allowed_tab) =     
          Synthesis.mk_new_term_bit mult_i (Synthesis.Hole.NTab.empty) (InstEnv.init thy);
val hole_nms = map (Constraints.Hole.mk o fst) init_holes;

val mult_nms = Constraints.Constraint.NTab.get_names (Constraints.get_constrTab mult_i);
val init_constr_tab = Constraints.Constraint.NTab.useup_names mult_nms 
                    (Constraints.Constraint.NTab.empty : Constraints.Constr Constraints.Constraint.NTab.T);
val constr_renamings = (Synthesis.rename_constraints mult_cstrs init_constr_tab)
                         |> Constraints.Constraint.nmap_of_renaming;

val (hole_constr_tab2, constr_tab2, allowed_tab2) = foldl (Synthesis.attach_constr mult_cstrs constr_renamings hole_nms)
                                                (Synthesis.Hole.NTab.empty, init_constr_tab, allowed_tab) 
                                                (map snd (Constraints.get_start_constrs mult_i));

val constr_dep_tab = Synthesis.update_constr_dep_tab (Constraints.Constraint.NTab.keys constr_tab2) 
                                                 constr_tab2 (Constraints.Constraint.NTab.empty : 
                                                              Constraints.Constraint.NSet.T Constraints.Constraint.NTab.T );
Constraints.Constraint.NTab.dest constr_tab2;
Synthesis.Hole.NTab.dest hole_constr_tab2;
Synthesis.Hole.NTab.dest allowed_tab2;
Constraints.Constraint.NTab.dest constr_dep_tab;

use "synthesis/synthesise.ML";
val strms = 
    PolyML.exception_trace (fn () => 
                               Synthesis.synthesise_eq_terms 5 thy cs);
map (fn strm => Trm.print (ProofContext.init thy) (Synthesis.get_term strm)) strms;

val SOME (trm, ctab) = (Synthesis.synthesise_eq_terms 7 thy cs; NONE)
    handle Constraints.update_exp x => SOME x;

val SOME ((arg, nw_nm), old_nm, (c_tab, cd_tab)) =
    (Synthesis.synthesise_eq_terms 5 thy cs; NONE) 
    handle Synthesis.parent_exp x => SOME x;
val SOME (hc_tab, c_tab, a_tab, cd_tab) = 
    (Synthesis.synthesise_eq_terms 5 thy cs; NONE) 
    handle Synthesis.my_exp x => SOME x;

val SOME (constr, (cd_tab, c_tab)) = 
    (Synthesis.synthesise_eq_terms 8 thy; NONE) 
    handle Synthesis.not_sim_exp x => SOME x;

val SOME (constr, (c_tab, cd_tab)) = 
    (Synthesis.synthesise_eq_terms 6 thy cs; NONE) 
    handle Synthesis.delete_exp x => SOME x;

val SOME (constr, (hc_tab, c_tab, a_tab, cd_tab)) = 
    (Synthesis.synthesise_eq_terms 8 thy; NONE) 
    handle Synthesis.not_allowed_exp x => SOME x;

val SOME ((hole,const), nw_holes, (hc_tab, c_tab, a_tab, cd_tab)) = 
    (Synthesis.synthesise_eq_terms 5 thy; NONE) 
    handle Synthesis. x => SOME x;

val SOME (arg, (notsim_nm, arg_constrs), nw_holes,  
                      (hc_tab, c_tab, a_tab, cd_tab)) =
    (Synthesis.synthesise_eq_terms 7 thy; NONE) 
    handle Synthesis.NotSim_exp x => SOME x;
val SOME (ifthen_nm, sub_constr,  
          (hc_tab, c_tab, cd_tab)) =
    (Synthesis.synthesise_eq_terms 7 thy; NONE) 
    handle Synthesis.IfThen_exp x => SOME x;

val SOME (eq_constr, hole, const, (hc_tab, c_tab, a_tab, cd_tab)) = 
    (Synthesis.synthesise_eq_terms 7 thy; NONE) 
    handle Synthesis.eq_exp  x => SOME x;

Constraints.Constraint.NTab.dest c_tab;
Synthesis.Hole.NTab.dest hc_tab;
Synthesis.Hole.NTab.dest a_tab;
Constraints.Constraint.NTab.dest cd_tab;

val SOME strm = 
    (Synthesis.synthesise_eq_terms 8 thy; NONE) 
    handle Synthesis.inst_hole_exp  x => SOME x;

Trm.print (ProofContext.init thy) (Synthesis.get_term strm);
Constraints.Constraint.NTab.dest (Synthesis.get_constrTab strm);
Synthesis.Hole.NTab.dest (Synthesis.get_holeConstrs strm);
Synthesis.Hole.NTab.dest (Synthesis.get_allowedTab strm);
Constraints.Constraint.NTab.dest (Synthesis.get_constrDepTab strm);
InstEnv.print(Synthesis.get_ienv strm);

val SOME (const_info, allowed_tab, ienv) = 
    (Synthesis.synthesise_eq_terms 4 thy; NONE) 
    handle Synthesis.term_bit_exp  x => SOME x;

val sub_constr = Constraints.Constraint.mk("C",19);
val (nw_ref_nms, (hc_tab2, c_tab2, a_tab2, cd_tab2)) =
                  Synthesis.propagate_equality sub_constr hole const nw_holes 
                  (hc_tab, c_tab, a_tab, cd_tab);

Synthesis.check_not_sim constr   (hc_tab2, c_tab2, a_tab2, cd_tab2);


Constraints.Constraint.NTab.dest (Synthesis.get_constrTab strm);
Synthesis.Hole.NTab.dest (Synthesis.get_holeConstrs strm);
Synthesis.Hole.NTab.dest (Synthesis.get_allowedTab strm);
Constraints.Constraint.NTab.dest (Synthesis.get_constrDepTab strm);


(* Bug that puts commuted definitions twice *)
print_depth 30;
use "synthesis/constInfo.ML";
use "synthesis/synthesise.ML";
open ConstInfo;
use_thy "dbg/SynthN";
val thy = theory "SynthN";
val ctxt = ProofContext.init thy
val cs = Constraints.mk_const_infos thy;

(* Initially empty *)
val add_i1 = the (Constraints.lookup_const cs (Constraints.Constant.mk "SynthN.add"));
map (Trm.print ctxt) (get_commuted_defs add_i1)

(* This gives two things, as expected. *)
val (cs2, prfs) = commuted_defs thy cs;
val add_i2 = the (Constraints.lookup_const cs2 (Constraints.Constant.mk "SynthN.add"));
map (Trm.print ctxt) (get_commuted_defs add_i2);

