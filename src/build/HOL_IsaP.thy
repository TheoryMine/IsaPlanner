theory HOL_IsaP
imports 
  Complex_Main 
  (* Generic parts of IsaPlanner*)
  "BasicIsaP"
  "EmbeddingNotation"

  (* Higher Order parts of IsaPlanner*)
  "IsaPHOLUtils" 
begin
  (* gproof methods *)
ML_file   "../pplan/subst.ML"
ML_file   "../critics/metavar_lib.ML"
ML_file   "../rtechn/basic/res.ML"
ML_file   "../rtechn/basic/rtechn_env.ML"

(* recursive path orders *)
ML_file   "../libs/term/termination.ML"

(* AC-matching *)
ML_file   "../libs/term/ac_eq.ML"
(* Benchmarks *)
(*  "../benchmarks/thread.ML"
  "../benchmarks/benchmarks_sql.ML"*)

(* counter examples *)
ML_file   "../cinfos/counterex_cinfo.ML"

(* rippling wave rule database *)
ML_file   "../rtechn/rippling/wrulesdb.ML"

(* dtacs *)
ML_file   "../rtechn/basic/isa_dtacs.ML"
ML_file   "../rtechn/induct/induct_dtac.ML"

ML_file   "../build/induct_HOL.ML"

(* techn *)
ML_file   "../rtechn/basic/dtac_rtechn.ML"
ML_file   "../rtechn/induct/induct_rtechn.ML"
ML_file   "../build/isar_attr.ML"
ML_file   "../rtechn/split/split_rtechn.ML"

  (* Lemma conjecturing *)
ML_file   "../rtechn/conj/conj_subsume.ML"
ML_file   "../rtechn/conj/conj_stack_cinfo.ML"
ML_file   "../rtechn/conj/conjecturedb_lib.ML"
ML_file   "../rtechn/conj/conjdb_cinfo.ML"
ML_file   "../rtechn/conj/lemma_conj_lib.ML"
ML_file   "../build/lemma_conj_HOL_data.ML"
ML_file   "../rtechn/conj/conj_rtechn.ML"

(* Counter example (quickcheck) and auto *)
ML_file   "../rtechn/quickcheck_auto.ML"

(* Simplification based proof technique (CADE'03) *)
ML_file   "../rtechn/induct_and_simp.ML"

(* Rippling wave rules DB from theory *)
ML_file   "../rtechn/rippling/wrules_gctxt.ML"

(* rippling critic libs *)
ML_file   "../critics/middleout_rw.ML"
ML_file   "../critics/lemma_speculation.ML"

(* rippling techniques *)
ML_file   "../rtechn/rippling/basic_cinfo.ML"
ML_file   "../rtechn/rippling/basic_rtechn.ML"
ML_file   "../rtechn/rippling/midout_cinfo.ML"
ML_file   "../rtechn/rippling/casesplit.ML"
ML_file   "../rtechn/rippling/casesplit_calc.ML"
ML_file   "../rtechn/rippling/postripple_casesplit.ML"
ML_file   "../rtechn/rippling/lemcalc.ML"
ML_file   "../rtechn/rippling/lemspec.ML"
(*
  "../rtechn/rippling/ripple_bf_techn.ML" 
*)

(* Relational Rippling *)
(*   "../rtechn/rrippling/rr_wrulesdb.ML" *)
(*  *** 
  "../rtechn/rrippling/rr_table.ML" (* Contains the definition of the rtable. Solves order-of-inclusion problem. *)
  "../rtechn/rrippling/rr_linkinfo.ML" (* Perhaps move these functions into rr_cinfo? May cause problems with order-of-inclusion! *)
  "../rtechn/rrippling/rr_embeddinglib.ML"
  "../rtechn/rrippling/rr_aterms.ML"
  "../rtechn/rrippling/rr_trmutil.ML" (* Functions that don't really belong anywhere else. Debug output for terms and eterms, etc. *)
  "../rtechn/rrippling/rr_measure.ML" (* Relational measure: (functional wave-fronts * relational wave-fronts). *)
  "../rtechn/rrippling/rr_measure_tabs.ML" (* The tables for type and positions of wave-fronts. *)
  "../rtechn/rrippling/rr_skel.ML"
(*   "../rtechn/rrippling/rr_thyinfo.ML" *)
  "../rtechn/rrippling/rr_cinfo.ML"
  "../rtechn/rrippling/rr_techn.ML" (* Relational rippling reasoning technique implementation proper. *)
*)

(* interface *)
ML_file   "../interface/interface.ML"

section {* Generic Theory Information for Rippling *}

(* the wave rule addtributes *)
(* syntax works as follows:
   [attr_name]  --  adds the thms to the attr_name set
   [attr_name add] -- as above
   [attr_name del] -- removes thsm from the attr_name set

   [wrule]  --  the wave rules set
   [all_wrule] -- wave rules without filtering bad rules

   [impwrule] -- adds implication for reasoning backwards (unsafe rewriting) 
 
   [fwd_impwrule] -- adds implications for reasoning forward
*)
attribute_setup wrule =
{* Attrib.add_del (Thm.declaration_attribute WRulesGCtxt.add_wrule_thm)
                  (Thm.declaration_attribute WRulesGCtxt.del_wrule_thm) *}
"add wave rules (filtering silly thing)"

attribute_setup all_wrule = 
{* Attrib.add_del (Thm.declaration_attribute WRulesGCtxt.addall_wrule_thm) 
                  (Thm.declaration_attribute WRulesGCtxt.delall_wrule_thm) *}
"add all wave rules (no filtering)"

attribute_setup impwrule =
{* Attrib.add_del (Thm.declaration_attribute WRulesGCtxt.add_impwrule_thm) 
                  (Thm.declaration_attribute WRulesGCtxt.del_impwrule_thm) *}
"add implication wave rule (reasoning backward)"

attribute_setup fwd_impwrule = 
{* Attrib.add_del 
     (Thm.declaration_attribute WRulesGCtxt.add_fwd_impwrule_thm)
     (Thm.declaration_attribute WRulesGCtxt.del_fwd_impwrule_thm) *}
"add implication wacve rule (reasoning forward)"

    
(** outer syntax for print_wrules
val () =
  OuterSyntax.improper_command "print_wrules" "print the currently used wave rules."
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o 
                   (Toplevel.keep
      ((*Toplevel.node_case 
         (print)*)
         (WRules.print o get_from_ctxt o Proof.context_of o Toplevel.proof_of)
    ))));
**)

section {* Rippling Implementations *}

-- "Ripple states with measures based on grouped flow"
ML {*
structure RippleSkel_flow = RippleSkelMesTracesFUN(FlowMeasure);
structure RippleSkel_flow = RippleSkelMesTracesFUN(FlowMeasure);
*}
-- "Rippling contextual information"
ML {*
structure RippleCInfo_flow = BasicRippleCInfoFUN(RippleSkel_flow);
*}
-- "Middle-out rippling contextual information"
ML {*
structure MidOutCInfo_flow = MidOutRippleCInfoFUN(RippleCInfo_flow);
*}
-- "Rippling Reasoning Techniques "
ML {*
structure RippleRTechn_flow = BasicRippleRTechnFUN(
  structure RippleCInfo = RippleCInfo_flow 
  structure ConjRTechn = ConjRTechn);
structure RippleCaseSplit_flow = RippleCaseSplitRTechnFUN(
                            structure BasicRipple = RippleRTechn_flow);
structure RippleCasePostSplit_flow = RippleCasePostSplitFUN(
                            structure BasicRipple = RippleRTechn_flow); 
*} 

-- "Rippling techniques with Lemma-calculationa and Case Analysis"
ML {*
structure RippleLemCalc_flow = RippleLemCalcFUN(
                          structure BasicRipple = RippleCaseSplit_flow);
structure RippleLemCalc_flow2 = RippleLemCalcFUN(
                          structure BasicRipple = RippleCasePostSplit_flow);
structure RippleLemSpec_flow =  RippleLemSpecFUN(
                           structure RippleLemCalc = RippleLemCalc_flow
                           structure MidOutRCInfo = MidOutCInfo_flow);
*} 

-- "All Flow-Rippling under one structure"
ML {* 
structure FlowRippler = struct
  structure Measure = FlowMeasure;
  structure Skel = RippleSkel_flow;
  structure CInfo = RippleCInfo_flow;
  structure MidOutCInfo = MidOutCInfo_flow;
  structure RTechn = struct 
    structure Basic = RippleRTechn_flow;
    structure LemCalc = RippleLemCalc_flow;
    structure LemSpec = RippleLemSpec_flow;
   end;
end;

(* IMPROVE: add again the best first rippler... ? structure Ripple_BF = Ripple_BFRTechn; *)
*}

-- "Sum of Distances measure (approx hamming distance, see DixonFLeuriot at TPHOLs'04)" 
ML {*
structure RippleSkel_dsum = RippleSkelMesTracesFUN(DSumMeasure);
structure RippleCInfo_dsum = BasicRippleCInfoFUN(RippleSkel_dsum);
structure MidOutCInfo_dsum = MidOutRippleCInfoFUN(RippleCInfo_dsum);
structure RippleRTechn_dsum = BasicRippleRTechnFUN(
  structure RippleCInfo = RippleCInfo_dsum 
  structure ConjRTechn = ConjRTechn);
structure RippleCaseSplit_dsum = RippleCaseSplitRTechnFUN(
                            structure BasicRipple = RippleRTechn_dsum);
structure RippleLemCalc_dsum = RippleLemCalcFUN( 
                          structure BasicRipple = RippleCaseSplit_dsum);
structure RippleLemSpec_dsum =  RippleLemSpecFUN(
                           structure RippleLemCalc = RippleLemCalc_dsum
                           structure MidOutRCInfo = MidOutCInfo_dsum);
*} 

-- "Set Rippling defaults"
ML {*
structure Rippler = FlowRippler;
structure RippleMeasure = Rippler.Measure;
structure RippleSkel = Rippler.Skel;
structure RippleCInfo = Rippler.CInfo;
structure MidOutCInfo = Rippler.MidOutCInfo;
structure RippleRTechn = Rippler.RTechn.Basic;
structure RippleLemCalc = Rippler.RTechn.LemCalc;
structure RippleLemSpec = Rippler.RTechn.LemSpec;
*} 

-- "Simplification based inductive prover (see DixonFleuriot at CADE'03)"
ML {*
  structure InductAndSimp = InductAndSimpRTechnFUN(ConjRTechn);
*}


-- {* Setup calls add entries to IsaPlanner's contextual info table (updates the initially 
      empty table in the theory) *}

-- "setup for different kinds of rippling"

setup RippleCInfo_flow.I.init_in_thy
setup RippleCInfo_dsum.I.init_in_thy
setup MidOutCInfo_flow.MidOutI.init_in_thy
setup MidOutCInfo_dsum.MidOutI.init_in_thy

-- "setup other inductive proof technique tools"

(* setup ConjStackCInfo.Ctxt.setup *)
setup CounterExCInfo.I.init_in_thy

end
