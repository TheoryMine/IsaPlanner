header {* Minimalistic IsaPlanner for HOL *}
theory IsaP
imports HOL Pure_IsaP IsaP_RippleNotation
uses 
"rtechn/rippling/ripple_wrulesdb.ML"

(* gproof methods *)
"gproof/prf/subst.ML"

(* dtacs *)
"gproof/isa/isa_dtacs.ML"
"gproof/isa/induct_dtac.ML"
"gproof/isa/splitter_dtac.ML"
"theories/HOL/induct_HOL.ML"
"theories/HOL/splitter_HOL_data.ML"

(* techn *)
"rtechn/dtac_rtechn.ML"
"rtechn/induct/induct_rtechn.ML"
"theories/HOL/isar_attr.ML"
"rtechn/split_rtechn.ML"
(* Lemma conjecturing *)
"rtechn/conj/lemma_conj_lib.ML"
"theories/HOL/lemma_conj_HOL_data.ML"
"rtechn/conj/conj_rtechn.ML"

(*Rippling*)
"rtechn/rippling/ripple_thyinfo.ML"
"rtechn/rippling/ripple_measure.ML"
"rtechn/rippling/ripple_skel.ML"
"rtechn/rippling/ripple_skel_onemeasure.ML"
"rtechn/rippling/ripple_skel_gm.ML"
"rtechn/rippling/ripple_cinfo.ML"
"rtechn/rippling/ripple_rtechn.ML"
(* "rtechn/rippling/ripple_bf_techn.ML" *)
"interface/mini_interface.ML"
begin

section {* Generic Theory Information for Rippling *}

setup RippleThyInfo.setup

subsection {* Making the techniques with functors... *}

ML {*
(* conjecturing...*)

(* structure LemmaConjLib = LemmaConjLibFUN(HOL_LemmaConjData);
structure ConjRTechn = ConjRTechnFUN(LemmaConjLib); *)

(* Ripple states with measures based on sum of distances *)
structure RippleMeasure_dsum = 
IntRippleMeasureFUN(
  val name = "distance sum"
  val atermifier = RippleATerms.cr_aterms_of_eterm
  val measuref = RippleATerms.dsum_measure_of);
structure RippleSkel_dsum = RippleSkelOneMeasureFUN(RippleMeasure_dsum);
structure RippleCInfo_dsum = RippleCInfoFUN(RippleSkel_dsum);
structure RippleRTechn_dsum = RippleRTechnFUN(
  structure RippleCInfo = RippleCInfo_dsum 
  structure ConjRTechn = ConjRTechn);

(* structure Ripple_BFRTechn_dsum = RippleBFRTechnFUN(
	structure RippleRTechn = RippleRTechn_dsum); *)

(* ML strcture binding for debugging *)
structure RippleSkel = RippleSkel_dsum;
structure RippleCInfo = RippleCInfo_dsum;
structure RippleRTechn = RippleRTechn_dsum;

(* structure Ripple_BF = Ripple_BFRTechn_dsum; *)


*}
setup RippleCInfo_dsum.I.setup

end;
