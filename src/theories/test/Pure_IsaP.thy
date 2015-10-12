header {* Minimalistic IsaPlanner with new proof-representation  *}

theory Pure_IsaP
imports CPure
uses

(* replacement for changed Isabelle version *)
 "libs/safe_object.ML"

(* *** proof *** *)
(* Generic Tools for namers, fresh names tables, and collections *)
"gproof/tools/fnamer.ML" (* idea of creating fresh names *)
 "gproof/tools/namers.ML" (* some things to choose names *)
 "gproof/tools/fnametab.ML" (* name tables which provide fresh names *)
 "gproof/tools/collection.ML" (* collections of things  *)

(* term debugging tools such as writeterm... *)
 "gproof/tools/dbg.ML"

(* copies of unification from Isabelle that track new generated
variable names, and goal names from which flex-flexes have come from *)
 "gproof/unif/myenvir.ML"
 "gproof/unif/mytypunify.ML"
 "gproof/unif/mypattern.ML"
 "gproof/unif/myunify.ML"

(* abstract notion of terms *)
 "gproof/prf/paramtab.ML" (* named, ordered, counted, parameter tables *)
 "gproof/prf/trm.ML" (* basic trm and trm where trm = basic + renaming *)
 "gproof/isa/isa_basic_trm.ML" (* basic Isabelle term instantiation *)
 "gproof/prf/trm_rename.ML" (* renaming of terms *)
 "gproof/isa/isa_trm.ML" (* Isabelle instantiation with renaming *)

(* abstract notion of instantiation and variable dependencies *)
 "gproof/prf/basic_instenv.ML"
 "gproof/prf/instenv.ML" (* extends basic instenv with unification *)
 "gproof/isa/isa_instenv.ML" (* Isabelle instantiation *)
 "gproof/prf/depenv.ML" (* dependency environment *)

(* declarative tactics which can record instantiations *)
 "gproof/prf/flexes.ML" (* for doing stuff with flex-flex pairs *)
 "gproof/prf/dtac.ML"

(* proofs *)
"gproof/prf/cx.ML" (* abstract context *)
"gproof/prf/rtree.ML" (* result trees = horn clauses *)
"gproof/prf/aprf.ML" (* abstract proof *)
"gproof/prf/prf.ML" (* real proof  with flexes *)

(* tactic/method language *)
"gproof/tools/m.ML"



(* generic search *)
"generic/gsearch.ML"
"generic/msearch.ML"
"generic/lsearch.ML"

(* Basic tactic additions to Isabelle *)
"sys/skip_meth.ML"
"sys/isap_tac.ML"

(* Term Related Libraries *)
"libs/prologify_terms.ML"
"libs/term_const_lib.ML"
"libs/type_tree_terms_lib.ML"
"libs/term_tree_handler_lib.ML"
"libs/embedding_name_table_lib.ML"
"libs/embedding_lib.ML"
"libs/generalise_lib.ML"

(* Equational reasoing with nets *)
"sys/rule_net.ML"


(* Evaluation tactic *)
(*"sys/thm_eval_net.ML"
"sys/eval_thyinfo.ML"
"sys/eval_orders.ML"
"sys/eval_tac.ML"
"sys/eval_meth.ML"
*)

(* Basic Generic Framework *)
(* "base/pscript.ML" *)
"base/pplan.ML"
"base/cinfo.ML"
"base/rstate.ML"
"base/inftools.ML"
"base/rtechn.ML"

(* declarative things *)
"base/Isar/dthm.ML"

(* Basic Isar Proof Planning bits *)
"base/Isar/isar_attr.ML"

(* make minimal names for frees vars etc *)
"libs/minimal_rename_lib.ML"

(* lemma conjecturing *)
(* "rtechn/conj/conjecturedb_lib.ML"
"rtechn/conj/conjdb_cinfo.ML"
"rtechn/conj/conj_stack_cinfo.ML" *)


(* Contextual Information *)
"cinfos/htrace/rst_name.ML"
"cinfos/htrace/descrip_cinfo.ML"
"cinfos/htrace/htrace_cinfo.ML"

(* Reasoning Technique Language *)
"rtechn/rst_pp.ML"
"rtechn/subspace.ML"
"rtechn/rtechn_comb.ML"
"rtechn/rtechn_env.ML"

(* Interface *)
"interface/searchtree.ML"
(*"interface/interface.ML"*)
begin
section {* Theory Modifications *}


(*setup SkipMeth.setup
	setup EvalThyInfo.setup
	setup EvalOrders.setup
	setup EvalMeth.setup
*)
setup CInfo.setup
(*setup TechnThyInfo.setup 
	setup DebugCInfo.I.setup
*)

setup DescripCInfo.I.setup
setup HTraceCInfo.I.setup

(* setup Conjdb_CtxtInfo.I.setup
setup ConjStackCInfo.I.setup *)

(*setup UserPointsCInfo.I.setup*)

(*setup GapTac.setup *)
(* things below might have been commented out before me but
 setup PPTac.setup  *)

end;
