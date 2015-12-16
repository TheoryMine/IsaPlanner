theory BasicIsaP1
imports
 HOL
 "~~/contrib/isaplib/pure_isaplib"
(*  "skel"  *)
begin

(* *** Isabelle extra *** *)
(* replacement for changed Isabelle version *)
ML_file "../libs/polym_table.ML"
ML_file "../libs/safe_object.ML" (* FIXME: remove and replace with polym table stuff *)
(* term debugging tools such as writeterm... *)
(* "../libs/term/termdbg.ML" *)
(* some additions to the top-level environment *)
ML_file "../libs/toplevel.ML"

(* generic measure traces *)
ML_file "../libs/measure_traces.ML"

(* *** proof *** *)

(* abstract notion of terms *)
ML_file "../libs/term/paramtab.ML" (* named, ordered, counted, parameter tables *)
ML_file "../libs/term/trm.ML" (* genericish terms *)
ML_file "../libs/term/isa_trm.ML" (* Isabelle instantiation of generic-ish terms  *)
ML_file "../libs/term/fterm.ML" (* Flattened Isabelle terms  *)
ML_file "../libs/term/fzipper.ML" (* Zipper for Flattened Isabelle terms  *)
(* "../gproof/prf/trm_rename.ML" *) (* renaming of terms *)

(* abstract notion of instantiation and variable dependencies *)
ML_file "../libs/term/instenv.ML"
ML_file "../libs/term/lifting.ML"

(* copies of unification from Isabelle that track new generated
variable names, and goal names from which flex-flexes have come from *)
ML_file "../libs/term/unif/norm.ML"
ML_file "../libs/term/unif/typ_unify.ML"
ML_file "../libs/term/unif/pattern.ML"
ML_file "../libs/term/unif/unify.ML"

ML_file "../libs/term/flexes.ML" (* for doing stuff with flex-flex pairs *)

(* declarative tactics which can record instantiations *)

(* pplan *)
ML_file "../pplan/isa_step.ML"
ML_file "../pplan/cx.ML" (* abstract context *)
ML_file "../pplan/depenv.ML" (* var/goal dependency environment *)
ML_file "../pplan/rtree.ML" (* result trees = horn clauses *)
ML_file "../pplan/aprf.ML" (* abstract proof *)
ML_file "../pplan/prf.ML" (* real proof  with flexes *)

(* tactic/method language *)
ML_file "../pplan/gtacs.ML" (* generic tacticcals for named results *)
(*  "../gproof/tools/m.ML" generic goal-named tactics *)

(* Term Related Libraries *)
ML_file "../libs/term/prologify_terms.ML"
ML_file "../libs/term/term_const_lib.ML"
ML_file "../libs/term/typed_terms_lib.ML"
ML_file "../libs/term/subsumption_net.ML"
(* "libs/term_tree_handler_lib.ML" *)

(* embeddings *)
ML_file "../libs/term/embedding/eterm.ML"
ML_file "../libs/term/embedding/ectxt.ML"
ML_file "../libs/term/embedding/embed.ML"

(* rippling libraries *)
ML_file "../rtechn/rippling/measure.ML"
ML_file "../rtechn/rippling/flow_measure.ML"
ML_file "../rtechn/rippling/dsum_measure.ML"
ML_file "../rtechn/rippling/skel.ML"
ML_file "../rtechn/rippling/skel_mes_traces.ML"
(* "../rtechn/rippling/skel_betters.ML" *)
(* "../rtechn/rippling/skel_better.ML" *)

(* generalisation *)
ML_file "../libs/term/generalise_lib.ML"

(* Equational reasoing with nets *)
(* "../sys/rule_net.ML" *)
ML_file "../rtechn/basic/prf_morph_net.ML"


(* Evaluation tactic *)
(*"sys/thm_eval_net.ML"
"sys/eval_thyinfo.ML"
"sys/eval_orders.ML"
"sys/eval_tac.ML"
"sys/eval_meth.ML"
*)

(* Basic Generic Framework *)
ML_file "../pplan/pplan.ML"
ML_file "../rstate/cinfo.ML"
ML_file "../rstate/lcinfo.ML"

end
