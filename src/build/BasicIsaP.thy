theory BasicIsaP
imports "BasicIsaP1"
begin

ML_file "../rstate/rstate.ML"
ML_file "../rstate/inftools.ML"
ML_file "../rstate/rtechn.ML"

(* declarative things; add datatype with more infor for Isar stuff *)
ML_file "../rtechn/basic/dtac.ML" (* declarative tactics *)
ML_file "../isar/dthm.ML" (* declarative theorms (possibly with attributes!) *)
ML_file "../isar/isar_attr.ML" (* specific Isar attributes with their names*)

(* make minimal names for frees vars etc *)
ML_file "../libs/term/minimal_rename_lib.ML"

(* lemma conjecturing *)
(* "rtechn/conj/conjecturedb_lib.ML"
"rtechn/conj/conjdb_cinfo.ML"
"rtechn/conj/conj_stack_cinfo.ML" *)


(* Contextual Information *)
ML_file "../cinfos/htrace/rst_name.ML"
ML_file "../cinfos/htrace/descrip_cinfo.ML"
ML_file "../cinfos/htrace/htrace_cinfo.ML"

(* Reasoning Technique Language *)
ML_file "../rtechn/basic/rst_pp.ML"
ML_file "../rtechn/basic/subspace.ML"
ML_file "../rtechn/basic/rtechn_comb.ML"

(* Interface *)
ML_file "../interface/searchtree.ML"

declare [[ML_exception_trace = true]]

ML {* 
fun print_count_list s l = 
    (Pretty.writeln (Pretty.str (s ^ " " ^ (Int.toString (length l)))); l);
fun print_count_seq s sq = 
    Seq.of_list (print_count_list s (Seq.list_of sq));
*}

section {* Theory Modifications *}

(*setup SkipMeth.setup
	setup EvalThyInfo.setup
	setup EvalOrders.setup
	setup EvalMeth.setup
*)

(* now done by functor call
   setup CInfo.setup *)

(*setup TechnThyInfo.setup 
	setup DebugCInfo.I.setup
*)

setup "DescripCInfo.I.init_in_thy"
setup "HTraceCInfo.I.init_in_thy"

(*setup UserPointsCInfo.I.setup*)

(*setup GapTac.setup *)
(* things below might have been commented out before me but
 setup PPTac.setup  *)

end