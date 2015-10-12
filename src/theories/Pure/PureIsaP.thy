header {* Logic Independent Parts of IsaPlanner for Isabelle *}

theory PureIsaP
imports HOL
uses "Pure_IsaP.ML"
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

(* setup Conjdb_CtxtInfo.I.setup *)

(*setup UserPointsCInfo.I.setup*)

(*setup GapTac.setup *)
(* things below might have been commented out before me but
 setup PPTac.setup  *)

end;
