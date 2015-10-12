
header {* IsaPlanner for ZF *}

theory ZF_IsaP 
imports FOL_IsaP 
  and FOL_ripple_notation
begin

("rtechn/apply_rtechn.ML" )
("rtechn/isar_rtechn.ML" )
("cinfos/cached_explore_cinfo.ML" )
("rtechn/explore_rtechn.ML" )
("rtechn/generalise_rtechn" )
("rtechn/lemma_conj_rtechn.ML" )
("rtechn/indandsimp_isar_rtechn.ML" )
("rtechn/rippling_rtechn.ML")

(* Isar attributes for Rippling *)
(* "sys/ripple_attr.ML" -- now in ripple_tac.ML *)
("sys/ripple_tac.ML" )

(* ML interface *) 
("interface/searchtree.ML" )
("interface/interface.ML" )
("benchmarks/benchmarks.ML" ) :


text {* IsaPlanner ML code: *}

use "rtechn/apply_rtechn.ML"
use "rtechn/isar_rtechn.ML"
use "cinfos/cached_explore_cinfo.ML"
setup CachedExploreCInfo.I.setup

use "rtechn/explore_rtechn.ML"
use "rtechn/generalise_rtechn"
use "rtechn/lemma_conj_rtechn.ML"
use "rtechn/indandsimp_isar_rtechn.ML" 
use "rtechn/rippling_rtechn.ML"

(* Isar attributes for Rippling *)
(* "sys/ripple_attr.ML" -- now in ripple_tac.ML *)
use "sys/ripple_tac.ML"
setup RippleTac.setup

(* ML interface *) 
use "interface/searchtree.ML"
use "interface/interface.ML"
use "benchmarks/benchmarks.ML"

end;
