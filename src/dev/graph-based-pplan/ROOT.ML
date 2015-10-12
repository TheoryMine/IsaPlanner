(* Generic Tools for namers, fresh names tables, and collections *)
use "tools/dbg.ML"; (* debugging tools *)
use "tools/fnamer.ML"; (* idea of creating fresh names *)
use "tools/namers.ML"; (* some things to choose names *)
use "tools/fnametab.ML"; (* name tables which provide fresh names *)
use "tools/collection.ML"; (* collections of things  *)

(* copies of unification from Isabelle that track new generated
variable names, and goal names from which flex-flexes have come from *)
use "unif/myenvir.ML";
use "unif/mytypunify.ML";
use "unif/mypattern.ML";
use "unif/myunify.ML";

(* abstract notion of terms *)
use "prf/paramtab.ML"; (* named, ordered, counted, parameter tables *)
use "prf/trm.ML"; (* basic trm and trm where trm = basic + renaming *)
use "isa/isa_basic_trm.ML"; (* basic Isabelle term instantiation *)
use "isa/my_thm_pretty.ML"; (* special thm/term pretty printing *)
use "prf/trm_rename.ML"; (* renaming of terms *)
use "isa/isa_trm.ML"; (* Isabelle instantiation with renaming *)

(* abstract notion of instantiation and variable dependencies *)
use "prf/basic_instenv.ML";
use "prf/instenv.ML"; (* extends basic instenv with unification *)
use "isa/isa_instenv.ML"; (* Isabelle instantiation *)
use "prf/depenv.ML"; (* dependency environment *)

(* declarative tactics which can record instantiations *)
use "prf/flexes.ML"; (* for doing stuff with flex-flex pairs *)
use "prf/dtac.ML";
(* use "isa/isa_dtacs.ML"; *)

(* proofs *)
use "prf/aprf.ML"; (* abstract proof *)
use "prf/prf.ML"; (* real proof - with flexes *)

(* tactic/method language *)
use "tools/m.ML";

(* Some ML level interface tools 
use "tools/i.ML";
*)
