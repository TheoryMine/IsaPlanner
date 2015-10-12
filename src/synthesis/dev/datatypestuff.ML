


use_thy "examples/N";
val thry = the_context();
val dtypestab = DatatypePackage.get_datatypes thry;
val datatypes = Symtab.dest dtypestab

(* The info has a descr field that tells us the names of the constructors etc *)
(* index, datatype name, type arguments, constructor name, types of constructor's arguments *)
(* type descr = (int * (string * dtyp list * (string * dtyp list) list)) list; *)



val natinfo = the (Symtab.lookup dtypestab "nat");
val descr = (#descr natinfo);
val inject = (#inject natinfo);
val [(ind, (typnm, typargs, [(zero_constr, zeroargs), (suc_constr, sucargs)]))] =
    descr;
val sorts = (#sorts natinfo);


(* *)
val thry = theory "N";
val distinct = #distinct natinfo;
val DatatypeAux.FewConstrs l =  distinct;
val _ = Thm.prop_of thm1;
val hol_sym = PureThy.get_thm thry "HOL.sym";
val hol_iffd1 = PureThy.get_thm thry "HOL.iffD1";
val hol_eq_False_thm = PureThy.get_thm thry "HOL.eq_False";
val hol_eq_False_thm_sym = Seq.hd (rtac hol_eq_False_thm 1 hol_sym);



(* below doesn't work because there is thm1 has no subgoals! *)
val 
Seq.list_of 
  (EqSubst.eqsubst_tac (ProofContext.init thry) [0] [hol_eq_False_thm_sym] 1 thm1);

(* other method: break up into simple resolution step... *)
val thm2 = thm1 RS (hol_eq_False_thm_sym RS hol_iffd1);


(* get the arguments as a type-type if we want to build terms.*)
val sucargtyp = DatatypeAux.typ_of_dtyp descr sorts (hd sucargs);

(* Need something similar for functions *)

use_thy "examples/N";
val thry = theory "N";

use_thy "examples/critics_isabelleWS07";
val thry = theory "critics_isabelleWS07"
val ctxt = ProofContext.init thry;


val cs = ["N.N.zero", "HOL.plus_class.plus", "N.N.suc"];
val types = map (Sign.the_const_type thry) cs;

raise Exception "stop"

(* ALternative for contexts *) 
val consts = ProofContext.consts_of ctxt; 
val naming = ProofContext.naming_of ctxt; 
val ctxtnm = NameSpace.path_of naming; (* this will name it local, not sure this is
right wrt. what our thorems are called. *)

val consts =Sign.consts_of thry; 
val naming = Sign.naming_of thry;
val thyname = NameSpace.path_of naming; 


(* val const_space  = Sign.const_space thry;
val ext_names = NameSpace.external_names naming
*)

val conststab =  (#constants(Consts.dest consts));
(* val ext_cs = NameSpace.extern_table conststab; *)
val int_cs = NameSpace.dest_table conststab;
print_depth 30;

(* This gives the constants and their types of theory N *)
val N_consts = filter (fn (x,y) => String.isPrefix "N." x) int_cs;

val thy_consts =  filter (fn (x,y) => String.isPrefix thyname x) int_cs;

(* Mega-ugly way of doing it. Doesn't work for constants with names
that are inherited from elsewhere eg plus. *)
val simps = map_filter (fn (n, stuff) => 
                           SOME (thms (n^".simps"))
                           handle ERROR s => NONE 
                       ) thy_consts;
                                 
(*
val conststab = snd (#constants(Consts.dest consts));
val consts = Symtab.dest consts;
*)
