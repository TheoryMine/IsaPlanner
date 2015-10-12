(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/dattrib.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    19 Oct 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Declarative version of Isar's "attrib.ML"
*)

structure DAttrib 
= struct

datatype T = DAttrib of {
         ctxt : Proof.context DCtxtAttr.T,
         thry : Theory.theory DCtxtAttr.T };

fun ctxt_attr_of (DAttrib rep) = #ctxt rep;
fun thry_attr_of (DAttrib rep) = #thry rep;

fun src_of da = Attrib.attribute (DCtxtAttr.attrf_of (thry_attr_of da), 
                                  DCtxtAttr.attrf_of (ctxt_attr_of da));

fun mk_dattrib (ctxt_prettyf, thry_prettyf, 
                ctxt_attrf, thry_attrf,
                eq, decf, encf) d = 
    DAttrib {
    ctxt = DCtxtAttr.mk_dattr (ctxt_prettyf, ctxt_attrf, eq, decf, encf) d,
    thry = DCtxtAttr.mk_dattr (thry_prettyf, thry_attrf, eq, decf, encf) d
    };

fun data_of k df = DCtxtAttr.mk_getdataf k df o ctxt_attr_of;

fun thry_pretty da ctxt = DCtxtAttr.prettyf_of (thry_attr_of da) ctxt;
fun ctxt_pretty da thry = DCtxtAttr.prettyf_of (ctxt_attr_of da) thry;

fun ctxt_attrf da = DCtxtAttr.attrf_of (ctxt_attr_of da);
fun thry_attrf da = DCtxtAttr.attrf_of (thry_attr_of da);

end;




(* the kind of a declarative attribute must have these things... *)
signature DATTR_KIND =
sig

type T

val ctxt_attrf : T -> Proof.context Thm.attribute
val thry_attrf : T -> Theory.theory Thm.attribute
val eq : T -> T -> bool
val ctxt_prettyf : T -> Proof.context -> Pretty.T
val thry_prettyf : T -> Theory.theory -> Pretty.T
val name : string

end;


(* to get an instance of a declarative attribute kind *)
signature DATTR_INST =
sig

type T

val kind : SafeObject.kind

val dattr_of : T -> DAttrib.T
val data_of : DAttrib.T -> T option

end;


functor DCtxtAttrInstFUN (structure K : DATTR_KIND)
        : DATTR_INST = 
struct

val kind = SafeObject.kind K.name;

type T = K.T;

local 
  exception Data of T;
  fun decf (Data x) = x
  fun encf d = (kind, Data d)
in

(* implicit extra arg: DThyAttr.T *)
val data_of = DAttrib.data_of kind decf;

(* implicit extra arg: T *)
val dattr_of = 
    DAttrib.mk_dattrib 
      (K.ctxt_prettyf, K.thry_prettyf, 
       K.ctxt_attrf, K.thry_attrf,
       K.eq, decf, encf);

end; (* local *)

end; (* DCtxtAttrInstFUN *)
