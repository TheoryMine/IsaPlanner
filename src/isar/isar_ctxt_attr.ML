(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/isar_ctxt_attr.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    28 Feb 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    the basic Isar language Attributes, in a declarative form - these are
    the normal Isabelle notion fo attributes for contexts or attributes. 
*)

structure IsarCtxtAttr = 
struct 

val base_thy = ThyInfo.theory "Main"; 
val dummy_thy = ThyInfo.theory "Main"; 

type dthm = DAttrib.T;

exception attr_exp of string;

structure RuleFormat = 
struct

  val name = "rule_format"

  type T = unit;

  fun prettyf () ctxt_or_thy = Pretty.str (name);

  fun attrf_aux f (fk,th) = 
      f fk (Args.src ((name, []), Position.none)) 
        (fk,th);

  fun ctxt_attrf () (ctxt,th) = 
      attrf_aux Attrib.context_attribute (ctxt,th);
  fun thy_attrf () (thry,th) = 
      attrf_aux Attrib.global_attribute (thry,th);

  structure A = 
    DCtxtAttrInstFUN(
      structure K = 
      struct
        type attrv = Proof.context;
        type T = T;
        val name = name;
        fun eq x y = true;
        val ctxt_attrf = ctxt_attrf;
        val ctxt_prettyf = prettyf;
        val thry_attrf = thy_attrf;
        val thry_prettyf = prettyf;
      end)

  val rule_format = A.dattr_of ();

end; (* RuleFormat *)



(* symetric attribute *)
structure Symmetric = 
struct

val name = "symmetric"

type T = unit;

  fun prettyf () ctxt_or_thy = Pretty.str name;

  fun attrf_aux f (fk,th) = 
      f fk (Args.src ((name, []), Position.none)) 
        (fk,th);
  fun ctxt_attrf () (ctxt,th) = 
      attrf_aux Attrib.context_attribute (ctxt,th);
  fun thy_attrf () (thry,th) = 
      attrf_aux Attrib.global_attribute (thry,th);

  structure A = 
    DCtxtAttrInstFUN(
      structure K = 
      struct
        type attrv = Proof.context;
        type T = T;
        val name = name;
        fun eq x y = true;
        val ctxt_attrf = ctxt_attrf;
        val ctxt_prettyf = prettyf;
        val thry_attrf = thy_attrf;
        val thry_prettyf = prettyf;
      end)

  val symmetric = A.dattr_of ();

end; (* RuleFormat *)

end;
