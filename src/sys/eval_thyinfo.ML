(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/eval_thyinfo.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    16 June 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Theory information for holding sets of evaluation nets and orders

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature EVAL_THY_INFO = 
sig

type T

(* adding rulenets and orders *)
val add_rnet_to_thy : ThmEvalNet.rulenet -> theory -> theory
val add_eord_to_thy : ThmEvalNet.evalord -> theory -> theory

(* getting nets and orders *)
val rnets_of_thy : theory -> ThmEvalNet.rulenet list
val rnets_of_ctxt : Proof.context -> ThmEvalNet.rulenet list

val eords_of_thy : theory -> ThmEvalNet.evalord list
val eords_of_ctxt : Proof.context -> ThmEvalNet.evalord list

val lookup_rnet_from_thy : (string * Theory.theory) -> ThmEvalNet.rulenet
val lookup_eord_from_thy : (string * Theory.theory) -> ThmEvalNet.evalord

val lookup_rnet_from_ctxt : (string * Proof.context) -> ThmEvalNet.rulenet
val lookup_eord_from_ctxt : (string * Proof.context) -> ThmEvalNet.evalord

(* adding and deleting rules *) 
val add_rule_to_thy : string -> theory attribute
val del_rule_from_thy : string -> theory attribute

val add_rule_to_ctxt : string -> Proof.context attribute
val del_rule_from_ctxt : string -> Proof.context attribute

(* Needed in order for method/attribute operations on proof context *)
val mapto_thyinfo_in_ctxt : 
    (T -> T) -> Proof.context -> Proof.context

val mapto_rnet_in_ctxt : 
    (ThmEvalNet.rulenet -> ThmEvalNet.rulenet) 
    -> string -> Proof.context -> Proof.context


(* printing *)
val print_from_thy : theory -> unit
val print_from_ctxt : Proof.context -> unit

val print_rnets_of_thy : theory -> unit
val print_rnets_of_ctxt : Proof.context -> unit

val print_eords_of_thy : theory -> unit
val print_eords_of_ctxt : Proof.context -> unit



(* setting the default net *)
(* val set_default_net : string -> theory -> theory *)

val setup : (theory -> theory) list

end;


structure EvalThyInfo : EVAL_THY_INFO = 
struct

exception eval_thy_info of string

datatype T = thyinfo of { rnets : ThmEvalNet.rulenet Symtab.table,
                          onet : ThmEvalNet.evalord Symtab.table };
fun rnets_of (thyinfo r) = #rnets r;
fun onet_of (thyinfo r) = #onet r;

val empty = (thyinfo {rnets = Symtab.empty, 
                      onet = Symtab.empty}) : T;


fun join_rulenets k (n1, n2) = 
    (SOME (ThmEvalNet.merge (n1, n2))
     handle ThmEvalNet.thm_eval_net_exp _ => 
            raise eval_thy_info "join_rulenets: conflicting rulenets");

fun join_evalords k (o1, o2) = 
    if SafeObject.eq_kind (ThmEvalNet.kind_of_evalord o1, 
                           ThmEvalNet.kind_of_evalord o2) then 
      SOME o1
    else
      raise eval_thy_info "join_evalords: conflicting evalords";


fun add_rnet (rnet, thyinfo{ rnets, onet}) = 
    thyinfo{rnets = Symtab.update_new (ThmEvalNet.name_of rnet, rnet) rnets, 
            onet = onet};

fun update_rnet (rnet, thyinfo{rnets, onet}) = 
    thyinfo{rnets = Symtab.update (ThmEvalNet.name_of rnet, rnet) rnets, 
            onet = onet};

fun add_eord (eord, thyinfo{rnets, onet}) = 
    thyinfo{rnets = rnets, 
            onet = Symtab.update_new 
              (ThmEvalNet.name_of_evalord eord, eord) onet};

fun lookup_rnet (s,thyinfo{rnets, onet}) = 
    (Library.the (Symtab.lookup rnets s)) 
    handle Option => 
           raise eval_thy_info "lookup_rnet: no such rulenet";

fun lookup_eord (s,thyinfo{rnets, onet}) = 
    (Library.the (Symtab.lookup onet s)) 
    handle Option => 
           raise eval_thy_info "lookup_eord: no such evalorder";



(* printing *)
fun pretty_rnets nets = 
    Pretty.chunks (map (ThmEvalNet.pretty o snd) (Symtab.dest nets));
fun pretty_onet onet = 
    Pretty.chunks (map (ThmEvalNet.pretty_evalord o snd) (Symtab.dest onet));
val print_rnets = Pretty.writeln o pretty_rnets;
val print_onet = Pretty.writeln o pretty_onet;

fun pretty d = 
    Pretty.chunks [Pretty.str "Evaluation nets: ",
                   pretty_rnets (rnets_of d),
                   Pretty.str "Evaluation orders: ",
                   pretty_onet (onet_of d)];

(* data associated with a theory *)
structure GlobalDataArgs : THEORY_DATA_ARGS =
struct
  val name = "IsaPlanner/Isar/evalinfo";
  type T = T ref;
  val empty = ref empty;
  fun copy (ref d) = (ref d) : T;
  val prep_ext = copy; (* what is this for? - copied from simp *)
  fun merge pp (ref d1, ref d2) = 
      ref (thyinfo {rnets = Symtab.join join_rulenets 
                                        (rnets_of d1, rnets_of d2),
                    onet = Symtab.join join_evalords 
                                        (onet_of d1, onet_of d2)});
  val extend = I; (* ? what is this for? *)
  fun print sign (ref rn) = Pretty.writeln (pretty rn);
end;
structure GlobalData = TheoryDataFun(GlobalDataArgs);

val print_from_thy = GlobalData.print;
val thyinfo_ref_of_thy = GlobalData.get;
val thyinfo_of_thy = ! o thyinfo_ref_of_thy;

fun add_rnet_to_thy rnet thry = 
    let 
      val dref = thyinfo_ref_of_thy thry
      val d1 = ! dref
      val d2 = add_rnet (rnet, d1)
    in (dref := d2; thry) end;

fun add_eord_to_thy eord thry = 
    let 
      val dref = thyinfo_ref_of_thy thry
      val d1 = ! dref
      val d2 = add_eord (eord, d1)
    in (dref := d2; thry) end;

fun lookup_rnet_from_thy (s,thry) = 
    lookup_rnet (s,thyinfo_of_thy thry);

fun lookup_eord_from_thy (s,thry) = 
    lookup_eord (s,thyinfo_of_thy thry);

(* data associated with the proof context *)
structure LocalDataArgs =
struct
  val name = "IsaPlanner/Isar/eval";
  type T = T;
  fun init thy = !(GlobalData.get thy);
  fun print ctxt rn = Pretty.writeln (pretty rn);
end;
structure LocalData = ProofDataFun(LocalDataArgs);
val print_from_ctxt = LocalData.print;
val thyinfo_of_ctxt = LocalData.get;

fun lookup_rnet_from_ctxt (s,ctxt) = 
    lookup_rnet (s,thyinfo_of_ctxt ctxt);

fun lookup_eord_from_ctxt (s,ctxt) = 
    lookup_eord (s,thyinfo_of_ctxt ctxt);


(* getting nets and orders *)
fun rnets_of_thy thry = map snd (Symtab.dest (rnets_of (thyinfo_of_thy thry)));
fun rnets_of_ctxt ctxt = map snd (Symtab.dest (rnets_of (thyinfo_of_ctxt ctxt)));

fun eords_of_thy thry = map snd (Symtab.dest (onet_of (thyinfo_of_thy thry)));
fun eords_of_ctxt ctxt = map snd (Symtab.dest (onet_of (thyinfo_of_ctxt ctxt)));

(* adding and deleting rules *) 
fun add_rule_to_thy s (a as (thry, th)) = 
    let 
      val d_ref = thyinfo_ref_of_thy thry
      val d = !d_ref
      val rnet = lookup_rnet (s, d)
    in (d_ref := update_rnet (ThmEvalNet.insert (th,rnet), d);
        a)
    end;

fun del_rule_from_thy s (a as (thry, th)) = 
    let 
      val d_ref = thyinfo_ref_of_thy thry
      val d = !d_ref
      val rnet = lookup_rnet (s, d)
    in (d_ref := update_rnet (ThmEvalNet.delete (th,rnet), d);
        a)
    end;

fun add_rule_to_ctxt s (ctxt, th) =
    let 
      val d = thyinfo_of_ctxt ctxt
      val rnet = lookup_rnet (s, d)
    in 
      (LocalData.put (update_rnet (ThmEvalNet.insert (th,rnet), d)) 
                     ctxt, th)
    end;

fun del_rule_from_ctxt s (ctxt,th) =
    let 
      val d = thyinfo_of_ctxt ctxt
      val rnet = lookup_rnet (s, d)
    in 
      (LocalData.put (update_rnet (ThmEvalNet.delete (th,rnet), d)) 
                     ctxt, th)
    end;


(* Needed in order for method/attribute operations on proof context *)
fun mapto_thyinfo_in_ctxt f ctxt =
    LocalData.put (f (LocalData.get ctxt)) ctxt;

(* Needed in order for method/attribute operations on proof context *)
fun mapto_rnet_in_ctxt f s ctxt =
    mapto_thyinfo_in_ctxt (fn d => update_rnet (f (lookup_rnet (s, d)),d)) ctxt;

(* printing *)
val print_rnets_of_thy = print_rnets o rnets_of o thyinfo_of_thy;
val print_rnets_of_ctxt = print_rnets o rnets_of o thyinfo_of_ctxt;
val print_eords_of_thy = print_onet o onet_of o thyinfo_of_thy;
val print_eords_of_ctxt = print_onet o onet_of o thyinfo_of_ctxt;

(* setup for Isar *)
val setup = [GlobalData.init, 
             LocalData.init]


(** outer syntax **)
val print_P =
  OuterSyntax.improper_command "print_evals" "print the evaluation mechanisms"
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o 
                   (Toplevel.keep
      (Toplevel.node_case print_from_thy
                          (print_from_ctxt o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [print_P];


end;
