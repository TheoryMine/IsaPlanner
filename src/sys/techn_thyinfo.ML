(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/techn_thyinfo.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    13 Sep 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Theory information for holding IsaPlanner reasoning techniques

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature TECHN_THY_INFO = 
sig

type technsyntax = ProofContext.context * Args.T list 
                    -> DTechn.T * (ProofContext.context * Args.T list)

datatype T = rtechn of 
         { name : string,
           syntax : technsyntax }

val technsyntax_of : T -> technsyntax
val techn_ctxt_syntax : Method.src -> Proof.context -> RState.rtechn
val opt_dtechn_ctxt_syntax : Method.src -> Proof.context -> DTechn.T option
val name_of : T -> string

(* adding rulenets and orders *)
val add_to_thy : T -> theory -> theory
val mk : string * technsyntax -> T

(* getting nets and orders *)
val of_thy : theory -> T Symtab.table
val of_ctxt : Proof.context -> T Symtab.table

val lookup_from_thy : (string * Theory.theory) -> T
val lookup_from_ctxt : (string * Proof.context) -> T



(* printing *)
val print_from_thy : theory -> unit
val print_from_ctxt : Proof.context -> unit

val setup : (theory -> theory) list

end;


structure TechnThyInfo : TECHN_THY_INFO = 
struct

exception techn_thyinfo_exp of string

type technsyntax = ProofContext.context * Args.T list 
                    -> DTechn.T * (ProofContext.context * Args.T list)

datatype T = rtechn of 
         { name : string,
           syntax : technsyntax };

fun name_of (rtechn r) = #name r;

fun technsyntax_of (rtechn r) = #syntax r;

fun mk (name, syntax) = rtechn {name = name, syntax = syntax};
val empty_ttab = Symtab.empty : T Symtab.table;

fun merge_ttab (n1, n2) = 
    (Symtab.merge (fn (x,y) => name_of x = name_of y) (n1, n2))
     handle Symtab.DUPS _ => 
            raise techn_thyinfo_exp "merge: techniques tables conflict.";

fun add (r as rtechn {name, syntax}, ttab) = 
    (Symtab.update_new (name, r) ttab)
    handle Symtab.DUPS _ => 
           raise techn_thyinfo_exp 
                   "add: technique with that name already exists.";

fun lookup (s,ttab) = 
    (case Symtab.lookup ttab s of 
       NONE => raise techn_thyinfo_exp "lookup: no such techniques."
     | SOME r => r);

(* printing *)
fun pretty ttab = 
    Pretty.chunks (map (Pretty.str o name_of o snd) (Symtab.dest ttab));
val print = Pretty.writeln o pretty;

type ttab = T Symtab.table ref;

(* data associated with a theory *)
structure GlobalDataArgs : THEORY_DATA_ARGS =
struct
  val name = "IsaPlanner/Isar/techns";
  type T = ttab; (* ref in order to update theories in Isar theory mode *)
  val empty = ref empty_ttab;
  fun copy (ref d) = (ref d) : ttab;
  val prep_ext = copy; (* what is this for? - copied from simp *)
  fun merge pp (ref d1, ref d2) = 
      ref (merge_ttab (d1, d2));
  val extend = I;
  fun print sign (ref d) = Pretty.writeln (pretty d);
end;
structure GlobalData = TheoryDataFun(GlobalDataArgs);

val print_from_thy = GlobalData.print;
val ref_of_thy = GlobalData.get;
val of_thy = ! o ref_of_thy;

fun add_to_thy r thry = 
    let 
      val dref = ref_of_thy thry
      val d1 = ! dref
      val d2 = add (r, d1)
    in (dref := d2; thry) end;

fun lookup_from_thy (s,thry) = 
    lookup (s,of_thy thry);

(* data associated with the proof context *)
structure LocalDataArgs =
struct
  val name = "IsaPlanner/Isar/techns";
  type T = T Symtab.table;
  fun init thy = !(GlobalData.get thy);
  fun print ctxt d = Pretty.writeln (pretty d);
end;
structure LocalData = ProofDataFun(LocalDataArgs);
val print_from_ctxt = LocalData.print;
val of_ctxt = LocalData.get;

fun lookup_from_ctxt (s,ctxt) = 
    lookup (s,of_ctxt ctxt);

(* printing *)
val print_thy = print o of_thy;
val print_ctxt = print o of_ctxt;

(* setup for Isar *)
val setup = [GlobalData.init, LocalData.init];


(** outer syntax **)
val print_P =
  OuterSyntax.improper_command "print_rtechns" "print the IsaPlanner techniques"
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o 
                   (Toplevel.keep
      (Toplevel.node_case print_from_thy
                          (print_from_ctxt o Proof.context_of)))));


val suggest_P =
  OuterSyntax.improper_command "suggest_pp" "list of suggested applicable techniques"
    OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o 
                   (Toplevel.keep
      (Toplevel.node_case print_from_thy
                          (print_from_ctxt o Proof.context_of)))));

val _ = OuterSyntax.add_parsers [suggest_P, print_P];


local 
  fun extra_syntax lookupf args = 
      let val (s,args2) = Scan.lift Args.name args
        val tech_syntaxf = lookupf s
      in tech_syntaxf args2 end;
  fun techn_lookupf ctxt s = 
      technsyntax_of 
        (lookup_from_ctxt (s,ctxt))
in
(* Syntax for parsing dtechniques from within a ctxt *)
fun techn_ctxt_syntax src ctxt = 
    let 
      val (ctxt',dtechn) = 
          Method.syntax (extra_syntax (techn_lookupf ctxt)) src ctxt
    in DTechn.techn_of dtechn end;
fun opt_dtechn_ctxt_syntax src ctxt = 
    let 
      val (ctxt',dtechnopt) = 
          Method.syntax (Scan.option (extra_syntax (techn_lookupf ctxt))) 
                        src ctxt
    in dtechnopt end;

end; (* local *)

end;
