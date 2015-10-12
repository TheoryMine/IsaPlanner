(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./sys/dtechn.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Generic extensible declarative IsaPlanner techniques for Isabelle theories

*)

(* declarative, but extensible methods *)
signature DTECHN =
sig

(* 'a is a reasoning state *)
type 'r T

(* exception bad_method_kind_exp of string *)

val kind_of : 'r T -> SafeObject.kind

val string_of : 'r T -> Proof.context -> string
val pretty_of : 'r T -> Proof.context -> Pretty.T
val techn_of : 'r T -> 'r -> 'r Seq.seq

(* used in the functor for making new kinds of declarartive methods *)
val mk_getdataf :
    SafeObject.kind -> (SafeObject.T -> 'a) -> 'r T -> 'a option

val mk :
       ('a -> Proof.context -> Pretty.T) *  (* prettyf *)
       ('a -> 'r -> 'r Seq.seq) * (* techn text *)
       ('a -> SafeObject.kind * SafeObject.T) -> (* encoding function  *)
       'a -> (* data *)
       'r T (* the new declarative object *)

val simple : string * ('r -> 'r Seq.seq) -> 'r T

end;




structure DTechn :> DTECHN = 
struct 


(* Note: the object data has already been given to the text and pretty
functions. Any modification of the data must be done through a
mechanism that updates the pretty and text functions appropriatly *)
type T = { kind : SafeObject.kind,
           data : SafeObject.T,
           prettyf : Proof.context -> Pretty.T,
           techn : RState.rtechn };

(* get the kind of declarative technique expressed by a thing of type T *)
fun kind_of {kind, ...} = kind;

(* create the pretty printing object, given the context *)
fun pretty_of {data, prettyf, ...} ctxt = 
    prettyf ctxt;

fun string_of d ctxt = Pretty.string_of (pretty_of d ctxt);

(* the technique *)
fun techn_of {techn, ...} = techn;


(* create a function to get the data from a technique *)
fun mk_getdataf k decf {kind, data, ... } = 
    if SafeObject.eq_kind (k, kind) then SOME (decf data) 
    else NONE;

(* function to make a generic dtechnique, we place the data in the pretty
and techn function directly. This is not a problem as anything that
edits the data must update the prettyf and techn also. *)
fun mk (prettyf, techn, encf) d = 
    let 
      val (kind, generic_d) = encf d
    in
      {kind = kind, 
       data = generic_d, 
       prettyf = prettyf d, 
       techn = techn d} : T
    end;



local 
  exception Data of unit;
  fun decf (Data x) = x
in
  fun simple (s,r) = 
      mk (K o K (Pretty.str s), K r, 
          (fn _ => (SafeObject.kind s, Data ()))) ();
end; (* local *)


end;


(* the kind of a declarative techn must have these things... *)
signature DTECHN_KIND =
sig

type T (* particular data for this kind of dtechn *)

val techn : T -> RState.rtechn
val syntax : ProofContext.context * Args.T list 
             -> T * (ProofContext.context * Args.T list)
val prettyf : T -> Proof.context -> Pretty.T
val name : string

end;


(* an instance of a declarative techn kind *)
signature DTECHN_INST =
sig

type T (* particular data for this kind of dtechn *)

val kind : SafeObject.kind

val dtechn : T -> DTechn.T
val syntax : ProofContext.context * Args.T list 
             -> DTechn.T * (ProofContext.context * Args.T list)
val data : DTechn.T -> T option

end;


functor DTechnInstFUN (structure K : DTECHN_KIND)
        : DTECHN_INST = 
struct

val kind = SafeObject.kind K.name;

type T = K.T;

local 
  exception Data of T;
  fun decf (Data x) = x
  fun encf d = (kind, Data d)
in

(* implicit extra arg: DMethod.T *)
val data = DTechn.mk_getdataf kind decf;

(* implicit extra arg: T *)
val dtechn = DTechn.mk (K.prettyf, K.techn, encf);

(* syntax tools for creating an instance of this dtechn *)
val syntax = Library.apfst dtechn o K.syntax;

end; (* local *)

end; (* DMethodInstFUN *)



