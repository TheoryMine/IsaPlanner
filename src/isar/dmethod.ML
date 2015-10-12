(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/dmethod.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Generic extensible declarative Isar Methods

*)

(* declarative, but extensible methods *)
signature DMETHOD =
sig

type T

(* exception bad_method_kind_exp of string *)

val kind_of : T -> SafeObject.kind
val string_of : T -> Proof.context -> string
val pretty_of : T -> Proof.context -> Pretty.T
val mtext_of : T -> Proof.context -> Method.text
val refine : T -> Proof.state -> Proof.state Seq.seq

(* used in the functor for making new kinds of declarartive methods *)
val mk_getdataf :
    SafeObject.kind -> (SafeObject.T -> 'a) -> T -> 'a option

val mk_dmeth :
       ('a -> Proof.context -> Pretty.T) *  (* prettyf *)
       ('a -> Proof.context -> Method.text) * (* method text *)
       ('a -> SafeObject.kind * SafeObject.T) -> (* encoding function  *)
       'a -> (* data *)
       T (* the new declarative method object *)

end;


structure DMethod :> DMETHOD = 
struct 

(* exception bad_method_kind_exp of string *)

(* Note: the object data has already been given to the text and pretty
functions. Any modification of the data must be done through a
mechanism that updates the pretty and text functions appropriatly *)
type T = { kind : SafeObject.kind,
           data : SafeObject.T,
           prettyf : Proof.context -> Pretty.T,
           textf : Proof.context -> Method.text };

(* get the kind of declarative method expressed by a thing of type DMethod.T *)
fun kind_of {kind, ...} = kind;

(* create the pretty printing object for this method, given the context *)
fun pretty_of {data, prettyf, ...} ctxt = 
    prettyf ctxt;

fun string_of d ctxt = Pretty.string_of (pretty_of d ctxt);

(* create the method text for this method, given the context *)
fun mtext_of {data, textf, ...} ctxt = 
    textf ctxt;

(* use method to refine an proof state *)
fun refine dm pst = Proof.refine (mtext_of dm (Proof.context_of pst)) pst;


(* create a function to get the data from a method *)
fun mk_getdataf k decf {kind, data, ... } = 
    if SafeObject.eq_kind (k, kind) then SOME (decf data) 
    else NONE;

(* function to make a generic method, we place the data in the pretty
and text function directly. This is not a problem as anything that
edits the data must update the prettyf and textf also. *)
fun mk_dmeth (prettyf, textf, encf) d = 
    let 
      val (kind, generic_d) = encf d
    in
      {kind = kind, 
       data = generic_d, 
       prettyf = prettyf d, 
      textf = textf d} : T
    end;

end;


(* the kind of a declarative method must have these things... *)
signature DMETHOD_KIND =
sig

type T

val textf : T -> Proof.context -> Method.text
val prettyf : T -> Proof.context -> Pretty.T

val name : string

end;


(* to get an instance of a declarative method kind *)
signature DMETHOD_INST =
sig

type T

val kind : SafeObject.kind

val dmeth_of : T -> DMethod.T
val data_of : DMethod.T -> T option

end;


functor DMethodInstFUN (structure K : DMETHOD_KIND)
        : DMETHOD_INST = 
struct

val kind = SafeObject.kind K.name;

type T = K.T;

local 
  exception Data of T;
  fun decf (Data x) = x
  fun encf d = (kind, Data d)
in

(* implicit extra arg: DMethod.T *)
val data_of = DMethod.mk_getdataf kind decf;

(* implicit extra arg: T *)
val dmeth_of = DMethod.mk_dmeth (K.prettyf, K.textf, encf);

end; (* local *)

end; (* DMethodInstFUN *)



