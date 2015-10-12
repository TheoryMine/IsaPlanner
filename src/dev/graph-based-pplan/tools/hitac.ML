(* IN PROGRESS -- abstract hierarchical declarative tactics. *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      gtacs.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Updated:    March 2007 - Lucas Dixon
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  

    tacticals for working with tactics that derive new results and
    produce named goals. 

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature HiTac = 
sig

type gname; (* name of goal *)
type rname; (* name of result/assumption *)
type prf; (* proof state *)


type state = ((rname list * gname list) * prf);

type fwd_gtac = rname -> prf -> state Seq.seq
type bck_gtac = gname -> prf -> state Seq.seq

type gtac = state -> state Seq.seq

val mk_map_fwd : fwd_gtac -> gtac
val mk_map_bck : bck_gtac -> gtac
val of_bckf : (gname -> prf -> (gname list * prf) Seq.seq) -> gtac;
val of_fwd1f : (rname -> prf -> (rname * prf) Seq.seq) -> gtac;

val fail : gtac;
val id : gtac;

val or : gtac list -> gtac
val thenl : gtac list -> gtac
val try : gtac -> gtac
val repeat : gtac -> gtac
val prove_or_fail : gtac -> gtac

val then_f : gtac -> (state -> state) -> gtac
val f_then : (state -> state) -> gtac -> gtac
val then_select : (state -> bool) -> gtac -> gtac

(* internal *)
(* also apply the list of functions gathering the results *)
val also : (prf -> state Seq.seq) list -> prf -> state Seq.seq

(* add results to each thing in a sequence *)
val addseq_listpair : 
    (rname list * gname list) 
    -> state Seq.seq 
    -> state Seq.seq 
val addseq_list : 
    (gname list) 
    -> (gname list * prf) Seq.seq 
    -> (gname list * prf) Seq.seq 

end;


(* result names; assumptions or goals *)
structure Rslt : STR_SNAME = SStrName;
type state = state;

(* tactic names *)
structure TName : STR_SNAME = SStrName;


functor AtomicTac
= struct

type state = RState.T;

datatype T = 
     Tac 
       {
        ins : Rslt.NSet.T, (* applicable to these results *)
        outs : Rslt.NSet.T, (* results in these results *)
        pretty : Pretty.T, (* brief info: pretty without state in mind *)
        pre_pretty : state -> Pretty.T, (* medium info: pretty on state before application *)
        post_pretty : state -> Pretty.T, (* long info: pretty on state after application *)
        f : state -> state Seq.seq, (* underlying function *)
       };

fun pretty (Tac rep) =
    Pretty.block 
      [#pretty rep, Pretty.str ": ",
       Pretty.block [Rslt.NSet.pretty (#ins rep), 
                     Pretty.str " => ", 
                     Rslt.NSet.pretty (#outs rep)]];

fun get_ins (Tac rep) = #ins rep;
fun get_outs (Tac rep) = #outs rep;
fun get_pretty (Tac rep) = #pretty rep;
fun pre_pretty (Tac rep) = #pre_pretty rep;
fun post_pretty (Tac rep) = #post_poretty rep;
fun apply (Tac rep) = #f rep;

val default_rname = Rslt.default_name;

(* make from pretty, ins, f, outs *)
fun mk' p ins f outs = 
    let val p = Pretty.str s
    in Tac {ins = ins,
            outs = outs,
            pretty = p,
            pre_pretty = p,
            post_pretty = p,
            f = f }
    end;

(* basic make from a string(name) and a function *)
fun mk s f = 
    let val p = Pretty.str s
        val rs = Rslt.NSet.single default_rslt_name
    in mk' default_rname rs f rs end;


fun get_outs (Tac rep) = #outs rep;
fun get_pretty (Tac rep) = #pretty rep;
fun get_pre_pretty (Tac rep) = #pre_pretty rep;
fun get_post_pretty (Tac rep) = #post_poretty rep;
fun get_f (Tac rep) = #f rep;




fun thenl [] st = Seq.single st
  | thenl (lfs as hf::tfs) st = (hf st) |> Seq.maps (thenl tfs);

(* fail *)
fun fail st = Seq.empty
fun id st = Seq.single st;

(* or = seq of f1's, f2's *)
fun or fs st = 
    Basics.fold (fn f => (fn seq => Seq.append (f st) seq)) fs Seq.empty;

(* try applying f, if we fail, we give back a the state without change  *)
fun try f st = 
    (case Seq.pull (f st) of 
       NONE => Seq.single st
     | SOME (h,t) => Seq.cons h t);

(* apply state function before or after *)
fun then_f f afterf = Seq.map afterf o f;
fun f_then beforef f = f o beforef;

(* apply f then filter results (select the ones you want to keep) *)
fun then_select selectf f = Seq.filter selectf o f;

(* leave no goals or fail *)
val prove_or_fail : gtac -> gtac
 = then_select (fn ((_,[]),_) => true | _ => false);

(* repeated application *)
fun repeat f st = (f st) |> Seq.maps (repeat f);

end;


structure GTacs = 
GTacsFun(
  type gname = Prf.gname 
  type rname = Prf.gname 
  type prf = Prf.T);
