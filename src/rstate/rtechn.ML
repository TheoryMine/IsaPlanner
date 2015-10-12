(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/rtechn.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Reasoning techniques basic functions
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

signature RTECHN = 
sig
  type T = RState.rtechn; (* = RTechn of string * (RState.T -> RState.T Seq.seq) *)

  val stopify : T -> T (* sets continuations to none *)
  val dummy : T (* does nothing successfully for one step *)
  val fail : T (* returns empty seq *)

  val ofstep : (RState.T -> RState.T) -> T (* technique of single function *)
  val then_f : T -> (RState.T -> RState.T) -> T (* apply f to final states *)
  val then_fs : T -> (RState.T -> RState.T Seq.seq) -> T (* apply f to final states *)
  val then_r : T -> T -> T (* traditional then *)
  val map : (RState.T -> RState.T) -> T -> T  
  val fold : ('a -> RState.T -> (RState.T * 'a)) -> 'a -> T -> T  

  val failedbranch_critic : T -> T -> T

  (* Basic options for if we succeed or fail to modify the proof plan *)
  val ppmod : (PPlan.T -> PPlan.T option) (* choice on this op *)
              -> T (* succes techn *)
              -> RState.T Seq.seq (* fail seq *)
              -> T (* resulting technique *)

  (* Basic options for if we succeed or fail to modify the proof plan *)
  val ppmod' : (PPlan.T -> PPlan.T option) (* choice on this op *)
              -> (RState.T -> RState.T) (* succes rst func *)
              -> RState.T (* fail state *)
              -> RState.T -> RState.T  (* resulting rstf *)

  (* stacked search strategy searching *)
  val search : RState.T MSearch.T -> T -> T

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
structure RTechn 
: RTECHN
= struct
  type T = RState.rtechn;

(* set there to being no continuation *)
fun stopify r = Seq.map (RState.set_rtechn NONE) o r;
val dummy = Seq.single o RState.set_rtechn NONE;
val fail = K Seq.empty : T;


(* set there to being no continuation *)
(* 
fun stopify r = RState.RTechn ("stop", Seq.map (RState.set_rtechn NONE) o r);
val dummy = RState.RTechn ("id", Seq.single o RState.set_rtechn NONE);
val fail = (RState.RTechn ("fail", K Seq.empty) : T;
*)

(* create rtechn from a funtion on reasoning states *)
fun ofstep f = Seq.single o RState.set_rtechn NONE o f;

(* Apply f to the last state of the reasoning using r. r is unfolded
 until it no continuation exists, at which point f is applies to the
 end state. 
*)
fun then_f r f st = 
    let 
      fun continue_from_st_with f st = 
          case (RState.get_rtechn st)
           of NONE => (f st)
            | SOME r1 => 
              RState.set_rtechn (SOME (then_f r1 f)) st
    in
      Seq.map (continue_from_st_with f) (r st)
    end;

fun then_fs r fseq st = 
    let 
      fun continue_from_st_with fseq st = 
          case (RState.get_rtechn st)
           of NONE => (fseq st)
            | SOME r1 => 
              Seq.single (RState.set_rtechn (SOME (then_fs r1 fseq)) st)
    in
      Seq.maps (continue_from_st_with fseq) (r st)
    end;

fun then_r (r1 : T) (r2 : T) = then_f r1 (RState.set_rtechn (SOME r2));

(* recursivly map a function to intermediate states *)
fun map (f : RState.T -> RState.T) 
        (r : RState.rtechn) 
        (st : RState.T) = 
    let
      fun set_cf f st = 
          case (RState.get_rtechn st) of 
            NONE => st
          | SOME r2 =>
            (RState.set_rtechn (SOME (map f r2)) st)
    in
      (Seq.map ((set_cf f) o f) (r st))
    end;

(* recursivly fold over intermediate states *)
fun fold (f : 'a -> RState.T -> (RState.T * 'a))  
         initdata r rst = 
    let
      fun set_cf f (st,a) = 
          case (RState.get_rtechn st) of 
            NONE => st
          | SOME r2 =>
            RState.set_rtechn (SOME (fold f a r2)) st
    in Seq.map ((set_cf f) o (f initdata)) (r rst) end;


(* apply critic "rc" : rtechn, when r (or a continuation of r) has
no further choices, note that we don't apply this to or-choices. only
when r results in no more choices, ie when we are at a leaf of the
search space only. *)
fun failedbranch_critic r c rst = 
    let 
      fun set_critic c st = 
          case RState.get_rtechn st of 
            NONE => st
          | SOME r => RState.set_rtechn (SOME (failedbranch_critic r c)) st
    in
      case Seq.pull (r rst) of
        NONE => c rst
      | SOME (rst2, rst2s) =>
        Seq.cons (set_critic c rst2) 
                  (Seq.map (set_critic c) rst2s)
    end;

(* Basic options for if we succeed or fail to modify the proof plan *)
fun ppmod ppf techn failresults rst = 
    case ppf (RState.get_pplan rst) of 
      SOME pp' => techn (RState.set_pplan pp' rst)
    | NONE => failresults;

(* Basic options for if we succeed or fail to modify the proof plan *)
fun ppmod' ppf successf failr rst = 
    case ppf (RState.get_pplan rst) of 
      SOME pp' => (successf (RState.set_pplan pp' rst))
    | NONE => failr;

(* use stacked search strategy *)
fun search searchstrategy r = 
      then_f
        (r o (RState.add_searchop (MSearch.addstrategy searchstrategy)))
        (RState.add_searchop MSearch.endstrategy);

end;
