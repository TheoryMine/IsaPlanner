(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/subspace_rtechn.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Updated:    30 Jun 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    For working with reasoning technique subspaces - the interaction
    between reasoning and search.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Generic notion of subspaces *)
signature SUBSPACE = 
sig
  type T

  val init : unit -> T
  val pretty : T -> Pretty.T
  val open_nds_of : T -> int
  val giveup_chk : T -> bool
  val continue_chk : T -> bool
  val explored_a_node : T -> T
  val new_node : T -> T
  val giveup : T -> T
end;

structure SubSpace : SUBSPACE = 
struct

type T = { nds : int, (* number of open nodes in space *)
           giveup : bool (* if we should give up without side effects *)
         };

fun init () = {nds = 1, giveup = false};

fun pretty {nds,giveup} = 
    Pretty.chunks 
      [Pretty.str ("SubSpace Info:"),
       Pretty.str ("  open nodes: " ^ (string_of_int nds)),
       Pretty.str ("  giveup: " ^ (if giveup then "true" else "false"))];

fun open_nds_of (rep : T) = #nds rep;
fun giveup_chk (rep : T) = #giveup rep;

fun continue_chk {nds,giveup = true} = false
  | continue_chk {nds,giveup = false} = not (nds < 1);

fun explored_a_node {nds,giveup} = {nds = nds - 1,giveup = giveup};
fun new_node {nds,giveup} = {nds = nds + 1,giveup = giveup};

fun giveup {nds,giveup} = {nds = nds,giveup = true};

end;



(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
signature SUBSPACE_RTECHN =
sig

  val subspace' : 
      {sref : SubSpace.T Unsynchronized.ref,
       name : string, 
       techn : RTechn.T, (* technqiue to be subspaced *)
       endspacef : (unit -> unit) (* side effect function *)
      } -> RTechn.T


  val subspace : 
      {sref : SubSpace.T Unsynchronized.ref,
       techn : RTechn.T, (* technqiue to be subspaced *)
       rstf : RTechn.T (* last empty state func *)
      } -> RTechn.T

end;




(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
structure SubSpaceRTechn : SUBSPACE_RTECHN =
struct

(* If a subspace becomes empty, then upon reaching the last state
   apply the lastrstf function to it.

   NOTE: a state having no continuation counts as a success state!
   thus if a single rst in the subspace has a none-continuation, then
   lastf will never be applied.
 *)
fun subspace 
      {sref : SubSpace.T Unsynchronized.ref,
       techn : RState.rtechn, (* technqiue to be subspaced *)
       rstf : RState.T -> RState.T Seq.seq (* side effect function *)
      } rst = 
    let 
      fun set_cf rst = 
          case (RState.get_rtechn rst) of 
            NONE => rst
          | SOME r =>
            rst |> ((RState.set_rtechn o SOME o subspace) 
                      {sref = sref,
                       techn = r, (* technqiue to be subspaced *)
                       rstf = rstf (* side effect technique *)
                   })

      fun r_unfold rstseq () = 
          if (SubSpace.continue_chk (!sref)) then 
            case Seq.pull rstseq of 
              NONE => (sref := SubSpace.explored_a_node (!sref); 
                       if (SubSpace.continue_chk (!sref)) then 
                         NONE
                       else (* if we closed the last closed node... *)
                         Seq.pull (rstf rst)
                      )
                      (*    SOME( HProofCInfo.then_rst (1, (rstf rst)), 
                               rstf rst,
                               Seq.empty ))*)
            | SOME (h, t) => 
              SOME ((sref := SubSpace.new_node (!sref); 
                     set_cf h),
                    Seq.make (r_unfold t))
          else
            NONE

      (* val ignore = (writeln "SUBSPACE_LASTF_TECHN:";
                    Pretty.writeln (SubSpace.pretty (!sref))) *)
    in
      Seq.make (r_unfold (techn rst))
    end;


(* If subspace becomes empty then perform function f 
   This is used to note when, for example, a conjecture can't be proved,
   and add it to the database of unprovable conjectures. 
 
   Note: can generalise this to an aribtrary search sub-space
   characteristic as the reasoning technique is the only way to unfold
   a reasoning state, and defines the search space. So we can talk
   about the space in terms of a shared referenced varaible (= global
   knowledge to subspace), dispite the fact that a search mechanism
   can search the space in any way it chooses. 

   "insref" is a pair of a integer reference and a bool. The integer
   reference is the number of nodes left in the search space. The bool
   is true when we have proved the lemma, and simply says that we
   should abandon the search. (it's also set to true when we reach the
   end of the search space.)

   "endspacef" is the side effect function, ie the side effect to have when the
   search space is exhausted.

   "r" is the reasoning technique that defines the subspace, and is
   what SUBSPACE_TECHN uses to become a technique in its own right.
*)
fun subspace' {sref : SubSpace.T Unsynchronized.ref,
                    name : string,
                    techn : RTechn.T, (* technqiue to be subspaced *)
                    endspacef : (unit -> unit) (* side effect function *)
                   } rst = 
    let 
      fun side_effect_techn rst = 
          ((* Pretty.writeln (SubSpace.pretty (!sref)); *)
           endspacef ();
           Seq.empty)
    in
      subspace {sref = sref,
                techn = techn,
                rstf = side_effect_techn
               } rst
    end;

end; (* struct *)  


(*            rst |> (RState.set_rtechn (SOME RTechn.FAIL_TECHN))
               |> (DescripCInfo.I.put_in_rst 
                     ("no more nodes in subspace \"" ^ name ^ "\", applying side effect")) *)