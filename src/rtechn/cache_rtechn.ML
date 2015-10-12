(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/cache_rtechn.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Created:    27 Oct 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    FIXME: UNFINISHED

    Caching subgoals; only consider one subgoal of each term; 

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

signature CACHE_RTECHN =
sig
  val CACHE : RState.rtechn -> RState.rtechn (* excludes current goal *)
  val CACHE' : RState.rtechn -> RState.rtechn (* include current goal *)
end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
structure CacheRTechn 
: CACHE_RTECHN
= struct

(*  *)
structure Nm = SStrName;
datatype T = Cache of Nm.NSet.T Termtab.table ref;
fun update f (c as Cache r) = (r := (f (!r)); c);
fun lookup (Cache tabref) t = 
fun init tab = Cache (ref tab);

(* updates cache and rst, given a goal *)
fun cache_foldf c rst = 
    let 
      val gs = (RState.get_goalnames rst)
      val ts = map (fn g => (g, RstPP.goal_concl rst g)) gs
    in
      case ts 
       of [] => (rst,c)
        | (t1::ts') => 
          case lookup t1 
           of NONE => (rst, update (Termtab.update (t,g)) c)
            | SOME  => 
          fold 
            
            ts
            

      case  of
        NONE => 
      | SOME g2 => (* already seen a goal like this, so fail *)
        (RState.set_rtechn (SOME RTechnEnv.fail) rst, c)
    end;

(* implicit rtechn , results in rtechn *)
val CACHE = RTechn.fold cache_foldf (init Termtab.empty);

fun CACHE' r g rst = 
    let 
      val (_,c2) = cache_foldf (init Termtab.empty) g rst
    in RTechn.fold cache_foldf c2 r rst end;

end; (* struct *)
