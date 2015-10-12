(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      m.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Updated:    March 2007 - Lucas Dixon
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  
    general purpose tacticals 
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

structure M = 
struct

fun add_goal_to_seq gs = Seq.map (fn (gs2,p) => (gs @ gs2,p));

fun andprove [] p = Seq.single ([],p)
  | andprove (hf::tfs) p = 
    (hf p) :-> (fn (gs,p2) => 
                  add_goal_to_seq gs (andprove tfs p2));


(* depth and breadth first search of then applications - the
difference is the order in which they treat intermediate goals, depth
first treating new goals first and breadth first treating all the old
goals first. *)

fun thendf [] (gs, p) = Seq.single (gs,p) (* end of tactic apps *)
  | thendf (hf::tfs) ([], p) = Seq.single ([],p) (* solved *)
  | thendf (lfs as hf::tfs) ((g::gs), p) = 
    (hf ([g],p)) 
    :-> (fn (gs2p2 as (gs2,p2)) => 
            (thendf tfs gs2p2)
            :-> (fn (gs3,p3) => 
                    add_goal_to_seq gs3 (thendf lfs (gs, p3))));

fun thenbf [] (gs, p) = Seq.single (gs,p) (* end of tactic apps *)
  | thenbf (hf::tfs) ([], p) = Seq.single ([],p) (* solved *)
  | thenbf (lfs as hf::tfs) ((g::gs), p) = 
    (hf ([g],p))
    :-> (fn (gs2,p2) => 
            (add_goal_to_seq gs2 (thenbf lfs (gs, p2)))
            :-> (thenbf tfs));


fun or f1 f2 gsp = 
    Seq.append (f1 gsp) (f2 gsp);

(* lifting ordinary proof tactics taking a single to goal to those
taking a list with the new proof state: interpretation is we apply to
all goals. *)
fun mk f (gs,ffp) = 
    andprove (map f gs) ffp;

(* try applying f to nid, if we fail, we give back ([nid],p)
indicating that the proof attempt failed. *)
fun try f g1sp = 
    (case Seq.pull (f g1sp) of 
       NONE => Seq.single g1sp
     | SOME (h,t) => Seq.cons h t);

end;
