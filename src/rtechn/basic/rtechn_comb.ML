(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Title:      rtechn/basic/rtechn_comb.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    created:    30 Jun 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  DESCRIPTION:

    Basic technique combinators with hierarchical traces

    Note: Although I don't think we use it, we can get recursion
    simply by not changing the continuation - very cunning.

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature RTECHN_COMB =
sig
  val allfail_critic : RTechn.T (* critic *)
                       -> RTechn.T (* techn *)
                       -> RTechn.T
  val try_then : RTechn.T (* try this *)
                       -> RTechn.T (* do this if all branches fail = critic *)
                       -> RTechn.T
  val branchfail_critic : RTechn.T -> RTechn.T -> RTechn.T
  val continue_with : RTechn.T -> RState.T -> RState.T
  val givename : RstName.T -> RTechn.T -> RTechn.T
(*  val init : RState.T -> RState.T *)
  val dummy : RstName.T -> RTechn.T
  val dummy_str : string -> RTechn.T
  val end_rst : RstName.T -> RState.T -> RState.T
  val fail : RTechn.T
  val ofstep : RstName.T -> (RState.T -> RState.T) -> RTechn.T
  val orr : RTechn.T * RTechn.T -> RTechn.T
  val orr_list : RTechn.T list -> RTechn.T
  val refine : RstName.T -> RTechn.T -> RTechn.T
  val refine' : RstName.T -> (RState.T -> RState.T)
                -> RTechn.T -> RTechn.T
  val repeat : RTechn.T -> RTechn.T
  val repeat_then : RTechn.T -> RTechn.T -> RTechn.T
  val repeatn : int -> RTechn.T -> RTechn.T
  val repeat_until : (RState.T -> bool) -> RTechn.T -> RTechn.T
  val repeat_while : (RState.T -> bool) -> RTechn.T -> RTechn.T
  val then_continue_with : RTechn.T -> RState.T -> RState.T
  val then_list : RTechn.T list -> RTechn.T
  val fthen : (RState.T -> RState.T) * RTechn.T -> RTechn.T
  val fsthen : (RState.T -> RState.T Seq.seq) * RTechn.T -> RTechn.T
  val thenf : RTechn.T * (RState.T -> RState.T) -> RTechn.T
  val thenfs : RTechn.T * (RState.T -> RState.T Seq.seq)
               -> (RState.T -> RState.T Seq.seq)
  val thenr : RTechn.T * RTechn.T -> RTechn.T
  val try1_orelse : RTechn.T * RTechn.T -> RTechn.T
  val try1_orelse_list : RTechn.T list -> RTechn.T
  val try1_then : RTechn.T * RTechn.T -> RTechn.T
  val rstif : (RState.T -> bool) -> RTechn.T -> RTechn.T -> RTechn.T
  val search : RState.T MSearch.T -> RTechn.T -> RTechn.T
  val solve_or_fail : RTechn.T -> RTechn.T
  val solve_or_nothing : RTechn.T -> RTechn.T
end;


structure RTechnComb
 : RTECHN_COMB
= struct

infixr 6 thenr;
infixr 7 thenf;
infixr 7 thenfs;
infixr 7 fthen;
infixr 7 fsthen;
infix 5 orr;
(* infixr 5 xorelse; *)
infixr 6 try1_then;
infixr 6 try1_orelse;

val fail = RTechn.fail;

(* basic apply function after technique *)
fun op thenf (r1, f) = RTechn.then_f r1 f;
fun op thenfs (r1, fseq) = RTechn.then_fs r1 fseq;

(* apply function to rst then do technique *)
fun op fthen (f, r) = r o f;
fun op fsthen (fseq, r) = Seq.maps r o fseq;

(* set continuation of a rst *)
val continue_with = RState.set_rtechn o SOME o HTraceCInfo.thenify;

(* then and or for techniques *)
fun op thenr (r1, r2) = r1 thenf (continue_with r2);
fun op orr (inr1, inr2) =
    let fun auxby (r1, r2) st = HTraceCInfo.orify (inr1, st) (inr2, st)
    in auxby (inr1, inr2)  end;

(* given a rst set continuation to do whatever it was going to, then
   start the given technique. *)
fun then_continue_with r rst =
    (case RState.get_rtechn rst of
       NONE => RState.set_rtechn (SOME (HTraceCInfo.thenify r)) rst
     | SOME c => RState.set_rtechn (SOME (c thenr r)) rst);

(* or and then of lists of techniques... *)
val orr_list = List.foldr (op orr) RTechn.fail;
fun then_list [] = RTechn.fail
  | then_list [r] = r
  | then_list (r1::rs) =
    r1 thenf (continue_with (then_list rs));

(* make a reasoning technique have the given name *)
(* implicit name and technique *)
val givename = DescripCInfo.set_techn;

(* a named technique that does nothing for one step *)
fun dummy n = givename n RTechn.dummy;
fun dummy_str s = dummy (RstName.str s);
fun end_rst n rst =
    rst |> DescripCInfo.set_rst n
        |> RState.set_rtechn NONE;

(* introduces a dummy step (does nothing) that refines the hierarchical trace *)
fun refine n r =
    HTraceCInfo.refinify ((dummy n) thenr r)

(* introduces a step that applies f and refines the hierarchical trace *)
fun refine' n f r =
    HTraceCInfo.refinify (((dummy n) thenf f) thenr r);

(* technique of a rst function *)
fun ofstep n = givename n o RTechn.ofstep;

(* make a technique suitable for initial proof planning *)
(*fun init rst =
    let
      val pp = RState.get_pplan rst
      val pst = PPlan.top_pst_of pp
      val ctxt = Proof.context_of pst
    in
      rst |> (ConjStackCInfo.add_term_rst ctxt (PPlan.top_goalterm_of pp))
          |> HTraceCInfo.init_rst
    end;
*)
(* try the first technique, if it gives back a state, then behave as
   if we are a normal thenr r2, else we behave simply as r2. *)
fun op try1_then (r, r2) rst =
    (case Seq.pull (r rst) of
       NONE => r2 rst
     | SOME (st, sts) =>
       Seq.map (then_continue_with r2) (Seq.cons st sts));

(* try first technqiue, if it does not imidiately fail continue as normal.
   If it does imidiately fail, then act as r2. *)
fun op try1_orelse (r, r2) rst =
    (case Seq.pull (r rst) of
       NONE => r2 rst
     | SOME (st, sts) => Seq.cons st sts);

(* try first technqiue, if it does not imidiately fail continue as normal.
   If it does imidiately fail, try the next thing in the list *)
fun try1_orelse_list [] rst = Seq.empty
  | try1_orelse_list (r::rs) rst =
    (case Seq.pull (r rst) of
       NONE => try1_orelse_list rs rst
     | SOME (st, sts) => Seq.cons st sts);

(* apply critic technique when every branch has failed, ie to
   last failed branch *)
(* implicit rst *)
fun allfail_critic critic r1 =
    SubSpaceRTechn.subspace
    {sref = Unsynchronized.ref (SubSpace.init()),
     techn = r1,
     rstf = HTraceCInfo.thenify critic};

fun try_then r1 r2 = allfail_critic r2 r1;

(* apply critic technique to every failed branch of the search space *)
fun branchfail_critic r c =
    RTechn.failedbranch_critic r (HTraceCInfo.thenify c);

(* repeat technique r, n times *)
fun repeatn n r rst =
    if n < 2 then r rst else (r thenr (repeatn (n-1) r)) rst;

(* repeat technique r, will continue forever or fail *)
fun repeat r rst = (r thenr (repeat r)) rst;

(* more useful form of above which will repeat until technique can't
   be applied anymore at which point it will apply technique 2 *)
fun repeat_then r r2 = branchfail_critic (repeat r) r2;

(* repeat until condition is true *)
fun repeat_untilf c r rst =
    if c rst then rst
    else continue_with (r thenf (repeat_untilf c r)) rst;
fun repeat_until c r = r thenf (repeat_untilf c r);

(* converse of above: repeat while condition is true *)
fun repeat_whilef c r rst =
    if c rst then continue_with (r thenf (repeat_whilef c r)) rst
    else rst
fun repeat_while c r = r thenf (repeat_whilef c r);

(* if branch for reasoning techniques *)
fun rstif c t f rst = if c rst then t rst else f rst;

val search = RTechn.search;

(* r must solve all goals of rst completely, ie. none of the
resulting reasoning states should have any new goalnames. *)
fun solve_or_fail r =
    r thenf (fn rst => if null (RState.get_goalnames rst)
                       then rst else RState.set_rtechn (SOME fail) rst);

(* same as above above, but avoids introducing failed state into trace *)
fun solve_or_nothing r =
    r thenfs (fn rst => if null (RState.get_goalnames rst)
                        then Seq.single rst else Seq.empty);


end;
