(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Title:      rtechn/conj/conj_stack_cinfo.ML
    Author:     Lucas Dixon, University of Edinburgh
                ldixon@inf.ed.ac.uk
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  DESCRIPTION:

    Contextual information for a stack of conjectures made so far, to
    allow loop avoidence by checking when we make a new conjecture
    against those previously made.

    This contextual information is local, ie only to this branch of
    proof planning. Each branch has its own copy of the conjecture
    stack.

    For future work: we could make this more effcicient by using a
    special mixed disrimination net which checks for new constants as
    well as doing the embedding check. -- this is probably quite tricky.

    Note: we will use the subsume to mean our own custom subsumtion
    check: this is a combination of an embedding-check and a
    not-containing-a-new-constant check.
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
signature CONJSTACK_CINFO =
sig

  structure Ctxt : PROOF_DATA where type T = ConjSubsume.T


  val add_term_rst : Term.term -> RState.T -> RState.T

  val subsume_chk_rst : RState.T -> Term.term -> bool

  val pretty_rst : RState.T -> Pretty.T


  (*
  structure I : LOCAL_INFO_ITEM

  val add_term_rst : PPlan.gname * Term.term -> RState.T -> RState.T

  val subsume_chk_rst : RState.T -> PPlan.gname -> Term.term -> bool

  val pretty_rst : RState.T -> PPlan.gname -> Pretty.T
  *)

end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
structure ConjStackCInfo
: CONJSTACK_CINFO
= struct

  structure Ctxt = Proof_Data(struct
    type T = ConjSubsume.T;
    fun init thy = ConjSubsume.empty;
  end);

  structure Rst = struct
    val get = Ctxt.get o RState.get_ctxt;
    val put = RState.update_ctxt o Ctxt.put;
    val map = RState.update_ctxt o Ctxt.map;
  end;

  fun pretty_rst rst = 
      let val ctxt = (RState.get_ctxt rst) 
      in ConjSubsume.pretty ctxt (Ctxt.get ctxt) 
      end;

  fun add_term_rst t rst =
      Rst.put (ConjSubsume.add_term t (Rst.get rst)) rst;

  (* rst conjecturing from, and the term being conjectured *)
  fun subsume_chk_rst rst t =
      ConjSubsume.subsume_chk (Rst.get rst) t;



(* TODO: think about this: it won't work as is because local cinfo doesn't get
   propegarted between goals, we'd need it to prpegate from parent to child
   lemma goals *)
(*
  structure I =
  LocalInfoFUN(
    struct
      type T = ConjSubsume.T;
      val name = "conjstack";
      val copy = I; (* copy is just identy as no references *)
      val pretty : ConjSubsume.T -> RState.T -> Pretty.T =
          K o ConjSubsume.pretty;
    end
  );

  val pretty_rst = I.pretty_rst;

  fun add_term_rst (gt as (g,t)) rst =
      I.update g (ConjSubsume.add_term (RstPP.get_ctxt rst) gt) rst;

  (* rst conjecturing from, and the term being conjectured *)
  fun subsume_chk_rst rst g t =
      ConjSubsume.subsume_chk (I.get rst g) t;
*)

end;
