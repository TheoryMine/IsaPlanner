(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      cinfo/rippling/ripple_skel_onemeasure.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucasd@dai.ed.ac.uk
    Created:    9 Feb 2004
    Modified:   Dominic Mulligan
                12 Sept 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    A ripple skeleton state that holds only a single measure. On multiple
    embeddings/annotations, it produces multiple states. 

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RRIPPLE_SKEL = 
  sig

    type T
    structure RRippleMeasure : BASIC_RRIPPLE_MEASURE
    
    val name : string
    (* choices to be searched over *)
    val init : (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T -> {skelname: string, skelterm: Term.term, target: Term.term} -> bool -> T list
    val mk_next : (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T -> Term.term -> T -> T list
    val mk_all_next : (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T -> Term.term -> T -> T list
    val mk_thld_next : (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T -> Term.term -> RRippleMeasure.T -> T -> T list
    val mk_next2 :  (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T -> Term.term -> T -> (T list) option
    val mk_next_rev : (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T -> Term.term -> T -> T list
    val measures_of :  T -> RRippleMeasure.T list
    (* this ripple state is a final one -- ie apply critics etc 
       (although we may also have next states) *)
    val success_chk : T -> bool
    val named_skel_term_of : T -> (string * Term.term)
    (* true if this state is blocked given the list of possible 
       future states *)
    val blocked_chk : T -> T list -> bool
    (*   val pretty : Sign.sg -> T -> Pretty.T *)
    val pretty : Proof.context -> T -> Pretty.T
end;

functor RRippleSkelOneMeasureFUN 
          (RRippleMeasure : BASIC_RRIPPLE_MEASURE) : RRIPPLE_SKEL =
  struct

    structure RRippleMeasure = RRippleMeasure;

    val name = "relational rippling skel - measure:" ^ RRippleMeasure.name;

    datatype T = state of 
      {
         skelterm : Term.term,
   skelname : string,
         measure : RRippleMeasure.T,
         aterm : RRipplingATerms.T
      };

    fun measure_of (state rep) = (#measure rep);
    fun measures_of (state rep) = [(#measure rep)];
    fun aterm_of (state rep) = #aterm rep;
    fun aterms_of (state rep) = [#aterm rep];
    fun skelterm_of (state rep) = #skelterm rep;
    fun skelname_of (state rep) = #skelname rep;

    fun update_measure f (state rep) = 
      state {skelterm = #skelterm rep, 
       skelname = #skelname rep,
             measure = f (#measure rep),
             aterm = #aterm rep};

    (* takes in new measure then old state *)
    val set_measure = update_measure o K;

    fun set_aterm_and_measure (a,m) (state rep) = 
      state {skelterm = #skelterm rep, 
             skelname = #skelname rep,
             measure = m, aterm = a};    

    (* quick removal of "rs" elements from "ls" when (eqf (r,l)) is true, ignores ordering. *)
    fun lrem eqf rs ls = 
      let
        fun list_remove rs ([],[]) = []
    | list_remove [] (xs,_) = xs
    | list_remove (r::rs) ([],leftovers) = 
        list_remove rs (leftovers,[])
    | list_remove (r1::rs) ((x::xs),leftovers) = 
        if eqf (r1, x) then
          list_remove (r1::rs) (xs,leftovers)
        else
    list_remove (r1::rs) (xs, x::leftovers)
      in
    list_remove rs (ls,[])
      end;

    fun mk_measures rtab instenv skel target =
      maps ((RRippleMeasure.of_eterm) o RREmbeddingLib.eterm_of_embedding) (Seq.list_of (RREmbeddingLib.embed rtab instenv skel target))

    (* choices to be searched over *)
    fun init rtab instenv {skelname: string,
         skelterm: Term.term, 
         target: Term.term} flag =
      map (fn m => state { skelterm = skelterm, skelname = skelname,
         measure = m, aterm = RRippleMeasure.aterm_of m })
      (mk_measures rtab instenv skelterm target);


    (* gives back the next states - only the ones that are better than the old measure *)
    fun mk_next rtab instenv target' d = 
      let
        val m = measure_of d
      in
    Library.map_filter 
            (fn m' =>
    if (RRippleMeasure.ord (m, m') = GREATER) then 
      SOME (set_aterm_and_measure (RRippleMeasure.aterm_of m',m') d)
                else
      NONE) (mk_measures rtab instenv (skelterm_of d) target') 
      end;

    (* For rippling in reverse *)
    fun mk_next_rev rtab instenv target' d = 
      let
        val m = measure_of d
      in
    Library.map_filter 
          (fn m' =>
        if (RRippleMeasure.ord (m, m') = LESS) then 
    SOME (set_aterm_and_measure (RRippleMeasure.aterm_of m',m') d)
              else NONE) (mk_measures rtab instenv (skelterm_of d) target') 
      end;

    (* Need to signal if failure occured due to no embedding found or no measure decrease *)
    fun mk_next2 gmi rtab instenv target' d = 
      let 
        val skel = skelterm_of d
  val m = measure_of d
  (* Get embeddings, incl, those that might violate sink constraints etc. *)
  val new_embs = Seq.list_of (RREmbeddingLib.embed rtab instenv skel target')
      in
        (* No embeddigns *)
  if (null new_embs) then
    NONE
  else 
          let 
            (* Make new measures if there were embeddings *)
            val new_mesrs = maps ((RRippleMeasure.of_eterm) o RREmbeddingLib.eterm_of_embedding) new_embs
            val new_embs =
                Library.map_filter 
                  (fn m' =>
          if (RRippleMeasure.ord (m, m') = GREATER) then 
                        SOME (set_aterm_and_measure (RRippleMeasure.aterm_of m',m') d)
                      else
      NONE) new_mesrs
          in
            SOME new_embs
          end
    end;


    (* gives back the next states - also the ones that are NOT better than the old measure *)
    fun mk_all_next rtab instenv target' d =
      map (fn m' =>  set_aterm_and_measure (RRippleMeasure.aterm_of m',m') d) (mk_measures rtab instenv (skelterm_of d) target');

    (* gives back next states, as long as they're better than the given threshold measure *)
    fun mk_thld_next rtab instenv target' thld_mes d =
      Library.map_filter 
        (fn m' =>
    if (RRippleMeasure.ord (thld_mes, m') = GREATER) then 
            SOME (set_aterm_and_measure (RRippleMeasure.aterm_of m',m') d)
          else
            NONE) (mk_measures rtab instenv (skelterm_of d) target');

    (* classic view of blocked - no new states *)
    fun blocked_chk st sts = null sts;

    (* everything rippled away - zero measure! *)
    (* implicit T *)
    val success_chk = RRippleMeasure.success_chk o measure_of;

    fun named_skel_term_of d = (skelname_of d, skelterm_of d);

    (* implicit T *)
    fun pretty_aux atpf d = 
      Pretty.chunks
        [Pretty.block 
          [Pretty.str "measure: ", RRippleMeasure.pretty (measure_of d)],
      Pretty.block 
              [Pretty.str "aterm: ", atpf (aterm_of d)]];

    (* implicit sgn/ctxt, T *)
    val pretty = pretty_aux o RRipplingATerms.pretty;
  end;

structure RRippleMeasure = RRippleMeasureFUN(val name = "relational rippling measure"
                                             val atermifier = RRipplingATerms.r_aterms_of_eterm
                                             val measuref = RRipplingATerms.relational_measure_of)
structure RRippleSkel = RRippleSkelOneMeasureFUN(RRippleMeasure);
