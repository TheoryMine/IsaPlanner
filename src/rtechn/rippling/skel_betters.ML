(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      cinfo/rippling/skel_betters.ML
    Author:     Lucas Dixon, University of Edinburgh
                
    Created: 2 Oct 2008 *) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*) 
(* 
   DESCRIPTION: Rippling state for a given skeleton, holds all measures 
   for a term, uses the measure functions to create better measures.  
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor RippleSkelBettersFUN(RippleMeasure : BASIC_RIPPLE_MEASURE)
: RIPPLE_SKEL
= struct

structure RippleMeasure = RippleMeasure;
val name = "rippling skel: better_measures"; (* unique id to define rippling *)

(* the ripple skeleton state for this branch of search *)
datatype T = RippleState of 
 {skelterm : Term.term, (* skeleton term *)
  skelname : string, (* skeleton result name *)
  (* all measures *)
  ems : (Embed.T * RippleMeasure.T) list };

 (* simple interface functions GET/SET *)
fun get_skelterm (RippleState rep) = #skelterm rep;
fun get_skelname (RippleState rep) = #skelname rep;
fun get_ems (RippleState rep) = #ems rep;
val get_measures = map snd o get_ems;
val get_embeddings = map fst o get_ems;

fun set_skel (skelt, skeln) (RippleState rep) = 
    RippleState {skelterm = skelt, 
                 skelname = skeln, 
                 ems = #ems rep };

fun set_ems ems2 (RippleState rep) = 
    (RippleState {skelterm = #skelterm rep, skelname = #skelname rep, ems = ems2 });

(* get the named skeleton used during rippling *)
fun get_named_skel_term ripst = (get_skelname ripst, get_skelterm ripst);

fun success_chk ripst = 
    List.exists RippleMeasure.success_chk (get_measures ripst);

(* blocked if all new states have no improved measure *)
fun blocked_chk st newsts = 
    List.all (fn st => case get_measures st of _::_ => false | [] => true) newsts

fun init_measures ectxt skel_trm target_trm =
    (Embed.embed ectxt skel_trm target_trm)
      |> Seq.list_of
      |> maps (fn e => map (pair e) (RippleMeasure.init_measure e));

fun better_next_measures oldms ectxt skel_trm target_trm =
    (Embed.embed ectxt skel_trm target_trm)
      |> Seq.list_of
      |> maps (fn e => map (pair e) (RippleMeasure.better_next_measures oldms  e));

fun all_next_measures oldms ectxt skel_trm target_trm =
    (Embed.embed ectxt skel_trm target_trm)
      |> Seq.list_of
      |> maps (fn e => map (pair e) (RippleMeasure.all_next_measures oldms e));

  (* choices to be searched over *)
fun init {ectxt    : Embed.Ectxt.T,
          skelname : string,
          skelterm : Term.term, 
          target   : Term.term} =
    let val ems = init_measures ectxt skelterm target
    in [RippleState {skelterm = skelterm, skelname = skelname, ems = ems}] end;

(* Search though all possible improveing measures *)
fun mk_better_next ectxt newtrm oldst = 
    (case better_next_measures (get_measures oldst) ectxt (get_skelterm oldst) newtrm 
      of [] => [] | (ems as (_::_)) => [set_ems ems oldst]);

(* Search though all possible measures *)
fun mk_all_next ectxt newtrm oldst = 
    (case all_next_measures (get_measures oldst) ectxt (get_skelterm oldst) newtrm 
      of [] => [] | (ems as (_::_)) => [set_ems ems oldst]);

(* For use in middle-out rippling. Keeps fixed threshold, so all
speculative steps have to be better than this. *) (* note from Lucas:
not sure this is right: when is this used? where does the threshold
come from? is it updated? *)
fun mk_thld_next ectxt newtrm (thld_e,thld_mes) oldst =
    (case better_next_measures [thld_mes] ectxt (get_skelterm oldst) newtrm
      of [] => [] | (ems as (_::_)) => [set_ems ems oldst]);

(* For terms with meta-varaiables. 'newtrms' are assumed to be projections of
   some term containing meta-variables. These are grouped with the alternative
   embeddings into one reasoning state. *)
fun mk_midout_next ectxt newtrms oldst =
    (case maps (better_next_measures (get_measures oldst) ectxt (get_skelterm oldst)) newtrms
      of [] => [] | (ems as (_::_)) => [set_ems ems oldst]);

(* ------------------------------------------------------------ *)
(* Pretty printing *)
(* ------------------------------------------------------------ *)

fun pretty_embed_and_measure (e,m) = 
    Pretty.chunks
      [Pretty.block 
         [Pretty.str "Measure: ", RippleMeasure.pretty m]
       (* Pretty.block 
         [Pretty.str "Embedding: ", Embed.pretty e]*) ]; 

fun pretty ctxt st = 
    Pretty.chunks 
      (map 
         (fn em => Pretty.block [(pretty_embed_and_measure em)])
         (get_ems st));

val print = Pretty.writeln oo pretty;

end;

