(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      cinfo/rippling/ripple_skel_gm_int.ML
    Author:     Moa Johansson, University of Edinburgh
                
    Created: 27 Aug 2007 *) 
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-*) 
(* 
   DESCRIPTION: Ripple skeleton state with grouped annotations
    usign an integer measure.
    
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
functor RippleSkelGroupedMeasuresFUN(RippleMeasure : BASIC_RIPPLE_MEASURE)
: RIPPLE_SKEL
= struct

structure RippleMeasure = RippleMeasure;
val name = "rippling skel: grouped measures/annotations with integer measure";

(* the ripple skeleton state for this branch of search *)
datatype T = RippleState of 
 {skelterm : Term.term,
  skelname : string,
  (* the current threshold measure *)   
  thold : Embed.T * RippleMeasure.T,
  (* the current best measure *) 
  best :  Embed.T * RippleMeasure.T,
  new_best : bool,
  (* other measures in case we need them *)
  all : (Embed.T * RippleMeasure.T) list };

 (* simple interface functions GET/SET *)
fun skelterm_of (RippleState rep) = #skelterm rep;
fun skelname_of (RippleState rep) = #skelname rep;
fun thold_m_of (RippleState rep) = #thold rep;
fun best_m_of (RippleState rep) = #best rep;
fun new_best_of (RippleState rep) = #new_best rep;
fun all_m_of (RippleState rep) = #all rep;
val measures_of = map snd o all_m_of;
val embeddings_of = map fst o all_m_of;

fun set_skel (skelt, skeln) (RippleState rep) = 
    RippleState {skelterm = skelt, 
                 skelname = skeln, 
                 thold= #thold rep,
                 best = #best rep,
                 new_best = #new_best rep,
                 all= #all rep };


fun set_thold_m thold2 (RippleState {skelterm,skelname,
                                     thold, best, new_best, all}) = 
    (RippleState {skelterm=skelterm,skelname=skelname, 
                  thold=thold2, best=best, new_best=new_best, all=all });

fun set_best_m best2 (RippleState {skelterm,skelname,
                                     thold, best, new_best, all}) = 
    (RippleState {skelterm=skelterm,skelname=skelname, 
                  thold=thold, best=best2, new_best=new_best, all=all });

fun set_new_best new_best2  (RippleState {skelterm,skelname,
                                     thold, best, new_best, all}) = 
    (RippleState {skelterm=skelterm,skelname=skelname, 
                  thold=thold, best=best, new_best=new_best2, all=all });

fun set_all_m_of all2 (RippleState {skelterm,skelname,
                                    thold, best, new_best,all}) = 
    (RippleState {skelterm=skelterm,skelname=skelname, 
                  thold=thold, best= best, new_best=new_best, all=all2 });

(* get the named skeleton used during rippling *)
fun named_skel_term_of ripst = (skelname_of ripst, skelterm_of ripst);

fun ord ((et1,m1),(et2,m2)) = RippleMeasure.ord (m1,m2);

 (* new threshold is new worst measure (already filtered to be better than old threshold). *)
(*fun get_thold_and_best [] ((best,isbest),thold) = ((best,isbest),thold)
    | get_thold_and_best (m::ms) ((best,isbest),thold) =
      get_thold_and_best ms ((if ord (m, best) = LESS then (m,true) else (best,false)), 
                              if ord (m, thold) = GREATER then m else thold);
*)
fun get_thold_and_best [] (best,thold) = (best,thold)
    | get_thold_and_best (m::ms) (best,thold) =
      get_thold_and_best ms ((if ord (m, best) = LESS then m else best), 
                              if ord (m, thold) = GREATER then m else thold);
fun success_chk d = 
    RippleMeasure.success_chk (snd (best_m_of d));

(* given list of next node measures (newsts), assess if
     rippling is blocked *)
fun blocked_chk st newsts = 
    (Basics.is_none (Library.find_first new_best_of newsts));                           
(*   new_best_of st andalso 
    (Basics.is_none (Library.find_first new_best_of newsts));
*)
fun init_measures ectxt skel_trm target_trm =
    (Embed.embed ectxt skel_trm target_trm)
      |> Seq.list_of
      |> maps (fn e => map (pair e) (RippleMeasure.init_measure e));

fun next_measures oldst ectxt skel_trm target_trm =
    (Embed.embed ectxt skel_trm target_trm)
      |> Seq.list_of
      |> maps (fn e => map (pair e) 
                           (maps 
                              (fn oldm => RippleMeasure.next_measure oldm e)
                              (map snd (all_m_of oldst))));

  (* choices to be searched over *)
fun init {ectxt    : Embed.Ectxt.T,
          skelname : string,
          skelterm : Term.term, 
          target   : Term.term} =
    let val mesrs = init_measures ectxt skelterm target
    in
      case mesrs of [] => []
                  | mss as m::ms =>
                    let val (best, thold) = get_thold_and_best ms (m,m)
                    in 
                      [RippleState { skelterm = skelterm, skelname = skelname,
                                     thold = thold, best = best, new_best=true,
                                     all = mss}]
                    end
    end;


(* Search though all possible improveing measures *)
fun mk_next ectxt newtrm (oldst as 
                                RippleState {skelterm, skelname, thold,
                                             best, new_best, all}) = 
    let val allms = next_measures oldst ectxt skelterm newtrm
        val allbetterms = Library.filter (fn m' => ord(m', thold) = LESS) allms
    in
      case allbetterms of [] => []
      | mss as (m::ms) => 
        let 
          val (best2,thold2) = (* ((best2,isbest),thold2) = *) 
              get_thold_and_best ms (m, m)
          val hasbest = (ord (best2, best)) = LESS
        in
          [RippleState {skelterm = skelterm, skelname=skelname, 
                        thold=thold2, best = best2, new_best = hasbest,
                        all = allbetterms}]
        end
    end;

(* Search though all possible measures *)
fun mk_all_next ectxt newtrm (oldst as RippleState {skelterm, skelname, thold,
                                 best, new_best, all}) = 
    let val allms = next_measures oldst ectxt skelterm newtrm
    in
      case allms of [] => []
      | mss as (m::ms) => 
        let 
          val (best2,thold2) =(* ((best2,isbest),thold2) = *)
              get_thold_and_best ms  (m,m)
           val hasbest = (ord (best2, best)) = LESS   
        in
          [RippleState {skelterm = skelterm, skelname=skelname, 
                        thold=thold2, best = best2, new_best = hasbest,
                        all = allms}]
        end
    end;

(* FIXME: THreashold and best measure should swap places *)
(* Search though all possible worse measures, for rippling in reverse. *)
(* Don't think this is needed anywhere - delete? *)
(*fun mk_next_rev ectxt newtrm (oldst as RippleState {skelterm, skelname, thold,
                                 best, new_best, all}) = 
    let val allms = next_measures oldst ectxt skelterm newtrm
        val allworsems = Library.filter (fn m' => ord(m', thold) = GREATER) allms
    in
      case allworsems of [] => []
      | mss as (m::ms) => 
        let 
         (* FIXME: Think of what this should be for reverse rippling. Best/Worst so far? *)
          val (best2,thold2) = 
              get_thold_and_best ms (m,m)
          val hasbest = (ord (best2, best)) = LESS (* GREATER ?*)    
        in
          [RippleState {skelterm = skelterm, skelname=skelname, 
                        thold=thold2, best = best2,  new_best = hasbest,
                        all = allworsems}]
        end
    end;
*)

(* For use in middle-out rippling. Keeps fixed threshold, so all speculative
steps have to be better than this. *)
fun mk_thld_next ectxt newtrm (thld_e,thld_mes) 
                 (oldst as RippleState {skelterm, skelname, thold,
                               best, new_best, all}) =
    let      
     val allms = next_measures oldst ectxt skelterm newtrm
     val allbetterms = Library.filter (fn m' => RippleMeasure.ord(snd m', thld_mes) = LESS) allms
    in
      case allbetterms of [] => []
      | mss as (m::ms) => 
        let 
          val (best2,thold2) = 
              get_thold_and_best ms (m, m)
          val hasbest = (ord (best2, best)) = LESS    
        in
          (* Should best-measure be updated? We take an optimistic view so maybe not *)
          [RippleState {skelterm = skelterm, skelname=skelname, 
                        thold= (thld_e, thld_mes), 
                        best = best2, new_best = hasbest, 
                        all = allbetterms}]
        end
    end;

(* For terms with meta-varaiables. 'newtrms' are assumed to be projections of
   some term containing meta-variables. These are grouped with the alternative
   embeddings into one reasoning state. *)
fun mk_midout_next ectxt newtrms (oldst as 
                                        RippleState {skelterm, skelname, thold,
                                                     best, new_best, all}) =
   let      
     val allms = maps (next_measures oldst ectxt skelterm) newtrms
     val allbetterms = Library.filter (fn m' => ord(m', thold) = LESS) allms
    in
      case allbetterms of [] => []
      | mss as (m::ms) => 
        let 
          val (best2,thold2) = 
              get_thold_and_best ms (m, m)
          val hasbest = (ord (best2, best)) = LESS    
        in
          [RippleState {skelterm = skelterm, skelname=skelname, 
                        thold=thold2, best = best2, new_best = hasbest,
                        all = allbetterms}]
        end
    end;


fun mk_next2 ectxt newtrm (oldst as RippleState {skelterm, skelname, thold,
                                 best, new_best, all}) = 
    let 
    val allembs = Seq.list_of (Embed.embed ectxt skelterm newtrm)
    val allms = next_measures oldst ectxt skelterm newtrm
    val allbetterms = Library.filter (fn m' => ord(m', thold) = LESS) allms
    in
      if (null allembs) then NONE
      else
         case allms of [] => SOME []
                     | mss as (m::ms) => 
                       let 
                       val (best2,thold2) = 
                           get_thold_and_best ms (m, m) 
                        val hasbest = (ord (best2, best)) = LESS    
                       in
                          SOME [RippleState {skelterm = skelterm, skelname=skelname, 
                                       thold=thold2, best = best2, new_best = hasbest,
                                       all = allms}] 
                       end
    end;

(* ------------------------------------------------------------ *)
(* Pretty printing *)
(* ------------------------------------------------------------ *)

fun pretty_embed_and_measure (e,m) = 
    Pretty.chunks
      [Pretty.block 
         [Pretty.str "measure: ", RippleMeasure.pretty m],
       Pretty.block 
         [Pretty.str "embed: ", Embed.pretty e]]; 

fun pretty st = 
    let
      val best = best_m_of st
      val isbest = new_best_of st 
      val thold = thold_m_of st
      val allms = all_m_of st
      val no_of_mesP = Pretty.str (string_of_int (length allms))
   in
      Pretty.chunks 
        ([Pretty.block [Pretty.str "Threshold ", Pretty.str "measure",
                       Pretty.enclose "(" ")" [Pretty.str "of ", 
                                               no_of_mesP],
                       Pretty.str ": "],
          pretty_embed_and_measure thold] @
          (if isbest andalso ord (best, thold) = LESS then
            [Pretty.str "Best measure:  ",
             pretty_embed_and_measure best]
          else [])
        )
    end;

val print = Pretty.writeln o pretty;

end;

