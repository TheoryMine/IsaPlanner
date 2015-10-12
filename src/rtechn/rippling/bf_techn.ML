(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/rippling/ripple_bf_rtechn.ML
    Author:     Lucas Dixon, Moa Johansson University of Edinburgh
                lucasd@dai.ed.ac.uk
    Date:       5 Aug 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Rippling with best-first search. 

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 

signature RIPPLE_BF = 
sig
  exception BadRippleMeasure of string;
  structure RippleCInfo : RIPPLE_CINFO;

  (*Comparison of reasoning states for bf-heuristic*)
  val compare_rsts : RState.T * RState.T -> order;
  val compare_rsts_mes : RState.T * RState.T -> order;
  val compare_rsts_skels : RState.T * RState.T -> order;

  (*Different ways of doing best-first rippling steps*)
  val basic_bf_steps : RState.T -> RState.T Seq.seq;
  val basic_bf_eager_steps : RState.T -> RState.T Seq.seq;
  val bf_lemmaconj_steps : RState.T -> RState.T Seq.seq;
  val global_bf_steps : RState.T -> RState.T Seq.seq;
 

  (*Do rippling *)
  val induct_and_ripple : RTechn.T -> RState.T -> RState.T Seq.seq;
(*  val induct_ripple_conj : RTechn.T -> RState.T -> RState.T Seq.seq;
  val d_induct_ripple_conj : RTechn.T -> RState.T -> RState.T Seq.seq;
  val st_induct_ripple_conj : RTechn.T -> RState.T -> RState.T Seq.seq;    
  val induct_ripple_conj_with_rule :
        RTechn.T -> xstring -> RState.T -> RState.T Seq.seq;
  val d_induct_ripple_conj_with_rule :
        RTechn.T -> xstring -> RState.T -> RState.T Seq.seq;
  val st_induct_ripple_conj_with_rule :
        RTechn.T -> xstring -> RState.T -> RState.T Seq.seq;
  val ord_induct_and_ripple_with_rule :
        xstring -> RState.T -> RState.T Seq.seq;
*)
end;


functor RippleBFRTechnFUN(structure RippleRTechn : RIPPLE_RTECHN )
        : RIPPLE_BF  =
struct

structure RippleCInfo = RippleRTechn.RippleCInfo;

local 
  open RTechnEnv;
in

exception rippling_rtechn_exp of string;

(* ------------------------------------------------------------------------*)
(*  Heuristic for Best first search used in rippling                       *)
(* ------------------------------------------------------------------------*)


(* Get the smallest measure for any ripple state of a reasoning state. *)
exception BadRippleMeasure of string;

val order = RippleCInfo.RippleSkel.RippleMeasure.ord;

fun find_best_measure [] = raise BadRippleMeasure ("Reasoning state has no ripple-measure ")
    | find_best_measure (x::xs) =
      let
        fun best_aux [] sm = sm
            | best_aux (h::t) sm =
              if (order(h, sm) = LESS) then
                best_aux t h else best_aux t sm;
            in
        best_aux xs x
    end;

fun find_worst_measure [] = raise BadRippleMeasure ("Reasoning state has no ripple-measure ") 
    | find_worst_measure (x::xs) =
      let 
        fun worst_aux [] m = m
            | worst_aux (h::t) m =
              if (order(h, m) = GREATER) then
                worst_aux t h else worst_aux t m;
            in
        worst_aux xs x
    end;

(* Find the best measure of the worst goal in the rst, as each goal has to be solved.
 We ignore subgoals that are not rippling. *)
fun get_measure rst =
     let 
      val measures = 
          map find_best_measure 
              (filter (not o null) 
                      (RstPP.map_cur_goals' 
                         (RippleCInfo.measures_of rst)  rst))
    in 
      find_worst_measure measures
    end;

(*Check if this state has a better ripple measure than its parent *)
fun prev_measure rst =
    let
      val prev = RState.get_prev rst
    in
      case prev of NONE => LESS
                 | SOME prev_rst => 
                     if (RippleCInfo.some_curgoal_is_ripple_valid 
                           prev_rst) then
                       order((get_measure rst),(get_measure prev_rst))
                     else LESS
    end;

(* Heuristic for best-first search. Compares the ripple measeures of two states.*)
(* Ripple steps which have a better (decreasing) measure from their predecessor are automatically
better than any states which stays the same or increase *)

fun largest_term rst =
    let 
      fun max [] m = m 
        | max (h::t) m = if m<h then max t h else max t m; 
    in
      max (map Term.size_of_term (RstPP.goals_concl rst)) 0
    end;

(* Change so compares the size of largest goalterm*)
fun cmp_termsize (rst1, rst2) =
    Library.int_ord (largest_term rst1, 
                     largest_term rst2);

fun compare_rsts_mes (rst1, rst2) =
      order(get_measure rst1, get_measure rst2);

(* comparison function taking non-skeleton preservation into account. *)
(* Valid ripple steps gets better score than non-skeleton preserving. *)
fun compare_rsts_skels (rst1, rst2) =
    let val has_skel1 = RippleCInfo.some_curgoal_is_ripple_valid rst1
        val has_skel2 = RippleCInfo.some_curgoal_is_ripple_valid rst2      
    in
      (* Deal with cases when one or both has no skeleton embedding and no measure *)
      (* For two non-skel preserving steps prefer the ones with smaller goalterm*)
    if (not has_skel1) andalso (not has_skel2) then 
      cmp_termsize (rst1,rst2)
    else if has_skel1 andalso (not has_skel2) then LESS
    else if (not has_skel1) andalso has_skel2 then GREATER
    else  (*Normal comparison *)
      compare_rsts_mes (rst1, rst2)
  end;

fun compare_rsts (rst1,rst2) =
    let 
      val is_ripple1 = RippleCInfo.some_curgoal_is_rippling rst1 
      val is_ripple2 = RippleCInfo.some_curgoal_is_rippling rst2 
    in
      if (is_ripple1) andalso (is_ripple2) then
        compare_rsts_skels (rst1,rst2) (*We're rippling*)

      (*Do non-explore steps before rippling as these are
       linear. Prefer non-rippling steps further down just
       to get on with rippling again.*)
      else if (is_ripple1 andalso (not is_ripple2)) then
        GREATER
      else if ((not is_ripple1) andalso is_ripple2) then
        LESS
        (*assuming "newer" rst have a larger id, prefer them.*)
      else Library.int_ord ((RState.get_id rst2),
                           (RState.get_id rst1))
    end;

(* ------------------------------------------------------------------------*)
(* The cache for same-check                                                *)
(* ------------------------------------------------------------------------*)

(* Why is this a term*unit ref net???*)
(*datatype Cache = cache of {net : (Term.term * unit ref) Net.net ref};*)
datatype Cache = cache of {net : (Term.term * PPlan.gname) Net.net ref}
fun netref_of (cache rep) = (#net rep);
val net_of = ! o netref_of;
fun update_net net c = (netref_of c := net; c);
fun init_cache net = cache {net = ref net};

(* checks that we have different unique ref's but the same term. *)
fun same_chk ((t1,id1),(t2,id2)) = not (id1 = id2) andalso (t1 = t2);

(* Filter out states seen elsewhere. Ignore non-rippling goals *)
fun filter_same _ [] = []
    | filter_same c (rst::rsts) =
      let
        fun check_goal [] (rst::rsts) = (rst::(filter_same c rsts))
            (*Should not happen as filter_same and check_goal mut.recursive*)
            | check_goal _ [] = 
              raise ERROR "Ripple_bf.check_goal: No reasoning states to check."  
        
            | check_goal (gname::gs) (rst::rsts) = 
            if (RippleCInfo.is_rippling rst gname) 
            then
              (let
                val gt = RstPP.goal_concl rst gname         
                val cache' = update_net 
                               (Net.insert_term same_chk 
                                (gt,(gt,gname)) (net_of c)) c
               in check_goal gs (rst::rsts) 
               end 
               handle Net.INSERT =>
                      (*should be ok, goals not rippled have same name still*)
                      filter_same c rsts) (*throw away rst's with previously seen ripples*)
            else check_goal gs (rst::rsts); (*ignore non-rippling states*)

      in
        case (RState.get_goalnames rst) of
           [] => rst::filter_same c rsts (* no goals - ignore *)
         | (gname::gs) => check_goal (gname::gs) (rst::rsts)
      end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Case-splitting                                                     *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* Case-splitting*)
fun case_split_if goal rst =
    let 
      val old_skels = RippleCInfo.all_skels_of rst goal
    in 
      Seq.maps
      (fn rs => (RippleCInfo.update_all old_skels) 
                   (RState.set_rtechn NONE rs))
      (SplitterRTechn.split_if_rtechn goal rst)
    end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Update the rippling state information.                              *)
(* This best-first version also get non-measure decreaseing &          *)
(* non-skeleton states                                                 *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
local 
  fun updateN dtac =
      RstName.f (fn rst => Pretty.chunks 
                             [Pretty.block 
                                [Pretty.str "Ripple Step by ",
                                 DTac.pretty dtac] 
                              (*@ (map (ProofContext.pretty_term (RstPP.get_ctxt rst)) 
                                     (RstPP.goals_concl rst))*),
                              RippleCInfo.pretty_curgoals_skels rst]);
in
fun update_step dtac old_skels rst =
    (givename (updateN dtac) 
              (RippleCInfo.update_all old_skels))
     (RState.set_rtechn NONE rst);
end;

fun possible_steps goal rst = 
    let 
      val old_skels = RippleCInfo.all_skels_of rst goal
      val dtacs = RippleCInfo.applicable_dtacs_of rst goal            
    in
      (apply_or_dtacs_to_g dtacs goal rst)
      |> Seq.maps (fn (dtac,rst) => update_step dtac old_skels rst)
    end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Ripple steps with embedding check                                 *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


  
(*Filter out states embedding some state on conjecture stack*)
  fun not_cached rst g cache_opt =
          case cache_opt of 
            SOME c => (
            if (RippleCInfo.is_rippling rst g)
            then(
               if (not(ConjStackCInfo.subsume_chk c (RstPP.goal_concl rst g)))
               then
                 SOME (ConjStackCInfo.add_term 
                         (RstPP.get_ctxt rst) (g, RstPP.goal_concl rst g) c)
               else NONE) (*No new cache, goal subsumed*)
            else SOME c (*ignore non-rippling goals*))
          | NONE => NONE 

(* Adds new states to the conjecture stack, returned updates cache
for each state. Return a list of pairs -states that doesn't embedd 
anything and their cache *)
fun chk_emb [] c sts = sts (*A list of pairs (rst,emb_cache)*)
  | chk_emb (rst::rsts) c sts =
    case (RState.get_goalnames rst) of
        [] => chk_emb rsts c ((rst,c)::sts) (*no open goals, ignore*)
      | (g::gs) =>
        let 
          val new_cache = fold (not_cached rst) (g::gs) (SOME c)
        in
          case new_cache of
            SOME newc => chk_emb rsts c ((rst,newc)::sts)
          | NONE => chk_emb rsts c sts
        end;


(* Ripple steps with caching checking for embeddings*)
fun cached_steps same_cache emb_cache rst = 
    let
      fun steps_goal same_cache emb_cache goal rst =
          (*Finished rippling*)
        if (RippleCInfo.success_chk rst goal) then
             Seq.single (dummy_rst 
              (RstName.str ("end rippling, strong fertilisation possible on goal "^goal)) rst)  
          else
            let 
              val not_sames = filter_same same_cache 
                              (Seq.list_of(possible_steps goal rst))
              val not_embs = chk_emb not_sames emb_cache []
              val possibles = 
                  map (fn (rst,c') => 
                          continue_with 
                            ((map_then case_split_if)
                               try1_then 
                               (map_then (steps_goal same_cache c'))) rst) 
                      not_embs  
            in 
              Seq.of_list
                (if (null possibles) 
                 then (* Blocked *)
                        (dummy_rst (RstName.str ("end rippling, goal "^goal)) rst) :: possibles
                 else possibles)
            end
    in
      (* the caching ignores other goals in the same rst at the moment. I think that's OK.*)
      map_then (steps_goal same_cache emb_cache) rst 
    end;
 
(* Eager weak-fertilisation and lemma conj *)
fun cached_steps_eager same_cache emb_cache rst =
    let 
      fun steps_goal same_cache emb_cache goal rst =
          (*Finished rippling*)
          if (RippleCInfo.success_chk rst goal) 
          then
            Seq.single (dummy_rst 
                          (RstName.str 
                          ("end rippling, strong fertilisation possible on goal "^goal)) rst)
          else (* actually make a step *)
              let 
                val not_sames = filter_same same_cache 
                                            (Seq.list_of (possible_steps goal rst))
                val not_embs = chk_emb not_sames emb_cache []
                val possibles =  map (fn (rst,c') => continue_with 
                                    ((map_then case_split_if)
                                       try1_then
                                     (cached_steps_eager same_cache c')) rst) not_embs  
                val has_skels = filter RippleCInfo.some_curgoal_is_ripple_valid possibles
              in 
                Seq.of_list
                  (if (null has_skels) 
                   then (* Blocked or only non-skel *)
                          (dummy_rst (RstName.str ("end rippling, goal: "^goal)) rst) :: possibles
                   else possibles)
              end
    in
      map_then (steps_goal same_cache emb_cache) rst
    end;    


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Auxillary functions to help rippling                                *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


(* Function to use with fold and subspace                              *)
(* Builds up a list of the most promising states to apply weak-fert    *)
(* and conjecture lemmas from on each branch.                          *)

fun best_exit_sts (best_sts : RState.T list ref)
            (rst_a, weakf_a) rst  = 
    let 
      val weakf = not (null (Seq.list_of (RippleRTechn.weak_fert rst)))
      
      fun cmp_rst (rst1, rst2) = (RState.get_id rst1) = (RState.get_id rst2)
      fun update_best best_sts rst =
          if (member cmp_rst (!best_sts) rst) then
            ()
          else 
            best_sts := (rst::(!best_sts))                   
    in
      case (RState.get_rtechn rst) of
        NONE =>
        let 
          val rst' = RState.set_rtechn (SOME RTechn.fail) rst 
        in
        if (weakf andalso (not weakf_a)) then
          let val _ = update_best best_sts rst in
            (rst', (rst,weakf)) end
        else if((not weakf) andalso weakf_a) then  
          let val _ = update_best best_sts rst_a in
          (rst', (rst_a,weakf_a))  end   
        else 
          if(compare_rsts_skels (rst_a, rst) = GREATER) then
            let val _ = update_best best_sts rst in
              (rst', (rst,weakf)) end
          else 
            let val _ = update_best best_sts rst_a  in
            (rst', (rst_a, weakf_a)) end
        end
        | SOME r =>
          if (weakf andalso (not weakf_a)) then
            (rst, (rst,weakf)) 
          else if((not weakf) andalso weakf_a) then  
            (rst, (rst_a,weakf_a))     
          else 
            if(compare_rsts_skels (rst_a, rst) = GREATER) then
              (rst, (rst,weakf)) 
            else 
              (rst, (rst_a, weakf_a))
    end;


(* Function to use with fold. Keeps track of which state      *)
(* is the best to conjecture a lemmma from on this branch     *)
fun best_exit_st (best_sts : RState.T list ref)
            (rst_a, weakf_a) rst  = 
    let 
      val weakf = not (null (Seq.list_of (RippleRTechn.weak_fert rst)))
      
      fun cmp_rst (rst1, rst2) = (RState.get_id rst1) = (RState.get_id rst2)
      fun update_best best_sts rst =
          (*Check if we're already considering this rst *)
          if (member cmp_rst (!best_sts) rst) then
            false
          else 
            let
              val _ = best_sts := (rst::(!best_sts)) in
               true 
            end
    in
      case (RState.get_rtechn rst) of
        
        NONE =>
        let 
          (*Not sure about this line... might not need it anymore...*)
          val rst' = RState.set_rtechn (SOME RTechn.fail) rst
        
        in
        if (weakf andalso (not weakf_a)) then
          if(update_best best_sts rst) then
            (rst, (rst,weakf))
          else (rst',(rst,weakf))

        else if((not weakf) andalso weakf_a) then  
          if(update_best best_sts rst_a) then
          ((dummy_rst (RstName.str "end rippling") rst_a), (rst_a,weakf_a))   
          else (rst',(rst_a,weakf_a))
        
        else 
          if(compare_rsts_skels (rst_a, rst) = GREATER) then
            if(update_best best_sts rst) then
              (rst, (rst,weakf))
            else (rst',(rst,weakf))
          else 
            if(update_best best_sts rst_a) then
              ((dummy_rst (RstName.str "end rippling") rst_a), (rst_a,weakf_a))   
            else (rst',(rst_a,weakf_a))
        end

        | SOME r =>
          if (weakf andalso (not weakf_a)) then
            (rst, (rst,weakf)) 
          else if((not weakf) andalso weakf_a) then  
            (rst, (rst_a,weakf_a))     
          else 
            if(compare_rsts_skels (rst_a, rst) = GREATER) then
              (rst, (rst,weakf)) 
            else 
              (rst, (rst_a, weakf_a))
    end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Variants of doing best-first rippling steps                         *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

(*Setup caching for same-checks (across OR-branches) and embedding checks
(local to the current branch)                                          *)
fun setup_caching rst = 
      let 
      val goals = filter (RippleCInfo.is_rippling rst) (RState.get_goalnames rst)
      val gs = map (fn g => (RstPP.goal_concl rst g, g)) goals
      val init_emb_cache = fold (ConjStackCInfo.add_term (RstPP.get_ctxt rst)) 
                                              (RstPP.goals_namedconcl rst) 
                                              (ConjStackCInfo.empty) 
      fun add_same_cache (gt,gname) net = 
            Net.insert_term same_chk 
                             (gt,(gt,gname)) net
      in
        (init_cache (fold add_same_cache gs Net.empty), init_emb_cache)
      end;

(* Conjecture from last state when blocked                             *)
fun basic_bf_steps rst = 
    let 
      val (same_cache, emb_cache) = setup_caching rst
    in
      (*CacheRTechn.CACHE' (cached_steps initcache) rst*)
      (cached_steps same_cache emb_cache) rst
    end;

(*Conjecture from last state when blocked, use eager lemma speculation *)
fun basic_bf_eager_steps rst = 
    let 
         val (same_cache, emb_cache) = setup_caching rst
    in
      (*CacheRTechn.CACHE' (cached_steps_eager initcache) rst*)
      (cached_steps_eager same_cache emb_cache) rst
    end;

(* Pick best state of this branch for attempting weak-fert when blocked *)
fun global_bf_steps rst = 
    let
      val (same_cache, emb_cache) = setup_caching rst

      val weakf = not (null (Seq.list_of (RippleRTechn.weak_fert rst)))  
      val best_rsts = ref [] : (RState.T list ref)
    (*val r = CacheRTechn.CACHE' (cached_steps initcache)*)
      val r = (cached_steps_eager same_cache emb_cache)
    in  
      RTechn.fold (best_exit_st best_rsts) (rst,weakf) r rst
    end;

(*Best-first fertilisation and lemma conjecturing after all rippling
has been done using subspacing.                                         *)
fun bf_lemmaconj_steps rst =
    let
      val (same_cache, emb_cache) = setup_caching rst
      val weakf = not (null (Seq.list_of (RippleRTechn.weak_fert rst)))
      val spaceref = ref (SubSpace.init ())
      val best_rsts = ref [] : (RState.T list ref)               
      (*val r = CacheRTechn.CACHE' (cached_steps initcache)*)
      val r = (cached_steps_eager same_cache emb_cache)

      fun finish_rippling best_rsts rst = 
          let val sorted_bests = Library.sort compare_rsts (!best_rsts) 
          in
            Seq.of_list(
            map (fn rst =>
                    (dummy_rst (RstName.str "end rippling") rst))
                (sorted_bests))
            end;
    in
    SubSpaceRTechn.subspace
              {sref = spaceref, 
               techn = RTechn.fold (best_exit_sts best_rsts) (rst,weakf) r,
               rstf= (finish_rippling best_rsts)}  rst
    end;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Induction with best-first rippling                                  *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
local 
  val stepcaseN = RstName.str "Solve the step case using rippling.";
in

 (* local *)
fun ripple_stepcase step_techn rst =
    (refine stepcaseN
           (RippleRTechn.startr
              thenr step_techn
              thenr RippleRTechn.endr))
      rst;

(*BF-Rippling using stacked search *)
fun st_ripple_stepcase step_techn indhyps = 
    refine stepcaseN
           ((RTechn.search (MSearch.bestfs compare_rsts) 
                           (RippleRTechn.startr
                              thenr step_techn))
              thenr RippleRTechn.endr);

end;(* local *)

(* Simplify the base case *)
local val basecaseN = 
          RstName.str "Solve the base case by simplification."; in
val simplify_basecase = 
    givename basecaseN DTacRTechn.simp_no_asm_simp_changes;
end;


(* induction and rippling technique *)
local 
  val induct_and_rippleN = RstName.str "Induction and bf-rippling."
in
fun induct_and_ripple step_techn rst = 
    refine induct_and_rippleN
      (InductRTechn.induction simplify_basecase (ripple_stepcase step_techn))     
    rst;
end;

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Induction and Best-first Rippling with Conjecturing                *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*
fun explconj_critic lemmatechn r = 
    r thenf 
      (fn rst => 
            if Expl.solved_chk_rst rst then rst
            else continue_with (ConjRTechn.prove_by_lemma lemmatechn) rst);

(* With delayed search *)
fun d_explconj_critic lemmatechn r = 
    r thenf 
      (fn rst => if Expl.solved_chk_rst rst then rst
                 else continue_with (ConjRTechn.prove_by_lemma' lemmatechn) rst);


fun simplify_conj_basecase lemmatechn = 
    explconj_critic lemmatechn simplify_basecase;

fun ripple_conj_stepcase step_techn lemmatechn indhyps =
    explconj_critic lemmatechn 
                    ((ripple_stepcase step_techn) indhyps)

(* With delayed search *)
fun d_simplify_conj_basecase lemmatechn = 
    d_explconj_critic lemmatechn simplify_basecase;

fun d_ripple_conj_stepcase step_techn lemmatechn indhyps =
    d_explconj_critic lemmatechn 
                    ((ripple_stepcase step_techn) indhyps)

(* Use stacked serach *)
fun st_ripple_conj_stepcase step_techn lemmatechn indhyps =
    explconj_critic lemmatechn 
                    ((st_ripple_stepcase step_techn) indhyps)

local val induct_and_rippleN = 
      RstName.str "Solve using Induction, Bf-Rippling, and Conjecturing." in
fun induct_ripple_conj step_techn rst = 
    refine induct_and_rippleN
           (InductRTechn.induction (simplify_conj_basecase (induct_ripple_conj step_techn))
                                   (ripple_conj_stepcase step_techn 
                                                         (induct_ripple_conj step_techn)))
           rst;

(*With delayed search *)
fun d_induct_ripple_conj step_techn rst =
    refine induct_and_rippleN
           (InductRTechn.induction (d_simplify_conj_basecase (d_induct_ripple_conj step_techn))
                                   (d_ripple_conj_stepcase step_techn 
                                                         (d_induct_ripple_conj step_techn)))
           rst;

(* With stacked search *)
fun st_induct_ripple_conj step_techn rst = 
    refine induct_and_rippleN
           (InductRTechn.induction (simplify_conj_basecase (st_induct_ripple_conj step_techn))
                                   (st_ripple_conj_stepcase step_techn 
                                                         (st_induct_ripple_conj step_techn)))
           rst;

end; (* local *)

(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Induction and rippling with custom induction-rule                   *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

local 
  val induct_and_rippleN = 
      RstName.str "Solve using (customised) Induction, Bf-Rippling, and Conjecturing."
in

fun induct_ripple_conj_with_rule step_techn rule rst = 
    refine induct_and_rippleN
      (InductRTechn.induction_with (thm rule) 
                                   (simplify_conj_basecase 
                                      (induct_ripple_conj_with_rule 
                                         step_techn rule))
                                   (ripple_conj_stepcase step_techn 
                                                         (induct_ripple_conj_with_rule 
                                                            step_techn rule)))
      rst;

(*With delayed search *) 
fun d_induct_ripple_conj_with_rule step_techn rule rst = 
    refine induct_and_rippleN
      (InductRTechn.induction_with (thm rule) 
                                   (d_simplify_conj_basecase 
                                      (d_induct_ripple_conj_with_rule 
                                         step_techn rule))
                                   (d_ripple_conj_stepcase step_techn 
                                                           (d_induct_ripple_conj_with_rule 
                                                              step_techn rule)))
      rst;


(* With stacked serach *)
fun st_induct_ripple_conj_with_rule step_techn rule rst = 
    refine induct_and_rippleN
      (InductRTechn.induction_with (thm rule) 
                                   (simplify_conj_basecase 
                                      (induct_ripple_conj_with_rule 
                                         step_techn rule))
                                   (st_ripple_conj_stepcase step_techn 
                                                         (induct_ripple_conj_with_rule 
                                                            step_techn rule)))
      rst;


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* Use for comparison with underlying ordinary ripple techn            *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

fun ord_induct_and_ripple_with_rule rule rst = 
    RippleRTechn.induct_ripple_conj_with_rule rule rst;

end;*)
end; (* local *)

end; (* functor *)
