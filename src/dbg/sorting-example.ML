
use_thy "/Users/louiseadennis/Systems/IsaPlanner/IsaPlanner/src/examples/sorting";
val thry = theory "sorting";
val rippling = RippleLemCalc.induct_ripple_lemcalc;

(* val myrst = PPInterface.ipp thry (rippling "g") ("g","sorted(insort l)"); *)

val rst = PPInterface.ipp thry (rippling "g") ("g","sorted l ==> sorted(ins a l)");
val goal = "aa";
val IHs = RippleCInfo.skeleton_names_of rst goal;
(* hackery to fix wrong selected IH *)
(* val (rsts as (rst::_)) = Seq.list_of (RippleLemCalc.BasicRipple.startr_on_goal goal rst); *)

(* val IHs = ["ab"]; *)
(* val asms = RstPP.asms_of_goal rst "aa";
val asm_asm = RstPP.asms_of_goal rst "ab";
val asm_ad = RstPP.asms_of_goal rst "ad";
val ac_term = RstPP.goal_concl rst "ac";
val ad_term = RstPP.goal_concl rst "ad";

val embeddings = Seq.list_of
  (Embed.embed (Ectxt.init (InstEnv.init thry) ParamRGraph.empty)
  ac_term ad_term);

(* print embeddings *)
val _ = map Embed.print embeddings;
*)

(* find some embeddings between two terms *)
(* fun embeds_into3 thry hypothesis IHhyp =
    let
     val  embeddings = (Seq.list_of (Embed.embed (Ectxt.init (InstEnv.init thry) ParamRGraph.empty) IHhyp hypothesis))
    in
      (case embeddings of
      [] => NONE
      | (h :: t) => SOME embeddings)
end;*)

(* Context.theory -> Term.term -> Term.term -> DB_Embed.T list option *)
(* val tmp = embeds_into3 thry (RstPP.goal_concl rst "ad") (RstPP.goal_concl rst "ac"); *)

(* Find embeddings between a term and some hypotheses of induction hypotheses - filter out self-embeddings *)
fun embeds_into2 thry rst hypothesis IHhyps =
    map_filter 
      (fn h => 
          if (h = hypothesis) then NONE
          else
            (case Seq.list_of (Embed.embed (Ectxt.init (InstEnv.init thry) ParamRGraph.empty) 
                                           (RstPP.goal_concl rst h) (RstPP.goal_concl rst hypothesis))
              of [] => NONE
               | (embeddings as _ :: _) =>  SOME (embeddings, h)))
      IHhyps;
(*
 Context.theory ->
   RState.T ->
   PPlan.gname -> PPlan.gname list -> (DB_Embed.T list * PPlan.gname) list

 val tmp2 = embeds_into2 thry rst "ad" (RstPP.asms_of_goal rst "ab");
val tmp2 = embeds_into2 thry rst "h" (RstPP.asms_of_goal rst "h");
*)

(* find embeddings of a term into the hypotheses of a list of induction hypothesese, filter out
embeddings into its own hypotheses *)
fun embeds_into thry rst hypothesis IHs =
    map_filter
    (fn h =>
        if (h = hypothesis) then NONE
        else  (case (embeds_into2 thry rst hypothesis (RstPP.asms_of_goal rst h)) of
                 [] => NONE
               | (ehpairs as _ :: _) => SOME (ehpairs, h)))
    IHs;
(*

   Context.theory ->
   RState.T ->
   PPlan.gname ->
   PPlan.gname list ->
   ((DB_Embed.T list * PPlan.gname) list * PPlan.gname) list

val tmp3 = embeds_into thry rst "ad" IHs;
*)


fun embeddinghyps thry rst goal asms =
    let
      val IHs = RippleCInfo.skeleton_names_of rst goal;
    in
      map_filter
        (fn h =>
            (case (embeds_into thry rst h IHs) of
               [] => NONE
             | (ihembs as _ :: _) => SOME (ihembs, h)))
        asms
    end;
(*
   Context.theory ->
   RState.T ->
   PPlan.gname ->
   PPlan.gname list ->
   (((DB_Embed.T list * PPlan.gname) list * PPlan.gname) list * PPlan.gname)
   list

val tmp4 = embeddinghyps thry rst "aa" (RstPP.asms_of_goal rst "aa");
*)

fun extract_all_pwf_lemmas thry rst goal =
    let
      val pair_list = embeddinghyps thry rst goal (RstPP.asms_of_goal rst goal);
    in
      case pair_list of 
        [] => NONE
      | (list as _ :: _) => SOME
                            (maps (fn (ihl, hyp) =>
                                     (maps (fn (ihhl, ih) =>
                                                    (map (fn (emb, ihh) => 
                                                             (Logic.mk_implies ((RstPP.goal_concl rst hyp), (RstPP.goal_concl rst ihh))))
                                                         ihhl))
                                                ihl))
                                 list)
end;



(*
 Context.theory ->
   RState.T -> PPlan.gname -> Term.term list option
val tmp5a = extract_all_pwf_lemmas thry rst "aa";
*)

fun extract_pwf_lemma_from thry rst goal =
    let
      val pair_list = embeddinghyps thry rst goal (RstPP.asms_of_goal rst goal);
    in
      case pair_list of 
        [] => NONE
      | (((((e, ihh)::t1), ih)::t2, h) :: t) => SOME (Logic.mk_implies ((RstPP.goal_concl rst h), (RstPP.goal_concl rst ihh)))
    end; 
(*
Context.theory ->
   RState.T -> PPlan.gname -> Term.term option
val tmp5 = extract_pwf_lemma_from thry rst "aa";
*)

(* val newconj = Logic.mk_implies ((RstPP.goal_concl rst "ad"), (RstPP.goal_concl rst "ac")); *)

(* Debugging stuff to place iwht new_conj *)
(*fun tfun thry rst goal = 
    case (extract_pwf_lemma_from thry rst goal) of
      SOME t => t;

val newterm = tfun thry rst "aa";

val (lemmaname, rst2) =  RstPP.new_conj_at ("newlemma", newterm) "aa" rst; *)

fun extract_hyp_ih_pair thry rst goal =
    let
      val pair_list = embeddinghyps thry rst goal (RstPP.asms_of_goal rst goal);
    in
      case pair_list of 
        [] => NONE
      | (list as _ :: _) => SOME
                            (maps (fn (ihl, hyp) =>
                                     (maps (fn (ihhl, ih) =>
                                                    (map (fn (emb, ihh) => 
                                                             (hyp, ihh, ih))
                                                         ihhl))
                                                ihl))
                                 list)
end;

(*

 Context.theory ->
   RState.T ->
   PPlan.gname -> (PPlan.gname * PPlan.gname * PPlan.gname) list option

val tmp6 = extract_hyp_ih_pair thry rst "aa";
*)


val pp = RState.get_pplan rst;
val ((ihc2, ihh2s), pp2) = Prf.lift_and_show_above "ab" ["ac"] "aa" pp;

val rst2 = RState.set_pplan pp2 rst;

fun simp_asm_full g rst = 
                RTechnEnv.apply_dtac_to_g (IsaDTac.simp_asm_full (Simplifier.simpset_of (RstPP.get_theory rst))) g rst;

(* PPlan.gname -> RState.T -> RState.T Seq.seq *)

val (rst3::_) = Seq.list_of (simp_asm_full (hd ihh2s) rst2);

local open RTechnEnv
fun start_ripplingN goal = 
    RstName.chunks [RstName.str "Start Rippling with state: ",
                    (fn rst => RippleCInfo.pretty_skels rst goal)];
 in
fun start_newr_on_goal skelnames goal rst = 
    let 
      val skels = map (fn n => (n,Prf.get_ndname_ctrm (RState.get_pplan rst) n)) skelnames;
    in
      rst |> RState.set_rtechn NONE
          |> (givename (start_ripplingN goal)
                       (RippleCInfo.start skels ParamRGraph.empty goal))
    end;
end;

val (rst4 :: _) = Seq.list_of (start_newr_on_goal [ihc2] goal rst3);

val rst5 = RState.set_rtechn (SOME (RippleCaseSplit.rsteps_on_goal goal)) rst4;

raise ERROR "stop here. ";

(* trace to if-split point, rippling gets blocked *)
val rst5' = PPInterface.ipp_rst rst5;

val g = "IsaP_split_ir";
val [dtac1] = Seq.list_of (RippleCInfo.applicable_dtacseq_of rst5' g);

val p = RState.get_pplan rst5';
Prf.print p;

val p2s = DTac.gtac dtac1 (([],[g]),ppl);
val [((sgs,fwds),p2)] = Seq.list_of p2s;

((["IsaP_split_it"], ["IsaP_split_it"]), ?)

val [rst6] = Seq.list_of (RTechnEnv.apply_dtac_to_g dtac1 goal rst5');


RippleCInfo.print rst5 "aa";

val [dtac1,dtac2] = Seq.list_of (RippleCInfo.applicable_dtacseq_of rst5 goal);
val [rst6] = Seq.list_of (RTechnEnv.apply_dtac_to_g dtac2 goal rst5);

val [rst7] = Seq.list_of (RippleCInfo.update_from_goal "aa" "ag" rst6);

PolyML.exception_trace (fn () => RippleCInfo.print rst7 "ag");

raise ERROR "stop here. ";

val [skel0] = RippleCInfo.skels_of rst7 "aa";
val [embedding0] = RippleSkel.get_embeddings skel0;
InstEnv.print (Embed.get_ienv embedding0);
val eterm = Embed.get_eterm embedding0;
val t = Embed.mk_prettyterm embedding0;

val skels_nts = RippleCInfo.skeleton_namedterms_of rst7 "aa";

val [skel] = RippleCInfo.skels_of rst7 "ag";
val [embedding] = RippleSkel.get_embeddings skel;

InstEnv.print (Embed.get_ienv embedding);
val eterm = Embed.get_eterm embedding;

RippleCInfo.print rst6 "ag";
    );

(*
val pp = RState.get_pplan rst3;
val SOME (((sgs,factname),ppl2),more) =
     (Seq.pull (PPlan.apply_res_fwd ("ac","ab") "newlemma" pp));

fun tmpfun g1 g2 g3 pp = Seq.pull (PPlan.apply_res_fwd (g1, g2) g3 pp);
fun tmpfun2 g1 g2 g3 pp = 
    case (tmpfun g1 g2 g3 pp) of
      NONE => []
    | SOME (ih, seq) => [(ih, Seq.list_of seq)];

Prf.print ppl2;
*)
