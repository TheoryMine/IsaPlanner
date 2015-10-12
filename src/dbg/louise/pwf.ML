fun get_ihs rst goal  = RippleCInfo.skeleton_names_of rst goal;

(* should produce a version that lifts all ihs*)
fun lift_hyp goal rst =
    let
      val (ihs as ih::_) = get_ihs rst goal;
      val ((ihc, ihh2s), pp2) = Prf.lift_and_show_above ih (RstPP.asms_of_goal rst ih) goal (RState.get_pplan rst);
    in
      ((ihc, ihh2s), RState.set_pplan pp2 rst)
    end;

(*
RState.T -> PPlan.gname -> (DB_APrf.gname * DB_APrf.gname list) * RState.T
val ((ihc, ihh2s), rst2) = lift_hyp rst "aa";
*)


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
val tmp2 = embeds_into2 thry rst2 "ad" ihh2s;
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
val tmp3 = embeds_into thry rst2 "ad" [ihc];
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


fun get_rstate_from_ih ih goal rst = (
    (case (Seq.list_of (RTechnEnv.apply_res ih goal rst)) of
       [] => NONE
     | lsts => SOME (lsts)));
(*
 PPlan.gname -> PPlan.gname -> RState.T -> RState.T list option
*)

fun rstates_from_ihs IHs goal rst =
    map_filter (fn h => (case (get_rstate_from_ih h goal rst) of
                           NONE => NONE
                         | SOME lsts => SOME(lsts, h))) IHs;

(*
PPlan.gname list ->
   PPlan.gname -> RState.T -> (RState.T list * PPlan.gname) list
rstates_from_ihs ihs "IsaP_split_ir" rst;
*)

fun rstates_can_be_fertilised goal1 goals rst =
    flat (map_filter (fn h => (case (rstates_from_ihs (get_ihs rst goal1) h rst) of
                           [] => NONE
                         | lst => 
                          SOME (map (fn (rs, ih) => (rs, h, ih)) lst)))
               goals);

(*
 PPlan.gname ->
   PPlan.gname list ->
   RState.T -> (RState.T list * PPlan.gname * PPlan.gname) list

rstates_can_be_fertilised "aa" (RState.get_goalnames rst) rst;
*)

fun hyp_to_open_goal_embeddings thry rst goal asms =
    map_filter
      (fn h =>
            (case (embeds_into2 thry rst h [goal]) of
               [] => NONE
             | (ihembs as _ :: _) => SOME (ihembs, h)))
        asms;

fun who_might_ripple thry rst =
    let
      val (goal::_) = RState.get_goalnames rst;
    in
      hyp_to_open_goal_embeddings thry rst goal (RstPP.asms_of_goal rst goal)
    end;

(*
Context.theory ->
   RState.T -> ((DB_Embed.T list * PPlan.gname) list * PPlan.gname) list
who_might_ripple thry rst3;
*)
(*
Context.theory ->
   RState.T ->
   PPlan.gname ->
   PPlan.gname list ->
   ((DB_Embed.T list * PPlan.gname) list * PPlan.gname) list

NB, get_curnames can be used to identify "af"
val tmp = hyp_to_open_goal_embeddings thry rst3 "af" (RstPP.asms_of_goal rst3 "af");
*)

fun simp_asm_full g rst = 
    RTechnEnv.apply_dtac_to_g (IsaDTac.simp_asm_full (Simplifier.simpset_of (RstPP.get_theory rst))) g rst;

fun try_forward_rippling thry rst =
    let
      val ((_, goal)::_, hyp)::_ = who_might_ripple thry rst;
    in
      ((RippleCInfo.start [(goal, RstPP.goal_concl rst goal)] ParamRGraph.empty hyp rst), hyp)
    end;


(*
Context.theory -> RState.T -> RState.T Seq.seq * PPlan.gname
 val (seq, hyp) =  (try_forward_rippling thry rst3);
*)

fun tmp goal rst ppl = map (fn g => 
                                                                                                 Prf.get_assumed_lthm ppl g)
                                                                                 (List.filter 
                                                                                                (fn g => null (Term.term_vars 
                                                                                                                                                                 (RstPP.goal_concl rst g)))
                                                                                                (PPlan.get_aasms ppl goal));

fun tmp2 goal rst ppl gname  = map (fn g => 
                                                                                                 Prf.get_assumed_lthm ppl g)
                                                                                 (List.filter 
                                                                                                (fn g => null (Term.term_vars 
                                                                                                                                                                 (RstPP.goal_concl rst g)))
                                                                                                (gname :: (PPlan.get_aasms ppl goal)));

fun simp_use_asms goal rst =  
                let 
                        val ppl = RState.get_pplan rst
                 (* get asumptions, excluding ones with meta-vars *)
                        val asms = map (fn g => 
                                                                                                 Prf.get_assumed_lthm ppl g)
                                                                                 (List.filter 
                                                                                                (fn g => null (Term.term_vars 
                                                                                                                                                                 (RstPP.goal_concl rst g)))
                                                                                                (PPlan.get_aasms ppl goal))
                        val simps = Simplifier.addsimps 
                                                                                (Simplifier.simpset_of (RstPP.get_theory rst),
                                                                                 asms)
                in
                        RTechnEnv.apply_dtac_to_g (IsaDTac.simp_no_asm simps) goal rst
                end;

fun simp_with_thms goal rst gname =  
                let 
                        val ppl = RState.get_pplan rst
                 (* get asumptions, excluding ones with meta-vars *)
                        val asms = map (fn g => 
                                                                                                 Prf.get_assumed_lthm ppl g)
                                                                                 (List.filter 
                                                                                                (fn g => null (Term.term_vars 
                                                                                                                                                                 (RstPP.goal_concl rst g)))
                                                                                                (gname :: (PPlan.get_aasms ppl goal)))
                        val simps = Simplifier.addsimps 
                                                                                (Simplifier.simpset_of (RstPP.get_theory rst),
                                                                                 asms)
                in
                        RTechnEnv.apply_dtac_to_g (IsaDTac.simp_no_asm simps) goal rst
                end;



(*
PPlan.gname -> RState.T -> RState.T Seq.seq
*)


fun mk_big_imp rst gname =
       let
           val list = RstPP.asms_of_goal rst gname
       in
           foldl (fn (gn, trm) => (Logic.mk_implies ((RstPP.goal_concl rst gn), trm))) (RstPP.goal_concl rst gname) list
       end; 

(* val mk_big_imp = fn : RState.T -> PPlan.gname -> Term.term *)

fun impify_asms rst =
    let
      val goals = RState.get_goalnames rst
    in
      flat (map (fn gn => (
              (map (fn asmn => (mk_big_imp rst asmn, gn)) (RstPP.lasms_of_goal rst gn))
          )) goals)
    end;

(*val impify_asms = fn : RState.T ->  (Term.term * PPlan.gname) *)

fun cex_asms rst =
    map (fn (term, gn) => ((CounterExCInfo.quickcheck_term (RstPP.get_theory rst) (CounterExCInfo_DB.codegen_params, []) term), gn)) (impify_asms rst);

(* val cex_asms = fn
: RState.T -> ((string * Term.term) list option * PPlan.gname) list *)

fun pick_res_goals rst =
    List.filter (fn (opt, gn) => (case opt of
                                    NONE => false 
                                  | (SOME cex) => true)) (cex_asms rst);

(* val pick_res_goals = fn
: RState.T -> ((string * Term.term) list option * PPlan.gname) LIST.list *)

fun pick_contr_goals rst =
    List.filter (fn (opt, gn) => (case opt of
                                    NONE => true 
                                  | (SOME cex) => false)) (cex_asms rst);

(* val pick_res_goals = fn
: RState.T -> ((string * Term.term) list option * PPlan.gname) LIST.list *)
