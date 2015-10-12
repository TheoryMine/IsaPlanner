(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      cinfo/rippling/ripple_cinfo.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    15 Mar 2003
    Modified:   Dominic Mulligan
                12th Sept 2007
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Contextual-information for performing rippling. The main purpose
    of this is to manage multiple skeletons, and tie together the
    database of wave rules to the process of rippling. Furthermore, we
    manage the overall ripppling process and provide information on
    matching rules.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RRIPPLE_CINFO = 
  sig
    type T
    type wruleT = RippleWRules.wrule;

    structure RRippleSkel : RRIPPLE_SKEL;

    structure I : LOCAL_INFO_ITEM where type T = T

    exception rrippling_cinfo_exp of string;
    exception rrippling_cinfo2_exp of ((string * Term.term) list * Term.term); (* skel * tgt *)

    (* working with rippling cinfo: starting/updating *)
    val start_i : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                      (string * Term.term) list -> PPlan.T -> PPlan.gname -> bool -> (PPlan.gname * T) list
    val start : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                    (string * Term.term) list -> bool -> PPlan.gname list -> RState.T -> RState.T Seq.seq
    val start_rev : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                        (string * Term.term) list -> bool -> RState.T -> RState.T Seq.seq

    val update_i : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                       ((string * Term.term) * RRippleSkel.T option) list -> PPlan.T -> PPlan.gname -> bool -> (PPlan.gname * T) list
    val update : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                      ((string * Term.term) * RRippleSkel.T option) list -> bool -> RState.T -> RState.T Seq.seq
    val update_all_i : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                           ((string * Term.term) * RRippleSkel.T option) list -> PPlan.T -> PPlan.gname -> bool -> (PPlan.gname * T) list
    val update_all : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                         ((string * Term.term) * RRippleSkel.T option) list -> bool -> RState.T -> RState.T Seq.seq
    val update_midout : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                            ((string * Term.term) * RRippleSkel.T option) list -> RRippleSkel.RRippleMeasure.T -> bool -> RState.T -> RState.T Seq.seq

    (* Update that can fire skeleton critic if no embeddings found. *)
    val update_skel_crit : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                               ((string * Term.term) * RRippleSkel.T option) list -> bool -> RState.T -> RState.T Seq.seq

    (* Update for rippling-in-reverse that allow rules to introduce vars.*)
    val update_rev : (string * ModalityInfo.GoalModeInfo) list -> (Term.term list * PPlan.gname) list RelationTab.table -> InstEnv.T ->
                         ((string * Term.term) * RRippleSkel.T option) list -> bool -> RState.T -> RState.T Seq.seq

    (* do we have some valid embedding for rippling *)
    val is_valid_ripple_state_i : T -> bool
    val is_valid_ripple_state_goal : RState.T -> PPlan.gname -> bool
    val some_curgoal_is_ripple_valid : RState.T -> bool
    (* we are blocked given possible nest states *)
    val blocked1_chk_i : T -> T list -> bool
    val blocked_chk : RState.T -> PPlan.gname -> RState.T list -> bool
    (* are we trying to ripple, even if we don't have any embeddings *)
    val is_rippling_i : T -> bool
    val is_rippling : RState.T -> PPlan.gname -> bool
    val some_curgoal_is_rippling : RState.T -> bool 
    (* is this goal's rippling successfull *) 
    val success_chk : RState.T -> PPlan.gname -> bool

    (* skeletons and measures *)
    val skels_of_i : T -> RRippleSkel.T list
    val skels_of : RState.T -> PPlan.gname -> RRippleSkel.T list

    val skeleton_namedterms_of_i : T -> (string * Term.term) list
    val skeleton_namedterms_of : RState.T -> PPlan.gname -> (string * Term.term) list
    val skeleton_names_of : RState.T -> PPlan.gname -> string list

    (* skeletons from all current rippling goals *)
    val all_skels_of_i : T -> ((string * Term.term) * RRippleSkel.T option) list
    val all_skels_of : RState.T -> PPlan.gname -> ((string * Term.term) * RRippleSkel.T option) list

    val measures_of_i : T -> RRippleSkel.RRippleMeasure.T list
    val measures_of : RState.T -> PPlan.gname -> RRippleSkel.RRippleMeasure.T list

    val has_embedding :  RState.T -> PPlan.gname -> bool
    
    val inst_skels_terms : RState.T -> PPlan.gname -> Term.term list

    (* applicable rules *)
    val applicable_dtacs_of_i : T -> DTac.T list
    val applicable_dtacs_of :  RState.T -> PPlan.gname -> DTac.T list
    val applicable_dtacseq_of_i : T -> DTac.T Seq.seq
    val applicable_dtacseq_of : RState.T -> PPlan.gname -> DTac.T Seq.seq

    val applicable_critics_of:  RState.T -> PPlan.gname -> RTechn.T list                                                            
    (* pretty printing *)
    val pretty_i : Proof.context -> T -> Pretty.T
    val pretty : RState.T -> PPlan.gname -> Pretty.T

    val pretty_skels_i : Proof.context -> T -> Pretty.T
    val pretty_skels : RState.T -> PPlan.gname -> Pretty.T
    (* pretty skeletons from the current rippling goals *)
    val pretty_curgoals_skels : RState.T -> Pretty.T

    val pretty_applicable_rules_i :  T -> Pretty.T
    val pretty_applicable_rules : RState.T -> PPlan.gname -> Pretty.T
    val print_applicable_rules : RState.T -> PPlan.gname -> unit

    (* internal/for debugging -- (int, thm) are subgoal and theorem *)
    val lookup_arules :  PPlan.T -> PPlan.gname -> bool -> DTac.T list
    
    val set_skels_i : ((string * Term.term) * RRippleSkel.T option) list -> T -> T
    val set_arules_i : DTac.T list -> T -> T
    val set_gmi_i : (string * ModalityInfo.GoalModeInfo) list -> T -> T;
    val set_rtab_i : (Term.term list * PPlan.gname) list RelationTab.table -> T -> T
    val set_instenv_i : InstEnv.T -> T -> T

end;


(* Contextual information for Rippling *)
functor RRippleCInfoFUN (RRippleSkel : RRIPPLE_SKEL) :> RRIPPLE_CINFO =
  struct

    structure RRippleSkel = RRippleSkel;

    exception rrippling_cinfo_exp of string;
    exception rrippling_cinfo2_exp of ((string * Term.term) list * Term.term); (* tgt *)

    type wruleT = RippleWRules.wrule;

    (* FIXME: make a clear notion of uninitialised cinfo - otherwsie
       failure to initialise it will be hard to debug. *)
    datatype T = rcinfo of { arules : DTac.T list, skels : ((string * Term.term) * RRippleSkel.T option) list,
                             rtab : (Term.term list * PPlan.gname) list RelationTab.table, instenv: InstEnv.T,
                             gmi : (string * ModalityInfo.GoalModeInfo) list };

    (* Return the skeletons that currently embedd *)
    fun select_valid_skels skels = (* clever filter for option lists *)
      List.mapPartial I (map snd skels);

    fun skels_of_i (rcinfo rep) = select_valid_skels (#skels rep);

    fun all_skels_of_i (rcinfo rep) = (#skels rep);

    fun applicable_dtacs_of_i (rcinfo rep) = #arules rep; 
    val applicable_dtacseq_of_i = Seq.of_list o applicable_dtacs_of_i;

    fun update_skels_i f (rcinfo rep) = 
      rcinfo { skels = f (#skels rep), 
               arules = #arules rep,
               rtab = #rtab rep,
               instenv = #instenv rep,
               gmi = #gmi rep };
    fun update_arules_i f (rcinfo rep) = 
      rcinfo { skels = #skels rep, 
               arules = f (#arules rep),
               rtab = #rtab rep,
               instenv = #instenv rep,
               gmi = #gmi rep };
    fun update_rtab_i f (rcinfo rep) =
      rcinfo { skels = #skels rep,
               arules = #arules rep,
               rtab = f (#rtab rep),
               instenv = #instenv rep,
               gmi = #gmi rep };
    fun update_instenv_i f (rcinfo rep) =
      rcinfo { skels = #skels rep,
               arules = #arules rep,
               rtab = #rtab rep,
               instenv = f (#instenv rep),
               gmi = #gmi rep };
    fun update_gmi_i f (rcinfo rep) =
      rcinfo { skels = #skels rep,
               arules = #arules rep,
               rtab = #rtab rep,
               instenv = #instenv rep,
               gmi = f (#gmi rep) };

    val set_skels_i = update_skels_i o K;
    val set_arules_i = update_arules_i o K;
    val set_rtab_i = update_rtab_i o K;
    val set_instenv_i = update_instenv_i o K;
    val set_gmi_i = update_gmi_i o K;

    (* pretty printing *)
    fun pretty_skels_i ctxt d =
      (case (skels_of_i d) of 
         [] => Pretty.str "No valid skeletons."
       | l => Pretty.chunks (map (RRippleSkel.pretty ctxt) l));

    fun pretty_applicable_rules_i d =
      Pretty.chunks (map DTac.pretty (applicable_dtacs_of_i d));

    fun pretty_rtab (rcinfo d) = (RRippleLinkInfo.pretty 
                                    (ProofContext.init (the_context ())) (#rtab d))

    fun pretty_gmis (rcinfo d) = (ModalityInfo.pretty_gmis (#gmi d))

    fun pretty_instenv (rcinfo d) = (InstEnv.pretty (#instenv d))

(*
  fun pretty_measuredec_rules ctxt d =
      Pretty.chunks 
        (map (DTac.pretty_of ctxt) f** (applicable_dtacs_of d));
  fun pretty_measuredec_rules rst =
      pretty_applicable_rules (RstPP.top_ctxt rst) (I.get_from_rst rst);
  val pretty_measuredec_rules =
      Pretty.writeln o pretty_applicable_rules_rst;
*)

    fun pretty_i ctxt d = 
      Pretty.chunks
        [Pretty.str "Ripple Skeleton States: ", pretty_skels_i ctxt d,
         Pretty.str "Applicable Rules: ", pretty_applicable_rules_i d,
         Pretty.str "Relation tab: ", pretty_rtab d,
         Pretty.str "GMIs: ", pretty_gmis d,
         Pretty.str "Instantiation environment: ", pretty_instenv d];

  (* contextual info sturcture *)
(* Information associated with goals in reasoning states during rippling *)
    structure I = LocalInfoFUN( 
      struct
        type T = T;
        val name = "local rrippleinfo:" ^ RRippleSkel.name;
        val copy = I;
        val pretty = (fn d => fn rst => 
          let
      val ctxt = Prf.get_context (RState.get_pplan rst)
    in
            pretty_i ctxt d
    end); (* print only rules *)
      end);

    fun init gmi gname rst =
      I.put (gname, set_gmi_i gmi (I.get rst gname)) rst

    fun pretty_applicable_rules rst goal = pretty_applicable_rules_i (I.get rst goal);
    fun print_applicable_rules rst goal = Pretty.writeln (pretty_applicable_rules rst goal);

    fun pretty rst goal = pretty_i (RstPP.get_ctxt rst) (I.get rst goal);
    fun pretty_skels rst goal = pretty_skels_i (RstPP.get_ctxt rst) (I.get rst goal);
    fun pretty_curgoals_skels rst = Pretty.chunks (RstPP.map_cur_goals pretty_skels rst);

    (* managing skeletons *)
    (* implicit T *)
    val skeleton_namedterms_of_i =  map RRippleSkel.named_skel_term_of o skels_of_i; 
    val skeleton_namedterms_of = skeleton_namedterms_of_i oo I.get;
    val skeleton_names_of = (map fst) oo skeleton_namedterms_of;

    (* implicit: rst gname *)
    val skels_of = skels_of_i oo I.get;
    val all_skels_of = all_skels_of_i oo I.get;

    val measures_of_i = maps RRippleSkel.measures_of o skels_of_i;
    fun measures_of rst gname = 
      case (I.get_opt rst gname) of 
        NONE => []
      | SOME info => measures_of_i info;

    fun has_embedding rst gname = Option.isSome (I.get_opt rst gname);

  (* Return a version of this skeleton with sinks instantiated to 
   their current contents. Might get duplicates, so remove these.*)
    fun inst_skels_terms rst gname =
      map (RRipplingATerms.inst_skel_term o RRippleSkel.RRippleMeasure.aterm_of) (measures_of rst gname)
            |> Library.distinct (fn (skl1,skl2) => Trm.trm_name_eq skl1 skl2);

  (* all skels are blocked w.r.t all possible new skels. *)
  fun blocked1_chk_i d nextds = 
      let val sts = maps skels_of_i nextds
        val curskels = skels_of_i d
      in
  List.all (fn st => RRippleSkel.blocked_chk st sts) curskels
      end;

  (* A rst is blocked if every child goal of every child-rst is blocked. *)
  fun blocked_chk rst goal rsts =
    let (* Get the ripplecinfos of the subgoals that are rippling them. 
           Can can ignore goals that have any ripple info *)
      fun infolist rst = 
  map_filter (I.get_opt rst) (RState.get_goalnames rst);
    in
      (List.all (fn st => (blocked1_chk_i (I.get rst goal) (infolist st))) rsts)
    end;

  (* get the applicable rules *)                       
  fun applicable_dtacs_of rst goal = applicable_dtacs_of_i (I.get rst goal);
  fun applicable_dtacseq_of rst goal = applicable_dtacseq_of_i (I.get rst goal); 

  (* get applicable critics during rippling, eg case-splitting *)
  fun applicable_critics_of rst goal = 
    if (SplitterRTechn.is_if rst goal) then
      [(RTechnEnv.map_then SplitterRTechn.split_if_rtechn)]
    else [];

  (* check to see if we are rippling ie have some skeleton that embeds *)
  (* implicit T *)
  val is_valid_ripple_state_i = not o null o skels_of_i;
  fun is_valid_ripple_state_goal rst goal = 
    case (I.get_opt rst goal) of
      NONE => false
    | SOME ripple_info => is_valid_ripple_state_i ripple_info;
  val some_curgoal_is_ripple_valid = RstPP.forsome is_valid_ripple_state_goal;

  (* Checks if this state has any skeletons, regardless of if they embedd *)
  val is_rippling_i = not o null o all_skels_of_i;
  fun is_rippling rst goal = 
    case (I.get_opt rst goal) of
      NONE => false
    | SOME ripple_info => is_rippling_i ripple_info;
  val some_curgoal_is_rippling = RstPP.forsome is_rippling;

  (* check to see if any skeleton has been rippled out
  completely, if so we can apply that assumption and solve the goal. *)
  (* implicit T *)
  val success_chk_i = List.exists RRippleSkel.success_chk o skels_of_i;
  fun success_chk rst goal = success_chk_i (I.get rst goal);

  (* lookup all rules and tehir aplication to the pplan. IMPROVE:
  rules should come from local contextual info: that we we can add to
  wave rules locally within a proof planning attempt *)
  fun lookup_arules pplan gname flag = 
    if flag then
      let
        val db = RippleThyInfo.wrules_of_ctxt (PPlan.get_context pplan)
        val t = Prf.get_ndname_ctrm pplan gname
        (* val eqs = RippleWRules.eqrule_zipper_lookup db pplan gname (Zipper.mktop t)
        val imps = RippleWRules.imprule_concl_lookup db pplan gname t *)
        val fwd_imps = RippleWRules.fwd_imprule_prems_lookup db pplan gname t
        (* val inv_eqs = RippleWRules.eqrule_zipper_lookup_inv db pplan gname (Zipper.mktop t) *)
      in
          (* (map (fn (imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_impwrule_sml imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of imps))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
       (K (Seq.single st)))) (Seq.list_of eqs))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
             (K (Seq.single st)))) (Seq.list_of inv_eqs))
     @ *)
          (map (fn (fwd_imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_fwd_impwrule_sml fwd_imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of fwd_imps))
      end
    else
      let
        val db = RippleThyInfo.wrules_of_ctxt (PPlan.get_context pplan)
        val t = Prf.get_ndname_ctrm pplan gname
        val eqs = RippleWRules.eqrule_zipper_lookup db pplan gname (Zipper.mktop t)
        val imps = RippleWRules.imprule_concl_lookup db pplan gname t
        (* val fwd_imps = RippleWRules.fwd_imprule_prems_lookup db pplan gname t *)
      in
          (map (fn (imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_impwrule_sml imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of imps))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
       (K (Seq.single st)))) (Seq.list_of eqs))
     (* @
          (map (fn (fwd_imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_impwrule_sml fwd_imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of fwd_imps)) *)
      end

  (* Lookup that includes rules not normally allowed, such as those
     introducing new variables. Reverse rippling needs this. *)
  fun lookup_arules_rev pplan gname flag =
    if flag then
      let
        val db = RippleThyInfo.wrules_of_ctxt (PPlan.get_context pplan)
        val t = Prf.get_ndname_ctrm pplan gname
        (* val eqs = RippleWRules.eqrule_zipper_lookup db pplan gname (Zipper.mktop t)
        val imps = RippleWRules.imprule_concl_lookup db pplan gname t *)
        val fwd_imps = RippleWRules.fwd_imprule_prems_lookup db pplan gname t
        (* val inv_eqs = RippleWRules.eqrule_zipper_lookup_inv db pplan gname (Zipper.mktop t) *)
      in
          (* (map (fn (imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_impwrule_sml imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of imps))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
       (K (Seq.single st)))) (Seq.list_of eqs))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
             (K (Seq.single st)))) (Seq.list_of inv_eqs))
     @ *)
          (map (fn (fwd_imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_fwd_impwrule_sml fwd_imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of fwd_imps))
      end
    else
      let
        val db = RippleThyInfo.wrules_of_ctxt (PPlan.get_context pplan)
        val t = Prf.get_ndname_ctrm pplan gname
        val eqs = RippleWRules.eqrule_zipper_lookup db pplan gname (Zipper.mktop t)
        val imps = RippleWRules.imprule_concl_lookup db pplan gname t
        (* val fwd_imps = RippleWRules.fwd_imprule_prems_lookup db pplan gname t *)
        val inv_eqs = RippleWRules.eqrule_zipper_lookup_inv db pplan gname (Zipper.mktop t)
      in
          (map (fn (imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_impwrule_sml imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of imps))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
       (K (Seq.single st)))) (Seq.list_of eqs))
           @ 
          (map (fn (wrule,st) => DTac.mk (RippleWRules.pretty_wrule wrule, 
             (K (Seq.single st)))) (Seq.list_of inv_eqs))
     (* @
          (map (fn (fwd_imprule,(subgoals,pplan)) => DTac.mk (RippleWRules.pretty_impwrule_sml fwd_imprule, 
        K (Seq.single (([],subgoals),pplan)))) (Seq.list_of fwd_imps)) *)
      end

  (* lists with one of each list of list of lists *)
  fun one_of_each [] = []
    | one_of_each [[]] = []
    | one_of_each [(h::t)] = [h] :: (one_of_each [t])
    | one_of_each ([] :: xs) = []
    | one_of_each ((h :: t) :: xs) = 
        (map (fn z => h :: z) (one_of_each xs)) @ (one_of_each (t :: xs));

  (* IMPROVE: optimise inclusion of RippleSkel, ie creating the list of
   skeleton embeddings... *)

  (* create the initial possible rippling contextual informations given the 
  skeletons (name, term) pairs and the target *)
  fun start_i gmi rtab instenv skels pplan goal flag = 
    let
      val goalterm = RRTrmUtil.drop_meta_var_args (Prf.get_ndname_ltrm pplan goal)
      val skellists = one_of_each
    (* Produce lists of states for each skeleton and combine them *)
          (map (fn (n,t) =>
    case RRippleSkel.init rtab instenv {skelterm=t, skelname=n, target=goalterm} flag
     (* skeleton does not currently embedd *)
     of [] => [((n,t), NONE)] 
      | (l as _::_) => map (fn e => ((n,t), SOME e)) l) skels)
    
    (* Check if any skeleton embed..*)
      val _ = if null (filter (fn skel => case skel of NONE => false | SOME _ => true) 
            (map snd (flat skellists)) ) then 
    (writeln "NONE of the skeletons embed into the goal!";
                 raise rrippling_cinfo2_exp (skels,goalterm))
              else ();
      val arules = lookup_arules pplan goal flag
    in
      map (fn sts => (goal, rcinfo { arules = arules, skels = sts, rtab = rtab, instenv = instenv, gmi = gmi })) skellists
    end;

  (* Each 'info' in the list belongs to a subgoal of the rst *)
  fun put_all_in rst []  = rst
    | put_all_in rst (info::t) =
        put_all_in (I.put info rst) t

  (* Make a list of lists of all combinations of embeddings for the goals in the
     reasoning state. Create a new rst for each such combo.*)
  fun start gmi rtab instenv skels flag fwdprf rst =       
    if not flag then
      let  
        val goal_embs = one_of_each (map (fn x => start_i gmi rtab instenv skels (RState.get_pplan rst) x flag) (RState.get_goalnames rst))
      in
        Seq.map (put_all_in rst) (Seq.of_list goal_embs)
      end
    else
      let
        val ppl = RState.get_pplan rst
        val tgts =  (filter (not o (IndPrf.assm_is_indhyp ppl)) (maps (Prf.get_ndname_lasms ppl) (filter (IndPrf.goal_is_stepcase ppl) fwdprf)))
        val goal_embs = one_of_each (map (fn x => start_i gmi rtab instenv skels ppl x flag) tgts)
      in
        Seq.map (put_all_in rst) (Seq.of_list goal_embs)
      end    

(* Start rippling in reverse, assuming we rippeled normally before. *)
  fun start_rev_i gmi rtab instenv skels pplan goal flag = 
    let 
      val goalterm = Prf.get_ndname_ctrm pplan goal 
      val skellists = one_of_each (* Produce lists of states for each skeleton and combine them *)
  (map (fn (n,t) =>
    case RRippleSkel.init rtab instenv { skelterm = t, skelname = n, target = goalterm } flag (* skeleton does not currently embedd *) of
      [] => [((n,t), NONE)] 
    | (l as _::_) => map (fn e => ((n,t), SOME e)) l) skels)

        (* Check if any skeleton embed..*)
      val _ = if null (filter (fn skel => case skel of NONE => false | SOME _ => true) (map snd (flat skellists)) ) then 
  (writeln "NONE of the skeletons embed into the goal!"; raise rrippling_cinfo2_exp (skels,goalterm))
              else ();
      val arules = lookup_arules_rev pplan goal flag
    in
      map (fn sts => (goal, rcinfo { arules = arules, skels = sts, rtab = rtab, gmi = gmi, instenv = instenv })) skellists
    end;

  fun start_rev gmi rtab instenv skels flag rst =
    let  
      val goal_embs = one_of_each (map (fn x => start_rev_i gmi rtab instenv skels (RState.get_pplan rst) x flag) (RState.get_goalnames rst))
    in
      Seq.map (put_all_in rst) (Seq.of_list goal_embs)
    end;
  
  (* update *)
  fun update_i gmi rtab instenv oldskels pplan newgname flag = 
    let
      val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
      val arules2 = lookup_arules pplan newgname flag
    in 
      (select_valid_skels oldskels)
        (* filter: keep only mes decreasing skels *)
        |> (Library.map_filter 
       (fn s => case RRippleSkel.mk_next rtab instenv newgoalterm s of
      [] => NONE | (l as _::_ ) => SOME (map (fn e => (RRippleSkel.named_skel_term_of e, SOME e)) l)))
        |> one_of_each
        |> map (fn sts2 => (newgname, rcinfo { arules = arules2, skels = sts2, rtab = rtab, instenv = instenv, gmi = gmi }))
        (* filter out cases where nothing embeds *)
        |> List.filter (is_valid_ripple_state_i o snd)
        (*|> fn l => if null l then delete_rcinfo newgname 
                                             delete if no embeddings*)
    end;

(* Update the reasoning state by finding embeddings for the new goals.
 A rippleCinfo is created for all goals that embedd. Reasoning states 
 are created for different combinations when several embeddings exist.
 Goals that do not embedd arenot given a ripplecinfo entry. If no goal
 embedd an empty sequece is returned.*) 
  fun update gmi rtab instenv oldskels flag rst = 
    (RState.get_goalnames rst)
    |> map (fn x => update_i gmi rtab instenv oldskels (RState.get_pplan rst) x flag)
    |> filter (not o null)
    |> one_of_each
    |> Seq.of_list
    |> Seq.map (put_all_in rst);


(* Update functions for doing rippling with middle-out rewriting,
i.e. in the presence of meta-variables that might stand
for extra term structure. Here, we copute the measure based
on the optimistic assumption that the meta-variables will just
be projections. A term is measure decreasign if its projection
has a better measure than the last normal ripple *)


  fun update_midout_i gmi rtab instenv oldskels mes_thld pplan newgname newgoalterm flag = 
    let
      val arules2 = lookup_arules pplan newgname flag
    in 
      (select_valid_skels oldskels)
  (* filter: keep only if not worse than treshold. *)
      |> (Library.map_filter (fn s =>
              case RRippleSkel.mk_thld_next rtab instenv newgoalterm mes_thld s of
          [] => NONE
        | (l as _::_ ) => SOME (map (fn e => (RRippleSkel.named_skel_term_of e,  SOME e)) l)))
        |> one_of_each
        |> map (fn sts2 => (newgname, rcinfo { arules = arules2, skels = sts2, gmi = gmi, rtab = rtab, instenv = instenv }))
        (* filter out cases where nothing embeds *)
        |> List.filter (is_valid_ripple_state_i o snd)
    end;

(* NOTE: Many projections of a goal might be OK, but at this stage we don't care.
         So, all we need is ONE projection per goal that embedds *)
  fun update_midout gmi rtab instenv oldskels mes_thld flag rst =
    let 
      val pplan = RState.get_pplan rst
      fun take_fst_emb goal = 
        let
          val mesrs = maps (fn x => update_midout_i gmi rtab instenv oldskels mes_thld pplan goal x flag) (Seq.list_of (LemmaSpec.proj_trms_pplan instenv pplan goal))
        in
    mesrs
            (*case mesrs of [] => []
                        | m::ms => [m] *)
  end;
    in
      (RState.get_goalnames rst)
      |> map take_fst_emb
      (*Get rid of [] from goals that don't embedd*)
      |> filter (not o null)
      |> one_of_each
      |> Seq.of_list
      |> Seq.map (put_all_in rst)
    end;


(* Update without filtering out non-measure decreasing skels*)
  fun update_all_i gmi rtab instenv oldskels pplan newgname flag = 
    let 
      (* Create embedding for this skeleton if it has any in the current target. *)
      fun does_embed (n,t) target =
  (case RRippleSkel.init rtab instenv { skelterm = t, skelname = n, target = target} flag of (* If this skeleton does not embedd at the moment *)
           [] => [((n,t), NONE)] 
  | (l as _::_) => map (fn e => ((n,t), SOME e)) l);
      val arules2 = lookup_arules pplan newgname flag
      val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
    in
      oldskels
      |> (map (fn ((n,t), skel) => case skel (* No previous embedding, check if embedds in new target *) of NONE => does_embed (n,t) newgoalterm
               (* The skeleton did embed previously, get new skels *)    | SOME skeleton => 
        case RRippleSkel.mk_all_next rtab instenv newgoalterm skeleton of
    [] => [((n,t), NONE)]        
  | (l as _::_) => map
      (fn e => (RRippleSkel.named_skel_term_of e, SOME e)) l ))
            |> one_of_each
            |> map (fn sts2 => (newgname, rcinfo { arules = arules2, skels = sts2, gmi = gmi, rtab = rtab, instenv = instenv }))
        (*  no filter: keep all skels *)
    end;
    
  fun update_all gmi rtab instenv oldskels flag rst = 
    (RState.get_goalnames rst)
    |> map (fn x => update_all_i gmi rtab instenv oldskels (RState.get_pplan rst) x flag)
    |> filter (not o null)
    |> one_of_each
    |> Seq.of_list
    |> Seq.map (put_all_in rst);

(* Update function that can call critic that modifies
   skeleton if no current skel embed. *)
  val mes_order = RRippleSkel.RRippleMeasure.ord;
  fun best_mes e = hd (Library.sort mes_order (RRippleSkel.measures_of e));

  (* Create embedding for this skeleton if it has any in the new target. MOVE: to ripple skel. Remove non mes-decr embeddings*)
  fun does_embed rtab instenv (n,t) target oldm flag =
    (case RRippleSkel.init rtab instenv { skelterm = t, skelname = n, target = target} flag of 
       (* If this skeleton does not embedd at the moment *)
       [] => [((n,t), NONE)] 
     | (l as _::_) => map (fn e => 
                            if (mes_order (oldm, (best_mes e)) = GREATER) then
                              ((n,t), SOME e)
                            else
            ((n,t), NONE)) l);

(* Reason fwd from oldskels to modify and find embedding *)
  fun skel_critic_i gmi rtab instenv oldskels goal flag rst =
    let
      val pplan = RState.get_pplan rst        
      val newgoalterm = Prf.get_ndname_ctrm pplan goal
      val db = RippleThyInfo.wrules_of_ctxt (PPlan.get_context pplan)
      val oldm = hd (Library.sort mes_order (map best_mes (select_valid_skels oldskels)));
      val eq_skels = 
          maps (fn ((n,t), emb) => 
                   (RippleWRules.eqrule_zipper_lookup db pplan n (Zipper.mktop t)) |> Seq.list_of) oldskels
                     
      fun nw_eqskels flag = 
          maps (fn (wr,((fwd_gs,oth_gs),ppl)) =>
            map (fn g => (ppl, does_embed rtab instenv (g, Prf.get_ndname_ctrm ppl g) newgoalterm oldm flag)) fwd_gs) eq_skels

      fun filt_skels flag = 
          (nw_eqskels flag)
            |> map (fn (ppl,skels) => 
                       (ppl,(filter (fn ((n,t),emb) => is_some emb) skels))) 
            |> filter (not o null o snd)

      fun skls flag = 
          (filt_skels flag)
            |> (map (fn (ppl,sts2) => 
                        (ppl,(goal, rcinfo { arules = lookup_arules ppl goal flag, skels = sts2, rtab = rtab, instenv = instenv, gmi = gmi }))))
    in
      (* Possibly efficency consideration, only allow for one new skel
         choose the one with the best measure or something *)
      (skls flag)       
      |> map (fn (ppl,info) =>  I.put info (RState.set_pplan ppl rst))
      |> Seq.of_list
    end;

  fun skel_critic gmi rtab instenv oldskels flag rst = 
    (RTechnEnv.givename 
    (RstName.str "Skeleton Critic: Trying to modify the skeleton")
    (RTechnEnv.map_then (fn x => skel_critic_i gmi rtab instenv oldskels x flag))) rst;

(* Can get outcomes:
- A list with rcinfos if we have some embedding. In this list the 'skel' entry
will consist of a list where all the rippleskel options are NONE if no measure
decreasing embedding was found. I think the all-NONE lists should be discarded
before we put rcinfos into the reasoning state. They are only there to
distinguish between measure failure and embedding failure.

- The list will be empty if none of the skeletons embedded into this goal *)

  fun update_skel_crit_i gmi rtab instenv oldskels pplan newgname flag = 
    let 
      val oldm = hd (Library.sort mes_order (map best_mes (select_valid_skels oldskels)));
      val arules2 = lookup_arules pplan newgname flag
      val newgoalterm = Prf.get_ndname_ctrm pplan newgname

      fun select_valid_skels' skels =
        filter (fn ((n,t), emb) => is_some emb) skels;       

      fun try_other_skels oldskels target = 
  (* Try to use a skeleton that didn't prev embedd *)
        oldskels
        |> (map_filter (fn ske => case ske of 
                                    ((n,t),NONE) => SOME (does_embed rtab instenv (n,t) newgoalterm oldm flag)
           | _ => NONE))
        |> one_of_each
        |> map (fn sts2 => (newgname, rcinfo { arules = arules2, skels = sts2, gmi = gmi, rtab = rtab, instenv = instenv }));

      val new_rcinfos = (select_valid_skels' oldskels) 
       |> (map_filter (fn ((n,t), s) => (case RRippleSkel.mk_next2 gmi rtab instenv newgoalterm (the s) of
             NONE => NONE
                                         | SOME embs =>
                                           (case embs of
                [] =>  SOME [((n,t),NONE)] (* no better mes*)      
              | (l as _::_) => SOME (map (fn e => (RRippleSkel.named_skel_term_of e, SOME e)) l)))))      
       |> one_of_each
       |> map (fn sts2 => (newgname, rcinfo { arules = arules2, skels = sts2, instenv = instenv, rtab = rtab, gmi = gmi }))
    in
      if (null new_rcinfos) then
        try_other_skels oldskels newgoalterm
      else
  new_rcinfos    
    end;

(* Update function that will fire a skeleton critic if there are no
embeddings for any of the new goals. The critic attempt to rewrite the
skeleton so that an embedding becomes possible.*)
 
  fun update_skel_crit gmi rtab instenv oldskels flag rst = 
    let 
      val infos = (RState.get_goalnames rst)
        |> map (fn x => update_skel_crit_i gmi rtab instenv oldskels (RState.get_pplan rst) x flag)
        |> filter (not o null)
        |> one_of_each;
    in
      if (null infos) then
  skel_critic gmi rtab instenv oldskels flag rst
      else
        (* Remove entries for goal for which no embedding decreased
           the measure (blocked) *)
        (map (fn l => filter (not o null o skels_of_i o snd) l) infos)
          |> filter (not o null)
          |> Seq.of_list
          |> Seq.map (put_all_in rst)
    end;
 

(* Update function for rippling-in-reverse, for use by induction
scheme revision critic*)

  fun update_rev_i gmi rtab instenv oldskels pplan newgname flag = 
    let
      val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
      val arules2 = lookup_arules_rev pplan newgname flag
    in 
      (select_valid_skels oldskels)
        (* filter: keep only mes increasing skels *)
        |> (Library.map_filter 
       (fn s => 
                case RRippleSkel.mk_next_rev rtab instenv newgoalterm s of
      [] => NONE
          | (l as _::_ ) => SOME (map (fn e => (RRippleSkel.named_skel_term_of e, SOME e)) l)))
        |> one_of_each
        |> map (fn sts2 => (newgname, rcinfo { arules = arules2, skels = sts2, gmi = gmi, rtab = rtab, instenv = instenv }))
        (* filter out cases where nothing embeds *)
        |> List.filter (is_valid_ripple_state_i o snd)
    end;

  fun update_rev gmi rtab instenv oldskels flag rst = 
    (RState.get_goalnames rst)
    |> map (fn x => update_i gmi rtab instenv oldskels (RState.get_pplan rst) x flag)
    |> filter (not o null)
    |> one_of_each
    |> Seq.of_list
    |> Seq.map (put_all_in rst);
                          
  end; (* struct *)


(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(* UNIT TESTS.                                                       *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
