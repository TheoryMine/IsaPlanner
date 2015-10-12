(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/rippling/basic_cinfo.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    15 Mar 2003
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Basic contextual-information for performing rippling. The main purpose
    of this is to manage multiple skeletons, and tie together the
    database of wave rules to the process of rippling. Furthermore, we
    manage the overall ripppling process and provide information on
    matching rules.

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature BASIC_RIPPLE_CINFO = 
sig
  type T
  type wruleT = WRules.wrule;

  structure RippleSkel : RIPPLE_SKEL;

  structure I : LOCAL_INFO_ITEM where type T = T

  exception rippling_cinfo_exp of string;
  exception rippling_cinfo2_exp of ((PPlan.gname * Term.term) list  (* skel *)
                                    * Term.term); (* tgt *)

    (* working with rippling cinfo: starting/updating *)
  val start : (PPlan.gname * Term.term) list 
              -> ParamRGraph.T ->
              PPlan.gname ->
              RState.T -> 
              RState.T Seq.seq;
      
  val update : PPlan.gname (* old goal *)
               -> PPlan.gname (* new goal *)
               -> RState.T -> RState.T Seq.seq

  val update_unrestricted : (* all applicable embeddings, 
                               even non-measure decreasing *)
      PPlan.gname  -> PPlan.gname -> RState.T -> RState.T Seq.seq

  (* internal update functions *)
  val update_i :  (PPlan.gname * 
                   ((PPlan.gname * Term.term) * RippleSkel.T option) list)
                -> PPlan.gname -> RState.T -> RState.T Seq.seq
  val update_unrestricted_i : (PPlan.gname *
                    ((PPlan.gname * Term.term) * RippleSkel.T option) list)
                   -> PPlan.gname -> RState.T -> RState.T Seq.seq

  val mk_rcinfo :  DTac.T list -> ParamRGraph.T -> 
                   ((PPlan.gname * Term.term) * RippleSkel.T option) list
                   -> T
                      
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
  val skels_of_i : T -> RippleSkel.T list
  val skels_of : RState.T -> PPlan.gname -> RippleSkel.T list
                                            
  val skeleton_namedterms_of_i : T -> (PPlan.gname * Term.term) list
  val skeleton_namedterms_of 
      : RState.T -> PPlan.gname -> (PPlan.gname * Term.term) list
  val skeleton_names_of  
      : RState.T -> PPlan.gname -> PPlan.gname list
                                   
  (* skeletons from all current rippling goals *)
  val all_skels_of_i : T -> ((PPlan.gname * Term.term) * 
                             RippleSkel.T option) list
  val all_skels_of : RState.T -> PPlan.gname-> 
                     ((PPlan.gname * Term.term) * 
                      RippleSkel.T option) list
                     
  val select_valid_skels :  ((PPlan.gname * Term.term) * 
                             RippleSkel.T option) list -> 
                            RippleSkel.T list
                            
  val measures_of_i : T -> RippleSkel.RippleMeasure.T list
  val measures_of : RState.T -> PPlan.gname-> 
                    RippleSkel.RippleMeasure.T list
                    
  val has_embedding : RState.T -> PPlan.gname -> bool
  val embeddings_of : RState.T -> PPlan.gname -> Embed.T list

  val inst_skels_terms : RState.T -> PPlan.gname -> Term.term list

  (* applicable rules *)
  val applicable_dtacs_of_i : T -> DTac.T list
  val applicable_dtacs_of :  RState.T -> PPlan.gname -> DTac.T list
  val applicable_dtacseq_of_i : T -> DTac.T Seq.seq
  val applicable_dtacseq_of : RState.T -> PPlan.gname -> DTac.T Seq.seq

  (* get relation graph used by relational rippling *)
  val get_relgraph :  RState.T -> PPlan.gname -> ParamRGraph.T

  (* if goal, looks up backwards applicable stuff, else fwd applicable stuff *)
  val lookup_arules :  PPlan.T -> PPlan.gname -> DTac.T list

  (* what are the backward proof/foward proof dtacs applicable? *)
  val lookup_bck_arules :  PPlan.T -> PPlan.gname -> DTac.T list
  val lookup_fwd_arules :  PPlan.T -> PPlan.gname -> DTac.T list

  (* for debugging *)
  val set_skels_i : ((PPlan.gname * Term.term) 
                     * RippleSkel.T option) list -> T -> T
  val set_arules_i : DTac.T list -> T -> T

  (* pretty printing *)
  val pretty_i : Proof.context -> T -> Pretty.T
  val pretty : RState.T -> PPlan.gname -> Pretty.T

  val print : RState.T -> PPlan.gname -> unit
  
  val pretty_skels_i : Proof.context -> T -> Pretty.T
  val pretty_skels : RState.T -> PPlan.gname -> Pretty.T
  (* pretty skeletons from the current rippling goals *)
  val pretty_curgoals_skels : RState.T -> Pretty.T

  val pretty_applicable_rules_i : Proof.context -> T -> Pretty.T
  val pretty_applicable_rules : RState.T -> PPlan.gname -> Pretty.T
  val print_applicable_rules : RState.T -> PPlan.gname -> unit
                                                          
                                                          
end;


(* Contextual information for Rippling *)
functor BasicRippleCInfoFUN (RippleSkel : RIPPLE_SKEL)
 : BASIC_RIPPLE_CINFO
= struct

  structure RippleSkel = RippleSkel;

  exception rippling_cinfo_exp of string;
  exception rippling_cinfo2_exp of ((PPlan.gname * Term.term) list  (* skel *)
                                    * Term.term); (* tgt *)

  type wruleT = WRules.wrule;

  (* FIXME: make a clear notion of uninitialised cinfo - otherwsie
  failure to initialise it will be hard to debug. *)
  datatype T = RCInfo of 
           {arules : DTac.T list, (* all aplicable rules *)
            relgraph : ParamRGraph.T, (* relational rippling relation graph *)
            skels : ((PPlan.gname * Term.term) (* skeleton name and term *)
                     * RippleSkel.T option) (* anntotations etc for a skel *)
                      list};

  (*Construct a basic rcinfo, for use by other variants of rippleCInfo *)
  fun mk_rcinfo arules relgraph skels = 
      RCInfo{arules=arules, relgraph = relgraph, skels=skels};

(* Return the skeletons that currently embedd *)
  fun select_valid_skels skels = (* clever filter for option lists *)
      List.mapPartial I (map snd skels);

  fun skels_of_i (RCInfo rep) = select_valid_skels (#skels rep);
  fun get_relgraph_i (RCInfo rep) = (#relgraph rep);
  fun all_skels_of_i (RCInfo rep) = (#skels rep);

  fun applicable_dtacs_of_i (RCInfo rep) = #arules rep; 
  val applicable_dtacseq_of_i = Seq.of_list o applicable_dtacs_of_i;

  fun update_skels_i f (RCInfo rep) = 
      RCInfo {skels = f (#skels rep), 
              relgraph = #relgraph rep,
              arules = #arules rep};
  fun update_relgraph_i f (RCInfo rep) = 
      RCInfo {skels = #skels rep, 
              relgraph = f (#relgraph rep),
              arules = #arules rep};
  fun update_arules_i f (RCInfo rep) = 
      RCInfo {skels = #skels rep, 
              relgraph = #relgraph rep,
              arules = f (#arules rep)};

  val set_skels_i = update_skels_i o K;
  val set_relgraph_i = update_relgraph_i o K;
  val set_arules_i = update_arules_i o K;

(* pretty printing *)
  fun pretty_skels_i ctxt d =
      (case (skels_of_i d) of 
         [] => Pretty.str "No valid skeletons."
       | l => Pretty.chunks (([Pretty.str "Skeleton Measures:"]) @ 
                             (map (RippleSkel.pretty ctxt) l)));

  fun pretty_applicable_rules_i ctxt d =
      let val rules = (applicable_dtacs_of_i d)
      in case rules 
          of [] => Pretty.str "No applicable rules."
           | (_::_) => 
             Pretty.chunks ([Pretty.str "Applicable Rules: "] @
                            (map (fn r => DTac.pretty r ctxt) rules))
      end;

  fun pretty_relgraph_i d = 
      let val relgraph = (get_relgraph_i d)
      in if ParamRGraph.is_empty relgraph then 
           Pretty.str "No relations graph."
         else 
           Pretty.block 
             [Pretty.str "RelGraph: ",
              ParamRGraph.pretty relgraph]
      end;

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
      Pretty.chunks [pretty_skels_i ctxt d,
                     pretty_relgraph_i d,
                     pretty_applicable_rules_i ctxt d];



  (* contextual info sturcture *)
(* Information associated with goals in reasoning states during rippling *)
structure I = 
  LocalInfoFUN( 
    struct
      type T = T;
      val name = "local rippleinfo:" ^ RippleSkel.name;
      val copy = I; (* copy is just Id as no refs *)
      val pretty = (fn d => fn rst => pretty_i (RState.get_ctxt rst) d); (* print only rules *)
    end
  );

  fun pretty_applicable_rules rst goal =
      pretty_applicable_rules_i (RState.get_ctxt rst) (I.get rst goal);
  val print_applicable_rules =
      Pretty.writeln oo pretty_applicable_rules;
  fun pretty_relgraph rst goal =
      pretty_relgraph_i (I.get rst goal);
  val print_relgraph =
      Pretty.writeln oo pretty_relgraph;
  fun pretty_skels rst goal =
      pretty_skels_i (RState.get_ctxt rst) (I.get rst goal);
  fun pretty_curgoals_skels rst =
      Pretty.chunks (RstPP.map_cur_goals pretty_skels rst);

  fun pretty rst goal  =
      pretty_i (RState.get_ctxt rst) (I.get rst goal);

 (* managing skeletons *)
  (* implicit T *)
  val skeleton_namedterms_of_i = 
      map RippleSkel.get_named_skel_term o skels_of_i; 
  val skeleton_namedterms_of = skeleton_namedterms_of_i oo I.get;
  val skeleton_names_of = (map fst) oo skeleton_namedterms_of;

  (* get relational rippling graph *)
  val get_relgraph = get_relgraph_i oo I.get;

  (* implicit: rst gname *)
  val skels_of = skels_of_i oo I.get;
  (* fun replace_skel oldskel newskel goal rst = 
      let 
        val oldskels = skeleton_names_of rst goal;
        val filtered_oldskels = filter (fn h => (h = oldskel)) oldskels;
      in *)
        
        
  val all_skels_of = all_skels_of_i oo I.get;

  val measures_of_i = maps RippleSkel.get_measures o skels_of_i;
  fun measures_of rst gname = 
      case (I.get_opt rst gname) of 
        NONE => []
      | SOME info => measures_of_i info;

  fun has_embedding rst gname = 
      Option.isSome (I.get_opt rst gname);

  val embeddings_of_i = 
      maps RippleSkel.get_embeddings o skels_of_i;
  fun embeddings_of rst gname = 
      case (I.get_opt rst gname) of 
        NONE => []
      | SOME info => embeddings_of_i info;


  (* Return a version of this skeleton with sinks instantiated to
   their current contents. Might get multiple src terms, only give
   back one of each for each skeleton.*)
  fun inst_skels_terms rst gname =
      maps (map Embed.src o RippleSkel.get_embeddings) 
           (skels_of rst gname)
           |> Library.distinct (fn (skl1,skl2) => Trm.trm_name_eq skl1 skl2);

  (* all skels are blocked w.r.t all possible new skels. *)
  fun blocked1_chk_i d nextds = 
      let val sts = maps skels_of_i nextds
          val curskels = skels_of_i d
      in List.all (fn st => RippleSkel.blocked_chk st sts)
                  curskels
      end;

  (* A rst is blocked if every child goal of every child-rst is
     blocked. *)
  fun blocked_chk rst goal rsts =
      let (* Get the ripplecinfos of the subgoals that are rippling them. 
             Can can ignore goals that have any ripple info *)
        fun infolist rst = 
            map_filter (I.get_opt rst) (RState.get_goalnames rst);
      in 
        (not (* no solved state *)
           (List.exists (* solved *)
              (fn st => null (RState.get_goalnames st))
              rsts))
        andalso 
        (List.all (* no states or all states do not ripple *)
           (fn st => (blocked1_chk_i (I.get rst goal) (infolist st)))
            rsts)
      end;


  (* get the applicable rules *)                       
  fun applicable_dtacs_of rst goal = 
      applicable_dtacs_of_i (I.get rst goal);
  fun applicable_dtacseq_of rst goal = 
      applicable_dtacseq_of_i (I.get rst goal); 

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
  val some_curgoal_is_ripple_valid = 
      RstPP.forsome is_valid_ripple_state_goal;

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
  val success_chk_i = 
     List.exists RippleSkel.success_chk o skels_of_i;
  fun success_chk rst goal = success_chk_i (I.get rst goal);

  (* lookup substitutions possible *)
  fun lookup_substs_i pplan gname = 
      let
        val t = Prf.get_ndname_ctrm pplan gname
        val db = WRulesGCtxt.wrules_of_ctxt (PPlan.get_context pplan)
        val eqs = WRules.eqrule_zipper_lookup 
                    db pplan gname (Zipper.mktop t)
      in eqs end;

  fun lookup_bck_res_i pplan gname = 
      let
        val t = Prf.get_ndname_ctrm pplan gname
        val db = WRulesGCtxt.wrules_of_ctxt (PPlan.get_context pplan)
        val imps = WRules.imprule_concl_lookup db pplan gname t
      in imps end;

  fun lookup_fwd_res_i pplan gname = 
      let
        val t = Prf.get_ndname_ctrm pplan gname
        val db = WRulesGCtxt.wrules_of_ctxt (PPlan.get_context pplan)
        val fwd_imps = WRules.fwd_imprule_prems_lookup db pplan gname t
      in fwd_imps end;

  (* lookup all rules and their aplication to the pplan. IMPROVE:
  rules should come from local contextual info: so we we can add to
  wave rules locally within a proof planning attempt *)
  fun lookup_bck_arules pplan gname = 
      let 
        val db = WRulesGCtxt.wrules_of_ctxt (PPlan.get_context pplan)
        val t = Prf.get_ndname_ctrm pplan gname
      in
        Seq.list_of
        (Seq.append (WRules.imprule_concl_lookup db pplan gname t)
                    (WRules.eqrule_zipper_lookup db pplan gname (Zipper.mktop t)))
      end;

  (* lookup all rules and their aplication to the pplan. IMPROVE:
  rules should come from local contextual info: so we we can add to
  wave rules locally within a proof planning attempt *)
  fun lookup_fwd_arules pplan gname = 
      let 
        val db = WRulesGCtxt.wrules_of_ctxt (PPlan.get_context pplan)
        val t = Prf.get_ndname_ctrm pplan gname
      in
        (map (fn (imprule,(subgoals,pplan)) => 
                 DTac.mk ((fn ctxt => WRules.pretty_fwd_impwrule_sml ctxt imprule), 
                          K (Seq.single (([],subgoals),pplan))))
             (Seq.list_of 
                (WRules.fwd_imprule_prems_lookup db pplan gname t)))
         @ 
         ((Seq.list_of (WRules.eqrule_zipper_lookup 
                              db pplan gname (Zipper.mktop t))))
      end;

  fun lookup_arules pplan gname = 
      if Prf.is_open_goal pplan gname then 
        lookup_bck_arules pplan gname
      else lookup_fwd_arules pplan gname;

  (* lists with one of each list of list of lists *)
  fun one_of_each [] = []
    | one_of_each [[]] = []
    | one_of_each [(h::t)] = [h] :: (one_of_each [t])
    | one_of_each ([] :: xs) = []
    | one_of_each ((h :: t) :: xs) = 
      (map (fn z => h :: z) (one_of_each xs)) 
      @ (one_of_each (t :: xs));

(* IMPROVE: optimise inclusion of RippleSkel, ie creating the list of
   skeleton embeddings... *)
(* Make a list of lists of all combinations of embeddings for the goals in the
   reasoning state. Create a new rst for each such combo.*)
  (* create the initial possible rippling contextual informations given the 
  skeletons (name, term) pairs and the target *)
  fun start skels relgraph goal rst = 
    let 
      val pplan = RState.get_pplan rst
      val goalterm = Prf.get_ndname_ctrm pplan goal 
      val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) relgraph;

      val skellists = one_of_each
    (* Produce lists of states for each skeleton and combine them *)
          (map (fn (n,t) =>
                   case RippleSkel.init {ectxt=ectxt, skelterm=t, 
                                         skelname=n, target=goalterm} 
     (* skeleton does not currently embedd *)
                    of [] => [((n,t), NONE)] 
                     | (l as _::_) => map (fn e => ((n,t), SOME e)) l) skels)
    
      (* Check if any skeleton embed..*)
      val _ = if null (filter (fn skel => case skel of NONE => false | SOME _ => true) 
                              (map snd (flat skellists)) ) then 
                (writeln "NONE of the skeletons embed into the goal!";
                 raise rippling_cinfo2_exp (skels,goalterm))
              else ();
      val arules = lookup_arules pplan goal
    in
      (map (fn sts => RCInfo{arules = arules,
                             relgraph = relgraph,
                             skels = sts})
           skellists)
        |> Seq.of_list
        |> Seq.map (fn rcinfo => I.put (goal, rcinfo) rst) 
    end;

(* update *)
fun update_i (oldgname,oldskels) newgname rst = 
    let
      val pplan = RState.get_pplan rst;
      val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
      val oldrelgraph = get_relgraph rst oldgname;
      val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) 
                                   oldrelgraph;
    in 
      (select_valid_skels oldskels) (* only look at improvements to non-NONE embeddings 
                                       Looking at other could lead to non-term. *)
        (* filter: keep only mes decreasing skels *)
        |> (Library.map_filter 
              (fn s => 
                  case RippleSkel.mk_better_next ectxt newgoalterm s
                   of [] => NONE
                    | (l as _::_ ) => 
                      SOME (
                      map (fn e =>
                              (RippleSkel.get_named_skel_term e,
                               SOME e)) l)))
        |> one_of_each
        |> map (fn sts2 => 
                   let val arules2 = lookup_arules pplan newgname;
                   in RCInfo{arules=arules2,
                             relgraph=oldrelgraph,
                             skels=sts2}
                   end)
        (* filter out cases where nothing embeds *)
        |> List.filter is_valid_ripple_state_i
        |> Seq.of_list
        (*|> fn l => if null l then delete_RCInfo newgname 
                     delete if no embeddings *)
        |> Seq.map (fn rcinfo => I.put (newgname, rcinfo) rst)
    end;

fun update oldgname newgname rst = 
    update_i (oldgname,all_skels_of rst oldgname) newgname rst;

(* Update without filtering out non-measure decreasing skels*)
fun update_unrestricted_i (oldgname,oldskels) newgname rst = 
    let 
      val pplan = RState.get_pplan rst
      val arules2 = lookup_arules pplan newgname
       val newgoalterm = Prf.get_ndname_ctrm pplan newgname;
      val oldrelgraph = get_relgraph rst oldgname 
      val ectxt = Embed.Ectxt.init (PPlan.get_ienv pplan) oldrelgraph;

      (* Create embedding for this skeleton if it
         has any in the current target. *)
      fun does_embed (n,t) target =
          (case RippleSkel.init {ectxt=ectxt, skelterm=t,
                                 skelname=n,target=target} of 
               (* If this skeleton does not embedd at the moment *)
                 [] => [((n,t), NONE)] 
             | (l as _::_) => map (fn e => ((n,t), SOME e)) l);
    in
      oldskels
        |> (map (fn ((n,t), skel) => 
                    case skel 
                (* No previous embedding, check if embedds in new target *)
                     of NONE => does_embed (n,t) newgoalterm
                (* The skeleton did embed previously, get new skels *)         
                      | SOME skeleton => 
                        case RippleSkel.mk_all_next ectxt newgoalterm skeleton 
                         of [] => [((n,t), NONE)]        
                          | (l as _::_) => 
                            map (fn e => (RippleSkel.get_named_skel_term e,  
                                          SOME e)) l ))
        |> one_of_each
        |> map (fn sts2 => RCInfo {arules = arules2,
                                   relgraph = oldrelgraph,
                                   skels = sts2})
        |> Seq.of_list
        |> Seq.map (fn rcinfo => I.put (newgname, rcinfo) rst)
        (*  no filter: keep all skels *)
    end;

fun update_unrestricted oldgoal newgoal rst = 
    update_unrestricted_i (oldgoal,all_skels_of rst oldgoal) newgoal rst;

(* Update function that can call critic that modifies
   skeleton if no current skel embed. *)
val mes_order = RippleSkel.RippleMeasure.ord;
fun best_mes e = hd (Library.sort mes_order (RippleSkel.get_measures e));


val print = Pretty.writeln oo pretty;

end; (* struct *)
