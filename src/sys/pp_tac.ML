(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      sys/pp_tac.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    13 Sep 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Tactic wrapper for performing proof planning

*)   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)


functor PPTac () = 
struct 

val dbg_explore_thm = ref NONE : Thm.thm option ref;
val dbg_gthm = ref NONE : Thm.thm option ref;
val dbg_prep_info = ref NONE : (string list * Thm.cterm list) option ref;
val dbg_outer_ctxt = ref NONE : Proof.context option ref;
val dbg_rst = ref NONE : RState.T option ref;

(* move the local explore theorem to the outer context *)
fun factor_out_isar_from_rst outer_ctxt i gthm rst = 
    let 
      val _ = (dbg_rst := SOME rst);
      val _ = (dbg_gthm := SOME gthm);
      val _ = (dbg_outer_ctxt := SOME outer_ctxt);

      val pp = RState.get_pplan rst;
      val _ = if !PPInterface.trace_isaplanner then 
                Pretty.writeln (HProofCInfo.pretty_rst rst) else ()
      val explore_thm = 
          if ExploreCInfo.no_steps_chk_rst rst 
          then PPlan.last_thm_of pp
          else ExploreCInfo.explorethm_of_rst rst
      val _ = (dbg_explore_thm := SOME explore_thm);
      val inner_ctxt = (Proof.context_of o PPlan.last_pst_of) pp;
      val local_fixed = ProofContext.fixed_names_of inner_ctxt 
                            \\ ProofContext.fixed_names_of outer_ctxt;
      val asms = Library.flat (map fst 
          (Library.drop (length (ProofContext.assumptions_of outer_ctxt), 
                                 ProofContext.assumptions_of inner_ctxt)));
      val _ = (dbg_prep_info := SOME (local_fixed,asms));
      val explore_thm' = 
          if null asms then explore_thm
          else Seq.hd (Method.insert_tac (map Thm.assume asms) 1 explore_thm);
      val renamepairs = 
          map (fn x => (x,Syntax.dest_skolem x) handle Fail _ => (x,x)) 
              local_fixed;
      val (n,th') = IsaND.prepare_goal_export (local_fixed,asms) explore_thm';
      val th = RWTools.rename_thm_bvars renamepairs th';
    in
      bicompose false (false, th, n) i gthm
    end;

(* make a rst from a technique and a goal (thm) *)
fun init_ctxt_rst ctxt techn i th = 
    let 
      val gterm = Library.nth_elem (i - 1, prems_of th)
      (* add in extra non-proof-planning information into cinfo -- 
         THINK: maybe we should not have this kind of duplication 
         of information? *)
    in
      (RState.init_from_ctxt_i ctxt gterm)
        |> RState.set_rtechn (SOME (HProofRTechn.INIT (techn ctxt)))
    end;

(* basic primitive for building a rst, searching, and factoring out 
   the result. *)
fun pptac_aux ctxt searchf rtechn i gthm = 
    Seq.flat (Seq.map (factor_out_isar_from_rst ctxt i gthm)
                      (searchf (init_ctxt_rst ctxt rtechn i gthm)));

(* note we provide all argus to force context evaluation to be
delated, as we are having to fake the context from the current theory
Really, these are only for debugging. *)
(* implicit: rtechn i gthm *)
fun pptac r i gthm = 
    pptac_aux 
      (Proof.context_of (Proof.init_state (the_context())))
      (GSearch.depth_fs (is_none o RState.get_rtechn)
                        RState.unfold)
      r i gthm;
fun ipptac r i gthm = 
    pptac_aux 
      (Proof.context_of (Proof.init_state (the_context())))
      (fn rst => Seq.single (PPInterface.ipp_rst rst))
      r i gthm;


(* method *)
fun ppmeth_aux searchf rtechn ctxt = 
 Method.METHOD
   (fn facts =>
       HEADGOAL (Method.insert_tac facts 
                 THEN' (pptac_aux ctxt searchf rtechn)));

(* implicit: rtechn ctxt *)
val ppmeth = 
    ppmeth_aux (GSearch.depth_fs (is_none o RState.get_rtechn) RState.unfold);
val ippmeth = ppmeth_aux (fn rst => Seq.single (PPInterface.ipp_rst rst));


(* add syntax for proof planning as an Isar method *)
val setup = 
    [Method.add_method ("ppmeth", 
                        ppmeth o TechnThyInfo.techn_ctxt_syntax , 
                        "Proof Planning"),
     Method.add_method ("ippmeth", 
                        ippmeth o TechnThyInfo.techn_ctxt_syntax, 
                        "Interactive Proof Planning")
];

end;