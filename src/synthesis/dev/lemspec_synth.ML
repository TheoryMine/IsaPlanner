
(* Version of synthesis to use instead of lemma speucation. 
   It should synthesise terms using the bits present in
   a blocked term. *)
structure LemSpecSynth
struct
local structure Synthesis = ConstrSynthesis; in

(* Use original synthesis, just remove everything not in skel or
   lhs term from the domains of the constants. Build an sterm
   from the lhs with a hole on the rhs, then never allow new
   variables to be introduced. *)
fun init_strm top_const thy const_infos (blocked_trm, skel) =
    let
      val ienv = InstEnv.of_trm thy blocked_term
      val typ = Term.type_of blocked_trm
      val (rhs_hole_trm, ienv2) = InstEnv.new_uninst_var (("h",1), ty) ienv
      val (rhs_var_nm, hole_typ) = Term.dest_var rhs_hole_trm
      val top_cinfo = the (Constraints.lookup_const constInfoTab top_const)

      val strms = 
          map (fn holes => 
          Synthesis.Sterm {term = HOLogic.mk_eq (blocked_trm, rhs_hole_trm),
                                  ienv = ienv2,
                                  allowedTab = ,
                                  constrTab = ,
                                  holeConstrs = ,
                                  constrDepTab = ,
                                  holes = ,
                                  max_vars = 0 (*dummy, we never put new vars*)}
              ) hole_size_combos (Constraints.get_commute_opt top_cinfo) 
              [(Synthesis.Hole.mk rhs_var_nm, hole_typ)] max-size-goes-here!

      val consts_of_skel = Term.term_consts skel
      val consts_of_blockage = Term.term_consts blocked_trm
      val minsize =  Term.size_of_term skel

    in
      foldl (fn const => Synthesis.synthesise_terms const (fn x => False) 
                        max_size max_vars thy const_infos) 
    end;

(* Idea: Synthesise something from a blocked goal, instead of
   lemma speculation. We get the lhs for free, its the blocked
   term. The rhs is synthesised from constants occuring in the
   lhs + maybe datatype constructors. The result must preserve
   the skeleton of course. *)
fun synth_from_blocked_goal embedding g rst = 
    let 
      val const_infos = Constraints.mk_const_infos_no_ac (RstPP.get_theory rst)
      val blocked_subtrms =                  
          maps (fn e => case (left_right_of_eterm (Embed.get_eterm e)) of
                          NONE => [e]     (* Goal isn't an equation *)                        
                        | SOME (el,er) => [Embed.set_eterm el e,
                                           Embed.set_eterm er e]) 
               embedings (* Goal is equation *)
               |> Library.distinct (fn (el,er) => (Embed.pretty el) = (Embed.pretty er))
               |> maps LemmaSpec.lem_subtrms
               |> map (fn e => ((Embed.tgt e), Embed.src e)) 
    in
      ??????
    end;

end; (* local *)
end
