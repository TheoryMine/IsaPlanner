(* The synthesis engine. Use constraint to synthesise terms. *)

structure TermSynthesis =
struct
local open SynthNames; in


datatype synth_step =
         DeadEnd
       | FinishedSynth of STerm.T
       | ProgressSynth of STerm.T Seq.seq;

(* FIXME: Need to differentiate terms that can't be fully inst, to those that are done! *)
fun synthesise_1step var_allowed_fn thyConstrs sterm = 
    case (STerm.get_holes_agenda sterm) of
      [] => FinishedSynth sterm
    | (_::_) =>
     let
       val const_insts = STerm.inst_nxt_hole_const thyConstrs sterm
       val var_insts = STerm.inst_nxt_hole_var var_allowed_fn sterm 
       val all_nw_strms = Seq.append var_insts const_insts
       in 
          case (Seq.pull all_nw_strms) 
          of NONE => DeadEnd
           | SOME _ => ProgressSynth all_nw_strms 
       end
          
(* lazy depth first search through synthesis of this size *)
fun synthesise var_allowed_fn thyConstrs strm_seq =
    let fun recf ss () = 
            (case Seq.pull ss 
              of NONE => NONE
               | SOME (hs,ss2) => 
                 (case synthesise_1step var_allowed_fn thyConstrs hs of 
                    ProgressSynth ss3 => recf (Seq.append ss3 ss2) ()
                  | FinishedSynth hs2 => SOME (hs2, Seq.make (recf ss2))
                  | DeadEnd => recf ss2 () ))
    in Seq.make (recf strm_seq) end;

fun synthesise_terms top_const var_allowed_fn {size, max_vars} ctxt thyConstrs = 
     let 
      val top_cinfo = TheoryConstraints.lookup_const thyConstrs top_const
      val init_sterm_seq = STerm.init_w_const (top_const, ConstInfo.get_typ top_cinfo) 
                                              size max_vars ctxt thyConstrs
      in synthesise var_allowed_fn thyConstrs init_sterm_seq end;
      
   
  (*    
      val commute_opt = Constraints.get_commute_opt top_cinfo
      
      val init_sterms = 
          map (fn holesizes =>
                  Sterm {term = init_trm,
                         ienv = ienv,
                         allowedTab = allowed_tab,
                         constrTab = constr_tab,
                         holeConstrs = hole_constr_tab,
                         constrDepTab = constr_dep_tab,
                         holes_agenda = hole_nms,
                         hole_sizes = holesizes,
                         max_vars = max_vars})
              ((hole_size_combos commute_opt hole_nms (size - 1))
               |> map (fn l => (fold HoleName.NTab.ins l HoleName.NTab.empty)))
  *) 

(* Start synthesis from a partially synthesised term, and fill in the remaining holes *)
(* TODO: Does not currently impose any constraints from the give context on the holes,
   starts from 'scartch' on these so to say. Do we want this? *) 
fun synthesise_terms' partial_term var_allowed_fn {size, max_vars} ctxt thyConstrs = 
    let 
      val init_sterm = STerm.init_w_term partial_term size max_vars ctxt thyConstrs
    in synthesise var_allowed_fn thyConstrs (Seq.single init_sterm) end;
      
end (* local open *)
end; (* struct *)
