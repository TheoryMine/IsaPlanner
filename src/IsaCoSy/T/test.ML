structure Test =
struct
local open SynthNames;
in


datatype synth_step =
         DeadEnd
       | FinishedSynth of STerm.T
       | ProgressSynth of STerm.T Seq.seq;


fun dont_inst hole sterm = 
    sterm |> STerm.update_hole_domains (HoleName.NTab.delete hole) (*remove the instantiated hole *)
          |> STerm.update_hole_constrs (HoleName.NTab.delete hole)
          |> STerm.update_hole_sizes (HoleName.NTab.delete hole)
          |> STerm.delete_from_holes_agenda hole
          |> Seq.single;

fun inst_nxt_hole thyConstrs sterm = 
    case (STerm.get_holes_agenda sterm) of 
      [] => Seq.empty
    | ((hole,_)::_) => 
      let 
       val holesize = STerm.lookup_hole_size sterm hole
       val no_inst = if (holesize < 1) then dont_inst hole sterm
                     else Seq.empty
      in 
        Seq.append no_inst (STerm.inst_nxt_hole_const thyConstrs sterm)
      end;

fun synthesise_1step thyConstrs sterm = 
    case (STerm.get_holes_agenda sterm) of
    (* Fished when no holes remain, or when no more consts can be inserted*)
      [] => FinishedSynth sterm
    | (_::_) =>
     let
       (* now also allow to do nothing *)
       val all_nw_strms = inst_nxt_hole thyConstrs sterm
       in 
          case (Seq.pull all_nw_strms)          
           of NONE => DeadEnd
           | SOME _ => ProgressSynth all_nw_strms 
       end;

(* lazy depth first search through synthesis of this size *)
fun synthesise thyConstrs strm_seq =
    let fun recf ss () = 
            (case Seq.pull ss 
              of NONE => NONE
               | SOME (hs,ss2) => 
                 (case synthesise_1step thyConstrs hs of 
                    ProgressSynth ss3 => recf (Seq.append ss3 ss2) ()
                  | FinishedSynth hs2 => SOME (hs2, Seq.make (recf ss2))
                  | DeadEnd => recf ss2 () ))
    in Seq.make (recf strm_seq) end;

fun synthesise_terms top_const {size, max_vars} ctxt thyConstrs = 
     let 
      val top_cinfo = TheoryConstraints.lookup_const thyConstrs top_const
      val init_sterm_seq = STerm.init_w_const (top_const, ConstInfo.get_typ top_cinfo) 
                                              size max_vars ctxt thyConstrs
      in synthesise thyConstrs init_sterm_seq end;



(* ========================================= *)
(* consts: The constants we want to use at the top level of our terms
   size: Size of terms generated, in number of function symbols.
   constr_params: constraint parameters for synthesis.
   init_ctxt: Isabelle context
   existing_trms: previously synthesised terms, not yet in any equation.
*)




  
  

       
           
(*  ========================================= *)



end (* local open *)
end;

