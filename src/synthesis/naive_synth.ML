(* Naive synthesis, just so we can compare the two *)

structure NaiveSynth =
struct
local open SynthNames; open Constraints; structure Synthesis = ConstrSynthesis; in

(* A stupid version, that doesn't have any constraints. *)

fun inst_hole_with_const ctxt strm1 hole const_info =
    let
      val typ = Synthesis.get_hole_type strm1 hole
      val size = Synthesis.get_hole_size strm1 hole
      val synth_trm = Synthesis.get_term strm1               
      
      val (const_trm, fresh_holes, ienv, allowed_tab) = 
          Synthesis.mk_new_term_bit const_info (Synthesis.get_allowedTab strm1) 
                                    (Synthesis.get_ienv strm1)
      val fresh_hole_nms_typs = map (fn (nm,ty) => (Hole.mk nm, ty)) fresh_holes
      val fresh_hole_nms = map fst fresh_hole_nms_typs

      val hole_trm = Trm.mk_var (Hole.dest hole, typ)  
      val unifiers = (MyUnify.unifiers (ienv, [(hole_trm, const_trm)]))
                       |> Seq.map (fn ienv' => (ienv', InstEnv.inst_trm ienv' synth_trm))

      (* Existing holes, not instantiated *)
      val remaining_holes = Library.remove (fn (hole1,h) => 
                                               Hole.name_eq (hole1,h)) 
                                           hole (Synthesis.get_holes_agenda strm1) 
   
      val holesizes = Synthesis.get_hole_sizes strm1
      val holesizes2list = 
          (Synthesis.hole_size_combos NONE fresh_hole_nms (size-1))
            |> map (fn l => (fold Hole.NTab.ins l holesizes))
    in
      if (null holesizes2list) 
      then 
        Seq.map (fn (ienv, trm) =>
                    Synthesis.Sterm{term = trm, 
                                    ienv = ienv,
                                    holes_agenda = remaining_holes,
                                    hole_sizes = holesizes,
                                    allowedTab = allowed_tab,
                                    constrTab = Synthesis.get_constrTab strm1,(* dummy value *)
                                    holeConstrs = Synthesis.get_holeConstrs strm1,(* dummy value *)
                                    constrDepTab = Synthesis.get_constrDepTab strm1,(* dummy value *)
                                    max_vars = Synthesis.get_max_vars strm1})
                 unifiers 
      else 
        Seq.maps (fn (ienv, trm) => 
                     Seq.map (fn holesizes2 => 
                                 Synthesis.Sterm{term = trm, 
                                                 ienv = ienv,
                                                 allowedTab = allowed_tab, 
                                                 holes_agenda = fresh_hole_nms @ remaining_holes,
                                                 hole_sizes = holesizes2,
                                                 constrTab = Synthesis.get_constrTab strm1,
                                                 holeConstrs = Synthesis.get_holeConstrs strm1,
                                                 constrDepTab = Synthesis.get_constrDepTab strm1,
                                       max_vars = Synthesis.get_max_vars strm1})
                             (Seq.of_list holesizes2list))
                 unifiers
    end;

fun inst_hole_with_var ctxt strm hole =
    let 
      val typ = Synthesis.get_hole_type strm hole
      val synth_trm = Synthesis.get_term strm              
      val paramtab = Trm.params_of synth_trm
      val hole_trm = Trm.mk_var (Hole.dest hole,typ)
      val frees = (Trm.TrmParams.get_plist paramtab)
                    |> map (fn (nm,ty) => Free(nm,ty))   
      val fresh_free =
          (Trm.TrmParams.add1 ("a", typ) paramtab)
            |> fst
            |> (fn nm => Free(nm,typ))

      val frees_unifiers = (fresh_free::frees)
                             |> Seq.of_list
                             |> Seq.maps (fn freevar => 
                                             MyUnify.unifiers (Synthesis.get_ienv strm, 
                                              [(hole_trm, freevar)]))
                             |> Seq.map (fn ienv => 
                                            (ienv, InstEnv.inst_trm ienv synth_trm))

      val remaining_holes = Library.remove (fn (hole1,h) => 
                                              Hole.name_eq (hole1,h)) 
                                          hole (Synthesis.get_holes_agenda strm)  
    in
      frees_unifiers
        |> Seq.map (fn (ienv, trm) =>
                   Synthesis.Sterm{term = trm,
                         ienv = ienv,
                         holes_agenda = remaining_holes,
                         hole_sizes = Synthesis.get_hole_sizes strm,
                         allowedTab = Synthesis.get_allowedTab strm,
                         constrTab = Synthesis.get_constrTab strm,
                         holeConstrs = Synthesis.get_holeConstrs strm,
                         constrDepTab = Synthesis.get_constrDepTab strm,
                         max_vars = Synthesis.get_max_vars strm})
    end;




fun synthesise (term_counter, next_print) ctxt cinfoTab sterm = 
    let val _ = if ((!term_counter >= !next_print)) 
                then let val _ = next_print := !next_print + 5000 in
                  writeln ("Terms: "^(Int.toString(!term_counter))) end
                else ()
    in
      case (Synthesis.get_holes_agenda sterm)
       of [] => let val _ = term_counter:= !term_counter +1 
                in Seq.single sterm end
        | (hole::hs) =>
          let 
            val size = 
                Synthesis.get_hole_size sterm hole
          in
            if (size = 1)
            then 
              let 
                val const_infos = 
                    (Synthesis.allowed_consts_of_hole sterm hole)
                      |> map (the o (Constant.NTab.lookup cinfoTab))
                      |> filter (fn cinfo => (Constraints.get_minsize cinfo) = size)
                val const_insts = 
                    (Seq.of_list const_infos) 
                      |> Seq.maps (inst_hole_with_const ctxt sterm hole)
              in
                const_insts
                  |> Seq.append (inst_hole_with_var ctxt sterm hole)
                  |> Seq.maps (synthesise (term_counter, next_print) ctxt cinfoTab)
              end
            else
              let
                val const_infos = 
                    (Synthesis.allowed_consts_of_hole sterm hole)
                      |> map (the o (Constant.NTab.lookup cinfoTab))
                      |> filter (fn cinfo => 
                                    let val minsize = Constraints.get_minsize cinfo
                                    in 1 < minsize andalso minsize <= size end)
              in
                (Seq.of_list const_infos) 
                  |> Seq.maps (inst_hole_with_const ctxt sterm hole)
                  |> Seq.maps (synthesise (term_counter, next_print) ctxt cinfoTab)            
              end
          end
    end;

(* Note: It only synthesises terms of max-size, not up to. *)  
fun synthesise_eq_terms max_size ctxt =
    let
      (* Make a constant info without any constraints *)
      val params = ThyConstraintParams.just_consts_of_ctxt ctxt;
      val cs = Constraints.init ctxt params;
      val top_cinfo = the (Constraints.lookup_const cs (Constant.mk "HOL.eq"));
      val (init_trm, init_holes, ienv, allowed_tab1) =     
          Synthesis.mk_new_term_bit top_cinfo (Hole.NTab.empty) (InstEnv.init ctxt);
      val hole_nms = map (fn (nm,ty) => Hole.mk nm) init_holes;
      val holesizes = Hole.NTab.empty;
      val holesizes2list = 
          (Synthesis.hole_size_combos NONE hole_nms (max_size-1))
            |> map (fn l => (fold Hole.NTab.ins l holesizes));
      val init_strms = 
          map (fn hole_sizes => 
                  Synthesis.Sterm{term = init_trm,
                                  ienv = ienv,
                                  holes_agenda = hole_nms,
                                  hole_sizes = hole_sizes,
                                  allowedTab = allowed_tab1,
                                  constrTab = Constraint.NTab.empty,
                                  holeConstrs = Hole.NTab.empty,
                                  constrDepTab = Constraint.NTab.empty,
                                  max_vars = 0 (* Dummy value *)})
              holesizes2list
      val term_counter = Unsynchronized.ref 0
      val print_ref = Unsynchronized.ref 5000

    in 
      (Seq.of_list init_strms)
      |> Seq.maps (synthesise (term_counter, print_ref) ctxt cs)
      |> Seq.map Synthesis.get_term
      |> Seq.list_of
      |> List.length
      (*|> Seq.list_of
      |> map_index I
      |> map (fn (i, seq) => 
                 let val l = Seq.list_of seq 
                 in writeln("Size "^Int.toString (i+3)^": "^Int.toString(List.length l)) end) *)
      (*|> Seq.map Synthesis.get_term
      |> Seq.list_of *)
      (* |> List.length *)
      (* |> map (Trm.print (ProofContext.init thy)) *)
        end;

fun print_num_trms size ctxt = 
    let 
      val num_trms = map (fn i => (i, synthesise_eq_terms i ctxt))
                         (3 upto size)
      val tot = List.foldl (fn ((ind, trms), a) => trms + a) 0 num_trms
      val _ =
          map (fn (i, trms) => writeln ("Size "^Int.toString i^": "^ Int.toString trms))
              num_trms
    in writeln ("---------------\n"^"Total: "^Int.toString tot) 
    end;


(* Print out the number of naive terms synthesied for given size *)
fun print_one_size size thy_nm ctxt =
    let
      val num_trms = synthesise_eq_terms size ctxt
    in
      writeln ("Theory: "^thy_nm^ ". Number of terms of size "^Int.toString size^": "^ Int.toString num_trms)
    end;

end; (* local *)
end;
