theory synth_upto_term
imports Complex_Main IsaP "src/benchmarks/synth_theories/N_plus_mult"
begin


ML {* 

val thy0 = theory "N_plus_mult"; 
val (cs1, thy1) = ConstInfo.mk_const_infos_ac thy0;

val cs2 = ConstInfo.mk_const_infos_no_ac thy0;
val thy2 = thy0;

*}

ML {* PolyML.exception_trace *}

ML {*

val ctxt = ProofContext.set_mode (ProofContext.mode_schematic) @{context};
fun read_term s = Syntax.read_term ctxt s;

val sterms = 
  Seq.list_of (Synthesis.sterm_of_term 
    (ProofContext.theory_of ctxt) Synthesis.is_hole_in_lhs cs2 
    (read_term "?x + ?w = ?y + ?k"));

(* observe we got the term we wanted - but we will need to updates sizes to get anything bigger. *)
val _ = Synthesis.print_sterm (hd sterms);

*}

ML {*
val t = (read_term "x + (?y * ?w) = (x + ?y) + ?w");
val max_size = size_of_term t;
val max_vars = length (Trm.frees_of t);
val thy =  (ProofContext.theory_of ctxt);

val sterms = Seq.list_of (Synthesis.dbg_synthesise_upto_given_term 
  thy Synthesis.is_hole_in_lhs 
  cs1 t
  (Synthesis.init_any_sterm thy cs1 max_size max_vars)
);

(* observe that we only manage to generate terms upto equality (?x = ?y) *)
val _ = Synthesis.print_sterm (hd sterms);

*}

end;