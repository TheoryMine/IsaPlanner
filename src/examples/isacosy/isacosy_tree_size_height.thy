theory isacosy_tree_size_height
imports "src/benchmarks/synth_theories/Tree_size_height"
begin

ML {* 
  val thy0 = theory "Tree_size_height";

  (* Create initial constant-informations,
     including looking for AC-properties *)
  val (cs, thy) = ConstInfo.mk_const_infos_ac thy0;

  (* Alt. without AC pre-processing *)
  (* val cs = ConstInfo.mk_const_infos_no_ac thy0;
  val thy = thy0; *)
*}

ML {*
Synthesis.reset_timers();

(* Synthesise from size 3 up to size 8, with max 2 variables *)
Synthesis.synth_w_stats (3, 8) 2 thy cs;

Synthesis.print_timers();
*}


end;