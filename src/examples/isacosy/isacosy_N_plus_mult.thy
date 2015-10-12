theory isacosy_N_plus_mult
imports "src/benchmarks/synth_theories/N_plus_mult"
begin

ML {* 
  val thy0 = theory "N_plus_mult";

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
Synthesis.synth_w_stats (3, 9) 3 thy cs;

Synthesis.print_timers();
*}


ML {*
 val thy = @{theory};
 val quickcheck_params = {size = 10, iterations = 50,default_type = SOME (Type("Int.int", []))};
 val t = @{term "a * b = suc 0"};
 val r = is_none (CounterExCInfo.quickcheck_term thy (quickcheck_params, []) t);
*} 

ML {*
  val (constInfoTab,thy) = Synthesis.mk_const_infos_ac @{theory};
  val ((cinfo,thy1),(r1,r2)) = Synthesis.synth_w_stats (2,14) 3 thy constInfoTab;
*}



end;