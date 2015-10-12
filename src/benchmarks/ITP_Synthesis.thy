theory ITP_Synthesis
imports IsaP
begin

(* This file is for experiments for the ITP paper *)


ML{*
(* Running synthesis on this theory will produce the lemmas
   used to prove the theorems in the paper. Warning, it takes a little
  while...*)
use_thy "src/benchmarks/synth_theories/ITPSynth";
val thy0 = theory "ITPSynth";
*}

ML{*
(* Create initial constant-informations,
   including looking for AC-properties *)
val (cs, thy) = ConstInfo.mk_const_infos_ac thy0;

(* Synthesise from size 3 up to size 10, with max 2 variables 
  is enough. *)
PrintMode.setmp [] (fn () => 
  Synthesis.synth_w_stats (3, 10) 2 thy cs) ();
*}

end;