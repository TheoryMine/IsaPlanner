structure IsarDTechns = 
struct

structure BaseDTechn = 
DTechnInstFUN(structure K = 
struct
type T = unit;
val name = "base_techn";
val techn = RTechn.base;
val syntax = Scan.succeed ();
fun prettyf () ctxt = Pretty.str "base_techn";
end);

structure StepDTechn = 
DTechnInstFUN(structure K = 
struct
type T = unit;
val name = "step_techn";
val techn = RTechn.step;
val syntax = Scan.succeed ();
fun prettyf () ctxt = Pretty.str "base_techn";
end);



(*
structure RippleDTechn = 
DTechnInstFUN(structure K = 
struct
type T = Term.term list * Thm.thm list;
val name = "rippling";
val techn = RippleRTechn.just_ripple;
val syntax = RippleTac.ripple_skel_syntax;
fun prettyf (ts, ths) ctxt = 
    let 
      fun pretty_skelts [] = Pretty.block []
        | pretty_skelts ts = 
          Pretty.block [Pretty.str " skelts: ",
                        Pretty.block 
                          (Library.separate 
                             (Pretty.str " ")
                             (map (ProofContext.pretty_term ctxt) ts))];
      fun pretty_skels [] = Pretty.block []
        | pretty_skels ts = 
          Pretty.block [Pretty.str " skels: ",
                        Pretty.block 
                          (Library.separate 
                             (Pretty.str " ")
                             (map (Pretty.str o Thm.name_of_thm) ts))];
    in
      Pretty.block [Pretty.str "rippling",
                    pretty_skelts ts,
                    pretty_skels ths]
    end;
end);
*)

end; (* IsarDTechns *)
