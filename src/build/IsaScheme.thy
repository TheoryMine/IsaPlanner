theory IsaScheme 
imports "HOL_IsaP"

uses
"../isar/isa_planner.ML"

begin

(* Antiquotation parsing metavariables *)
ML {*
val _ = 
    let 
      val parser = Args.context -- Scan.lift Args.name_source 
      fun term_pat (ctxt, str) = 
          str |> ProofContext.read_term_pattern ctxt 
              |> ML_Syntax.print_term 
              |> ML_Syntax.atomic 
    in 
      ML_Antiquote.inline "term_pat" (parser >> term_pat)
    end 
*}

end;