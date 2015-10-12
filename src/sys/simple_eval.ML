(* Simple evaluation from left to right, on a terms HOAS *)
structure SimpleEval = 
struct 

val mv_left = IsaFTerm.focus_left;
val mv_right = IsaFTerm.focus_right;
val mv_lam = IsaFTerm.focus_right;
val mv_abs = IsaFTerm.focus_abs;

infix or_try;
val (op or_try) = Seq.append;

(* given a function that perfroms matching, gives redexes for 
   evluating the focus term *)
fun eval_matches f ft = 
    let
      fun maux ft = 
          (case (IsaFTerm.focus_of_fcterm ft) of 
            (l $ r) => 
            (maux (mv_left ft))
              or_try (maux (mv_right ft))
              or_try (f ft)
          | (Abs(s,ty,t)) => maux (mv_abs ft)
          | _ => f ft)
    in (maux ft) end;

val eord = ThmEvalNet.mk_evalord ("Simple", eval_matches);
val net = ThmEvalNet.new("Simple", eord);

val setup = [EvalThyInfo.add_eord_to_thy eord,
             EvalThyInfo.add_rnet_to_thy net];

end;
