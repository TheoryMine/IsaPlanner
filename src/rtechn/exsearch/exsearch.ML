(* val (a1, p) = p |> assume "ALL X. (is_a X knight) xor (is_a X knave)";
val (a2, p) = p |> assume "ALL X. is_a X knight --> (ALL A. says X A --> A)";
val (a3, p) = p |> assume "ALL X. is_a X knave --> (ALL A. says X A --> ~ A)";
val (a4, p) = p |> assume "says zoey (is_a mel knave)";
val (a5, p) = p |> assume "says mel (~ (is_a zoey knave | is_a mel knave))";
val (c, p) = p |> conjecture "EX Y Z. is_a mel Y & is_a zoey Z";
*)

use_thy "examples/ijcar2008/IJCAR2008";

val rst = 
PPInterface.init_rst (theory "IJCAR2008") ("g",
" [| \
\    !! X. (is_a X knight) xor (is_a X knave); \
\    !! X A. is_a X knight ==> says X A ==> A; \
\    !! X A. is_a X knave ==> says X A ==> ~ A; \
\    says zoey (is_a mel knave); \
\    says mel (~ (is_a zoey knave | is_a mel knave)) \
\ |] ==> is_a mel ?Y & is_a zoey ?Z");
