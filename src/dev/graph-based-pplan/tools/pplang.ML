(* IN PROGRESS -- parser for proof planning language *)

structure PPLangParse
= struct 



datatype token_kind = Ident | Keyword | Error of string | Space | Comment;
datatype token = Token of int * (token_kind * string) | EOF;

local  open Scan  in 
fun incr_line scan = Scan.depend (fn (n: int) => scan >> pair (n + 1));
val keep_line = Scan.lift;


fun lex_err msg ((n, cs), _) = "PPlang lexical error (line " ^ string_of_int n ^ "): " ^ msg cs;
fun !!! msg scan = Scan.!! (lex_err (K msg)) scan;

(* blank space *)
val scan_blank =
  incr_line ($$ "\n") ||
  keep_line (Scan.one Symbol.is_ascii_blank);
val scan_blanks = Scan.repeat scan_blank >> implode;
val scan_blanks1 = Scan.repeat1 scan_blank >> implode;

(* basic keyword symbols *)
val keywords = ["|-", "{", "}", ":-", "=>", ",", ".", ":", "=", "?", "*", "anygoal"];
val scan_keyword = Scan.literal (Scan.make_lexicon (map explode keywords)) >> implode;
val scan_letdigs =
  Scan.many (Symbol.is_ascii_letter orf Symbol.is_ascii_digit orf Symbol.is_ascii_quasi) >> implode;
(* alphanum for ident *)
val scan_alphanumeric = Scan.one Symbol.is_ascii_letter ^^ scan_letdigs;
(* 
val scan_longident =
  (Scan.repeat1 (scan_alphanumeric ^^ ($$ ".")) >> implode) ^^ scan_alphanumeric;
*)

(* we allow ML style nested comments *)
local
val scan_cmt =
  Scan.lift scan_blank ||
  Scan.depend (fn (d: int) => keep_line ($$ "(" ^^ $$ "*") >> pair (d + 1)) ||
  Scan.depend (fn 0 => Scan.fail | d => keep_line ($$ "*" ^^ $$ ")") >> pair (d - 1)) ||
  Scan.lift (keep_line ($$ "*" --| Scan.ahead (~$$ ")"))) ||
  Scan.lift (keep_line (Scan.one (fn s => s <> "*" andalso Symbol.is_regular s)));
in
val scan_comment =
  keep_line ($$ "(" ^^ $$ "*") ^^
  !!! "missing end of comment"
    (Scan.pass 0 (Scan.repeat scan_cmt >> implode) ^^ keep_line ($$ "*" ^^ $$ ")"));
end;


fun token_leq (Token (_, (_, x)), Token (_, (_, x'))) = x <= x';

val scan =
  let
    val scanner = Scan.state :|-- (fn n =>
      let
        fun token k x = Token (n, (k, x));
      in
        scan_blanks1 >> token Space ||
        scan_comment >> token Comment ||
        keep_line (Scan.max token_leq
          (scan_keyword >> token Keyword)
          (scan_alphanumeric >> token Ident))
      end);
  in !! (lex_err (fn cs => "bad input " ^ quote (Symbol.beginning 10 cs))) scanner end;



local

val is_junk = (not o Symbol.is_blank) andf Symbol.is_regular;

fun recover msg = Scan.state :|-- (fn n =>
  keep_line (Scan.many is_junk) >> (fn cs => [Token (n, (Error msg, implode cs))]));

in

fun source src =
  Source.source' 1 Symbol.stopper (Scan.bulk scan) (SOME (false, recover)) src;

end;

end (* local *)
end; (* sturct *)

(* 
structure PPLang 
= struct
end; *)


(* source

val example_src = Source.of_string (File.read (Path.explode "./example.ppl"));
val example = Source.exhaust (PPLangParse.source example_src);
*)
