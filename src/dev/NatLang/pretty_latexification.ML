
use "$ISAPLANNER_DIRECTORY/src/dev/NatLang/list_string_aux.ML";

(* Prettification *)
val pretty_breaking = (fn x => Pretty.blk (0,x)) o Pretty.breaks 
                o (map Pretty.str) o (space_explode " ") o Pretty.string_of

fun pretty_trm p t = Pretty.unbreakable (Trm.pretty (APrf.get_context p) t);

fun pretty_cut_or_tie_latex p1 p2 = 
  let val ss1 = Pretty.str_of p1
      val ss2 = Pretty.str_of p2
  in
    if size ss1 + size ss2 > 250 then 
      Pretty.chunks 
        [Pretty.block 
            [Pretty.str (insert_string_at_nth "& " (Pretty.string_of p1) 0), 
             Pretty.str "\\notag \\\\"],
         Pretty.block [Pretty.str "& \\mbox{\\quad\\quad\\quad\\quad\\quad}", p2]]
     else Pretty.block [p1, Pretty.str "\\; ", p2]
  end

fun pretty_cut_or_tie_latex_pair [p1, p2] =  pretty_cut_or_tie_latex p1 p2

fun pretty_interleave_lists_break [] _ = []
  | pretty_interleave_lists_break _ [] = []
  | pretty_interleave_lists_break (h1::t1) (h2::t2) = 
        ((Pretty.block [h1, Pretty.fbrk, h2]) :: pretty_interleave_lists_break t1 t2)

fun pretty_sep_block s l = 
    Pretty.block (list_sep (Pretty.str s) l);
    
fun sep_with_string [] s = ""
  | sep_with_string [l] s = l
  | sep_with_string (h::t) s = h ^ s ^ (sep_with_string t s)
    
fun pretty_commas_and [] = []
  | pretty_commas_and [l] = [l]
  | pretty_commas_and [ll,l] = [ll,Pretty.str " and ",l]
  | pretty_commas_and (h::t) = [h,Pretty.str ", "] @ (pretty_commas_and t)

fun pretty_commas [] = []
  | pretty_commas [l] = [l]
  | pretty_commas (h::t) = [h,Pretty.str ", "] @ (pretty_commas t)

fun pretty_dots [] = []
  | pretty_dots [l] = [l, Pretty.str ". \\; "]
  | pretty_dots (h::t) = [h,Pretty.str ". \\; "] @ (pretty_dots t)

fun pretty_block_commas_and [] = []
  | pretty_block_commas_and [l] = [l]
  | pretty_block_commas_and [ll,l] = ll :: [Pretty.block [Pretty.str " and ", l]]
  | pretty_block_commas_and (h1::(h2::t)) = 
      h1 :: (pretty_block_commas_and ((Pretty.block [Pretty.str ", ", h2]) :: t))
    
fun pretty_latex_mathmode p = Pretty.enclose "$" "$" [p]

fun pretty_latex_eqmode p = Pretty.enclose "$$" "$$" [p]

fun latex_env env s pL = 
     ([Pretty.str ("\\begin{"^env^"}"^s)]
    @ pL
    @ [Pretty.str ("\\end{"^env^"}")])
     
     
     