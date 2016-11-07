
(* Some auxiliary functions *)
fun erase_nth_element _ [] = []
  | erase_nth_element 0 (_::t) = t
  | erase_nth_element n (h::t) = h :: (erase_nth_element (n-1) t)


fun map_numbering _ _ [] = []
  | map_numbering i f (h::t) = (f i h)::(map_numbering (i+1) f t)

(* like map but with a list of functions *)
fun map_many _ [] = []
  | map_many [] l = l
  | map_many (fh::ft) (h::t) = (fh h) :: (map_many ft t)

fun list_sep x [] = []
  | list_sep x [a] = [a]
  | list_sep x (h::t) = 
    h :: x :: (list_sep x t);
    
fun in_list x [] = false
  | in_list x (h::t) = (x = h orelse in_list x t)
  
fun remove_duplicates L =
let 
  fun rdrec _ [] = []
    | rdrec acc (h::t) = 
      if in_list h acc then rdrec acc t
      else h :: rdrec (h::acc) t
in
  rdrec [] L
end

fun string_until "" _ = ""
  | string_until s subs = 
    if String.isPrefix subs s then ""
    else (substring(s,0,1))^(string_until (String.extract(s,1,NONE)) subs)
fun string_until_including "" _ = ""
  | string_until_including s subs = 
    if String.isPrefix subs s then subs
    else (substring(s,0,1))^(string_until_including (String.extract(s,1,NONE)) subs)
    
fun string_from "" _ = ""
  | string_from s subs = 
    if String.isPrefix subs s then String.extract(s,size subs,NONE)
    else string_from (String.extract(s,1,NONE)) subs
    
fun insert_string_at_nth s1 s2 0 = s1 ^ s2
  | insert_string_at_nth s1 s2 i = 
    let val k = Int.max (0, Int.min (i, (size s2))) in
      String.extract (s2, 0, SOME k) ^ s1 ^ String.extract (s2, k, NONE)
    end
    
fun commas_and [] = ""
  | commas_and [h] = h
  | commas_and [h1,h2] = h1^" and "^h2
  | commas_and (h::t) = h^", "^(commas_and t)

fun interleave_lists [] _ = []
  | interleave_lists _ [] = []
  | interleave_lists (h1::t1) (h2::t2) = 
        ([h1, h2] :: interleave_lists t1 t2)
  
fun remove_immediate_rels _ _ [] = []
  | remove_immediate_rels prev R (h::t) = 
      if R prev h then remove_immediate_rels h R t
      else h::(remove_immediate_rels h R t)

fun int_of_string s = 
let
  fun lrec i x lim =
    if string_of_int i = x then i
    else if i >= lim then raise ERROR "odd index"
      else lrec (i+1) x lim
in
  lrec 0 s 30
end

val greek_chars = 
  ["\\alpha",	"\\beta","\\gamma","\\delta","\\epsilon","\\zeta","\\eta","\\theta","\\iota",
  "\\kappa","\\lambda","\\mu","\\nu","\\xi","\\omicron","\\pi","\\rho","\\sigmaf","\\sigma",
  "\\tau","\\upsilon","\\phi","\\chi","\\psi","\\omega","\\thetasym","\\upsih","\\piv" ]
  
val abc_chars = 
  ["a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t",
                  "u","v","w","x","y","z"]
  
fun expand_alphabet A 0 = A
  | expand_alphabet A n = (expand_alphabet A (n-1)) @ (map (fn x => x^"_{\\mbox{\\tiny "^(string_of_int n)^"}}") A)
  
fun char_from_int A i = 
let
 fun lrec j = nth (expand_alphabet A j) (i-1) handle Subscript => lrec (j+1)
in lrec 0
end

fun int_to_greek i = char_from_int greek_chars i
fun int_to_abc i = char_from_int abc_chars i


 
fun which_is_prefix [] _ = NONE
  | which_is_prefix (h::t) s = 
    if String.isPrefix h s 
    then SOME h 
    else which_is_prefix t s

fun string_from_options _ "" = (NONE,"")
  | string_from_options subs s = 
    case which_is_prefix subs s of 
      NONE => string_from_options subs (String.extract(s,1,NONE)) 
    | SOME sub => (SOME sub, String.extract(s,size sub,NONE))
    
fun sum _ [] = 0
  | sum f (x::xs) = f x + sum f xs
  