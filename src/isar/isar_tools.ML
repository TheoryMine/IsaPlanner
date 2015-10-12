(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ./base/Isar/isar_tools.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    Created:    14 Oct 2004
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Useful tools related working with the Isar langauge 
*)

structure IsarTools = 
struct 

exception attr_exp of string; (* general exception to handle to attribute failures *)
exception meth_exp of string; (* general exception to handle to method failures *)
exception isar_tools_exp of string;

  fun assert_named_thm th = 
      if Thm.name_of_thm th = "" then
        raise isar_tools_exp 
                ("assert_named_thm: theorem has not been named: " ^ 
                 (Display.string_of_thm th))
      else ();
 
  val string_of_thm_name = Sign.base_name o Thm.name_of_thm; 
  val long_string_of_thm_name = Thm.name_of_thm; 
  val pretty_thm_name = Pretty.str o string_of_thm_name;  



fun unsuffix_free_names (a $ b) = 
    (unsuffix_free_names a) $ (unsuffix_free_names b)
  | unsuffix_free_names (f as Free (n, ty)) = 
    (Free (Syntax.dest_skolem n handle Fail s => n, ty))
  | unsuffix_free_names (Abs (n, ty, t)) = 
    Abs (n, ty, unsuffix_free_names t)
  | unsuffix_free_names t = t;

(* string of a term in an Isar Proof Context, most of the work
   involves unsuffixing free variables that have previously been fixed by
   Isar. (fixme!!! fix for locales!) *)
fun string_of_term_in_ctxt ctxt t = 
      Pretty.string_of 
         (ProofContext.pretty_term ctxt (unsuffix_free_names t));


(* string of a term in an Isar Proof Context, most of the work
   involves unsuffixing free variables that have previously been fixed by
   Isar. (fixme!!! fix for locales!) *)
fun string_of_term_in_thy thy t = 
    Pretty.string_of (Sign.pretty_term (Theory.sign_of thy) t);




end;