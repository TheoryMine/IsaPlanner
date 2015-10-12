(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      ThyConstr.ML
    Author:     Moa Johansson
                moa.johansson@chalmers.se                
                             
 
How IsaCoSy theory constraints, which are associated with each constant
it uses during synthesis.

*)
(* -------------------------------------------------------------------------*)
signature THY_CONSTR =
sig 
  type pos
  type T
  val top_args_of_constr : T -> int list 
  val print_constr : T -> unit
  val pretty_pos : pos -> Pretty.T 
  val pretty_constr : T -> Pretty.T
  val mk_UnEqual_constrs : term -> T list
  val mk_NotConst_constrs : term -> T list
  val default_name : SynthNames.ConstraintName.name
end;

structure ThyConstr =
struct
  local open SynthNames in   


datatype pos = 
         Path of int list

datatype T = 
         UnEqual of pos list
       | NotConst of pos * ConstantName.name
       | Or of T list

(* ------------------------------------------------------------*)
(* Pretty print constraints.*)
(* ------------------------------------------------------------*)

fun pretty_pos (Path l) =
      Pretty.block [Pretty.str "Path ",  
                    Pretty.list "[" "]" (map (Pretty.str o Int.toString) l)];
  
fun pretty_constr (UnEqual l) =
      Pretty.block [Pretty.str "UnEqual ", 
                    Pretty.list "[" "]" (map pretty_pos l)]
    | pretty_constr (NotConst (p, constn)) = 
      Pretty.block [Pretty.str "NotConst(", 
                    pretty_pos p,
                    Pretty.str ", ",
                    ConstantName.pretty_name constn,
                    Pretty.str ")"]
    | pretty_constr (Or sub_constrs) =
      Pretty.block [Pretty.str "OR ", 
                    Pretty.list "[" "]"
                      (map pretty_constr sub_constrs)];

val print_constr = Pretty.writeln o pretty_constr;
(* ------------------------------------------------------------*)

(* Default name for constraints *)
val default_name = ConstraintName.mk ("C",0);

(* Check if this is a path to the immediate argument positions of some function,
   i.e. that it's a singleton path. *)
fun path_to_arg p = case p of Path ([arg_pos]) => SOME arg_pos | _ => NONE;
               
(* Check under which 'top'-position constraint refer to *)        
fun top_args_of_constr (NotConst(p,_)) = 
      (case p of Path(p::ps) => [p] | _ => [])
   | top_args_of_constr (UnEqual ps) = 
          map_filter (fn p => case p of Path (p::ps) => SOME p | _ => NONE) ps
   | top_args_of_constr (Or cs) = maps top_args_of_constr cs; 

(* ------------------------------------------------------------*)
(* Create constraints from terms. *)
(* ------------------------------------------------------------*)

exception mk_constr_exp of (Term.term * string);

(*Record paths to all variables, those occuring more than once make an UnEqual constraint *)
fun mk_UnEqual_constrs t = 
    let
      fun get_var_paths vtab path (t1$t2) = 
            let val (hd, args) = Term.strip_comb (t1$t2) in 
              List.foldl (fn ((ind,arg), vtab') => 
                            get_var_paths vtab' (path@[ind]) arg)
                          (get_var_paths vtab path hd) 
                          (Library.map_index I args)
            end
            | get_var_paths vtab path (Var(nm,_)) =
              (case (StrIntNTab.lookup vtab nm) of
                 NONE => StrIntNTab.ins (nm, [Path path]) vtab
               | SOME other_pos => StrIntNTab.update (nm, (Path path)::other_pos) vtab
               ) 
           | get_var_paths vtab _ _ = vtab
           
       fun mk_UnEqual paths =
           case paths of [] => NONE
                       | [p] => NONE
                       | ps => SOME (UnEqual(ps))
     in   
      (get_var_paths StrIntNTab.empty [] t)
      |> StrIntNTab.values 
      |> map_filter mk_UnEqual
     end;  
 
fun mk_NotConst_constrs t = 
    case t of
      (t1$t2) => (
      
      let
        (*Compute constraint on arguments of this function application. *) 
        fun mk_NotConsts path (t1$t2) constrs = 
            let 
              val (hd, args) = Term.strip_comb (t1$t2) 
            in
              if Term.is_Const hd then
                List.foldl (fn ((ind,arg), constrs') => 
                               mk_NotConsts (path@[ind]) arg constrs') 
                            (mk_NotConsts path hd constrs) 
                            (Library.map_index I args)
              else raise mk_constr_exp (t1$t2,
                         "Does not support constraint generation from terms without a Const in head position.")
            end
          | mk_NotConsts path (Const(nm,_)) constrs =
                (NotConst(Path path, ConstantName.mk nm))::constrs
          | mk_NotConsts _ _ constrs = constrs;

        val (top_const, args) = Term.strip_comb t;
      in      
        if Term.is_Const top_const then 
          List.foldl (fn ((ind,arg), constrs) =>
                         mk_NotConsts [ind] arg constrs)
                     [] (Library.map_index I args)
        else
          raise mk_constr_exp (t,
                         "Does not support constraint generation from terms without a Const in head position.")
      end )
   | _ => []; (* Nothing to do *)

end (* local open SynthNames *)

end; (*struct *)
