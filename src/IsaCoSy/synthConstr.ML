(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      SynthConstr.ML
    Author:     Moa Johansson
                moa.johansson@chalmers.se                
                             
 
How IsaCoSy theory constraints, which are associated with each constant
it uses during synthesis.

*)
(* -------------------------------------------------------------------------*)

structure SynthConstr =
struct
  local open SynthNames in   


datatype pos = 
           Hole of HoleName.name
         | HolePath of HoleName.name * int list

datatype T = 
         UnEqual of pos list
       | NotConst of pos * ConstantName.name
       | NotVar of pos * string (* disallowing a forall-bound variable during synthesis *)
       | Or of T list
       | SATISFIED (* Trivally satisfied constraint *)
       | VIOLATED  (* Trivially violated *)

(* ------------------------------------------------------------*)
(* Pretty print constraints.*)
(* ------------------------------------------------------------*)

fun pretty_pos (Hole n) = 
      Pretty.block [Pretty.str "Hole ",  HoleName.pretty_name n]
    | pretty_pos (HolePath (h,p)) = 
      Pretty.block [Pretty.str "HolePath ", Pretty.str "(", 
                    Pretty.str "Hole ",  HoleName.pretty_name h,
                    Pretty.list "[" "]" (map (Pretty.str o Int.toString) p),
                    Pretty.str ")"];
  
fun pretty_constr (UnEqual l) =
      Pretty.block [Pretty.str "UnEqual ", 
                    Pretty.list "[" "]" (map pretty_pos l)]
    | pretty_constr (NotConst (p, constn)) = 
      Pretty.block [Pretty.str "NotConst(", 
                    pretty_pos p,
                    Pretty.str ", ",
                    ConstantName.pretty_name constn,
                    Pretty.str ")"]
    | pretty_constr (NotVar (p,varnm)) = 
      Pretty.block [Pretty.str "NotVar(", 
                    pretty_pos p,
                    Pretty.str ", ",
                    Pretty.str varnm,
                    Pretty.str ")"]               
    | pretty_constr (Or sub_constrs) =
      Pretty.block [Pretty.str "OR ", 
                    Pretty.list "[" "]"
                    (map pretty_constr sub_constrs)]
    | pretty_constr SATISFIED = Pretty.str "SATISFIED"
    | pretty_constr VIOLATED = Pretty.str "VIOLATED";

val print_constr = Pretty.writeln o pretty_constr;
(* ------------------------------------------------------------*)

(* Default name for constraints *)
val default_name = ConstraintName.mk ("C",0);    

fun hole_of_pos p = case p of Hole(hole) => SOME hole | _ => NONE;
                       
fun holes_of_constr (NotConst(p,_)) = (case p of Hole (hole) => [hole] | _ => [])
   | holes_of_constr (UnEqual ps) = 
          map_filter (fn p => (case p of Hole (hole) => SOME hole | _ => NONE)) ps
   | holes_of_constr (NotVar(p,_)) = (case p of Hole (hole) => [hole] | _ => [])
   | holes_of_constr (Or subconstrs) = maps holes_of_constr subconstrs
   | holes_of_constr _ = [];
 
fun top_hole_of_pos (Hole h) = h
  | top_hole_of_pos (HolePath(h,_)) = h;

fun top_holes_of_constr' (NotConst(p,_)) = [top_hole_of_pos p]
   | top_holes_of_constr' (UnEqual ps) = map top_hole_of_pos ps
   | top_holes_of_constr' (Or subconstrs) = maps top_holes_of_constr' subconstrs
   | top_holes_of_constr' (NotVar(p,_)) = [top_hole_of_pos p]
   | top_holes_of_constr' _ = [];

fun top_holes_of_constr c = Library.distinct HoleName.name_eq (top_holes_of_constr' c);
   
(* Synth constraints are created from theory constraints, given a mapping from 
   Argument numbers to HoleNames. *)
exception Path of (string * int list)

fun try_from_path' arg_to_hole p =
     case p of [] => raise Path ("from_path: Empty Path.", p)
             | [p] => (case(ArgName.NTab.lookup arg_to_hole p) of
                           SOME nw_pos => SOME (Hole(nw_pos))
                         | NONE => NONE)
             | (p::ps) => (case(ArgName.NTab.lookup arg_to_hole p) of
                            SOME nw_pos => SOME (HolePath(nw_pos, ps))
                          | NONE => NONE);

fun try_from_path arg_to_hole (ThyConstr.Path p) = try_from_path' arg_to_hole p;

fun from_thy_constr arg_to_hole constr =
    case constr of
       ThyConstr.NotConst(p, c) => NotConst(the (try_from_path arg_to_hole p), c)
     | ThyConstr.UnEqual(ps) => UnEqual(map (the o try_from_path arg_to_hole) ps)
     | ThyConstr.Or(cs) => Or(map (from_thy_constr arg_to_hole) cs);

fun add_to_path (Hole h) i = HolePath(h,[i])
   | add_to_path (HolePath(h,p)) i = HolePath(h,p@[i]); 

exception dbg_exp of (HoleName.name ArgName.NTab.T * HoleName.name * ConstantName.name * T);

(* Given that hole has been instantiated to const, update all constraints that mention hole *)
fun update_constrs_on_hole arg_to_hole hole const constr = 
    (case constr of
        NotConst(p,c) => 
          if (HoleName.name_eq(top_hole_of_pos p, hole)) then
              (case p of (Hole(_)) => if ConstantName.name_eq(c,const) then VIOLATED else SATISFIED
                      | (HolePath(_,p)) => 
                        (case (try_from_path' arg_to_hole p) of
                           SOME nw_pos => NotConst(nw_pos, c)
                         | NONE => SATISFIED)) (* No new hole for the pos this refered to, hence trivially sat.*)
          else NotConst(p,c)
      | NotVar(p,c) => 
          if (HoleName.name_eq(top_hole_of_pos p, hole)) then 
              (case p of Hole(_) => SATISFIED
                      | HolePath(_,p) => 
                        (case (try_from_path' arg_to_hole p) of 
                           SOME nw_pos => NotVar(nw_pos,c)
                         | NONE => SATISFIED))  (* No new hole for the pos this refered to, hence trivially sat.*)
          else NotVar(p,c)
      | Or(cs) => 
          let 
            val nw_cs = 
                map_filter (fn c => case (update_constrs_on_hole arg_to_hole hole const c) of 
                               VIOLATED => NONE | nwc => SOME nwc) cs 
          in
            if (exists (fn c => case c of SATISFIED => true | _ => false) nw_cs) then SATISFIED  
            else (case nw_cs of [] => VIOLATED | [newc] => newc | _ => Or(nw_cs))
          end
      | UnEqual(ps) => 
        (* First of all, is hole mentioned in ps? If not no update aside from positions. If yes,
           more involved update. *)
          let
            fun hole_eq (nm1,h2) = case h2 of Hole(nm2) => HoleName.name_eq(nm1,nm2)| _ => false
          in
          if (member hole_eq ps hole) 
          then 
              let 
                (* Not all of the other positions can be instantiated to const *)
                val not_consts = 
                    map_filter (fn p => if (HoleName.name_eq(top_hole_of_pos p, hole)) then 
                                           (case p of Hole(_) => NONE (* drop ref to this hole *)
                                                    | HolePath(_,p) => 
                                                      case (try_from_path' arg_to_hole p) of
                                                        SOME nw_pos => SOME(NotConst(nw_pos,const))
                                                      | NONE => NONE)
                                         else SOME(NotConst(p,const)))
                                 ps
                (* If they are all instantiated to const, they need to differ in the arguments *)
                val other_ps = Library.remove hole_eq hole ps
                val uneqs = map
                            (fn (ind,nw_hole) =>
                              UnEqual ((Hole(nw_hole) :: 
                                       (map (fn p => add_to_path p ind) other_ps)))) 
                            (ArgName.NTab.list_of arg_to_hole)
                in 
                  case (not_consts@uneqs) of 
                        [] => raise ERROR "UnEqual updated to empty. Shouldn't happen."
                      | [c] => c
                      | (c::cs) => Or(c::cs) 
                end
          (* We only need to update some position-information, not the constraint itself *)   
          else
              UnEqual (map_filter 
                         (fn p => if(HoleName.name_eq(top_hole_of_pos p,hole)) then 
                                    (case p of Hole(_) => raise ERROR "Bug. This hole can't be here. "
                                             | HolePath(_,p) => try_from_path' arg_to_hole p)
                                  else SOME p) 
                           ps) 
          end
     | VIOLATED => VIOLATED
     | SATISFIED => SATISFIED)
handle UNDEF => raise dbg_exp (arg_to_hole, hole, const, constr);



(* Update the constraints on hole after it has been instantiated to a Free variable *)
fun update_constrs_on_hole_var hole varnm constr = 
     case constr of 
       NotConst(p,c) => if (HoleName.name_eq(top_hole_of_pos p, hole)) then SATISFIED
                          else NotConst(p,c)
     | NotVar(p,v) => if (HoleName.name_eq(top_hole_of_pos p, hole)) then 
                               (case p of Hole(_) => (if varnm=v then VIOLATED else SATISFIED) 
                                        | HolePath(_,p) => SATISFIED)
                             else NotVar(p,v)
     | Or(cs) =>  
         let 
            val nw_cs = map_filter (fn c => case (update_constrs_on_hole_var hole varnm c) of 
                                            VIOLATED => NONE | nwc => SOME nwc) cs
         in
            if (exists (fn c => case c of SATISFIED => true | _ => false) nw_cs) then SATISFIED  
            else (case nw_cs of [] => VIOLATED | [newc] => newc | _ => Or(nw_cs))
         end 
     | UnEqual(ps) => 
     (* First of all, is hole itself mentioned in ps? If so, update.
        If not mentioned, must mean we're under an OR, so this constraint shouldn't change *)                         
        let
           fun hole_eq (nm1,h2) = case h2 of Hole(nm2) => HoleName.name_eq(nm1,nm2)| _ => false
        in
          if (member hole_eq ps hole) 
          then 
              let 
                (* Not all of the other positions can be instantiated to const *)
                val not_vars = 
                    map_filter (fn p => if (HoleName.name_eq(top_hole_of_pos p, hole)) then NONE
                                        else SOME(NotVar(p,varnm))) ps
              in
                 case not_vars of [] => SATISFIED | [c] => c | (c::cs) => Or(c::cs) 
             end 
          else UnEqual(ps) end
     | SATISFIED => SATISFIED
     | VIOLATED => VIOLATED;                       
 
end (* local open SynthNames *)

end; (*struct *)
