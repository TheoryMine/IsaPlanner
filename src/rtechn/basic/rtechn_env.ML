(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  Title:      rtechn/rtechn_env.ML
    Author:     Lucas Dixon, University of Edinburgh
                lucas.dixon@ed.ac.uk
    created:    30 Jun 2005
*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
(*  DESCRIPTION:

    Basic ML envrinoment for writing techniques, combinators and 
    basic manipulations of the reasoning state. 

*)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *) 
infixr 6 thenr;
infixr 7 thenf;
infixr 7 thenfs;
infixr 7 fthen;
infixr 7 fsthen;
infixr 5 orr;
infixr 5 xorelse;
infixr 6 try1_then;
infixr 6 try1_orelse;

signature RTECHN_ENV =
sig
include RTECHN_COMB

(* goal based technique combinators *)
val fold_over_each_goal : (PPlan.gname -> RTechn.T) -> RTechn.T
val and_then :  PPlan.gname list * RTechn.T -> 
                PPlan.gname list * RTechn.T -> 
                RTechn.T
val split_then : (PPlan.gname -> bool) ->
                   RTechn.T ->
                   RTechn.T -> RTechn.T

(* create new reasoning techniques *)
val map_then : (PPlan.gname -> RTechn.T) -> RTechn.T
val try_map_then : (PPlan.gname -> RTechn.T) -> RTechn.T (* FIX THIS *)

(* for manipulation of the current state*)
val map_rstf : (PPlan.gname -> RState.T -> RState.T) -> RState.T -> RState.T
val map_rstseqf : (PPlan.gname -> RState.T -> RState.T Seq.seq) 
                  -> RState.T -> RState.T Seq.seq

(* utility *)
val split_goals : (PPlan.gname -> bool) -> PPlan.gname list 
                  -> PPlan.gname list * PPlan.gname list 

(* apply dtac to a specific goal *)
val apply_dtac_to_g : DTac.T -> PPlan.gname -> RTechn.T 

(* applies dtac to all current goals *)
val apply_dtac :  DTac.T -> RTechn.T 

(* apply, as or-choice, the dtacs to every goal *)
val apply_or_dtacs :  DTac.T list -> RTechn.T 

(* applies or-choice of dtacs to a goal (gives back applied dtac and rst *) 
val apply_or_dtacs_to_g :  
    DTac.T list -> PPlan.gname -> RState.T -> (DTac.T * RState.T) Seq.seq

(* internal application of dtac without naming state or updating descrip etc *)

val also_apply_dtac_to_g : DTac.T -> PPlan.gname -> RTechn.T


(* resolution *)
val apply_res : PPlan.gname -> PPlan.gname -> RTechn.T
val apply_fres :
       PPlan.gname (* an assumption *)
       * PPlan.gname (* of this goal *)
       -> PPlan.gname -> RState.T -> 
       ((PPlan.gname list (* subgoals *)
         * PPlan.gname) (* new fact name *)
        * RState.T) Seq.seq

(* resolution with theorems *)
val rule_dthm_dtac : DThm.T -> DTac.T

(* resolution with theorems *)
val apply_erule_dthm :
       DThm.T -> PPlan.gname -> PPlan.gname -> RTechn.T
val apply_rule_dthm : DThm.T -> PPlan.gname -> RTechn.T
val apply_restr_rule_dthm : DThm.T -> PPlan.gname -> RTechn.T
val apply_frule_dthm :
       DThm.T -> PPlan.gname -> RState.T -> RState.T Seq.seq

(* substition with internal results 
   1st argument is equation, 
   2nd argument is symmerty flag, if true, rewrites right to left
   3rd argument is goal name 
*)
val subst_eq : PPlan.gname -> bool -> PPlan.gname -> RTechn.T

(* substition in lhs and rhs of an equality goal *)
val subst_in_lhs : PPlan.gname -> bool -> PPlan.gname -> RTechn.T
val subst_in_rhs : PPlan.gname -> bool -> PPlan.gname -> RTechn.T

(* substition with a theorem *)
val subst_thm : Thm.thm -> bool -> PPlan.gname -> RTechn.T

end;

structure RTechnEnv_DB
= struct
open RTechnComb;


(* Apply a dtac to all goalnames in a rst. Get back a seq of rst which are
all combination of or-choises over the application of the dtac
to the goals in the rst. Each rst contains one application of the dtac for
each goal  *)
(* note: this does not remove g from goals *)

(* note: does not set name *)
fun also_apply_dtac_to_g dtac g rst =
      Seq.map
        (fn (rsgs,ppl) => 
            rst |> RState.add_curnames rsgs
                |> RState.set_pplan ppl
          (*      |> RState.push_lcinfo g *)
        ) (DTac.gtac dtac (([],[g]), RState.get_pplan rst));

(* Apply a dtac to a goal, producing new rsts containing the new goals only*)
fun apply_dtac_to_g dtac g rst =
      Seq.map
        (fn (rsgs,ppl) => 
            rst |> RState.set_curnames rsgs
                |> RState.set_pplan ppl
             (*   |> RState.push_lcinfo g *)
                |> RState.set_rtechn NONE
                |> DescripCInfo.set_rst (RstName.dtac dtac))
        (DTac.gtac dtac (([],[g]),RState.get_pplan rst));

fun apply_dtac_to_r dtac r rst =
      Seq.map
        (fn (rsgs,ppl) => 
            rst |> RState.set_curnames rsgs
                |> RState.set_pplan ppl
           (*     |> RState.push_lcinfo r *)
                |> RState.set_rtechn NONE
                |> DescripCInfo.set_rst (RstName.dtac dtac))
        (DTac.gtac dtac (([r],[]),RState.get_pplan rst));

(* or-choice over dtacs *)
fun apply_or_dtacs_to_g dtacs g rst =
    Seq.maps 
      (fn dtac => Seq.map (fn rst => (dtac,rst)) 
                          (apply_dtac_to_g dtac g rst))
      (Seq.of_list dtacs);

(* apply to all goals in every possible way *)
(* apply f to each goal in every way, in general many permutations*)
fun fold_over_each_goal f rst =
    fold (Seq.maps o f)
         (RState.get_goalnames rst)
         (Seq.single (RState.set_goalnames [] rst));

(* Note: probably don't actually want to call this unless there is
only one goalname in the rst, otherwise you get a wild explosion in
the permutations of ways of applying the dtac to different goals --
which is necessary for goals containing meta-variables but not for
other goals. *) 
(* implicit dtac *)
fun apply_dtac dtac = 
    RTechnComb.givename 
      (RstName.dtac dtac) 
      (RTechn.stopify (fold_over_each_goal (also_apply_dtac_to_g dtac)));

val apply_or_dtacs = orr_list o map apply_dtac;

(* ----------- Resolution with thms, dthms ----------- *)
fun rule_thm_dtac th =
    DTac.mk (K (Pretty.str ("Resolution backward using thm " ^ (Thm.get_name_hint th))), 
             GTacs.of_bckf (PPlan.apply_rule_thm th));

(* resultion backwards from dthm *)
fun rule_dthm_dtac dthm =
    DTac.mk (K (Pretty.block [Pretty.str "Resolution backward using dthm ", 
                           DThm.pretty dthm]), 
             GTacs.of_bckf (PPlan.apply_rule_thm (DThm.finalthm_of dthm)));

(* restricted to not allow top-level meta-varaibles to throw away all
   their arguments *)
fun restr_rule_dthm_dtac dthm =
    DTac.mk (K (Pretty.block [Pretty.str "Resolution (restricted) backward using dthm ", 
                           DThm.pretty dthm]), 
             GTacs.of_bckf (Res.restr_res (DThm.finalthm_of dthm)));


(* first prem of dthm is matched against aname. Gives new goal and assumptions *)
(* TODO: shouldn't this be seen as a forward gtac ??? *)
fun erule_dthm_dtac dthm aname =
    DTac.mk (K (Pretty.block [Pretty.str "Resolution backward using dthm ", 
                           DThm.pretty dthm]), 
             GTacs.of_bckf (PPlan.apply_erule_thm (DThm.finalthm_of dthm) 
                                                  aname));

(* assume thm has only one premise and this first prem is matched against 
   aname. to give new result *)
(* TODO: shouldn't this be seen as a forward gtac ??? *)
fun frule_dthm_dtac dthm =
    DTac.mk (K (Pretty.block [Pretty.str "Resolution foward using dthm ", 
                           DThm.pretty dthm]), 
             GTacs.of_fwd1f (PPlan.apply_frule_thm (DThm.finalthm_of dthm)));


(* ----------- Resolution results ----------- *)
(* resoltuion backwards from another result *)
fun rule_dtac fname =
    DTac.mk (K (Pretty.block [Pretty.str "Resolution backward using ", 
                           Pretty.str fname]), 
             GTacs.of_bckf (PPlan.apply_res_bck fname));


(* ----------- Resolution with thms, dthms ----------- *)
(* implicit: thm gname rst *)
val apply_rule_dthm = apply_dtac_to_g o rule_dthm_dtac;
val apply_restr_rule_dthm = apply_dtac_to_g o restr_rule_dthm_dtac;
(* implicit: thm rname gname rst *)
val apply_erule_dthm = apply_dtac_to_g oo erule_dthm_dtac;
(* implicit: thm fname rst *)
val apply_frule_dthm = apply_dtac_to_r o frule_dthm_dtac;

(* ----------- Resolution with other results ----------- *)

(* implicit: factname gname rst *)
val apply_res = apply_dtac_to_g o rule_dtac;

(* ----------- Resolution techniques ----------- *)

(* forward resolution: resolve a fact with an assumption "aname" of
other result "cname". Produces the a new cname result without the
assumption. *)
fun apply_fres (aname,cname) factname rst = 
      Seq.map
        (fn (cname2,ppl) => 
            (cname2, rst |> RState.set_pplan ppl
                         |> RState.set_rtechn NONE
                         |> DescripCInfo.set_rst 
                         (RstName.str ("resolving assumption " 
                           ^ aname ^ " of " ^ cname ^ " using " 
                                       ^ factname))))
        (PPlan.apply_res_fwd (aname,cname) factname (RState.get_pplan rst));


(* substitution with equations *)
fun subst_eq eqname sym gname rst = 
    Seq.map (fn ((newg,gs), ppl) => 
                 rst |> RState.set_goalnames gs
                     |> RState.set_pplan ppl
                  (*   |> RState.push_lcinfo gname *)
                     |> RState.set_rtechn NONE
                     |> DescripCInfo.set_rst (RstName.str "subst"))
    (Subst.apply eqname sym gname (RState.get_pplan rst));


fun subst_in_lhs eqname sym gname rst = 
    Seq.map (fn ((newg,gs), ppl) => 
                 rst |> RState.set_goalnames gs
                     |> RState.set_pplan ppl
                  (*   |> RState.push_lcinfo gname *)
                     |> RState.set_rtechn NONE
                     |> DescripCInfo.set_rst (RstName.str "subst lhs"))
    (Subst.apply_at_lhs eqname sym gname (RState.get_pplan rst));

fun subst_in_rhs eqname sym gname rst = 
    Seq.map (fn ((newg, gs), ppl) => 
                 rst |> RState.set_goalnames gs
                     |> RState.set_pplan ppl
                   (*  |> RState.push_lcinfo gname *)
                     |> RState.set_rtechn NONE
                     |> DescripCInfo.set_rst (RstName.str "subst rhs"))
    (Subst.apply_at_rhs eqname sym gname (RState.get_pplan rst));

fun subst_thm thm sym gname  rst = 
    Seq.map (fn ((newg, gs), ppl) => 
                 rst |> RState.set_goalnames gs
                     |> RState.set_pplan ppl
                   (*  |> RState.push_lcinfo gname *)
                     |> RState.set_rtechn NONE
                     |> DescripCInfo.set_rst (RstName.str "subst thm"))
    (Subst.apply_thm thm sym gname (RState.get_pplan rst));



(* Apply the reasoning technique to the goals.*)
(* implicit rst *)
fun apply_to_goals gnames rtech =
    rtech o RState.set_goalnames gnames;

(* split goals into two collections using a split function *)
fun split_goals splitf goals =
    let
      fun split_aux splitf (trues,falses) [] =  (trues,falses)
        | split_aux splitf (trues,falses) (h::t) =
          if (splitf h) then split_aux splitf (h::trues, falses) t
          else split_aux splitf (trues, h::falses) t
    in
      split_aux splitf ([],[]) goals
    end;        
  
(* Need two cases, if no goalnames for the 1st techn to be applied to
this just behaves as apply_to_goals of the second technique.
Similarly if no goals for 2nd technique, don't add it as continue.*)
fun and_then ([],_) (goals2, tech2) =  
    tech2 o RState.set_goalnames goals2
  | and_then (goals1, tech1) ([],_) = 
    tech1 o RState.set_goalnames goals1
  | and_then (goals1,tech1) (goals2,tech2) = 
    ((RState.set_goalnames goals1) fthen tech1)
      thenf (fn rst => 
                let val endoftech1_goals = RState.get_goalnames rst
                in
                  rst |> RState.set_goalnames goals2 
                      |> RState.set_rtechn 
                      (SOME (tech2 thenf (RState.add_goalnames endoftech1_goals)))
                end);

fun split_then splitfun truetech falsetech rst =
    let 
      val (true_gs, false_gs) = split_goals splitfun (RState.get_goalnames rst)
    in
      and_then (true_gs,truetech) (false_gs,falsetech) rst
    end;

(* evaluate each goal THEN the next, apply the technique to 
   the goals one at the time *)
fun map_then gtechn rst0 = 
    let 
      fun mapt [] = fail (* alternative idea: could have id *)
        | mapt [g] = ((RState.set_goalnames []) fthen (gtechn g))
        | mapt (g::goalnames) =
          (((RState.set_goalnames []) fthen (gtechn g))
            thenf (fn rst' => 
                   let val endoftech_goals = RState.get_goalnames rst'
                   in
                     rst' 
                       |> RState.set_rtechn 
                       (SOME ((mapt goalnames) thenf 
                         (RState.add_goalnames endoftech_goals)))
                   end));
    in
      mapt (RState.get_goalnames rst0) rst0
    end;

(* apply rstf to each goal *)
(* function is expected to generate/make new goal names! *)
fun map_rstf rstf rst0 = 
    let 
       fun goalfoldf g (newgoals, rst) = 
           let 
             val rst' = 
                 rst |> RState.set_goalnames []
                     |> rstf g
             val morenewgoals = RState.get_goalnames rst'
           in (morenewgoals @  newgoals, rst') end;

    val (allnewgoals, rst2) = 
        fold goalfoldf (RState.get_goalnames rst0) ([],rst0)

    in RState.set_goalnames allnewgoals rst2 end;

(* function is expected to generate/make new goal names! *)
fun map_rstseqf rstseqf rst0 = 
    let 
      fun goalfoldf g (newgoals, rst) = 
           let 
             val rsts' = 
                 rst |> RState.set_goalnames []
                     |> rstseqf g

             fun nextf rst' =
                 let val morenewgoals = RState.get_goalnames rst'
                 in (morenewgoals @  newgoals, rst') end
           in Seq.map nextf rsts' end;
    in 
      (Seq.single ([],rst0))
        |> fold (Seq.maps o goalfoldf) (RState.get_goalnames rst0) 
        |> Seq.map (fn (allnewgoals, rst2) =>
                        RState.set_goalnames allnewgoals rst2)
    end;

(* like map then but allows gtechn to not apply to some goals,
ie, if gtechn doesn't apply, the goal goes through unchanged. *)
fun try_map_then gtechn rst0 = 
    let 
      fun mapt [] = fail (* alternative idea: could have id *)
        | mapt [g] = ((RState.set_goalnames []) fthen (gtechn g))
        | mapt (g::goalnames) =
          (((RState.set_goalnames []) fthen ((gtechn g) try1_orelse (fn rs => (Seq.single (RState.set_goalnames [g] rs)))))
            thenf (fn rst' => 
                   let val endoftech_goals = RState.get_goalnames rst'
                   in
                     rst' 
                       |> RState.set_rtechn 
                       (SOME ((mapt goalnames) thenf 
                         (RState.add_goalnames endoftech_goals)))
                   end));
    in
      mapt (RState.get_goalnames rst0) rst0
    end;




end;
structure RTechnEnv : RTECHN_ENV = RTechnEnv_DB;




(* A one-step reasoning technique that; given a pretty print info and
a function on proof states and a goal name.  *)
(* val rtechn_of_prf_f 
    : Pretty.T (* description *)
      * (PPlan.gname 
         -> PPlan.T
         -> (PPlan.gname list * PPlan.T) 
              Seq.seq) (* proof plan modifier *)
      -> PPlan.gname (* apply to this goal name *)
      -> RTechn.T

(* make a one-step reasoning technique, that needs to be given a goal
name, from a pretty print info and a function on proof states. *)
fun rtechn_of_prf_f (p,f) g rst = 
     Seq.map 
       (fn (sgs,p2) => 
           rst |> RState.set_pplan p2
               |> RState.set_curnames ([],sgs)
               |> RState.set_rtechn NONE
               |> DescripCInfo.set_rst (RstName.pretty p))
       (f g (RState.get_pplan rst));

*)





(* work forwards using a theorem. gives back (gname, rst), with rst
having new subgoals being any remaining conditions. gname is the name
of the new introduced fact *)
(* 

fun fwd_thm th gnamel rst = 
    let 
      val p = RState.get_pplan rst
      val ((fwd_name, subgnames),p2) = 
          Prf.insert_fwd_thm (map (K true) gnamel) th p

      fun resol_step (r,g) (sgs, p) = 
          Seq.map 
            (fn (sgs1,p') => (sgs1 @ sgs,p'))
            (Prf.apply_goal_resol r g p);
    in 
      Seq.map (pair fwd_name)
              (fold (Seq.maps o resol_step) (gnamel ~~ subgnames) 
                    (Seq.single ([],p2)))
    end;
*)
