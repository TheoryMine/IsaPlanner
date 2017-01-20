(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Multfert extension of basic_rtechn.ML                                *)
(*  Author: Daniel Raggi, Lucas Dixon                                  *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)

signature RIPPLE_MULTFERT =
sig
  exception rippling_rtechn_exp of string
  structure RippleCInfo : BASIC_RIPPLE_CINFO 
  structure BasicRipple : BASIC_RIPPLE
  
  val endr_multfert :  RTechn.T
  val weak_multfert_goal :  PPlan.gname -> RTechn.T
 
  val ripple_stepcase_multfert :  PPlan.gname -> RTechn.T
  val induct_and_ripple_multfert : PPlan.gname -> RTechn.T
  val induct_and_ripple_with_rule_multfert : PPlan.gname -> xstring -> RTechn.T

end;


functor RippleMultFertRTechnFUN
          (structure RippleCInfo : BASIC_RIPPLE_CINFO
           structure ConjRTechn : CONJ_RTECHN)
= struct

structure RippleCInfo = RippleCInfo;
local
  open RTechnEnv;
in

exception rippling_rtechn_exp of string;
  
structure BasicRipple = 
   BasicRippleRTechnFUN(structure RippleCInfo = RippleCInfo 
                        structure ConjRTechn = ConjRTechn);
   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Multiple Fertilisation                                             *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
fun small_seq n s = 
  case Seq.pull s of 
    SOME (h,t) => Seq.make (fn () => SOME (h, small_seq (n-1) t))
  | NONE => Seq.empty
  
fun subst_in_lhs_until_fail skelnm sym goal rst =
    let
      val newseq = givename RstName.weak_fert_leftN (RTechnEnv.subst_in_lhs skelnm sym goal) rst
      val no_more_ferts = (end_rst (RstName.end_fertN goal) rst |> RState.set_goalnames [goal] )
    in
      case Seq.pull newseq of
        NONE => Seq.single no_more_ferts
      | SOME _ => Seq.append 
                    newseq
                    (Seq.map (RState.set_rtechn
                                (SOME (HTraceCInfo.thenify 
                                        (map_then (subst_in_lhs_until_fail skelnm sym)))))
                             newseq
                    )
    end ;


fun subst_in_rhs_until_fail skelnm sym goal rst =
    let
      val newseq = givename RstName.weak_fert_rightN (RTechnEnv.subst_in_rhs skelnm sym goal) rst
      val no_more_ferts = (end_rst (RstName.end_fertN goal) rst |> RState.set_goalnames [goal])
    in
      case Seq.pull newseq of
        NONE => Seq.single no_more_ferts
      | SOME _ => Seq.append 
                    newseq
                    (Seq.map (RState.set_rtechn
                                (SOME (HTraceCInfo.thenify 
                                        (map_then (subst_in_rhs_until_fail skelnm sym)))))
                             newseq
                    )
    end;


fun subst_skel_multfert goal (skelnm,skel) rst =
  (if BasicRipple.is_eq_term skel then
       let
         val gt = RstPP.goal_concl rst goal
         val z = Zipper.mktop gt
       in
         if BasicRipple.is_eq_term gt then
           (orr_list [subst_in_lhs_until_fail skelnm false goal,
                     subst_in_rhs_until_fail skelnm true goal])
         else
           (* try the skelequation both ways around *)
           orr_list [RTechnEnv.subst_eq skelnm false goal,
                     RTechnEnv.subst_eq skelnm true goal]
       end else fail) rst;


fun subst_skels goal skels = orr_list (map (subst_skel_multfert goal) skels);

fun subst_skels_multfert2 goal [] rst = Seq.single (RState.set_goalnames [goal] rst)
  | subst_skels_multfert2 goal (skel1::skels) rst =
    (subst_skel_multfert goal skel1 rst)
      |> Seq.maps (fold_over_each_goal (fn g => subst_skels_multfert2 g skels));


fun weak_multfert_skels_goal skels goal rst =
   subst_skels_multfert2 goal skels rst;


fun weak_multfert_goal goal rst =
  rst 
   |> (refine RstName.weak_fert_startN
        (weak_multfert_skels_goal (RippleCInfo.skeleton_namedterms_of rst goal) goal)) 
   |> small_seq 4;
   
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
(*  Induction and Rippling: no conjecturing                            *)
(* -=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=- *)
fun endr_multfert rst =
    rstif (null o RState.get_goalnames)
          (dummy RstName.solved_by_ripplingN)
          (split_then (RippleCInfo.success_chk rst)
                      (map_then BasicRipple.strong_fert_goal)
                      ((map_then weak_multfert_goal)
                         try1_then
                         ((map_then DTacRTechn.simp_noasm)
                            try1_orelse
                            (dummy (RstName.str "Step case stuck")))))
      rst;
      
fun ripple_stepcase_multfert goal rst =
    (refine RstName.stepcase_by_ripplingN
            ((BasicRipple.startr_on_goal goal)
               thenr (BasicRipple.rsteps_on_goal goal)
               thenr endr_multfert))
      rst;

fun induct_and_ripple_multfert g rst =
    (refine RstName.induct_and_rippleN
           (InductRTechn.induction_on_goal
              g
              (map_then BasicRipple.simplify_basecase)
              (map_then ripple_stepcase_multfert)))
           rst;

fun induct_and_ripple_with_rule_multfert g rule rst =
    (refine RstName.induct_and_ripple_with_ruleN
           (InductRTechn.induction_on_goal_with
              g
              (Proof_Context.get_thm (RState.get_ctxt rst) rule)
              (map_then BasicRipple.simplify_basecase)
              (map_then ripple_stepcase_multfert)))
      rst;

            
end; (* RTechnEnv local *)

end; (* struct *)
