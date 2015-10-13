signature ISAP_SPLITTER_DATA =
sig
 val conjI : Thm.thm
 val impI : Thm.thm
 val split_if : Thm.thm
 val if_P : Thm.thm
 val if_not_P : Thm.thm
 val is_if : Trm.T -> bool
 val subst_bool : Thm.thm

end;
structure HOLIsaP_SplitData : ISAP_SPLITTER_DATA =
struct

val conjI = @{thm "HOL.conjI"};
val split_if = @{thm "IsaPHOLUtils.IsaP_split_if"};
val impI = @{thm "HOL.impI"};
val if_P = @{thm "HOL.if_P"};
val if_not_P = @{thm "HOL.if_not_P"};
val subst_bool = @{thm "IsaPHOLUtils.subst_bool"};

fun is_if t =
    let 
      (* Search for if-statements *)
      (*fun sf_if z = 
          case Zipper.trm z 
           of (_ $ _) => [Zipper.LookIn (Zipper.move_down_left z),
                          Zipper.LookIn (Zipper.move_down_right z)]
            | (Abs _) => [Zipper.LookIn (Zipper.move_down_abs z)]
            | (Const("HOL.If",_)) => [Zipper.Here z]
            | _ => [];*)

      val ifs = Seq.filter (fn z => case (Zipper.trm z) 
                                               of (Const("HOL.If",_)) => true
                                                | _ => false) 
                                   (ZipperSearch.leaves_lr (Zipper.mktop t))
    in
      not (null (Seq.list_of ifs))
    end;

end;

structure SplitterRTechn =
struct
local 
  open RTechnEnv;
in

fun is_if goal rst = 
    HOLIsaP_SplitData.is_if (RstPP.goal_concl goal rst);

fun try_if_branch branch_thm goal rst =
    let
      fun prove_cond old_rst ((newg, all_gs), ppl) =
          let  
            val rst = RState.set_pplan ppl old_rst
            val asms = PPlan.get_lasms ppl goal
            (* Solve the conditions by simplification *)
            val cond_gs = filter (fn g => not (g=newg)) all_gs
            val rsts' = ((map_then 
                            (fn g => (orr_list  
                                        (map (fn asm => apply_res asm g) 
                                             asms))))
                          try1_orelse 
                          DTacRTechn.multi_simp_no_asm_simp_changes)
                          (RState.set_goalnames cond_gs rst)
          in
            Seq.map (RState.set_goalnames [newg])
                    (Seq.filter (null o RState.get_goalnames) rsts')
          end
    in
      Seq.maps (prove_cond rst) 
               (Subst.apply_thm branch_thm false goal (RState.get_pplan rst))
    end;


val splitN = RstName.str "Case-split if-statement";
val ifTrueN = RstName.str "then-branch of if-statement"
val ifFalseN = RstName.str "else-branch of if-statement" 

(* If the condition can be proven true or false by resolution
with an assumption, go down that branch.
Otherwise introduce a case-split *)
fun split_if_rtechn goal = 
    (* if condition is proved true *)
      (givename ifTrueN            
                (try_if_branch HOLIsaP_SplitData.if_P goal))
      try1_orelse
      (* if condition is proved false *)
      (givename ifFalseN
                (try_if_branch HOLIsaP_SplitData.if_not_P goal))
      try1_orelse
      (*if condition not provable *)
      (*Introduce a case-split on the if-condition*)
      (givename splitN
                (apply_restr_rule_dthm (DThm.mk HOLIsaP_SplitData.split_if) 
                                       goal));


(*-------------------------------------------------------------- *)
(*                  Splitting case-statements                    *)
(*-------------------------------------------------------------- *)

(* Get the case-split theorem and a list of theorems to rewrite
a case-statemnent if we know which case to go for. *)
(*fun casesplit_thms_of_type thry (typ,dt) =
    let
     (* val dtypestab = Datatype.get_all thry;
      val ty_str = case ty of 
                     Type(ty_str, _) => ty_str
                   | TFree(s,_)  => raise error 
                                            ("Free type: " ^ s)   
                   | TVar((s,i),_) => raise error 
                                            ("Free variable: " ^ s)

      val dt = case Symtab.lookup dtypestab ty_str
                of SOME dt => dt
                 | NONE => error ("Not a Datatype: " ^ ty_str) *)

      val rw_list = (#case_rewrites dt)                     
    in
       rw_list
    end;
*)

(* If there are case-statements, try and identify them by 
cheking if they match the "case-name" for any of our known datatypes *)

(* IMPROVE: don't go through every element in thelist - do a
   lookup directly based on the names in datatype names the goal 
   (This involves a table of const-names to case stuff about them.)
*)
fun get_cases_of pp goal = 
    let  
      val thry = PPlan.get_theory pp;
      val t = Prf.get_ndname_ctrm pp goal;
      (* TODO(Isabelle2015): not sure if this is the right datatype package *)
      val dtypestab = BNF_LFP_Compat.get_all thry [];

      (* Pairs type-string * datatype_info.*)
      val datatypes = Symtab.dest dtypestab;
      val z = Zipper.mktop t;
  
      val cases = Seq.map_filter 
                    (fn z => case (Zipper.trm z) of 
                               (Const(constnm,_)) => 
                               let 
                                 val dt = List.find (fn (tynm,dtinfo) => 
                                                     constnm=(#case_name dtinfo)) 
                                                       datatypes
                               in
                                case dt of
                                  SOME dt => SOME (z,dt)
                                | NONE => NONE
                               end

                             | _ => NONE) 
                    (ZipperSearch.leaves_lr (Zipper.mktop t));
    in Seq.list_of cases end;

fun goal_in_rst_has_cases rst goal = 
    not (null (get_cases_of (RState.get_pplan rst) goal));

(* get all case theorems applicable to this goal *)
fun get_case_thms_for pp goal = 
    let 
      val thry = PPlan.get_theory pp;
      val ctxt = PPlan.get_context pp;

      (* IMPROVE: we compute the caseinfos twice if we check this is applicable first *)
      val caseinfos = get_cases_of pp goal;

      (* Case rewrites for this type *)
      val case_rws = maps (fn (z,(tynm,dt)) => (#case_rewrites dt))
                          caseinfos;

      (* get case-split theorem for this type *)
      (* FIXME: what's the right way to get these theorems? string lookup is not robust! *)
      val split_thms = map (fn (z,(tynm,dt)) => Global_Theory.get_thm thry (tynm^".split"))
                           caseinfos;
     
      (* Put the split theorem into a form that can be used by our
      restricted version of resolution *)
      val res_split_thms =
           Seq.maps ((fn thrm => rtac thrm 1 HOLIsaP_SplitData.subst_bool)
                       THEN (Classical.safe_tac ctxt))
                    (Seq.of_list split_thms);
    in (case_rws, Seq.list_of res_split_thms) end;


fun split_case_rtechn goal rst = 
    let val (case_rws, res_split_thms) = get_case_thms_for (RState.get_pplan rst) goal
    in
      (givename (RstName.str "Branch of case-statement")
                (orr_list (map (fn thm => (subst_thm thm false goal)) case_rws))
      try1_orelse
      (orr_list (map (fn thm => 
                     apply_restr_rule_dthm (DThm.mk 
                                               (Thm.put_name_hint "split_case_statement" thm)) goal) 
                     res_split_thms)))
      rst 
    end;

end (*local*)
end;
