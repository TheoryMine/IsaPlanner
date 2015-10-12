use "ROOT.ML";
use_thy "benchmarks/BestF_L";
Trm.drop_var_args_flag := false;
val ripple =  PPInterface.ipp RippleRTechn.induct_and_ripple;

fun metagoal rst goal = 
    let
        val old_metavars = RstPP.get_ienv rst
        val thy = RstPP.get_theory rst
   
        val goal_t = RstPP.goal_concl rst goal
        val goal_zip = Zipper.mktop goal_t
       
        
        val lhs = Subst.move_to_lhs_of_eq goal_zip
        val (nw_instenv, meta_lhs) = LemmaSpec.ins_metavars old_metavars [] [] (Zipper.trm lhs)
         
        val rhs = Subst.move_to_rhs_of_eq goal_zip  
        val (nw_instenv2, meta_rhs) = LemmaSpec.ins_metavars nw_instenv [] [] (Zipper.trm rhs)

        fun dest_tp (Const("HOL.Trueprop", _) $ T) = T
          | dest_tp T = T; 
                 
        val metatrm = lhs
                         |> Zipper.set_trm meta_lhs
                         |> Zipper.goto_top
                         |> Subst.move_to_rhs_of_eq
                         |> Zipper.set_trm meta_rhs
                         |> Zipper.top_trm 

        (* Think it's ok to insert at top level, but need take care so
        we can get the skeleton later when rippling in reverse *)

        val (nw_g, nw_ppl) = PPlan.new_topgoal ("crit", metatrm) 
                                               (RState.get_pplan rst)                            
    in
      
     RState.set_pplan nw_ppl (RState.set_goalnames [nw_g] rst) 
    end;



val start = RippleRTechn.RippleCInfo.start_rev;
val rev_ripple = RippleRTechn.steps_rev
val rst = ripple ("a","evenR(len(l@t)) = evenR(len(t@l))");
val rst2 = hd (Seq.list_of (RippleRTechn.startr_rev rst));
val rst3 = RState.set_rtechn (SOME (RippleRTechn.steps_rev)) rst2;
PolyML.exception_trace (fn () => PPInterface.ipp_rst rst3);
 PolyML.exception_trace (fn () => Seq.list_of(RippleRTechn.steps_rev rst2));
val rst2 = metagoal rst "m";
PolyML.exception_trace (fn () => (Seq.list_of(MiddleOutRW.midout_rw "crit" (RState.set_rtechn NONE rst2))));

RippleCInfo.start_rev;
