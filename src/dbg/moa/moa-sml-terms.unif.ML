use_thy "benchmarks/Trees";
val thry = (the_context());

fun print_inst (v,(ty,t)) = 
    let val ctxt = ProofContext.init (the_context())
    in
      (Pretty.writeln 
         (Pretty.block 
            [Pretty.str "", 
             Trm.Var.pretty_name v,
             Pretty.str " : ",
             Trm.Var.pretty_typ ctxt ty,        
             Pretty.str " = ",
             Trm.pretty ctxt t]);
       (v,(ty,t)))
    end;

(* This is the offending subterm of the goal *)
 (*  Const ("List.foldl", "('a => 'b => 'a) => 'a => 'b List.list => 'a") $
         Free ("g", "'a => 'b => 'a") $ Free ("aa", "'a") : Term.term
*)
val g = (((Const("List.foldl", Type("fun", [Type("fun", [TFree("'a", 
["HOL.type"]), Type("fun", [TFree("'b", ["HOL.type"]), TFree("'a", 
["HOL.type"])])]), Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), TFree("'a", 
["HOL.type"])])])]))) $
 (Free("g", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[TFree("'b", ["HOL.type"]), TFree("'a", ["HOL.type"])])])))) $
 (Free("aa", TFree("'a", ["HOL.type"]))));

(* This is the bit of the rule, looking like this *)
(* foldl (?f f a xs ys b yt aa g xt) (?a f a xs ys b yt aa g xt) *)

val t = (((Const("List.foldl", Type("fun", [Type("fun", [TVar( ("'a", 
0), ["HOL.type"]), Type("fun", [TVar( ("'b_1", 0), ["HOL.type"]), TVar( 
("'a", 0), ["HOL.type"])])]), Type("fun", [TVar( ("'a", 0), 
["HOL.type"]), Type("fun", [Type("List.list", [TVar( ("'b_1", 0), 
["HOL.type"])]), TVar( ("'a", 0), ["HOL.type"])])])]))) $
 ((((((((((Var( ("f",0), Type("fun", [Type("fun", [TFree("'a", 
["HOL.type"]), Type("fun", [TFree("'b", ["HOL.type"]), TFree("'a", 
["HOL.type"])])]), Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), Type("fun", 
[TFree("'b", ["HOL.type"]), Type("fun", [Type("List.list", [TFree("'b", 
["HOL.type"])]), Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", [TFree("'b", 
["HOL.type"]), TFree("'a", ["HOL.type"])])]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), Type("fun", [TVar( 
("'a", 0), ["HOL.type"]), Type("fun", [TVar( ("'b_1", 0), ["HOL.type"]), 
TVar( ("'a", 0), ["HOL.type"])])])])])])])])])])])]))) $
 (Free("f", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[TFree("'b", ["HOL.type"]), TFree("'a", ["HOL.type"])])])))) $
 (Free("a", TFree("'a", ["HOL.type"])))) $
 (Free("xs", Type("List.list", [TFree("'b", ["HOL.type"])])))) $
 (Free("ys", Type("List.list", [TFree("'b", ["HOL.type"])])))) $
 (Free("b", TFree("'b", ["HOL.type"])))) $
 (Free("yt", Type("List.list", [TFree("'b", ["HOL.type"])])))) $
 (Free("aa", TFree("'a", ["HOL.type"])))) $
 (Free("g", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[TFree("'b", ["HOL.type"]), TFree("'a", ["HOL.type"])])])))) $
 (Free("xt", Type("List.list", [TFree("'b", ["HOL.type"])]))))) $
 ((((((((((Var( ("a",0), Type("fun", [Type("fun", [TFree("'a", 
["HOL.type"]), Type("fun", [TFree("'b", ["HOL.type"]), TFree("'a", 
["HOL.type"])])]), Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), Type("fun", 
[TFree("'b", ["HOL.type"]), Type("fun", [Type("List.list", [TFree("'b", 
["HOL.type"])]), Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", [TFree("'b", 
["HOL.type"]), TFree("'a", ["HOL.type"])])]), Type("fun", 
[Type("List.list", [TFree("'b", ["HOL.type"])]), TVar( ("'a", 0), 
["HOL.type"])])])])])])])])])]))) $
 (Free("f", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[TFree("'b", ["HOL.type"]), TFree("'a", ["HOL.type"])])])))) $
 (Free("a", TFree("'a", ["HOL.type"])))) $
 (Free("xs", Type("List.list", [TFree("'b", ["HOL.type"])])))) $
 (Free("ys", Type("List.list", [TFree("'b", ["HOL.type"])])))) $
 (Free("b", TFree("'b", ["HOL.type"])))) $
 (Free("yt", Type("List.list", [TFree("'b", ["HOL.type"])])))) $
 (Free("aa", TFree("'a", ["HOL.type"])))) $
 (Free("g", Type("fun", [TFree("'a", ["HOL.type"]), Type("fun", 
[TFree("'b", ["HOL.type"]), TFree("'a", ["HOL.type"])])])))) $
 (Free("xt", Type("List.list", [TFree("'b", ["HOL.type"])])))));


val cg = Thm.cterm_of thry g;
val ct = Thm.cterm_of thry t;

val ienv = InstEnv.init thry;
val ienv2 = TypUnify.unify_trms thry [(g,t)] ienv;

val [(g2,t2)] = map (fn (t,s) => (InstEnv.inst_trm ienv2 t, 
                                   InstEnv.inst_trm ienv2 s))
                     [(g,t)]; 

InstEnv.print_full ienv2;

val cg2 = Thm.cterm_of thry g2;
val ct2 = Thm.cterm_of thry t2;


fun print_unif t (env, flexes) = 
    let 
      val alist = Envir.alist_of env;
      val tyenv = Vartab.dest (Envir.type_env env);
      val ct = Thm.cterm_of thry (Envir.norm_term env t);
    in (print alist; print tyenv; print ct) end;
        

(* This causes an exception *)
map (apfst InstEnv.print_full)
    (Seq.list_of (MyUnify.unifiers thry (InstEnv.init thry, [(g2, t2)])));

map (print_unif t2)
    (Seq.list_of (Unify.unifiers (thry, Envir.empty 0, [(g2,t2)])));

raise ERROR "stop";

PolyML.exception_trace (fn () => 
    MyUnify.unifies thry (InstEnv.init thry, [(g2, t2)])
);

val SOME ((env, insts),more) = (Seq.pull (Unify.unifiers (thry, Envir.empty 0, [(g2,t2)])));


val SOME ((env, insts),more) = (Seq.pull (Unify2.unifiers (thry, Envir.empty 0, [(g2,t2)])));
val alist = Envir.alist_of env;
val tyenv = Vartab.dest (Envir.type_env env);
Thm.cterm_of thry (Envir.norm_term env t2);


(* This causes an exception *)
val SOME ((v as (n,(ty,t))), e) = 
    (MyUnify.unifiers thry (InstEnv.init thry, [(g2, t2)]); NONE) 
    handle InstEnv.bad_var_inst_exp x => SOME x;

print_inst v;

PolyML.exception_trace (fn () => 
    MyUnify.unifies thry (InstEnv.init thry, [(g, t)])
);

(* This causes an exception *)
val SOME ((v as (n,(ty,t))), e) = 
    (MyUnify.unifies thry (InstEnv.init thry, [(g, t)]); NONE) 
    handle InstEnv.bad_var_inst_exp x => SOME x;


(* This is appears to be OK *)
val envinsts = (Seq.list_of (Unify.unifiers (tyry, Envir.empty 0, [(gt3,rt3)])));
val (env,insts) = hd envinsts;
val alist = Envir.alist_of env;
val tyenv = Vartab.dest (Envir.type_env env);
Thm.cterm_of thry (Envir.norm_term env t2);
