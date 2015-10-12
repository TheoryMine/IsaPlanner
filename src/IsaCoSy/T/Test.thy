theory Test
imports IsaP N

uses

("eqClass.ML")
("test.ML")
("TCoSy.ML")
begin

use "eqClass.ML"
use "test.ML"
use "TCoSy.ML"

ML{*

val def_thms = [@{thm "add_0"}, @{thm "add_suc"}, @{thm "mult_0"}, @{thm "mult_suc"} ]

val cparams = ConstraintParams.empty @{context}
        |> ConstraintParams.add_eq @{context}
        |> ConstraintParams.add_datatype @{context} @{typ "N"}
        |> ConstraintParams.add_consts_of_string_names @{context} ["N.plus_N" , "N.mult_N"]
        |> ConstraintParams.add_thms @{context} def_thms;
*}

ML {*
val consts = map SynthNames.ConstantName.mk ["N.plus_N", "N.mult_N", "N.N.suc", "N.N.zero"];
val ctxt = @{context};
*}


ML{*
val (cparams,ctxt,rem) = TCoSy.run consts {max_size = 1, min_size = 0, max_nesting = SOME 2} (cparams, @{context});
*}
ML{*
val trms = TCoSy.dbg_synth consts 2 (cparams, ctxt);
map (Trm.print ctxt) trms;

map (Trm.print ctxt) rem;
*}



ML{*

val (cparams,ctxt,rem) = TCoSy.run consts {max_size = 2, min_size = 0, max_nesting = SOME 2} (cparams, @{context});

*}
ML{*
List.foldl;
SynthInterface.print_thms (cparams,ctxt);
*}

ML{*

val trms = TCoSy.dbg_synth consts 2 (cparams, ctxt);
map (Trm.print ctxt) trms;

*}

ML{*
val thyConstrs = TheoryConstraints.init ctxt cparams;

fun synth_one_const top_const = 
          (* Compute current thy constraints and synthesise some terms *)
          (Test.synthesise_terms top_const 
                            {size = 2, max_vars = 1} 
                            ctxt thyConstrs)
            |> Seq.map STerm.get_term
            |> Seq.list_of;

val trms = maps synth_one_const consts;
map (Trm.print ctxt) trms;
*}
ML{*

fun var_order (t1,t2) = Library.rev_order 
  (Library.int_ord (List.length (Trm.vars_of t1), List.length(Trm.vars_of t2)));

val (t1::t2::ts) = trms;
var_order (t1,t2);
 
 val x = Library.sort var_order trms;
map (Trm.print ctxt) x;

*}

ML{*
fun print trm = ((Trm.pretty @{context})) trm;

Pretty.writeln (Pretty.chunks (map print trms));
*}

ML{* 


*}