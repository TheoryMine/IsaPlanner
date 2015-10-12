#echo 'cd ".."; PolyML.use "benchmarks/synth_theories/run_synth_bmarks_nat3.ML"; quit(); ' | isabelle HOL_IsaP
#echo "Finished nat (3 vars)"; 
#echo 'cd ".."; PolyML.use "benchmarks/synth_theories/run_synth_bmarks_rev_len3.ML"; quit();' | isabelle HOL_IsaP
#echo "Finished rev_len (3 vars)"; 
#echo 'cd ".."; PolyML.use "benchmarks/synth_theories/run_synth_bmarks_rev_map3.ML"; quit();' | isabelle HOL_IsaP 
#echo "Finished rev_map (3 vars)";
#echo 'cd ".."; PolyML.use "benchmarks/synth_theories/run_synth_bmarks_fold3.ML"; quit();' | isabelle HOL_IsaP 1> /dev/null
#echo "Finished fold (3 vars)";

# echo 'PolyML.use "benchmarks/run_casesplit_bmarks.ML"; quit();' | isabelle HOL_IsaP

echo 'cd ".."; PolyML.use "benchmarks/synth_theories/run_synth_bmarks_tree3.ML"; quit();' | isabelle HOL_IsaP 
echo "Finished trees (3 vars)";
(*echo 'cd ".."; PolyML.use "benchmarks/synth_theories/run_synth_bmarks_rev_qrev3.ML"; quit();' | isabelle HOL_IsaP 
echo "Finished rev_qrev (3 vars)";
*)
echo "Finished IsaPlanner Benchmarks!!"; 