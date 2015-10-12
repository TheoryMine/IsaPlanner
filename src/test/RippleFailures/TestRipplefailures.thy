theory TestRippleFailures
imports CaseAnalysis_L

begin

ML {* val thry = @{theory}; *}


-- "ML function to interactively prove goals in Peano arithematic using
     with Rippling and Lemma Calculation "
ML{*
fun i_rippling goals = 
    PPInterface.ipp_of_strings 
      (ProofContext.init_global thry) (RTechnEnv.map_then RippleLemCalc.induct_ripple_lemcalc) goals;
*}

-- "Something IsaCoSy discovers, it's subsumed by more general things it can prove, but still."
ML {* val myrst = i_rippling ["(a + b) + a = (a + a) + (b ::nat)"];*}

-- "Couple of things about lists"
ML {* val myrst = i_rippling ["rev (rev a @ b) = rev b @ a "];*}

-- "A few examples from the conditional domain. There are lots more online (see testset from ITP paper)".
ML {* val myrst = i_rippling ["xs ~= [] ==> butlast xs @ (last xs)#[] = xs"]; *}
ML {* val myrst = i_rippling ["butlast (xs @ ys) = (if ys = [] then butlast xs else xs @ butlast ys)"];*}
ML {* val myrst = i_rippling ["butlast (xs @ [x]) = xs"];*}                                                  
ML {* val myrst = i_rippling ["count n l = count n (rev l)];*}                                                
ML {* val myrst = i_rippling [" count x l = count x (sort l)"];*}  
ML {* val myrst = i_rippling [" (m + n) minus n = m"];*}    
ML {* val myrst = i_rippling [" (i minus j) minus k = i minus (k minus j) "];*}        
ML {* val myrst = i_rippling [" drop n (xs @ ys) = drop n xs @ drop (n minus (len xs)) ys "];*}    
ML {* val myrst = i_rippling [" drop n (drop m xs) = drop (n + m) xs"];*}                                     
ML {* val myrst = i_rippling [" drop n (take m xs) = take (m minus n) (drop n xs)"];*} 
ML {* val myrst = i_rippling [" drop n (zip xs ys) = zip (drop n xs) (drop n ys) "];*}


end