
use "ROOT.ML";
use_thy "examples/critics_isabelleWS07";
Trm.drop_var_args_flag := false;
val ripple =  PPInterface.ipp RippleRTechn.induct_ripple_lemspec;
val (thry, (ienv, [(t1,t2)])) = the ((ripple("a", "evenR(len(x@x))"); 
NONE) handle MyUnify.hounifiers_exp (thry, (ienv, [(t1,t2)]))  => SOME 
(thry, (ienv, [(t1,t2)])));

