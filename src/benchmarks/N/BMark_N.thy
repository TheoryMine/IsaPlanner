header{* Peano Arithmetic - Datatype Definition *}

theory BMark_N
imports Main IsaP
begin

datatype N = zero  ("zero")
           | suc N ("suc _" [100] 100)

instance N :: one ..
instance N :: ord ..
instance N :: plus ..
instance N :: times ..

translations "0" == "zero"

(*defs (overloaded) one_def: "1 == suc 0"*)

declare N.inject[impwrule]

end;
