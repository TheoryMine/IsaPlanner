theory O
imports Main IsaP
begin

datatype Ord = 
    Zero_Ord             ("Zero")
  | Suc_Ord Ord          ("Sc _" [90] 90)
  | Lim_Ord "nat \<Rightarrow> Ord" ("Lim _" [90] 90)

declare Ord.inject[wrule]

instance Ord :: ord ..
instance Ord :: one ..
instance Ord :: plus ..
instance Ord :: times ..

defs one_def: "1 == Sc Zero"

primrec
  ord_add_Zero  [wrule]: "(x + Zero) = (x :: Ord)"
  ord_add_Sc    [wrule]: "x + (Sc y) = Sc (x + y)"
  ord_add_Lim   [wrule]: "x + (Lim f) = Lim (%n. x + (f n))"

primrec
  ord_mul_Zero  [wrule]: "x * Zero = Zero"
  ord_mul_Sc    [wrule]: "x * (Sc y) = (x * y) + x"
  ord_mul_Lim   [wrule]: "x * (Lim f) = Lim (%n. x * (f n))"

consts ord_exp :: "Ord => Ord => Ord"   (infixr "exp" 80)
translations "op ^" == "op exp"
primrec
  ord_exp_Zero  [wrule]: "x ^ Zero = Sc Zero"
  ord_exp_Sc    [wrule]: "x ^ (Sc y) = (x ^ y) * x"
  ord_exp_Lim   [wrule]: "x ^ (Lim f) = Lim (%n. x ^ (f n))"

end;
