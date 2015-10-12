header {* IsaPlanner Rippling Notation for HOL *}

theory IsaP_RippleNotation
imports CPure
uses "rtechn/rippling/ripple_aterms.ML"
begin

section {* Rippling Notation *}

consts wave_front_out :: "'a \<Rightarrow> 'a"   ("['< _ '>]")
consts wave_front_in :: "'a \<Rightarrow> 'a"   ("['> _ '<]")
consts sink :: "'a \<Rightarrow> 'a" ("\\_'/")

ML {* 
structure RippleNotation : RIPPLE_NOTATION= 
struct 
  val wave_front_out = "IsaP_RippleNotation.wave_front_out";
  val wave_front_in = "IsaP_RippleNotation.wave_front_in";
  val sink = "IsaP_RippleNotation.sink";
end; 
structure RippleATerms = RippleATermsFUN(RippleNotation);
*}

end;
