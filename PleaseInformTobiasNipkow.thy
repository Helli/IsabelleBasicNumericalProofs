theory PleaseInformTobiasNipkow
imports
  "$AFP/IEEE_Floating_Point/RoundError"
begin

lemma "\<bar>x\<bar> < threshold float_format \<Longrightarrow> Finite (Float x)"
  sledgehammer
  by (smt Finite_def Float_def Isdenormal_def Isnormal_def Iszero_def closest_is_closest defloat_float_round is_closest_def is_finite_def is_finite_finite is_finite_nonempty mem_Collect_eq round.simps(1))

end