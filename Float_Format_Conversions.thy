theory Float_Format_Conversions
imports
  "$AFP/IEEE_Floating_Point/FloatProperty"
  "$AFP/IEEE_Floating_Point/Code_Float"
  "$AFP/IEEE_Floating_Point/RoundError"
  "~~/src/HOL/Library/Float"
begin

term Val
term Float
term round
term ulp
term fadd
term One

value "valof float_format (1, bias float_format, 124)"

definition ferr::"format \<Rightarrow> roundmode \<Rightarrow> real \<Rightarrow> real"
where "ferr x m a = valof x (round x m a) - a"

term "truncate_down 53"

definition
  "float_format_of_Float x f =
    ((if f \<ge> 0 then 0 else 1),
      nat (Float.exponent f + bias x),
      nat (abs (Float.mantissa f) - 1) * fracwidth x)"

fun Float_of_float_format where
  "Float_of_float_format x (s,e,f) =
    Float ((-1::int)^s * (fracwidth x + int f)) (int e - int (bias x) - fracwidth x)"

lemma
  shows "valof x (float_format_of_Float x f) = real_of_float f"
  unfolding mantissa_exponent
  apply (auto simp: float_format_of_Float_def)
  sorry

lemma
  shows "real_of_float (Float_of_float_format x f) = valof x f"
  apply (cases f)
  apply (auto simp: float_format_of_Float_def )
  thm divide_simps
  thm field_simps
  sorry

lemma
  shows "is_valid x (float_format_of_Float x f)" "is_finite x (float_format_of_Float x f)"
  sorry

term threshold
lemma closest_eq:
  assumes "blabla r"\<comment>\<open>normal, klein genug, etc...\<close>
  shows "closest (valof x) p (Collect (is_finite x)) r =
    (
      let
        l = truncate_down (fracwidth x) r;
        u = truncate_up (fracwidth x) r;
        lf = float_of l;
        uf = float_of u
      in if abs (l - r) < abs (u - r) then
          float_format_of_Float x lf
        else if abs (l - r) > abs (u - r) then float_format_of_Float x uf
        else undefined)"
        sorry

lemma lemma1:
  "abs (ferr x To_nearest (valof x a + valof x b)) \<le> abs (valof x a)"
proof cases
  assume "abs (valof x a) \<ge> abs (valof x b)"
  term "closest (valof x) (\<lambda>a. even (fraction a)) (Collect (is_finite x)) (valof x a + valof x b)"
  have "\<exists>aa. is_closest (valof x) (Collect (is_finite x))
      (valof x a + valof x b) aa \<and>
     ((\<exists>ba. is_closest (valof x) (Collect (is_finite x)) (valof x a + valof x b) ba \<and> even (fraction ba)) \<longrightarrow>
      even (fraction aa))"
    sorry
  show ?thesis
    unfolding ferr_def 
    apply (simp )
    apply auto
    prefer 4
    sorry
next
  fix P show P sorry
qed
  

lemma corollary2:
  "\<exists>c. ferr x m (valof x a + valof x b) = valof x c"
  sorry

end
