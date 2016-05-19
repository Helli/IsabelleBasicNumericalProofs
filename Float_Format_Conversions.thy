theory Float_Format_Conversions
imports
  "$AFP/IEEE_Floating_Point/FloatProperty"
  "$AFP/IEEE_Floating_Point/Code_Float"
  "$AFP/IEEE_Floating_Point/RoundError"
  "~~/src/HOL/Library/Float"
begin

term Val
value "valof float_format (1, bias float_format, 124)"
value "valof float_format (0, 0, 0)"

fun Float_of_normal :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_normal x (s,e,f) =
    Float ((-1)^s * (2 ^ fracwidth x + f)) (int e - bias x - fracwidth x)"

lemma two_powr: "2 ^ a = 2 powr a"
  using powr_realpow by simp

lemma Float_of_normal_correct:
  assumes "e > 0" (* only normal numbers *)
  shows "real_of_float (Float_of_normal x (s, e, f)) = valof x (s, e, f)"
using assms
  apply (simp add: two_powr powr_divide2[symmetric])
  apply (simp add: field_simps)
  done

corollary "is_normal x f \<Longrightarrow> real_of_float (Float_of_normal x f) = valof x f"
unfolding is_normal_def
  apply (cases f)
  apply (auto simp del: Float_of_normal.simps simp add: Float_of_normal_correct)
  done

fun Float_of_subn_or_0 :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_subn_or_0 x (s, _ ,f) =
    Float ((-1)^s * f) ((1 :: int) - bias x - fracwidth x)"

lemma Float_of_subn_or_0_correct: (* only subnormal numbers or 0 *)
  shows "real_of_float (Float_of_subn_or_0 x (s, 0, f)) = valof x (s, 0, f)"
  apply (simp add: two_powr powr_divide2[symmetric])
  done

(* todo: corollary und Kombination von beidem *)

thm field_simps
thm divide_simps

definition float_format_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation" where
  "float_format_of_Float x f =
    (if 0 \<le> real_of_float f (*einfacher möglich?*) then 0 else 1,
    nat (Float.exponent f + int (bias x)),
    nat (\<bar>Float.mantissa f\<bar> - 1) * fracwidth x)"
thm float_format_of_Float_def[simplified]

lemma
  shows "valof x (float_format_of_Float x f) = real_of_float f"
  unfolding mantissa_exponent
  apply (auto simp: float_format_of_Float_def)
  oops

section \<open>Lifting important results\<close>
(* Todo *)

definition ferr :: "format \<Rightarrow> roundmode \<Rightarrow> real \<Rightarrow> real"
where "ferr x m a = valof x (round x m a) - a"

term "truncate_down 53"

lemma
  shows "is_valid x (float_format_of_Float x f)" "is_finite x (float_format_of_Float x f)"
  oops

term threshold
lemma closest_eq:
  assumes "blabla r"\<comment>\<open>normalisiert, klein genug, etc...\<close>
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