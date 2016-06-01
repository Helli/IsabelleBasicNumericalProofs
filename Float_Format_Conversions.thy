theory Float_Format_Conversions
imports
  "$AFP/IEEE_Floating_Point/FloatProperty"
  "$AFP/IEEE_Floating_Point/Code_Float"
  "$AFP/IEEE_Floating_Point/RoundError"
  "~~/src/HOL/Library/Float"
begin

value "valof float_format (1, bias float_format, 124)"
value "valof float_format (0, 0, 0)"

section \<open>IEEE.float to Float.float\<close>

fun Float_of_normal :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_normal x (s,e,f) =
    Float ((-1)^s * (2 ^ fracwidth x + f)) (int e - bias x - fracwidth x)"

lemma Float_of_normal_correct:
  assumes "e > 0" --\<open>only normal numbers\<close>
  shows "real_of_float (Float_of_normal x (s,e,f)) = valof x (s,e,f)"
using assms
  apply (simp add: powr_realpow powr_divide2[symmetric])
  apply (simp add: field_simps)
  done

corollary Float_of_normal_rep:
  "is_normal x r \<Longrightarrow> real_of_float (Float_of_normal x r) = valof x r"
unfolding is_normal_def
  apply (cases r)
  apply (simp del: Float_of_normal.simps add: Float_of_normal_correct)
  done

fun Float_of_subn_or_0 :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_subn_or_0 x (s,_,f) =
    Float ((-1)^s * f) ((1 :: int) - bias x - fracwidth x)"

lemma Float_of_subn_or_0_correct:
  --\<open>only subnormal numbers or 0 (e = 0)\<close>
  shows "real_of_float (Float_of_subn_or_0 x (s,0,f)) = valof x (s,0,f)"
  apply (simp add: powr_realpow powr_divide2[symmetric])
  done

corollary Float_of_subn_or_0_rep:
  "is_denormal x r \<or> is_zero x r \<Longrightarrow> real_of_float (Float_of_subn_or_0 x r) = valof x r"
using assms
unfolding is_denormal_def is_zero_def
  apply (cases r)
  apply (auto simp del: Float_of_subn_or_0.simps simp add: Float_of_subn_or_0_correct)
  done

thm field_simps
thm divide_simps

subsection \<open>Combining the finite cases\<close>

fun Float_of_finite :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_finite x (s,0,f) = Float_of_subn_or_0 x (s,0,f)" |
  "Float_of_finite x (s,e,f) = Float_of_normal x (s,e,f)"

lemma Float_of_finite_correct: "real_of_float (Float_of_finite x r) = valof x r"
  apply (cases r)
  using Float_of_finite.simps Float_of_normal_correct Float_of_subn_or_0_correct
  apply (metis Suc_pred neq0_conv)
  done


text \<open>To match the definition of @{const valof}, @{const Float_of_finite} does not check the triple for validity, this even applies to the lifted version from below. Hence, also special values like @{const Plus_infinity} can use this calculation.
They are then interpreted wrongly, see below.\<close>

section \<open>Possibly counter-intuitive behaviour\<close>

--\<open>Val return a real even for infinite values:\<close>
schematic_goal sg1: "Rep_float Plus_infinity = (?s, ?e, ?f)"
  unfolding Plus_infinity_def
  using is_valid_special Abs_float_inverse
  apply simp
  unfolding plus_infinity_def emax_def "expwidth.simps" float_format_def
  apply simp
  done
schematic_goal "Val Plus_infinity = ?x"
  unfolding Val_def sg1 float_format_def
  apply simp
  done

section \<open>Float.float to IEEE.float\<close>

(* Obacht! Stark negative Exponenten werden auch mit bias noch negativ sein.
  In eine representation dürfen aber nur natürliche Zahlen geschrieben werden...*)
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

definition Float_of_Finite :: "IEEE.float \<Rightarrow> Float.float" where
  "Float_of_Finite f = Float_of_finite float_format (Rep_float f)"

lemma Float_of_Finite_correct: "real_of_float (Float_of_Finite f) = Val f"
  unfolding Float_of_Finite_def Val_def
  using Float_of_finite_correct[of float_format "Rep_float f"].

(* Todo: expand *)


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