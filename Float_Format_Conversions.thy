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

--\<open>Val returns a real, even for special value input:\<close>
schematic_goal sg1: "Rep_float Plus_infinity = (?s, ?e, ?f)"
  unfolding Plus_infinity_def
  using is_valid_special Abs_float_inverse
  apply simp
  unfolding plus_infinity_def emax_def "expwidth.simps" float_format_def
  apply simp
  done
schematic_goal sg2: "Val Plus_infinity = ?x"
  unfolding Val_def sg1 float_format_def
  apply simp
  done


section \<open>Float.float to IEEE.float\<close>

definition normal_rep_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation"
(*obtain a triple that, when interpreted as normal IEEE.float, has the same value*)
where
  "normal_rep_of_Float x f =
  (if is_float_pos f then 0 else 1,
    nat (Float.exponent f + int (bias x)),
    nat (\<bar>Float.mantissa f\<bar> - 1) * 2 ^ fracwidth x)"
thm normal_rep_of_Float_def[simplified]

lemma normal_rep_of_Float_correct:
  assumes f_not_zero: "\<not>is_float_zero f" (*avoid that special case for now*)
  assumes nat_transform: "Float.exponent f + int (bias x) > 0" (*make sure this can be converted to a nat without loss of information, also avoid the result being interpreted as subnormal number*)
  shows "valof x (normal_rep_of_Float x f) = real_of_float f"
using assms
proof  (cases "is_float_pos f")
case True
  have if_false: "\<not>nat
         (Float.exponent f +
          int (bias x)) =
        0"
        using nat_transform by linarith
  have a: "?thesis \<longleftrightarrow> (- 1) ^ 0 *
          (2 ^
           nat
            (Float.exponent f +
             int (bias x)) /
           2 powr bias x) *
          (1 +
           real
            (nat
              (\<bar>mantissa f\<bar> - 1) *
             2 ^ fracwidth x) /
           2 ^ fracwidth x) =
    real_of_int (mantissa f) *
    2 powr
    real_of_int (Float.exponent f)"
    using if_false normal_rep_of_Float_def mantissa_exponent valof.simps powr_realpow 
      by (simp add: True)
  have m_greater: "mantissa f > 0"
    by (metis Float.compute_is_float_pos Float_mantissa_exponent True)
  then have "\<bar>mantissa f\<bar> = mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> - 1)) = \<bar>mantissa f\<bar> - 1"
    by (simp add: \<open>0 < mantissa f\<close> nat_0_le)
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = real_of_int (mantissa f)"
    using \<open>0 < mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + real (bias x)) = real_of_int (Float.exponent f + bias x)"
    by simp
  show ?thesis
    unfolding a
  apply (simp add: s2 s3 field_simps powr_add[symmetric])
  unfolding s4
    by (smt powr_int nat_transform)
next
case False
  have if_false: "\<not>nat
         (Float.exponent f +
          int (bias x)) =
        0"
        using nat_transform by linarith
  have a: "?thesis \<longleftrightarrow>  (- 1) ^ 1 *
          (2 ^
           nat
            (Float.exponent f +
             int (bias x)) /
           2 powr bias x) *
          (1 +
           real
            (nat (\<bar>mantissa f\<bar> - 1) *
             2 ^ fracwidth x) /
           2 ^ fracwidth x) =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
    unfolding normal_rep_of_Float_def valof.simps mantissa_exponent nat_transform
    apply (simp add: False)
    using nat_transform powr_realpow by auto
  have m_greater: "mantissa f < 0"
    by (smt False Float.compute_is_float_pos Float.compute_is_float_zero Float_mantissa_exponent f_not_zero)
  then have "\<bar>mantissa f\<bar> = - mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> - 1)) = - mantissa f - 1"
    by (simp add: \<open>0 > mantissa f\<close> nat_0_le)
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = - real_of_int (mantissa f)"
    using \<open>0 > mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + real (bias x)) = real_of_int (Float.exponent f + bias x)" by simp
  show ?thesis
    unfolding a
  apply (simp add: s2 s3 field_simps powr_add[symmetric])
  unfolding s4
    by (smt powr_int nat_transform)
qed

definition rep_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation" where
  "rep_of_Float x f = (
    if is_float_zero f
      then (0,0,0)
      else normal_rep_of_Float x f
  )"

lemma rep_of_Float_correct:
  assumes nat_transform: "Float.exponent f + int (bias x) > 0"
  shows "valof x (rep_of_Float x f) = real_of_float f"
unfolding rep_of_Float_def
by (simp add: is_float_zero.rep_eq nat_transform normal_rep_of_Float_correct)

value "exponent 0"
value "mantissa 0"
(*ToDo: lemmas about transforming twice? *)

(*ToDo: Does this terminate?
value "normal_rep_of_Float float_format (Float 3 2)"
*)

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
  shows "is_valid x (float_rep_of_Float x f)" "is_finite x (float_rep_of_Float x f)"
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