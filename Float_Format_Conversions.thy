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
  have a: "?thesis \<longleftrightarrow>
    (- 1) ^ 0 *
    (2 ^ nat (Float.exponent f + int (bias x)) / 2 powr bias x) *
    (1 + real (nat (\<bar>mantissa f\<bar> - 1) * 2 ^ fracwidth x) / 2 ^ fracwidth x)
    =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
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
  have a: "?thesis \<longleftrightarrow>
    (- 1) ^ 1 *
    (2 ^ nat (Float.exponent f + int (bias x)) / 2 powr bias x) *
    (1 + real (nat (\<bar>mantissa f\<bar> - 1) * 2 ^ fracwidth x) / 2 ^ fracwidth x)
    =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
    unfolding normal_rep_of_Float_def valof.simps mantissa_exponent nat_transform
    apply (simp add: False)
    using nat_transform powr_realpow by auto
  have "mantissa f < 0"
    by (smt False Float.compute_is_float_pos Float.compute_is_float_zero Float_mantissa_exponent f_not_zero)
  moreover then have "\<bar>mantissa f\<bar> = - mantissa f"
    by simp
  ultimately have s2: "real (nat (\<bar>mantissa f\<bar> - 1)) = - mantissa f - 1"
    by (simp add: nat_0_le)
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = - real_of_int (mantissa f)"
    using \<open>0 > mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + real (bias x)) = real_of_int (Float.exponent f + bias x)" by simp
  show ?thesis
    unfolding a
  apply (simp add: s2 s3 field_simps powr_add[symmetric])
  unfolding s4
    by (smt powr_int nat_transform)
qed

definition normal_rep_of_Float' :: "format \<Rightarrow> Float.float \<Rightarrow> representation"
(* This version needs an extra assumption, but can produce uneven mantissas*)
where
  "normal_rep_of_Float' x f =
  (if is_float_pos f then 0 else 1,
    nat (Float.exponent f + int (bias x) + int (fracwidth x)),
    nat (\<bar>Float.mantissa f\<bar> - 2 ^ fracwidth x))"
thm normal_rep_of_Float'_def[simplified]

lemma normal_rep_of_Float'_correct:
  assumes f_not_zero: "\<not>is_float_zero f"
  assumes special_transform: "0 \<le> \<bar>Float.mantissa f\<bar> - 2 ^ fracwidth x"
  assumes nat_transform: "Float.exponent f + int (bias x) + int (fracwidth x) > 0" (*make sure this can be converted to a nat without loss of information, also avoid the result being interpreted as subnormal number*)
  shows "valof x (normal_rep_of_Float' x f) = real_of_float f"
using assms
proof  (cases "is_float_pos f")
case True
  have if_false: "\<not>nat
         (Float.exponent f +
          int (bias x) + int (fracwidth x)) =
        0"
        using nat_transform by linarith
  have a: "?thesis \<longleftrightarrow>
    (- 1) ^ 0 *
    (2 ^ nat (Float.exponent f + int (bias x) + int (fracwidth x)) / 2 powr bias x) *
    (1 + real (nat (\<bar>mantissa f\<bar> - 2 ^ fracwidth x)) / 2 ^ fracwidth x)
    =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
    using if_false normal_rep_of_Float'_def mantissa_exponent valof.simps powr_realpow
      by (simp add: True)
  have m_greater: "mantissa f > 0"
    by (metis Float.compute_is_float_pos Float_mantissa_exponent True)
  then have "\<bar>mantissa f\<bar> = mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> - 2 ^ fracwidth x))
    = \<bar>mantissa f\<bar> - 2 ^ fracwidth x"
    using special_transform by auto
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = real_of_int (mantissa f)"
    using \<open>0 < mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + (real (fracwidth x) + real (bias x)))
    = real_of_int (Float.exponent f + bias x + fracwidth x)"
    by simp
  show ?thesis
    unfolding a
  apply (simp add: s2 s3)
  apply (simp add: divide_simps powr_realpow[symmetric] powr_add[symmetric])
  unfolding s4
  using nat_transform by auto
next
case False
  have if_false: "\<not>nat
         (Float.exponent f +
          int (bias x) + fracwidth x) =
        0"
        using nat_transform by linarith
  have a: "?thesis \<longleftrightarrow>
    (- 1) ^ 1 *
    (2 ^ nat (Float.exponent f + int (bias x) + fracwidth x) / 2 powr bias x) *
    (1 + real (nat (\<bar>mantissa f\<bar> - 2 ^ fracwidth x)) / 2 ^ fracwidth x)
    =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
    unfolding normal_rep_of_Float'_def valof.simps mantissa_exponent nat_transform
    apply (simp add: False)
    using nat_transform powr_realpow by auto
  have m_smaller: "mantissa f < 0"
    by (smt False Float.compute_is_float_pos Float.compute_is_float_zero Float_mantissa_exponent f_not_zero)
  then have "\<bar>mantissa f\<bar> = - mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> - 2 ^ fracwidth x)) = - mantissa f - 2 ^ fracwidth x"
    using special_transform by auto
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = - real_of_int (mantissa f)"
    using \<open>0 > mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + (real (bias x) + real (fracwidth x)))
    = real_of_int (Float.exponent f + bias x + fracwidth x)"
    by simp
  show ?thesis
    unfolding a
  apply (simp add: s2 s3 divide_simps powr_realpow[symmetric] powr_add[symmetric])
  unfolding s4
  using nat_transform by auto
qed

definition float_rep_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation" where
  "float_rep_of_Float x f = (
    if is_float_zero f
      then (0,0,0)
      else normal_rep_of_Float x f
  )"

lemma float_rep_of_Float_correct:
  assumes nat_transform: "Float.exponent f + int (bias x) > 0"
  shows "valof x (float_rep_of_Float x f) = real_of_float f"
unfolding float_rep_of_Float_def
by (simp add: is_float_zero.rep_eq nat_transform normal_rep_of_Float_correct)

definition normal_rep_of_Float_b :: "format \<Rightarrow> nat \<Rightarrow> Float.float \<Rightarrow> representation"
where
  "normal_rep_of_Float_b x b f =
  (if is_float_pos f then 0 else 1,
    nat (Float.exponent f + int (bias x) + b),
    nat (\<bar>Float.mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))"
(*Todo: 2^fracwidth ausklammern? \<longrightarrow> Dann aber drinnen kein int mehr?*)
thm normal_rep_of_Float_b_def[simplified]

lemma normal_rep_of_Float_b_correct:
  fixes b :: nat
  assumes f_not_zero: "\<not>is_float_zero f"
  assumes nat_transform: "0 < Float.exponent f + int (bias x) + int b"
  and special_transform: "0 \<le> \<bar>Float.mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
  and yet_another_assumption: "fracwidth x \<ge> b"
  shows "valof x (normal_rep_of_Float_b x b f) = real_of_float f"
using assms
proof  (cases "is_float_pos f")
case True
  have if_false: "\<not>nat (Float.exponent f + int (bias x) + b) = 0"
        using nat_transform by linarith
  have a: "?thesis \<longleftrightarrow>
    2 ^ nat (Float.exponent f + int (bias x) + int b) *
    (1 + real (nat (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x)) / 2 ^ fracwidth x) /
    2 ^ bias x
    =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
    using if_false normal_rep_of_Float_b_def mantissa_exponent valof.simps powr_realpow
      by (simp add: True)
  have m_greater: "mantissa f > 0"
    by (metis Float.compute_is_float_pos Float_mantissa_exponent True)
  then have "\<bar>mantissa f\<bar> = mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))
    = \<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    using special_transform by auto
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = real_of_int (mantissa f)"
    using \<open>0 < mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + (real (fracwidth x) + real (bias x)))
    = real_of_int (Float.exponent f + bias x + fracwidth x)"
    by simp
  have s5: "real (nat (Float.exponent f + int (bias x) + int b)) + real (fracwidth x - b)
    = real_of_int (Float.exponent f + int (bias x) + int (fracwidth x))"
     using if_false yet_another_assumption by linarith
  show ?thesis
    unfolding a
  apply (simp add: s2)
  apply (simp add: s3)
  apply (simp add: divide_simps powr_realpow[symmetric] powr_add[symmetric])
  unfolding s4 s5
    by simp
next
case False
  have if_false: "nat (Float.exponent f + int (bias x) + int b) \<noteq> 0"
        using nat_transform by linarith
  have a: "?thesis \<longleftrightarrow>
    - (2 ^ nat (Float.exponent f + int (bias x) + int b) *
    (1 + real (nat (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x)) / 2 ^ fracwidth x) /
    2 ^ bias x)
    =
    real_of_int (mantissa f) *
    2 powr real_of_int (Float.exponent f)"
    using if_false normal_rep_of_Float_b_def mantissa_exponent valof.simps powr_realpow
      by (simp add: False)
  have m_smaller: "mantissa f < 0"
    by (smt False Float.compute_is_float_pos Float.compute_is_float_zero Float_mantissa_exponent f_not_zero)
  then have "\<bar>mantissa f\<bar> = - mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))
    = \<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    using special_transform by auto
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = - real_of_int (mantissa f)"
    using \<open>0 > mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + (real (fracwidth x) + real (bias x)))
    = real_of_int (Float.exponent f + bias x + fracwidth x)"
    by simp
  have s5: "real (nat (Float.exponent f + int (bias x) + int b)) + real (fracwidth x - b)
    = real_of_int (Float.exponent f + int (bias x) + int (fracwidth x))"
     using if_false yet_another_assumption by linarith
  show ?thesis
    unfolding a
  apply (simp add: s2)
  apply (simp add: s3)
  apply (simp add: divide_simps powr_realpow[symmetric] powr_add[symmetric])
  unfolding s4 s5
    by simp
qed

lemma replace_from_special_transform: "\<bar>i\<bar> < 2 ^ nat (bitlen \<bar>i\<bar>)"
by (metis (full_types) bitlen_bounds bitlen_def less_le_trans linorder_not_less nat_0 not_one_le_zero power_0)

lemma better: "i \<noteq> 0 \<Longrightarrow> 2 powr -bitlen \<bar>i\<bar> < \<bar>i\<bar>"
  by (smt abs_real_le_2_powr_bitlen of_int_less_1_iff of_int_minus powr_less_cancel_iff powr_zero_eq_one)

lemma even_better: "\<bar>i\<bar> / 2 ^ nat (bitlen \<bar>i\<bar>) < 1"
by (metis (no_types, hide_lams) abs_if divide_less_eq_1_neg divide_less_eq_1_pos not_numeral_less_one one_less_numeral_iff real_of_int_less_numeral_power_cancel_iff replace_from_special_transform semiring_norm(76) zero_less_numeral zero_less_power_abs_iff)

value "(5::int) - (6::nat)"
value "2 ^ -bitlen \<bar>4\<bar>"

lemma normal_rep_of_Float_bitlen:
(*Problem: Why doesn't special_transform follow from the other assumptions?\<dots>*)
  assumes special_transform: "0 \<le> \<bar>Float.mantissa f\<bar> * 2 ^ (fracwidth x - bitlen (mantissa f)) - 2 ^ fracwidth x"
(*...It is possible to conclude yet_... from this (after fixing the type), but not the other way around as it should be? *)
  assumes "\<not>is_float_zero f"
  assumes "-int (bias x) < exponent f"
  and "Float.exponent f + int (bias x) + fracwidth x < 2^(expwidth x)"
  defines "r \<equiv> normal_rep_of_Float_b x (nat (bitlen \<bar>mantissa f\<bar>)) f"
  shows "valof x r = real_of_float f"
  and "is_valid x r"
unfolding r_def
apply (rule normal_rep_of_Float_b_correct)
  apply fact
  using assms(3) apply auto[1]
  apply (simp add: divide_simps)
using even_better[of "mantissa f"]
  sledgehammer
  using replace_special_transform

  apply (simp add: assms(1) dual_order.strict_implies_order nat_le_iff)

definition float_rep_of_Float_b :: "format \<Rightarrow> Float.float \<Rightarrow> representation" where
  "float_rep_of_Float_b x f = (
    if is_float_zero f
      then (0,0,0)
      else normal_rep_of_Float_b x (nat (bitlen \<bar>mantissa f\<bar>)) f
  )"

lemma float_rep_of_Float_b_correct:
  assumes nat_transform: "Float.exponent f + int (bias x) > 0"
  shows "valof x (float_rep_of_Float_b x f) = real_of_float f"
unfolding float_rep_of_Float_b_def
  by (simp add: is_float_zero.rep_eq nat_transform normal_rep_of_Float_b_correct)

lemma float_rep_of_Float_superb:
  (*s. Zettel N\<degree> 1337*)
  fixes x f
  defines "r \<equiv> float_rep_of_Float_b x f"
  shows "valof x r = real_of_float f"
  and "is_valid x r"

value "exponent 0"
value "mantissa 0"
(*ToDo:
  lemmas about transforming twice?
  (make sure we get the same value back for normal IEEE.floats?)
*)

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
  shows "is_valid x (float_rep_of_Float x f)"
  (*and "is_finite x (float_rep_of_Float x f)"*)
unfolding is_valid_def float_rep_of_Float_def normal_rep_of_Float_def
  apply simp
  oops (*\<bar>mantissa f\<bar> \<le> 1 ? Need another approach for the conversion*)

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