(* Author: Fabian Hellauer
           Fabian Immler
*)
theory Float_Format_Conversions
  imports
    "IEEE_Floating_Point.IEEE_Properties"
    "IEEE_Floating_Point.Code_Float"
    "IEEE_Floating_Point.IEEE"
    "~~/src/HOL/Library/Float"
begin

section \<open>IEEE.float to Float.float\<close>

fun Float_of_normal :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_normal x (s,e,f) =
    Float ((-1)^s * (2 ^ fracwidth x + f)) (int e - bias x - fracwidth x)"

lemma Float_of_normal_correct:
  assumes "e > 0"
  shows "real_of_float (Float_of_normal x (s,e,f)) = valof x (s,e,f)"
  using assms
  by (simp add: powr_realpow powr_diff) (simp add: field_simps)

corollary Float_of_normal_rep:
  "is_normal x r \<Longrightarrow> real_of_float (Float_of_normal x r) = valof x r"
  unfolding is_normal_def
  by (cases r) (simp del: Float_of_normal.simps add: Float_of_normal_correct)

fun Float_of_subn_or_0 :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_subn_or_0 x (s,_,f) =
    Float ((-1)^s * f) ((1 :: int) - bias x - fracwidth x)"

lemma Float_of_subn_or_0_correct:
  shows "real_of_float (Float_of_subn_or_0 x (s,0,f)) = valof x (s,0,f)"
  by (simp add: powr_realpow powr_diff)

corollary Float_of_subn_or_0_rep:
  "is_denormal x r \<or> is_zero x r \<Longrightarrow> real_of_float (Float_of_subn_or_0 x r) = valof x r"
  unfolding is_denormal_def is_zero_def
  by (cases r) (auto simp del: Float_of_subn_or_0.simps simp add: Float_of_subn_or_0_correct)


subsection \<open>Combining the finite cases\<close>

fun Float_of_finite :: "format \<Rightarrow> representation \<Rightarrow> Float.float" where
  "Float_of_finite x (s,0,f) = Float_of_subn_or_0 x (s,0,f)" |
  "Float_of_finite x (s,e,f) = Float_of_normal x (s,e,f)"

theorem Float_of_finite_correct: "real_of_float (Float_of_finite x r) = valof x r"
  using Float_of_finite.simps Float_of_normal_correct Float_of_subn_or_0_correct
  by (cases r) (metis Suc_pred neq0_conv)

section \<open>Float.float to IEEE.float\<close>

definition normal_rep_of_Float_b :: "format \<Rightarrow> nat \<Rightarrow> Float.float \<Rightarrow> representation"
  where
    "normal_rep_of_Float_b x b f =
  (if is_float_pos f then 0 else 1,
    nat (Float.exponent f + int (bias x) + b),
    nat (\<bar>Float.mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))"

lemma normal_rep_of_Float_b_correct:
  fixes b :: nat
  assumes f_not_zero: "\<not>is_float_zero f"
  assumes exponent_b: "0 < Float.exponent f + int (bias x) + b"
    and mantissa_b: "0 \<le> \<bar>Float.mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    and b_ok: "fracwidth x \<ge> b"
  shows "valof x (normal_rep_of_Float_b x b f) = real_of_float f"
  using assms
proof  (cases "is_float_pos f")
  case True
  have if_false: "\<not>nat (Float.exponent f + int (bias x) + b) = 0"
    using exponent_b by linarith
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
    using mantissa_b by auto
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = real_of_int (mantissa f)"
    using \<open>0 < mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + (real (fracwidth x) + real (bias x)))
    = real_of_int (Float.exponent f + bias x + fracwidth x)"
    by simp
  have s5: "real (nat (Float.exponent f + int (bias x) + int b)) + real (fracwidth x - b)
    = real_of_int (Float.exponent f + int (bias x) + int (fracwidth x))"
    using if_false b_ok by linarith
  show ?thesis
    unfolding a
    by (simp add: s2 s3 divide_simps powr_realpow[symmetric] powr_add[symmetric])
        (simp add: s4 s5)
next
  case False
  have if_false: "nat (Float.exponent f + int (bias x) + int b) \<noteq> 0"
    using exponent_b by linarith
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
    by (metis False Float.compute_is_float_pos Float.compute_is_float_zero Float_mantissa_exponent
        f_not_zero linorder_neqE_linordered_idom)
  then have "\<bar>mantissa f\<bar> = - mantissa f"
    by simp
  then have s2: "real (nat (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x))
    = \<bar>mantissa f\<bar> * 2 ^ (fracwidth x - b) - 2 ^ fracwidth x"
    using mantissa_b by auto
  have s3: "\<bar>real_of_int (mantissa f)\<bar> = - real_of_int (mantissa f)"
    using \<open>0 > mantissa f\<close> by linarith
  have s4: "(real_of_int (Float.exponent f) + (real (fracwidth x) + real (bias x)))
    = real_of_int (Float.exponent f + bias x + fracwidth x)"
    by simp
  have s5: "real (nat (Float.exponent f + int (bias x) + int b)) + real (fracwidth x - b)
    = real_of_int (Float.exponent f + int (bias x) + int (fracwidth x))"
    using if_false b_ok by linarith
  show ?thesis
    unfolding a
    by (simp add: s2 s3 divide_simps powr_realpow[symmetric] powr_add[symmetric])
      (simp add: s4 s5)
qed

lemma floorlog_pos_iff: "floorlog b x > 0 \<longleftrightarrow> x > 0 \<and> b > 1"
  by (auto simp: floorlog_def)

lemma bitlen_pos_iff: "bitlen x > 0 \<longleftrightarrow> x > 0"
  by (auto simp: bitlen_def floorlog_pos_iff)

definition normal_rep_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation" where
  "normal_rep_of_Float x f = normal_rep_of_Float_b x (nat (bitlen \<bar>mantissa f\<bar> - 1)) f"

lemma normal_rep_of_Float_correct:
  assumes "\<not>is_float_zero f"
  assumes mantissa: "bitlen \<bar>mantissa f\<bar> \<le> fracwidth x"
  assumes exponent: "- int (bias x) - bitlen \<bar>mantissa f\<bar> + 1 < Float.exponent f"
    "exponent f < 2^(expwidth x) - int (bias x) - fracwidth x"
  shows "valof x (normal_rep_of_Float x f) = real_of_float f" (is ?th1)
    and "is_valid x (normal_rep_of_Float x f)" (is ?th2)
    and "is_normal x (normal_rep_of_Float x f)" (is ?th3)
proof -
  from assms(1) have mnz[simp]: "mantissa f \<noteq> 0"
    by (auto simp: is_float_zero_def mantissa_exponent)
  let ?bl = "bitlen \<bar>mantissa f\<bar>"
  have bl_pos: "?bl > 0"
    by (auto simp: bitlen_pos_iff)
  have "\<bar>Float.mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1)) - 2 ^ fracwidth x \<ge>
    2 ^ (nat (?bl - 1)) * 2 ^ (fracwidth x - nat (?bl - 1)) - 2 ^ fracwidth x"
    using bitlen_bounds[of "\<bar>mantissa f\<bar>"] bl_pos
    by (auto simp: bitlen_def floorlog_def)
  also have "2 ^ (nat (?bl - 1)) * 2 ^ (fracwidth x - nat (?bl - 1)) - 2 ^ fracwidth x
    = (2::int) ^ (nat (?bl - 1) + (fracwidth x - nat (?bl - 1))) - 2 ^ fracwidth x"
    unfolding power_add[symmetric]
    by auto
  also have "(nat (?bl - 1) + (fracwidth x - nat (?bl - 1))) = fracwidth x"
    using assms by simp
  finally have mantissa_ok: "0 \<le> \<bar>mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1)) - 2 ^ fracwidth x"
    by simp
  have "\<bar>mantissa f\<bar> * (2::real) ^ (fracwidth x - nat (?bl - 1)) <
      2 ^ nat (?bl) * (2::real) ^ (fracwidth x - nat (?bl - 1))"
    using abs_real_le_2_powr_bitlen bitlen_nonneg powr_int
    by auto
  also have "\<dots> = 2 ^ (nat (?bl) + fracwidth x - nat (?bl - 1))"
    unfolding power_add[symmetric]
    using mantissa
    by simp
  also
  have "?bl > 0" by fact
  then have "nat (?bl) + fracwidth x - nat (?bl - 1) = fracwidth x + 1"
    using assms
    by (simp)
  finally
  have "\<bar>mantissa f\<bar> * (2::real) ^ (fracwidth x - nat (?bl - 1)) < 2 ^ (fracwidth x + 1)"
    by simp
  then have "real_of_int (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1))) <
    real_of_int (2 ^ (fracwidth x + 1) - 1) + 1"
    by simp
  then have "\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1)) < 2 ^ (fracwidth x + 1)"
    unfolding int_le_real_less[symmetric]
    by simp
  then have "\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1)) < 2 ^ (fracwidth x + 1)"
    by simp
  then have "\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1)) - 2 ^ fracwidth x < 2 ^ fracwidth x"
    by (simp)
  with mantissa_ok
  have l: "nat (\<bar>mantissa f\<bar> * 2 ^ (fracwidth x - nat (?bl - 1)) - 2 ^ fracwidth x) < 2 ^ fracwidth x"
    by (simp add: nat_less_iff)

  have emax: "nat (Float.exponent f + int (bias x) + (bitlen \<bar>mantissa f\<bar> - 1)) < emax x"
    using exponent mantissa
    by (auto simp: emax_def nat_less_iff of_nat_diff)
  show ?th1
    unfolding normal_rep_of_Float_def
    using assms mantissa_ok mantissa
    by (intro normal_rep_of_Float_b_correct) auto
  show ?th2
    unfolding normal_rep_of_Float_def
    using assms l
    by (auto simp: normal_rep_of_Float_b_def nat_less_iff is_valid)
  show ?th3
    using bl_pos exponent emax
    by (auto simp: normal_rep_of_Float_def normal_rep_of_Float_b_def is_normal_def bl_pos emax_def)
qed

lemma general_valof_topfloat:
  assumes ew_ok: "expwidth x \<ge> 2"
  shows "valof x (topfloat x) = largest x"
proof -
  let ?fw = "2 ^ fracwidth x"
  from ew_ok have "((2::nat) ^ expwidth x - 1 - 1) \<ge> 1"
    by simp (metis Suc_1 Suc_leI linorder_neqE_nat nat.simps(1) not_le not_numeral_le_zero
        numerals(2) power.simps(1) power_inject_exp power_one_right zero_less_diff zero_less_power)
  moreover have "real (?fw - Suc 0) = real (?fw) - 1"
    by (simp add: of_nat_diff)
  moreover have "(?fw - (1::real)) / ?fw = 1 - 1 / ?fw"
  proof -
    have f1: "\<forall>r ra rb. (r::real) / rb + ra / rb + - 1 * ((ra + r) / rb) = 0"
      by (simp add: add_divide_distrib)
    have "- (1::real) + ?fw + 1 = ?fw"
      by auto
    then have f2: "(1::real) / ?fw + (- 1 + ?fw) / ?fw + - 1 * (?fw / ?fw) = 0"
      using f1 by metis
    have f3: "((?fw - (1::real)) / ?fw \<noteq> 1 - 1 / ?fw) = ((1::real) / ?fw + (- 1 + ?fw) / ?fw \<noteq> 1)"
      by fastforce
    have "(1::real) / ?fw + (- 1 + ?fw) / ?fw = 1"
      using f2 by simp
    then show "(?fw - (1::real)) / ?fw = 1 - 1 / ?fw"
      using f3 by meson
  qed
  ultimately show ?thesis
    unfolding emax_def topfloat_def largest_def
    by auto
qed

definition subnormal_rep_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation"
  where
    "subnormal_rep_of_Float x f =
  (if is_float_nonneg f then 0 else 1,
    0,
    nat (\<bar>Float.mantissa f\<bar> * 2 ^ nat (exponent f + bias x + fracwidth x - 1)))"

lemma floorlog_leD: "floorlog b x \<le> w \<Longrightarrow> b > 1 \<Longrightarrow> x < b ^ w"
  by (metis One_nat_def floorlog_bounds less_Suc0 less_le_trans neq0_conv power_0 power_increasing_iff zero_le)

lemma bitlen_leD: "nat x < 2 ^ w" if "bitlen x \<le> w"
  using that
  by (auto simp: bitlen_def dest!: floorlog_leD)

lemma subnormal_rep_of_Float_correct:
  assumes "\<not>is_float_zero f"
  assumes mantissa: "bitlen \<bar>mantissa f\<bar> \<le> 1 - exponent f - bias x"
  assumes exponent: "fracwidth x - int (bias x) < exponent f"

shows "valof x (subnormal_rep_of_Float x f) = real_of_float f" (is ?th1)
  and "is_valid x (subnormal_rep_of_Float x f)" (is ?th2)
  and "is_denormal x (subnormal_rep_of_Float x f)" (is ?th3)
proof -
  have mnz: "mantissa f \<noteq> 0" using assms(1) by (auto simp: is_float_zero_def mantissa_exponent)
  then have "bitlen (\<bar>mantissa f\<bar> * 2 ^ nat (Float.exponent f + int (bias x) + int (fracwidth x) - 1)) =
    bitlen \<bar>mantissa f\<bar> + Float.exponent f + int (bias x) + int (fracwidth x) - 1"
    using exponent
    by simp
  also have "\<dots> \<le> fracwidth x"
    using mantissa
    by simp
  finally have "bitlen (\<bar>mantissa f\<bar> * 2 ^ nat (Float.exponent f + int (bias x) + int (fracwidth x) - 1)) \<le> fracwidth x"
    .
  from bitlen_leD[OF this]
  have 1: "nat (\<bar>mantissa f\<bar> * 2 ^ nat (Float.exponent f + int (bias x) + int (fracwidth x) - 1))
    < 2 ^ fracwidth x"
    by (auto simp: bitlen_def)

  have 2: "\<bar>mantissa f\<bar> * 2 ^ nat (Float.exponent f + int (bias x) + int (fracwidth x) - 1) > 0"
    using mnz
    by (auto simp: intro!: mult_pos_pos)

  have req: "real (nat (Float.exponent f + int (bias x) + int (fracwidth x) - 1)) =
        real_of_int (Float.exponent f) + real (bias x) + real (fracwidth x) - 1"
    using exponent by auto
  have not_le: "2 powr real_of_int (Float.exponent f) \<le> 0 \<longleftrightarrow> False"
    by (simp add: antisym_conv)
  show ?th2
    using 1
    by (auto simp: subnormal_rep_of_Float_def is_valid_def)
  show ?th3
    using 2
    by (auto simp: subnormal_rep_of_Float_def is_denormal_def)
  show ?th1
    by (auto simp: subnormal_rep_of_Float_def powr_realpow[symmetric] powr_add diff_add_eq req
        powr_diff is_float_nonneg_def zero_le_mult_iff not_le
        mantissa_exponent)
qed

definition float_rep_of_Float :: "format \<Rightarrow> Float.float \<Rightarrow> representation" where
  "float_rep_of_Float x f = (
    if is_float_zero f
    then (0,0,0)
    else
      let (m, e) = (mantissa f, exponent f)
      in
        if bitlen (abs m) + e \<le> 1 - int (bias x)
        then subnormal_rep_of_Float x f
        else normal_rep_of_Float x f
  )"

lemma is_valid_0: "is_valid x (0, 0, 0)"
  by (auto simp: is_valid_def)

lemma is_zero_0: "is_zero x (0, 0, 0)"
  by (auto simp: is_finite_def is_denormal_def is_normal_def is_valid_0 is_zero_def)

theorem float_rep_of_Float:
  "valof x (float_rep_of_Float x f) = real_of_float f"
  "is_valid x (float_rep_of_Float x f)"
  "is_finite x (float_rep_of_Float x f)"
  if "bitlen \<bar>mantissa f\<bar> \<le> int (fracwidth x)"
    "int (fracwidth x) - int (bias x) < Float.exponent f"
    "Float.exponent f < 2 ^ expwidth x - int (bias x) - int (fracwidth x)"
  using that
  by (auto simp: float_rep_of_Float_def is_float_zero_def is_finite_def is_zero_0
      intro!: subnormal_rep_of_Float_correct normal_rep_of_Float_correct is_valid_0)


section \<open>Lifting to Type @{type float}\<close>

definition "Float_of_IEEE x = Float_of_finite float_format (Rep_float x)"

theorem Float_of_IEEE: "real_of_float (Float_of_IEEE x) = Val x"
  by (auto simp: Float_of_IEEE_def Float_of_finite_correct Val_def)

definition "IEEE_of_Float x = Abs_float (float_rep_of_Float float_format x)"

lemma Finite_Abs_float_iff:
  "Finite (Abs_float x) \<longleftrightarrow> is_finite float_format x" if "is_valid float_format x"
  using that
  by (auto simp: Finite_def Isnormal_def Abs_float_inverse is_finite_def
      Isdenormal_def Iszero_def)

theorem IEEE_of_Float: "Val (IEEE_of_Float x) = real_of_float x"
  and IEEE_of_Float_Finite: "Finite (IEEE_of_Float x)"
  if "bitlen (abs (mantissa x)) \<le> 52" "- 971 < exponent x" "exponent x < 973"
  using that float_rep_of_Float[of x float_format]
  by (auto simp: Val_def IEEE_of_Float_def float_format_def bias_def Abs_float_inverse
      Finite_Abs_float_iff)

end