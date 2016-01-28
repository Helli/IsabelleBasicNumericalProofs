theory test
imports
  "$AFP/IEEE_Floating_Point/RoundError"
  "$AFP/IEEE_Floating_Point/FloatProperty"
begin

definition TwoSum :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "TwoSum a b = (let
    x = a + b;
    b\<^sub>v = x - a;
    a\<^sub>v = x - b\<^sub>v;
    b\<^sub>r = b - b\<^sub>v;
    a\<^sub>r = a - a\<^sub>v;
    y = a\<^sub>r + b\<^sub>r
    in (x, y))"

lemma finite_0: "Finite Plus_zero"
  by (simp add: Finite_def float_zero1)

lemma val_0_0: "Val Plus_zero = 0"
  using Iszero_def Val_def float_zero1 val_zero by auto

lemma err_smaller: "\<bar>a\<bar> < threshold float_format \<Longrightarrow> \<bar>error a\<bar> \<le> \<bar>a\<bar>"
  using error_at_worst_lemma[of a Plus_zero, OF _ finite_0]
  by (simp add: val_0_0)

lemma err1: "0 \<le> a \<Longrightarrow> a < threshold float_format \<Longrightarrow> error a \<le> a"
  thm error_at_worst_lemma
  using error_at_worst_lemma[of a Plus_zero, OF _ finite_0]
  by (simp add: val_0_0)

lemma
  assumes "\<bar>a\<bar> < threshold float_format" and "\<bar>b\<bar> < threshold float_format"
  assumes "\<bar>a + b\<bar> \<le> \<bar>a\<bar>" and "\<bar>a + b\<bar> \<le> \<bar>b\<bar>"
  shows "error (a + b) = 0"
  oops

lemma lower_then_finite:
  "\<bar>x\<bar> < threshold float_format \<Longrightarrow> Finite (Float x)"
by (smt Finite_def Float_def Isdenormal_def Isnormal_def Iszero_def defloat_float_round is_finite_closest is_finite_def round.simps(1))

lemma
  assumes "Finite a" "Finite b" "\<bar>Val a + Val b\<bar> < threshold float_format"
  assumes "(s, e) = TwoSum a b"
  shows "Val s + Val e = Val a + Val b"
  proof (cases "0 \<le> Val a + Val b")
  case True
    have smaller: "Val a + Val b < threshold float_format"
      using assms(3) by auto
    note 1 = float_add[OF assms(1, 2, 3)]
    then have "\<bar>Val (a + b) - Val a\<bar> = \<bar>Val b + error (Val a + Val b)\<bar>" by simp
    thm err1[of "Val a + Val b", OF True smaller]
    also have "... \<le> \<bar>Val b\<bar> + \<bar>error (Val a + Val b)\<bar>"
      by (simp add: abs_triangle_ineq)
    also have "... \<le> \<bar>Val b\<bar> + \<bar>Val b\<bar>"
      using error_at_worst_lemma[of "Val a + Val b" a, OF assms(3, 1)]
      by (metis (no_types) abs_minus_cancel add_diff_cancel_left' add_left_mono minus_diff_eq)
    thm float_add
    thm err_smaller[of "Val a + Val b", OF assms(3)]
    thm error_is_zero
    thm error_at_worst_lemma
    thm error_float_sub[of "a+b" a, OF 1(1) assms(1)]
    also have "\<dots> < threshold float_format"
      sledgehammer
      oops
    note error_float_sub[of "a+b" a]
    

thm float_add