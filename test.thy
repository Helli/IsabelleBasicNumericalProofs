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
  and "\<bar>a + b\<bar> < threshold float_format"
  assumes "\<bar>a + b\<bar> \<le> \<bar>a\<bar>" and "\<bar>a + b\<bar> \<le> \<bar>b\<bar>"
  shows "error (a + b) = 0"
  oops

lemma lower_then_finite:
  "\<bar>x\<bar> < threshold float_format \<Longrightarrow> Finite (Float x)"
by (smt Finite_def Float_def Isdenormal_def Isnormal_def Iszero_def defloat_float_round is_finite_closest is_finite_def round.simps(1))

lemma lower_then_finite':
  "Finite x \<Longrightarrow> \<bar>Val x\<bar> < threshold float_format"
  using float_val_gt_threshold float_val_lt_threshold by fastforce

lemma err_simp: "error x = Val (Float x) - x"
  by (simp add: Float_def error_def)

lemma
  assumes "Finite a" "Finite b" "\<bar>Val a + Val b\<bar> < threshold float_format"
  assumes "(s, e) = TwoSum a b"
  shows "Val s + Val e = Val a + Val b"
  proof -
    let ?x = "a + b"
    let ?bv = "?x - a"
    let ?av = "?x - ?bv"
    let ?br = "b - ?bv"
    let ?ar = "a - ?av"
    let ?y = "?ar + ?br"
    note 1 = float_add[OF assms(1, 2, 3)]
    then have "\<bar>Val (?x) - Val a\<bar> = \<bar>Val b + error (Val a + Val b)\<bar>" by simp
    also have "... \<le> \<bar>Val b\<bar> + \<bar>error (Val a + Val b)\<bar>"
      by (simp add: abs_triangle_ineq)
    also have "\<dots> < threshold float_format"
      (*prove "\<bar>f\<bar> < threshold float_format \<Longrightarrow> error f < ulp Max_float" ? *)
      sorry
    ultimately
      have "\<bar>Val (?x) - Val a\<bar> < threshold float_format"
        by simp
    note 2 = float_sub[of ?x a, OF "1"(1) assms(1) this]
    thm float_sub [of ?x ?bv]
    then have "\<bar>Val (?x) - Val (?bv)\<bar> = \<bar>Val (?x) - (Val (?x) - Val a +
    error (Val (?x) - Val a))\<bar>"
      by simp
    also have "\<dots> = \<bar>Val a - error (Val (?x) - Val a)\<bar>"
      by simp
    also have "\<dots> < threshold float_format"
      sorry
    ultimately have "\<bar>Val (?x) - Val (?bv)\<bar> < threshold float_format"
      by simp
    note 3 = float_sub [of ?x ?bv, OF 1(1) 2(1) this]
    from 2 have "\<bar>Val b - Val ?bv\<bar> = \<bar>Val b - (Val (?x) - Val a +
    error (Val (?x) - Val a))\<bar>" by simp
    also have "... < threshold float_format"
      (* sledgehammer: inform Tobias Nipkow *)
      by (smt "1"(2) \<open>\<bar>Val b\<bar> + \<bar>error (Val a + Val b)\<bar> < threshold float_format\<close> assms error_at_worst_lemma)
    ultimately have "\<bar>Val b - Val ?bv\<bar> < threshold float_format"
      by simp
    note 4 = float_sub[of b ?bv, OF assms(2) 2(1) this]
    from 3 have "\<bar>Val a - Val ?av\<bar> = \<bar>Val a - (Val ?x - Val ?bv + error (Val ?x - Val ?bv))\<bar>"
      by simp
    also have "\<dots> < threshold float_format"
      by (smt "1"(1) "2"(2) \<open>\<bar>Val (a + b) - Val (a + b - a)\<bar> < threshold float_format\<close> \<open>\<bar>Val (a + b) - Val a\<bar> < threshold float_format\<close> assms(1) err_smaller error_at_worst_lemma float_val_gt_threshold float_val_lt_threshold)
    ultimately have "\<bar>Val a - Val ?av\<bar> < threshold float_format"
      by simp
    note 5 = float_sub[of a ?av, OF assms(1) 3(1) this]
    thm float_add[of ?ar ?br] 1 2 3 4 5
    from 4 have "\<bar>Val ?ar + Val ?br\<bar> = \<bar>Val ?ar + Val b - Val (a + b - a) +
    error (Val b - Val (a + b - a))\<bar>"
      by simp
    from 5 have "... = \<bar>Val a -
    Val (a + b - (a + b - a)) +
    error
     (Val a -
      Val (a + b - (a + b - a))) + Val b - Val (a + b - a) +
    error (Val b - Val (a + b - a))\<bar>"
      by simp
    thm this [simplified]
    have "error (Val ?x - Val a) = 0"

thm float_add