theory MPF
imports
  test_utils
  "$AFP/IEEE_Floating_Point/Code_Float"
  "$AFP/IEEE_Floating_Point/FloatProperty"
  "~~/src/HOL/Library/Monad_Syntax"
begin

--\<open>Define the "Multiple Precision Float"\<close>
type_synonym mpf = "float \<times> float list"

fun approx :: "mpf \<Rightarrow> float" where
  "approx (a, es) = a"

fun errors :: "mpf \<Rightarrow> float list" where
  "errors (a, es) = es"

lemma "approx = fst" and "errors = snd"
  by auto

definition Plus_zero_mpf :: mpf where
  "Plus_zero_mpf = (Plus_zero, [])"

definition Minus_zero_mpf :: mpf where
  "Minus_zero_mpf = (Minus_zero, [])"

definition One_mpf :: mpf where
  "One_mpf = (One, [])"

--\<open>Use another notation for the possibly inexact IEEE-operations\<close>
abbreviation round_affected_plus :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<oplus>" 65) where
  "round_affected_plus a b \<equiv> a + b"

abbreviation round_affected_minus :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<ominus>" 65) where
  "round_affected_minus a b \<equiv> a - b"

abbreviation round_affected_times :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<otimes>" 65) where
  "round_affected_times a b \<equiv> a * b"

context
  fixes a b :: float
  assumes ge: "float_abs a \<ge> float_abs b"
begin

  definition FastTwoSum :: "float \<times> float" where
    "FastTwoSum = (let
      x = a \<oplus> b;
      b\<^sub>v = x \<ominus> a;
      y = b \<ominus> b\<^sub>v
      in (x, y))"
    
  lemma FastTwoSum_correct1: "FastTwoSum = (x, y) \<Longrightarrow> x = a \<oplus> b"
    by (auto simp: FastTwoSum_def Let_def)
  
  lemma FastTwoSum_correct2:
    fixes x y :: float
    assumes "Finite a"
    assumes "Finite b"
    assumes "Finite (a \<oplus> b)"
    assumes out: "(x, y) = FastTwoSum"
    shows "Val a + Val b = Val x + Val y"
    sorry

end
thm FastTwoSum_def FastTwoSum_correct1 FastTwoSum_correct2

definition TwoSum :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "TwoSum a b = (let
    x = a \<oplus> b;
    b\<^sub>v = x \<ominus> a;
    a\<^sub>v = x \<ominus> b\<^sub>v;
    b\<^sub>r = b \<ominus> b\<^sub>v;
    a\<^sub>r = a \<ominus> a\<^sub>v;
    y = a\<^sub>r \<oplus> b\<^sub>r
    in (x, y))"

lemma TwoSum_correct1: "TwoSum a b = (x, y) \<Longrightarrow> x = a \<oplus> b"
  by (auto simp: TwoSum_def Let_def)

lemma TwoSum_correct2:
  fixes a b x y :: float
  assumes "Finite a"
  assumes "Finite b"
  assumes "Finite (a \<oplus> b)"
  assumes out: "(x, y) = TwoSum a b"
  shows "Val a + Val b = Val x + Val y"
  sorry

lemma swap: "TwoSum a b = TwoSum b a"
  sorry

text\<open>We embed @{const TwoSum} to make sure overflow will be noticed:\<close>
definition "safe_TwoSum a b =
  (let r = TwoSum a b in
    if Finite (fst r) \<and> Finite (snd r)
    then Some r
    else None)"

lemma safe_TwoSum_finite:
  assumes "safe_TwoSum a b = Some (s, e)"
  shows safe_TwoSum_finite1: "Finite s"
  and safe_TwoSum_finite2: "Finite e"
  using assms
  by (auto simp: safe_TwoSum_def Let_def split: split_if_asm)

lemma safe_TwoSum_correct1:
  "safe_TwoSum a b = Some (x, y) \<Longrightarrow> x = a \<oplus> b"
  by (auto simp: safe_TwoSum_def Let_def TwoSum_correct1 split: split_if_asm)

lemma safe_TwoSum_correct2:
  fixes a b x y :: float
  assumes "Finite a" "Finite b" "Finite (a \<oplus> b)"
  assumes out: "safe_TwoSum a b = Some (x, y)"
  shows "Val a + Val b = Val x + Val y"
  using assms
by (auto intro!: TwoSum_correct2 simp: safe_TwoSum_def Let_def split: split_if_asm)

definition "IsZero_mpf mpf \<longleftrightarrow> Iszero (approx mpf) \<and> errors mpf = []"
fun Val_mpf :: "mpf \<Rightarrow> real" where
  "Val_mpf (a, es) = Val a + listsum (map Val es)"
--\<open>sophisticated methods using Float.float might be faster\<close>
fun Finite_mpf :: "mpf \<Rightarrow> bool" where
  "Finite_mpf (a, es) \<longleftrightarrow> Finite a \<and> list_all Finite es"

fun valid :: "mpf \<Rightarrow> bool" where
  "valid (a, es) = (case Iszero a of
    True \<Rightarrow> es = [] |
    False \<Rightarrow> Finite a \<and> list_all (\<lambda>f. Isdenormal f \<or> Isnormal f) es)"

lemma float_distinct_10: "\<not> (Isnormal f \<and> Iszero f)"
  by (auto simp add: float_defs is_normal_def is_zero_def)

lemma valid_no_zero_components: "valid (a, es) \<Longrightarrow> list_all (\<lambda>f. \<not>Iszero f) es"
  apply (simp split: bool.splits)
  apply (induction es)
  using float_distinct(9) float_distinct_10
  apply auto
  done

lemma valid_finite: "valid (a, es) \<Longrightarrow> Finite_mpf (a, es)"
  apply (simp split: bool.splits)
  using float_cases_finite float_distinct apply fastforce
  by (metis (no_types, lifting) Ball_set Finite_def)

--\<open>Recursive versions for induction proofs:\<close>
lemma rec_val: "Val_mpf (a, e # es) = Val a + Val_mpf (e, es)"
  by simp
lemma rec_finite: "Finite_mpf (a, e # es) \<longleftrightarrow> Finite a \<and> Finite_mpf (e, es)"
  by simp

subsection \<open>MPF operations\<close>

fun safe_grow_mpf_rec :: "mpf \<Rightarrow> float \<Rightarrow> mpf option" where
  "safe_grow_mpf_rec (a, []) f =
    do {
      (x, y) \<leftarrow> safe_TwoSum f a;
      Some (x, [y])
    }" |
  "safe_grow_mpf_rec (a, e # es) f =
    do {
      (a', es') \<leftarrow> safe_grow_mpf_rec (e, es) f;
      (x, y) \<leftarrow> safe_TwoSum a' a;
      Some (x, y # es')
    }"

lemmas safe_grow_mpf_induct = safe_grow_mpf_rec.induct[case_names no_error in_between]

lemma preserve_finite:
  assumes "safe_grow_mpf_rec mpf x = Some r"
  assumes "Finite x" "Finite_mpf mpf"
  shows "Finite_mpf r"
using assms
proof (induction mpf x arbitrary: r rule: safe_grow_mpf_induct)
--\<open>The base case is the case where the mpf is a single float with an empty error-list:\<close>
case (no_error a f)
--\<open>We apply the definition of @{const safe_grow_mpf_rec}:\<close>
from no_error.prems(1) have "do {(x, y) \<leftarrow> safe_TwoSum f a; Some (x, [y])} = Some r"
    unfolding safe_grow_mpf_rec.simps(1) .
--\<open>Since we required the result to be some value, we can give it a name:\<close>
  then obtain x y where xy: "safe_TwoSum f a = Some (x, y)" and r: "r = (x, [y])"
    by (auto simp: bind_eq_Some_conv)
--\<open>and then delegate to the corresponding property of @{const safe_TwoSum}:\<close>
  moreover from safe_TwoSum_finite[OF xy]
    have "Finite x" "Finite y".
  ultimately show ?case
    by simp
next
case (in_between a e es f r_full)
--\<open>This case is similar except that we need to prove more floats to be finite\<close>
  note "in_between.prems"(1)[simplified, unfolded bind_eq_Some_conv, simplified]
  then obtain l r where goal1: "safe_grow_mpf_rec (e, es) f = Some (l, r)"
    and r1: "do {(x, y) \<leftarrow> safe_TwoSum l a; Some (x, y # r)} = Some r_full"
      by blast
  then obtain l2 r2 where l2: "safe_TwoSum l a = Some (l2, r2)" and
     r2: "(l2, r2 # r) = r_full"
     using r1[unfolded bind_eq_Some_conv, simplified] by auto
  from r2 have "?case = Finite_mpf (l2, r2 # r)" by simp
  moreover have "Finite l2"
    using safe_TwoSum_finite1[OF l2].
  moreover have "Finite r2"
    using safe_TwoSum_finite2[OF l2].
  moreover from "in_between.IH"[OF goal1 "in_between.prems"(2)] have "list_all Finite r"
    using "in_between.prems"(3)
      by simp
  ultimately
    show ?case
    by simp
qed

theorem preserve_val:
  assumes "safe_grow_mpf_rec mpf x = Some r"
  assumes "Finite x" "Finite_mpf mpf"
  shows "Val_mpf r = Val_mpf mpf + Val x"
using assms
proof (induction mpf x arbitrary: r rule: safe_grow_mpf_induct)
case (no_error a f)
  from no_error.prems(1) have "safe_TwoSum f a \<bind> (\<lambda>(x, y). Some (x, [y])) = Some r"
    unfolding safe_grow_mpf_rec.simps(1) .
  then obtain x y where xy: "safe_TwoSum f a = Some (x, y)" and r: "r = (x, [y])"
    by (auto simp: bind_eq_Some_conv)
  from safe_TwoSum_finite1[OF xy]
  have "Finite x".
  from no_error have an: "Finite a" by simp
  show ?case
    using safe_TwoSum_correct2[OF \<open>Finite f\<close> an _ xy] \<open>Finite x\<close>
      safe_TwoSum_correct1[OF xy]
    by (auto simp: r split: prod.split)
next
case (in_between a e es f r_full)
  note "in_between.prems"(1)[simplified, unfolded bind_eq_Some_conv, simplified]
  then obtain l r where goal1: "safe_grow_mpf_rec (e, es) f = Some (l, r)"
    and r1: "safe_TwoSum l a \<bind> (\<lambda>(x, y). Some (x, y # r)) = Some r_full"
      by blast
  then obtain l2 r2 where l2: "safe_TwoSum l a = Some (l2, r2)" and
     r2: "(l2, r2 # r) = r_full"
     using r1[unfolded bind_eq_Some_conv, simplified] by auto
  then have "Val_mpf r_full = Val_mpf (l2, r2 # r)" by simp
  also have "\<dots> = Val l2 + Val_mpf (r2, r)"
    by (simp add: rec_val)
  also have "\<dots> = Val l2 + Val r2 + listsum(map Val r)"
    by simp
  also have "\<dots> = Val l + Val a + listsum(map Val r)"
    proof -
      from "in_between.prems" have "Finite l"
        using goal1 preserve_finite by auto
      moreover have "Finite a"
        using "in_between.prems"(3) by simp
      moreover have "Finite (l + a)"
        using l2 safe_TwoSum_correct1 safe_TwoSum_finite1 by auto
      moreover have "Val l + Val a = Val l2 + Val r2"
        using safe_TwoSum_correct2[OF calculation l2].
      ultimately show ?thesis
        by simp
    qed
  finally show ?case
    using in_between goal1 rec_finite by auto
qed

lemmas safe_grow_mpf_correct =
  preserve_finite
  preserve_val

fun mpf_neg :: "mpf \<Rightarrow> mpf" where
  "mpf_neg (a, es) = (float_neg a, map float_neg es)"

subsection \<open>Testing\<close>

definition "sehrgross = undefined"
definition "gross = undefined"
definition "mittel = undefined"
definition "klein = undefined"
definition "sehrklein = undefined"
definition "test_mpf = (sehrgross, [gross, mittel, klein, sehrklein])"

(* generate unfolded view in "output" *)
definition "output = safe_grow_mpf_rec test_mpf (float_of 1)"
lemma "P output" unfolding output_def test_mpf_def safe_grow_mpf_rec.simps
  apply (clarsimp split: prod.splits) oops

fun build_mpf :: "float list \<Rightarrow> mpf option" where
  "build_mpf [] = undefined" |
  "build_mpf [f] = Some (f, [])" |
  "build_mpf (f # fs) = do {
    a \<leftarrow> build_mpf fs;
    safe_grow_mpf_rec a f
  }"

fun plus_mpf :: "mpf \<Rightarrow> mpf \<Rightarrow> mpf option" where
  "plus_mpf (a1, []) mpf2 = safe_grow_mpf_rec mpf2 a1" |
  "plus_mpf (a1, e1 # es1) mpf2 = do {
    a \<leftarrow> plus_mpf (e1, es1) mpf2;
    safe_grow_mpf_rec a a1
  }"

fun minus_mpf where
  "minus_mpf mpf1 mpf2 = plus_mpf mpf1 (mpf_neg mpf2)"

ML \<open>val grow_mpf_ml = @{code safe_grow_mpf_rec}\<close>
ML \<open>val test1 =  (2341.0, [~12.324, 0.0003])\<close> (* \<approx>2328.6763 *)
ML \<open>val test2 =  (2351.0, [~12.325, 0.00003])\<close> (* \<approx>2338.67503 *)
ML \<open>grow_mpf_ml test1 5000.00\<close>
ML \<open>grow_mpf_ml test1 0.001\<close>
ML \<open>val test1_list = fst test1 :: snd test1\<close>
ML \<open>val test2_list = fst test2 :: snd test2\<close>
ML \<open>val test_list = test1_list @ test2_list\<close>
ML \<open>@{code build_mpf} test_list\<close>
ML \<open>@{code plus_mpf} test1 test2\<close>
ML \<open>@{code minus_mpf} test1 test2\<close>

end