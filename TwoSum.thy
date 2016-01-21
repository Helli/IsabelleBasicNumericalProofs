theory TwoSum
imports
  TwoProdFMA
  test_utils
  "$AFP/IEEE_Floating_Point/FloatProperty"
begin

subsection \<open>Further operations\<close>

code_printing
  code_module "ULP_Float" \<rightharpoonup> (SML)
  \<open>fun ulp_float x =
  let
    val (m, e) = tomanexp x
  in
    Real.fromManExp {man = 1.0, exp = e}
  end\<close>

definition ulp_float::"float \<Rightarrow> float" where "ulp_float x = undefined"
code_printing constant "ulp_float :: float \<Rightarrow> float" \<rightharpoonup> (SML) "ulp'_float"
declare ulp_float_def[code del]


subsection \<open>Needed Float Properties\<close>

lemma fadd_finite_notIsnan: "Finite a \<Longrightarrow> Finite b \<Longrightarrow> \<not>Isnan (a + b)"
  sorry


subsection \<open>Implementation\<close>

(* s for sum, e for error *)
fun twoSum::"float * float \<Rightarrow> float *float"
  where "twoSum (a, b) =
    (let
      s = a + b;
      an = s - b;
      bn = s - an;
      da = a - an;
      db = b - bn;
      e = da + db
    in (s, e))"


subsection \<open>Properties\<close>

lemma twoSum_correct1_eq:
  shows "fst (twoSum (a, b)) = a + b"
  by (metis Pair_inject prod.collapse twoSum.simps)

corollary twoSum_correct1:
  assumes "Finite (a + b)"
  shows "fst (twoSum (a, b)) \<doteq> (a + b)"
  using assms float_eq twoSum_correct1_eq by presburger

corollary s_finite: "Finite (a + b) \<longleftrightarrow> Finite (fst (twoSum(a, b)))"
  using twoSum_correct1_eq by simp

corollary twoSum_swaps:
  assumes "Finite a" and "Finite b"
  assumes "(s, e) = twoSum (a, b)"
  assumes "(s', e') = twoSum (b, a)"
  shows twoSum_swap: "s' = s" (*TODO: and "e' = e" *)
  and twoSum_swap': "s' \<doteq> s" (*TODO: and "e' \<doteq> e" *)
  apply (metis assms float_plus_comm_eq fst_conv twoSum_correct1_eq)
  apply (metis assms float_plus_comm_eq fst_conv twoSum_correct1_eq
    float_eq_refl fadd_finite_notIsnan)
  done

lemma twoSum_correct2:
  assumes "Finite a" and "Finite b" and "Finite (a + b)"
  assumes "(s, e) = twoSum (a, b)"
  shows "Val a + Val b = Val s + Val e"
  sorry

lemma fadd_twoSum_s_e:
  assumes "(s, e) = twoSum (a, b)"
  assumes "Finite a" "Finite b" "Finite s" "Finite e"
  shows "(s + e) \<doteq> s"
  using assms
  sorry

corollary twoSum_idempotent:
  assumes "(s, e) = twoSum (a, b)"
  assumes "(s', e') = twoSum (s, e)"
  assumes "Finite a" "Finite b" "Finite s" "Finite e"
  shows "s' \<doteq> s" (*TODO: and "e' \<doteq> e"*)
  using assms
  apply (metis fadd_twoSum_s_e fst_conv twoSum_correct1_eq)
  done

lemma twoSum_e_le_ulp:
  assumes "(s, e) = twoSum (a, b)"
  assumes "Finite a" "Finite b" "Finite s" "Finite e"
  shows"e \<le> ulp_float s"
  sorry

lemma twoSum_abs_le:
  assumes "(s, e) = twoSum (a, b)"
  assumes "Finite a" "Finite b" "Finite s" "Finite e"
  shows "float_abs e \<le> float_abs s"
  sorry

lemma err:
  assumes "Isnormal a" "Isnormal b" "Isnormal (a + b)"
  shows "abs (Val a + Val b - Val (a + b)) \<le> abs (Val a)" (is "?abs_err \<le> abs (Val a)")
using assms
proof cases
  assume f1: "abs (Val a) \<ge> abs (Val b)"
  have f2: "Finite (a + b)"
    by (simp add: Finite_def assms(3))
  with f1 f2 have f4: "\<forall>fp. abs (Val a + Val b - Val fp) \<ge> ?abs_err"
    sorry
  then have "?abs_err \<le> abs (Val b)"
    by (meson eq_iff order_trans sin_bound_lemma)
  with f1 show ?thesis
    by simp
next
  assume "\<not>abs (Val a) \<ge> abs (Val b)"
  show ?thesis sorry
qed

subsection \<open>regular and safe_bound\<close>

--\<open>Ensure that the multiplication in safe_bound is exact.
  ToDo: find a more sensible constraint using fracwidth\<close>
fun length_ok :: "float list \<Rightarrow> bool" where
  "length_ok [] = True" |
  "length_ok (a # as) \<longleftrightarrow> (let
    n = float_of_int (length as);
    u = ulp_float a
    in Finite (n*u) \<and> Iszero (snd (twoProdFMA n u)))"

fun regular :: "float list \<Rightarrow> bool" where
  "regular [] = True" |
  "regular (a # as) \<longleftrightarrow> Finite a \<and> list_all (\<lambda>y. float_abs y \<le> ulp_float a) as
    \<and> length_ok (a # as)"

--\<open>safe_bound, when applied to a regular multiple precision float x (e.g. as produced by vecSum),
gives a pair (v, b), such that x represents a value in v + [-b; b]\<close>
fun safe_bound :: "float list \<Rightarrow> float \<times> float" where
  "safe_bound [] = (Plus_zero, Plus_zero)" |
  "safe_bound (x # xs) = (x, float_of_int (length xs) * ulp_float(x))"

end