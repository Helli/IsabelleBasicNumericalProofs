theory TwoSum
imports
  test_utils
  "$AFP/IEEE_Floating_Point/FloatProperty"
begin

subsection \<open>Further operations\<close>

definition "fma_float a b c = Float (Val a * Val b + Val c)"

code_printing constant "fma_float :: float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.*+ ((_), (_), (_))"
declare fma_float_def [code del]

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

lemma twoSum_correct1:
  shows "fst (twoSum (a, b)) = a + b"
  by (metis Pair_inject prod.collapse twoSum.simps)

corollary twoSum_correct1':
  assumes "Finite (a + b)"
  shows "fst (twoSum (a, b)) \<doteq> (a + b)"
  using assms float_eq twoSum_correct1 by presburger

corollary s_finite: "Finite (a + b) \<longleftrightarrow> Finite (fst (twoSum(a, b)))"
  using twoSum_correct1 by simp

corollary twoSum_swaps:
  assumes "Finite a" and "Finite b"
  assumes "(s, e) = twoSum (a, b)"
  assumes "(s', e') = twoSum (b, a)"
  shows twoSum_swap: "s' = s" (*TODO: and "e' = e" *)
  and twoSum_swap': "s' \<doteq> s" (*TODO: and "e' \<doteq> e" *)
  apply (metis assms float_plus_comm_eq fst_conv twoSum_correct1)
  apply (metis assms float_plus_comm_eq fst_conv twoSum_correct1
    float_eq_refl fadd_finite_notIsnan)
  done

lemma twoSum_correct2:
  assumes "Finite a" and "Finite b" and "Finite (a + b)"
  assumes "twoSum (a, b) = (r, s)"
  shows "Val a + Val b = Val r + Val s"
  sorry

end