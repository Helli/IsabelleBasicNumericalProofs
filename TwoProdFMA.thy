theory TwoProdFMA
imports
  test_utils
  "$AFP/IEEE_Floating_Point/FloatProperty"
begin

subsection \<open>Fused Multiply-Add (FMA)\<close>

--\<open>FMA returns the float closest to the exact result of a*b+c\<close>
definition "fma_float a b c = Float (Val a * Val b + Val c)"

code_printing constant "fma_float :: float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.*+ ((_), (_), (_))"
declare fma_float_def [code del]

--\<open>This definition might not work in all special cases, consider

value [code] "fma_float Plus_zero (float_neg Plus_zero) (float_neg Plus_zero)"

However, it should suffice for our purposes.\<close>


subsection \<open>Implementation\<close>

definition twoProdFMA :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "twoProdFMA a b = (let
    p = a * b;
    e = fma_float a b (float_neg p)
    in (p, e))"


subsection \<open>Properties\<close>

lemma twoProdFMA_correct1_eq:
  assumes "(p, e) = twoProdFMA a b"
  shows "p = a * b"
  using assms by (metis prod.inject twoProdFMA_def)

lemma twoProdFMA_correct1:
  assumes "(p, e) = twoProdFMA a b"
  assumes "Finite (a * b)"
  shows "p \<doteq> (a * b)"
  using assms float_eq twoProdFMA_correct1_eq by blast

lemma twoProdFMA_correct2:
  assumes "(p, e) = twoProdFMA a b"
  assumes "Finite (a * b)"
  --\<open>a*b must be representable as the sum of two floats.
    A sufficient condition is (from HFPA):\<close>
  assumes "Exponent a + Exponent b \<ge>
    - bias float_format + fracwidth float_format + 1"
  shows "Val p + Val e = Val a * Val b"
  sorry

end