theory VecSum
imports
  TwoSum
begin

fun itVecSum :: "float list \<Rightarrow> float list \<Rightarrow> float list" where
  "itVecSum [] hs = rev hs" |
  "itVecSum [a] hs = a # rev hs" |
  "itVecSum (a1 # a2 # as) hs = (let
    (s, e) = twoSum (a2, a1)
    in itVecSum (s # as) (e # hs))"

lemma itVecSum_correct1:
  --\<open>listsum is not available due to missing monoid properties of fadd\<close>
  shows "hd (itVecSum (a # as) bs) = fold op+ as a"
  apply (induction as arbitrary: a bs)
  apply (simp_all add: twoSum_correct1 split_def del: twoSum.simps)
  done

fun vecSum :: "float list \<Rightarrow> float list" where
  "vecSum mpf = itVecSum mpf []"

lemma vecSum_correct1:
  shows "hd (vecSum (a # as)) = fold op + as a"
  by (simp add: itVecSum_correct1)

corollary vecSum_correct1':
  assumes "Finite (fold op + as a)"
  shows "hd (vecSum (a # as)) \<doteq> fold op + as a"
  using assms float_eq vecSum_correct1
  by presburger

lemma vecSum_correct2:
  assumes "list_all Finite mpf"
  assumes "list_all Finite (vecSum mpf)"
  shows "listsum (map Val (vecSum mpf)) = listsum (map Val mpf)"
  sorry

end