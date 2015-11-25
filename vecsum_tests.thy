theory VecSum_tests
imports
  test_utils
  VecSum
begin

subsection \<open>Test Values\<close>

definition l1 :: "float list" where
  "l1 = [
    float_of_int 43,
    float_of_int 34538,
    float_of_int (-348976754389282980)]"

definition l2 :: "float list" where
  "l2 = [
    float_of_int 3,
    float_of_int 6,
    float_of_int 44,
    float_of_int 2 / float_of_int 5]"

subsection \<open>Printing\<close>

(* output panel *)
abbreviation "toNF \<equiv> normfloat o toFloat"
value [code] "map toNF (vecSum l1)"
value [code] "map toNF (vecSum l2)"

(* alternative: print to raw output *)
value "map (println_sw_float o toFloat) (vecSum l1)"
value "map (println_sw_float o toFloat) (vecSum l2)"

subsection \<open>Testing against another implementation\<close>

fun VecSum_Joldes_et_al :: "float list \<Rightarrow> float list" where
  "VecSum_Joldes_et_al [] = []"
| "VecSum_Joldes_et_al [a] = [a]"
| "VecSum_Joldes_et_al (a0 # a1 # as) = (let
    (s, e) = twoSum (a0, a1) in
    (e # VecSum_Joldes_et_al (s # as)))"

definition t_a where "t_a = rev (vecSum l1)"
definition t_b where "t_b = VecSum_Joldes_et_al l1"

value "map (\<lambda>(x, y). x \<doteq> y) (zip t_a t_b)"
(* ToDo: replace by lemma *)

end