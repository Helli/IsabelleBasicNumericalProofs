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
    float_of_int 3 / float_of_int 43,
    float_of_int 0,
    float_of_int 0,
    float_of_int (-348976754389282980)]"
  (* result:
  [Float.Float (- 5452761787332007) 6, Float.Float 723951696777 (- 35),
  Float.Float 0 0, Float.Float 0 0, Float.Float (- 146313) (- 56), Float.Float 0 0]
  *)

definition l2 :: "float list" where
  "l2 = [
    float_of_int 3,
    float_of_int 6,
    float_of_int 44,
    float_of_int 2 / float_of_int 5,
    float_of_int 1 / float_of_int 23]"
  (* result:
  [Float.Float 7521500899407355 (- 47), Float.Float 89 (- 55), Float.Float 13 (- 53),
  Float.Float 0 0, Float.Float 0 0]
  *)

definition l3 :: "float list" where
  "l3 = [
    float_of_int 3452345234533456344,
    float_of_int 3,
    float_of_int 5 / float_of_int 325432345453464552
  ]"
  (* result:
    [Float.Float 6742861786198157 9, Float.Float 4985960341560939 (- 108), 3]
  *)

value "let (a, b) = (float_of_int 345234523, float_of_int 34)
  in fst (twoSum (a, b)) \<doteq> hd (vecSum [a, b])
  \<and> snd (twoSum (a, b)) \<doteq> last (vecSum [a, b])"

subsection \<open>Printing\<close>

--\<open>convert hardware floats to Float.float for an exact representation\<close>
abbreviation toNF :: "float \<Rightarrow> Float.float" where
  "toNF \<equiv> normfloat o toFloat"

(* print to the output panel *)
value "map toNF (vecSum l1)"
value "map toNF (vecSum l2)"
value "map toNF (vecSum l3)"

(* alternative: print to raw output *)
value [code] "let
  _ = println (STR ''Test 1:'');
  _ = map (println_sw_float o toFloat) (vecSum l1);
  _ = println (STR ''Test 2:'');
  _ = map (println_sw_float o toFloat) (vecSum l2);
  _ = println (STR ''Test 3:'');
  _ = map (println_sw_float o toFloat) (vecSum l3)
  in println (STR ''Done.'')"

subsection \<open>Testing against another implementation\<close>

fun VecSum_Joldes_et_al :: "float list \<Rightarrow> float list" where
  "VecSum_Joldes_et_al [] = []"
| "VecSum_Joldes_et_al [a] = [a]"
| "VecSum_Joldes_et_al (a0 # a1 # as) = (let
    (s, e) = twoSum (a0, a1) in
    (e # VecSum_Joldes_et_al (s # as)))"

definition t_a where "t_a = vecSum l1"
definition t_b where "t_b = VecSum_Joldes_et_al l1"

value "map (\<lambda>(x, y). x \<doteq> y) (zip t_a (last t_b # butlast (t_b)))"
(* ToDo: replace by lemma *)

end
