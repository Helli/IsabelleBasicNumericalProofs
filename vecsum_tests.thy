theory vecsum_tests
imports
  Float_twosum
  VecSum
begin

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

abbreviation "toNF \<equiv> normfloat o toFloat"

(* output panel*)
value [code] "map toNF (vecsum l2)"

(*alternative: print to raw output*)
value "map (println_sw_float o toFloat) (vecsum l1)"

end