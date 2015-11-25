theory TwoSum_tests
imports
  test_utils
  TwoSum
begin

subsection \<open>Input data\<close>

definition twoSum_input :: "(float*float) list"
where "twoSum_input = [
  (float_of_int 0, float_of_int 0),
  (float_of_int 9 / float_of_int 10, float_of_int 8 / float_of_int 10),
  (float_of_int 353905643, float_of_int (-23423)),
  (float_of_int 352, float_of_int 2342345903),
  (float_of_int (-353), float_of_int 353),
  (float_of_int 1 / float_of_int 353, float_of_int 2676543423),
  (float_of_int 353, float_of_int 1 /  float_of_int 29893423),
  (float_of_int 353, float_of_int 1 /  float_of_int (-29893423)),
  (float_of_int (-45), float_of_int (-34529693554493592))
  ]"

definition input_sw_float :: "(Float.float*Float.float) list"
where "input_sw_float = map (\<lambda>(x, y). (toFloat x, toFloat y)) twoSum_input"


subsection \<open>Output data\<close>

definition twoSum_output :: "(float*float) list"
where "twoSum_output = map twoSum twoSum_input"

definition output_sw_float :: "(Float.float*Float.float) list"
where "output_sw_float = map (\<lambda>(x, y). (toFloat x, toFloat y)) twoSum_output"


subsection \<open>Test results\<close>

definition a_plus_b :: "Float.float list"
where "a_plus_b = map (\<lambda>(x, y). x + y) input_sw_float"

definition s_plus_e :: "Float.float list"
where "s_plus_e = map (\<lambda>(x, y). x + y) output_sw_float"

definition test_data :: "(Float.float * Float.float) list"
where
  " 
  test_data = zip a_plus_b s_plus_e
  
    (* fake test result: (6, 4). Comment in for a negative result*)
    (* @[(Float.Float 3 1, Float.Float 4 0)]   *)
  "


subsection \<open>Printing\<close>

(* short overview on raw output *)

fun print_result :: "(Float.float * Float.float) \<Rightarrow> unit"
where "print_result (x, y) = (let
  _ = print (if (x=y) then (STR ''OK     | '') else (STR ''FAILED | ''));
  _ = println_sw_float y
  in ())"

value [code] "(let _ = println (STR ''\<newline>result | s+t\<newline>-------|----------'');
  _ = map print_result test_data;
  _ = println (if (list_all (\<lambda>(x, y). x = y) test_data)
    then (STR ''All tests passed.'')
    else (STR ''One or more tests failed. Use print_details for more information.''))
  in ())"


(*details for a single test case*)

definition print_details :: "nat \<Rightarrow> unit"
where "print_details n = (let
  _ = print (STR ''\<newline>Details for case '');
  _ = print (int_to_string n);
  _ = println (STR '':'');
  _ = print (STR ''a = '');
  _ = println_sw_float (fst (input_sw_float ! n));
  _ = print (STR ''b = '');
  _ = println_sw_float (snd (input_sw_float ! n));
  _ = print (STR ''s = '');
  _ = println_sw_float (fst (output_sw_float ! n));
  _ = print (STR ''t = '');
  _ = println_sw_float (snd (output_sw_float ! n));
  _ = print (STR ''a+b = '');
  _ = println_sw_float (a_plus_b ! n);
  _ = print (STR ''s+t = '');
  _ = println_sw_float (s_plus_e ! n);
  _ = println (if a_plus_b ! n = s_plus_e ! n
    then STR ''OK (a+b = s+t)''
    else STR ''FAILED (a+b != s+t)'')
  in ())"

value [code] "print_details 8"

(*
value [code] "map print_details [0, 4, 5]"
*)

subsection \<open>Testing Twosum with STORE\<close>

(*ensure rounding: store variables*)
definition "STORE x = x"
code_printing constant "STORE :: 'a \<Rightarrow> 'a" \<rightharpoonup>
  (SML) "(Unsynchronized.! (Unsynchronized.ref ((_))))"
declare [[code drop: STORE]]

(* twoSum with STORE *)
fun twoSumSTORE :: "float * float \<Rightarrow> float *float"
  where "twoSumSTORE (a, b) =
    (let
      s =  STORE(a + b);
      an = STORE(s - b);
      bn = STORE(s - an);
      da = STORE(a - an);
      db = STORE(b - bn);
      e =  STORE(da + db)
    in (s, e))"

definition twoSumSTORE_output :: "(float*float) list"
where "twoSumSTORE_output = map twoSumSTORE twoSum_input"

definition tsSTORE_sum_tests :: "(float*float) list"
where "tsSTORE_sum_tests = zip (map fst twoSum_output) (map fst twoSumSTORE_output)"

definition tsSTORE_err_tests :: "(float*float) list"
where "tsSTORE_err_tests = zip (map snd twoSum_output) (map snd twoSumSTORE_output)"

definition tsSTORE_sum_results :: "bool list"
where "tsSTORE_sum_results = map (\<lambda>(x, y). float_eq x y) tsSTORE_sum_tests"

definition tsSTORE_err_results :: "bool list"
where "tsSTORE_err_results = map (\<lambda>(x, y). float_eq x y) tsSTORE_err_tests"

(* These should be true no matter what *)
value [code] "tsSTORE_sum_results"

(*
  These should be true if twoSumSTORE\<equiv>twoSum in your installation
  check README for details
*)
value [code] "tsSTORE_err_results"


subsection \<open>Test for use with other ml-compilers\<close>

context begin

  private definition test_input :: "float*float"
    where "test_input = (float_of 33, float_of 1 / float_of 1243313)"

  private definition test_result :: "float*float"
    where "test_result = twoSum test_input"

  primrec test where "test () =
    (let
      _ = print (STR ''a = ''); _ = println (string_of_float (fst test_input));
      _ = print (STR ''b = ''); _ = println (string_of_float (snd test_input));
      _ = print (STR ''r = ''); _ = print (string_of_float (fst test_input + snd test_input));
      _ = println (STR '' (the float closest to a+b)'');
      _ = print (STR ''s = ''); _ = println (string_of_float (fst test_result));
      _ = print (STR ''t = ''); _ = println (string_of_float (snd test_result))
    in println (STR ''done''))"

  primrec test2 where "test2 () = 
    (let
      (a, b) = test_input;
      (s, t) = twoSum test_input;
      (af, bf) = (toFloat a, toFloat b);
      (sf, tf) = (toFloat s, toFloat t)
    in (normfloat (af + bf), normfloat (sf + tf)))"

  value [code] "test2 ()"

end

(* hide_const (open) a *)

subsection \<open>Output\<close>

(*
definition hello_world::"unit \<Rightarrow> unit" where
  "hello_world _ = (println (STR ''Starting 2sum example...''))"
value [code] "hello_world ()"

value [code] "test ()"
*)

export_code test in SML module_name Test
(*
export_code test in SML module_name Test file "test.sml"
*)


end
