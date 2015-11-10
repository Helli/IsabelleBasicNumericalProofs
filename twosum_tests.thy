theory twosum_tests
imports
  Float_twosum
begin

subsection \<open>Input data\<close>

definition twosum_input :: "(float*float) list"
where "twosum_input = [
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
where "input_sw_float = map (\<lambda>(x, y). (toFloat x, toFloat y)) twosum_input"


subsection \<open>Output data\<close>

definition twosum_output :: "(float*float) list"
where "twosum_output = map twosum twosum_input"

definition output_sw_float :: "(Float.float*Float.float) list"
where "output_sw_float = map (\<lambda>(x, y). (toFloat x, toFloat y)) twosum_output"


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

subsection \<open>Testing Twosum without STORE\<close>
  
(* twosum without STORE *)
fun twosumNew::"float * float \<Rightarrow> float *float"
  where "twosumNew (a, b) =
    (let
      s =  (a + b);
      an = (s - b);
      bn = (s - an);
      da = (a - an);
      db = (b - bn);
      e =  (da + db)
    in (s, e))"

definition twosumNew_output :: "(float*float) list"
where "twosumNew_output = map twosumNew twosum_input"

definition tsNew_sum_tests :: "(float*float) list"
where "tsNew_sum_tests = zip (map fst twosum_output) (map fst twosumNew_output)"

definition tsNew_err_tests :: "(float*float) list"
where "tsNew_err_tests = zip (map snd twosum_output) (map snd twosumNew_output)"

definition tsNew_sum_results :: "bool list"
where "tsNew_sum_results = map (\<lambda>(x, y). float_eq x y) tsNew_sum_tests"

definition tsNew_err_results :: "bool list"
where "tsNew_err_results = map (\<lambda>(x, y). float_eq x y) tsNew_err_tests"

(* These should be true no matter what *)
value [code] "tsNew_sum_results"

(* These should be true if twosumNew\<equiv>twosum in your installation*)
value [code] "tsNew_err_results"

end