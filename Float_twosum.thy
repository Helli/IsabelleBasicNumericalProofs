theory Float_twosum
imports
  Complex_Main
  "~~/src/HOL/Library/Code_Target_Numeral"
  "$AFP/IEEE_Floating_Point/RoundError"
  "$AFP/IEEE_Floating_Point/Code_Float"
begin

subsection \<open>ensure rounding: store variables\<close>

definition "STORE x = x"
code_printing constant "STORE :: 'a \<Rightarrow> 'a" \<rightharpoonup>
  (SML) "(Unsynchronized.! (Unsynchronized.ref ((_))))"
declare [[code drop: STORE]]

subsection \<open>just for debugging: floats to strings and printing\<close>

instantiation float::term_of
begin
definition term_of::"float \<Rightarrow> term" where "term_of x = undefined"
instance ..
end

definition string_of_float::"float \<Rightarrow> String.literal" where
  "string_of_float x = STR ''''"

code_printing constant "string_of_float :: float \<Rightarrow> String.literal" \<rightharpoonup>
  (SML) "Real.toString"
declare [[code drop: "string_of_float"]]

definition print::"String.literal \<Rightarrow> unit" where
  "print x = ()"

code_printing constant "print :: String.literal \<Rightarrow> unit" \<rightharpoonup>
  (SML) "TextIO.print"
declare [[code drop: "string_of_float"]]

lemma [code]: "term_of_class.term_of (x::float) \<equiv> Code.abort (string_of_float x) (\<lambda>_. undefined)"
  by (rule term_of_anything)

definition println::"String.literal \<Rightarrow> unit" where
  "println x = (let _ = print x in print (STR ''\<newline>''))"

subsection \<open>Implementation\<close>

fun twosum::"float * float \<Rightarrow> float *float"
  where "twosum (a, b) =
    (let
      s = STORE (a + b);
      an = STORE (s - b);
      bn = STORE (s - an);
      da = STORE (a - an);
      db = STORE (b - bn);
      t = STORE (da + db)
    in (s, t))"


subsection \<open>Test Values\<close>

definition a :: "float"
  where "a = float_of 33"

definition b :: "float"
  where "b = float_of 1 / float_of 1243313"

definition r :: "float"
  where "r = a+b"

definition test_input :: "float*float"
  where "test_input = (a, b)"

definition test_result :: "float*float"
  where "test_result = twosum test_input"

definition s :: "float"
  where "s = fst test_result"


subsection \<open>Output\<close>

definition hello_world::"unit \<Rightarrow> unit" where
  "hello_world _ = (println (STR ''Starting 2sum example...''))"
value [code] "hello_world ()"

primrec test where "test () =
  (let
    _ = print (STR ''a = ''); _ = println (string_of_float a);
    _ = print (STR ''b = '') ; _ = println (string_of_float b);
    _ = print (STR ''r = '') ; _ = print (string_of_float (a+b));
    _ = println (STR '' (the float closest to a+b)'');
    _ = print (STR ''s = '') ; _ = println (string_of_float s);
    _ = print (STR ''t = '') ; _ = println (string_of_float (snd test_result))
  in println (STR ''done''))"

value [code] "test ()"

export_code test in SML module_name Test
export_code test in SML module_name Test file "test.sml"

(*This equality test should be true:*)
value [code] "r \<le> s \<and> r \<ge> s "

end