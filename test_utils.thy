theory test_utils
imports
  "~~/src/HOL/Library/Float"
  "$AFP/IEEE_Floating_Point/Code_Float"
begin


subsection \<open>Conversion from int\<close>

definition "float_of_int i = Float (real_of_int i)"

context includes integer.lifting begin
lift_definition float_of_integer::"integer \<Rightarrow> float" is float_of_int .
end

lemma float_of_int[code]:
  "float_of_int i = float_of_integer (integer_of_int i)"
  by (auto simp: float_of_integer_def)

code_printing
  constant "float_of_integer :: integer \<Rightarrow> float" \<rightharpoonup> (SML) "Real.fromInt"
declare [[code drop: float_of_integer]]


subsection \<open>Conversion to software floats\<close>

code_printing
code_module "ToManExp" \<rightharpoonup> (SML)
  \<open>fun tomanexp x =
  let
    val {man = m, exp = e} = Real.toManExp x;
    val p = Math.pow (2.0, 53.0);
    val ms = m * p;
    val mi = Real.floor ms;
    val ei = op Int.- (e, 53);
  in (mi, ei)
  end\<close>

consts tomanexp::"float \<Rightarrow> integer * integer"
code_printing constant "tomanexp :: float \<Rightarrow> integer * integer" \<rightharpoonup>
  (SML) "tomanexp"

definition toFloat::"float \<Rightarrow> Float.float" where
  "toFloat x = (let (m, e) = tomanexp x in Float.Float (int_of_integer m) (int_of_integer e))"

value [code] "((Float.Float 123 (-13)) + (Float.Float 13 (-13))) * ((Float.Float 123 (-13)))"
value [code] "toFloat (float_of 1 / float_of 1243313)"


subsection \<open>Conversion from software floats\<close>

code_printing
code_module "FromManExp" \<rightharpoonup> (SML)
  \<open>fun frommanexp m e = Real.fromManExp {man = Real.fromLargeInt m, exp = e}\<close>
consts frommanexp::"integer \<Rightarrow> integer \<Rightarrow> float"
code_printing constant "frommanexp :: integer \<Rightarrow> integer \<Rightarrow> float" \<rightharpoonup>
  (SML) "frommanexp"

definition of_Float::"Float.float \<Rightarrow> float" where
  "of_Float x = (frommanexp (integer_of_int (Float.mantissa x)) (integer_of_int (Float.exponent x)))"


subsection \<open>just for debugging: floats to strings and printing\<close>

subsubsection \<open>integers to strings\<close>

definition int_to_string::"int \<Rightarrow> String.literal"
  where "int_to_string x = STR ''''"

context includes integer.lifting begin

lift_definition integer_to_string::"integer \<Rightarrow> String.literal"
  is int_to_string .

end

lemma [code]: "int_to_string x = integer_to_string (integer_of_int x)"
  by (simp add: integer_to_string_def)

code_printing
  constant "integer_to_string :: integer \<Rightarrow> String.literal" \<rightharpoonup> (SML) "IntInf.toString"
declare [[code drop: integer_to_string]]


subsection \<open>printing floats\<close>

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
declare [[code drop: "print"]]

consts float_of_string::"String.literal \<Rightarrow> float"

lemma [code]: "term_of_class.term_of (x::float) \<equiv>
  Code_Evaluation.App
    (Code_Evaluation.termify of_Float)
    (term_of_class.term_of (normfloat (toFloat x)))"
  by (rule term_of_anything)

value [code] "(One::float) + One + One"

definition println::"String.literal \<Rightarrow> unit" where
  "println x = (let _ = print x in print (STR ''\<newline>''))"


subsection \<open>printing Float.floats\<close>

definition println_sw_float::"Float.float \<Rightarrow> unit" where
  "println_sw_float x = (let
      _ = print (int_to_string (Float.mantissa x));
      _ = print (STR '' * 2 ^ '');
      _ = println (int_to_string (Float.exponent x))
     in
       ())"

code_printing constant "Isnormal :: float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isNormal"
declare [[code drop: "Isnormal"]]

end