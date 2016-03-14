(*<*)
theory Main_Thesis
imports
  "~~/src/HOL/Library/Monad_Syntax"
  "~~/src/HOL/Library/Float"
begin
(*>*)

chapter\<open>Introduction\<close>
text\<open>
When attacking computational problems by machine, often times fixed precision numbers have to be used: Arbitrary precision numbers are very slow, mostly because they don't use the hardware floating point operations that are available to modern systems. If the finite set of these machine numbers suffice (or an approximation within their range), the use of hard-wired operations can speed up the computation by a large factor. However, they introduce the problem of round-off, which, when not handled, will affect the output's precision in complex ways.\<close>
section\<open>Round-off\<close>
text\<open>
Round-off occurs when the result of a floating-point operation cannot be represented as a datum of the same format. This happens in particular if the size of exponent and mantissa is fixed, as it is case for floats defined by the IEEE standard for floating-point arithmetic@{cite IEEE}. Round-off also occurs when casting measured or infinitely precise data to such a limited precision format.\<close>
paragraph\<open>Dealing with round-off\<close>
text\<open>If round-off affected arithmetic is used in a long sequence of operations, the result will only approximate within a certain range. Correctness proofs for assertions to this range will require a tedious numerical analysis of the algorithms which is very complex to do formally.\<close>
paragraph\<open>Avoiding round-off\<close>
text\<open>Another approach is to avoid round-off altogether. However, using an implementation of infinitely precise rationals might severely slow down the code's execution due to them not making use of hardware floating point operations that modern machines provide.\<close>
paragraph\<open>Float expansions\<close>
text\<open>If a finite set of numbers with magnitude and precision in the range of IEEE floats suffices however, both the precision and fast execution speed can be preserved: This thesis presents the "float expansion" approach, where the accumulated errors are stored in a list alongside with an approximation for the result of the executed sequence. It provides addition, subtraction and multiplication within the numbers representable in this way (a finite superset to IEEE floats).\<close>

section\<open>Problem statement\<close>
text\<open>Isabelle@{cite NipkowPaulsonWenzel} already provides the arbitrary precision format @{typ real} in its @{theory Complex_Main} library. The widely popular "IEEE-floats"@{cite IEEE} are modelled in an Isabelle theory \<open>IEEE_Floating_Point/IEEE\<close>@{cite "IEEE_Floating_Point-AFP"} provided by the "Archive of Formal Proofs" (AFP).

The task for this bachelor thesis is to use this formalization to present a "multiple precision" float arithmetic in Isabelle/HOL. In several scientific papers this is described as "floating point expansion"@{cite priest}@{cite mioara} or "multiple term"@{cite mioara} strategy. It is an easy way to gain considerable amounts of precision while still using the IEEE floating point specification to enable the widely available acceleration of hardware operations.\<close>

section\<open>Contributions\<close>
text\<open>We explain different aspects of the "floating point expansion" approach and then provide the data format @{text mpf}, which stands for "multiple precision float". It implements error-free addition, subtraction and multiplication within the numbers representable in this format (a finite superset to IEEE floats).
We use the formal setting of Isabelle/HOL to specify and prove the algorithms correct, but we make sure all of them can easily be executed by adapting Isabelle's Standard ML (SML) code generation for IEEE-floats.
\<close>

chapter\<open>Code Analysis\<close>
section\<open>IEEE in Isabelle\<close>
text\<open>The IEEE standard for floating point arithmetic (IEEE 754-2008)@{cite IEEE} is already modelled in Lei Yu's AFP entry \<open> IEEE_Floating_Point/IEEE\<close>.
The formalization is quite general to accommodate for the many different allowed formats that arise when different precisions and exponent ranges are combined (the decimal formats are omitted). However, a strong precedence for the "binary64" format and the "roundTiesToEven" rounding mode can be observed. The operations using this format and rounding rule (called \<open>float_format\<close> respectively \<open>To_nearest\<close> in the theory) are wrapped into definitions with simpler names, e.g.\<close>
text\<open>@{theory_text \<open>
definition plus_float :: "float \<Rightarrow> float \<Rightarrow> float" where
"a + b = Abs_float (fadd float_format To_nearest (Rep_float a) (Rep_float b))"
\<close>}\<close>
text\<open>In the case of the format, this is justifiable by "binary64" being widely popular and hardware-implemented on most systems.

In the case of the rounding mode, the IEEE standard defines "roundTiesToEven" to be the default (@{cite IEEE}p. 16).

We also use this format and rounding mode, which enables us to use the code printing defined in the theory \<open>Code_Float\<close> from the same AFP entry. The "roundTiesToEven" rule is explicitly required for the TwoSum-properties (@{cite HFPA} sect. 4.3.3) and thus for all the presented algorithms.
\<close>


(*<*)
(*Type synonyms*)
type_synonym format = "nat \<times> nat" 
type_synonym representation = "nat \<times> nat \<times> nat" 

fun expwidth :: "format \<Rightarrow> nat" where
"expwidth (ew, fw) = ew" 

fun fracwidth :: "format \<Rightarrow> nat" where
"fracwidth (ew, fw) = fw"

(*<*)
definition wordlength :: "format \<Rightarrow> nat" where
"wordlength x = (expwidth(x) + fracwidth(x) + 1)"
(*>*)

definition emax :: "format \<Rightarrow> nat" where
"emax x =  2^(expwidth x) - 1"

(*<*)
definition bias :: "format \<Rightarrow> nat" where
"bias x = 2^(expwidth x - 1) - 1 "

subsection {*Predicates for the four IEEE formats*}

definition is_single :: "format \<Rightarrow> bool" where
"is_single x = ((expwidth x = 8) \<and> (wordlength x = 32))"

definition is_double :: "format \<Rightarrow> bool" where
"is_double x = ((expwidth x = 11) \<and> (wordlength x = 64))"

definition is_single_extended :: "format \<Rightarrow> bool" where
"is_single_extended x = ((expwidth x \<ge> 11) \<and> (wordlength x \<ge> 43))"

definition is_double_extended :: "format \<Rightarrow> bool" where
"is_double_extended x = ((expwidth x \<ge> 15) \<and> (wordlength x \<ge> 79))"

subsection {*Extractors for fields*}
(*>*)
fun sign :: "representation \<Rightarrow> nat" where
"sign (s, e, f) = s"

fun exponent :: "representation \<Rightarrow> nat" where
"exponent (s, e, f) = e"

fun fraction :: "representation \<Rightarrow> nat" where
"fraction (s, e, f) = f"
(*<*)

subsection{*Partition of numbers into disjoint classes*}

definition is_nan :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_nan x a = ((exponent a = emax x) \<and> \<not>(fraction a = 0))"

definition is_infinity :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_infinity x a = ((exponent a = emax x) \<and> (fraction a = 0))"

definition is_normal :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_normal x a = ((0 < exponent a) \<and> (exponent a < emax x))"

definition is_denormal :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_denormal x a = ((exponent a = 0) \<and> \<not>(fraction a = 0))"

definition is_zero :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_zero x a = ((exponent a = 0) \<and> (fraction a = 0))"
(*>*)
definition is_valid :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_valid x a = (sign a < 2 \<and> (exponent a < 2^(expwidth x) \<and> (fraction a < 2^(fracwidth x))))"
(*<*)
definition is_finite :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_finite x a = ((is_valid x a) \<and> ((is_normal x a) \<or> (is_denormal x a) \<or> (is_zero x a)))"


subsection{*Special values*}

definition plus_infinity :: "format \<Rightarrow> representation" where
"plus_infinity x = (0, emax x, 0)"

definition minus_infinity :: "format \<Rightarrow> representation" where
"minus_infinity x = (1, emax x, 0)"

definition plus_zero :: "format \<Rightarrow> representation" where
"plus_zero x = (0, 0, 0)"

declare plus_zero_def [simp]

definition minus_zero :: "format \<Rightarrow> representation" where
"minus_zero x = (1, 0, 0)"

declare minus_zero_def [simp]

definition topfloat :: "format \<Rightarrow> representation" where
"topfloat x = (0, (emax x - 1), 2^(fracwidth x) - 1)"

definition bottomfloat :: "format \<Rightarrow> representation" where
"bottomfloat x = (1, (emax x - 1), 2^(fracwidth x) - 1)" 

subsection{*Negation operation on floating point values*}

definition minus :: "format \<Rightarrow> representation \<Rightarrow> representation" where
"minus x a = (1 - sign a, exponent a, fraction a)"

declare minus_def [simp]

subsection{*Concrete encodings*}
fun encoding :: "format \<Rightarrow> representation \<Rightarrow> nat" where
"encoding x (s, e, f) = ((s * power 2 (wordlength(x) - 1)) + (e * power 2 (fracwidth x)) + f) "

subsection{*Real number valuations*}
fun valof :: "format \<Rightarrow> representation \<Rightarrow> real" where
"valof x (s, e, f) = 
(if (e = 0) 
 then (-1::real)^s * (2 / (2^bias x)) * (real f/2^(fracwidth x))
 else (-1::real)^s * ((2^e) / (2^bias x)) * (1 + real f/2^fracwidth x))"

(*The largest value that can be represented in floating point format*)
definition largest :: "format \<Rightarrow> real" where
"largest x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^fracwidth x))"


(*threshold, used for checking overflow *)
definition threshold :: "format \<Rightarrow> real" where
"threshold x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^(Suc(fracwidth x))))"

(*ulp*)
definition ulp :: "format \<Rightarrow> representation \<Rightarrow> real" where
"ulp x a = valof x (0, exponent a, 1) - valof x (0, exponent a, 0)"

(*>*)
text "in a begin (figure) ?"
(*Enumerated type for rounding modes*)
datatype roundmode = To_nearest | float_To_zero | To_pinfinity | To_ninfinity
text \<open>The required rounding modes according to standard 4.3.3\<close>
(*<*)

(*Characterization of best approximation from a set of abstract values*)
definition is_closest 
where
"is_closest v s x a \<equiv> (a \<in> s) \<and> (\<forall>b. b \<in> s \<longrightarrow> abs((v a) - x ) \<le> abs ((v b) - x))"



(*Best approximation with a deciding preference for multiple possibilities*)
definition closest 
where
"closest v p s x = (\<some>a. is_closest v s x a \<and> ((\<exists>b. is_closest v s x b \<and> (p b)) \<longrightarrow> p a))"


subsection{*Rounding*}
fun round :: "format \<Rightarrow> roundmode \<Rightarrow> real \<Rightarrow> representation" where
 "round x To_nearest y = 
           (if y \<le> -(threshold x) 
            then minus_infinity x 
            else if y \<ge> threshold x
            then plus_infinity x 
            else (closest (valof x) (\<lambda>a. even (fraction a)) {a. is_finite x a} y) )"

| "round x float_To_zero y = 
           (if y < -(largest x) 
            then (bottomfloat x)
            else if y > largest x
            then (topfloat x)
            else (closest (valof x) (\<lambda>a. True) {a. (is_finite x a) \<and> abs(valof x a) \<le> abs y} y))"

| "round x To_pinfinity y =
           (if y < -(largest x)
            then (bottomfloat x)
            else if y > largest x
            then (plus_infinity x)
            else (closest (valof x) (\<lambda>a. True) {a. (is_finite x a) \<and> (valof x a) \<ge> y} y)) "

| "round x To_ninfinity y =
           (if y < -(largest x)
            then (minus_infinity x)
            else if y > largest x
            then (topfloat x)
            else (closest (valof x) (\<lambda>a. True) {a. (is_finite x a) \<and> (valof x a) \<le> y} y)) "

(*Rounding to integer values in floating point format*)
 
definition is_integral :: "format \<Rightarrow> representation \<Rightarrow> bool" where
"is_integral x a = ((is_finite x a) \<and> (\<exists> n::nat. abs(valof x a) = real n))"

fun intround :: "format \<Rightarrow> roundmode \<Rightarrow> real \<Rightarrow> representation" where
 "intround x To_nearest y = 
          (if y \<le> -(threshold x) 
           then (minus_infinity x)
           else if y \<ge> threshold x 
           then (plus_infinity x)
           else (closest (valof x) 
                         (\<lambda>a. (\<exists>n::nat. even n \<and> abs(valof x a) = real n)) 
                         {a. is_integral x a} 
                         y))"

|"intround x float_To_zero y = 
          (if y < -(largest x)
           then (bottomfloat x)
           else if y > largest x
           then (topfloat x)
           else (closest (valof x) 
                         (\<lambda>x. True) 
                         {a. is_integral x a \<and> abs(valof x a) \<le> abs y}
                         y))"

|"intround x To_pinfinity y = 
          (if y < -(largest x)
           then (bottomfloat x)
           else if y > largest x
           then (plus_infinity x)
           else (closest (valof x) 
                         (\<lambda>x. True) 
                         {a. is_integral x a \<and> valof x a \<ge>  y}
                         y))"

|"intround x To_ninfinity y = 
          (if y < -(largest x)
           then (minus_infinity x)
           else if y > largest x
           then (topfloat x)
           else (closest (valof x) 
                         (\<lambda>x. True) 
                         {a. is_integral x a \<and> valof x a \<ge> y}
                         y))"

(*non-standard of NaN*)
definition some_nan :: "format \<Rightarrow> representation" where
"some_nan x = (\<some>a. is_nan x a)"

(*Coercion for signs of zero results*)
definition zerosign :: "format \<Rightarrow> nat \<Rightarrow> representation \<Rightarrow> representation" where
"zerosign x s a = (if is_zero x a 
                   then (if s = 0 then plus_zero x else minus_zero x)
                   else a)" 

(*Reminder operation*)
definition rem :: "real \<Rightarrow> real \<Rightarrow> real" where
"rem x y = (let n = closest id (\<lambda>x. (\<exists>n ::nat. even n \<and> (abs x = real n))) 
                            {x. \<exists>n :: nat. abs x = real n} (x/y) in x - n * y)"

definition frem :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation" where
"frem x m a b = (if is_nan x a \<or> is_nan x b \<or> is_infinity x a \<or> is_zero x b
                 then some_nan x
                 else zerosign x (sign a) (round x m (rem (valof x a) (valof x b))))"

subsection{*Definitions of the arithmetic operations*}

definition fintrnd :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation" where
"fintrnd x m a = (if is_nan x a then (some_nan x)
                  else if is_infinity x a then a
                  else zerosign x (sign a) (intround x m (valof x a)))"

definition fadd :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation" where
"fadd x m a b = (if (is_nan x a) \<or> (is_nan x b) \<or> 
                    (is_infinity x a \<and> is_infinity x b \<and> (sign a \<noteq> sign b))
                 then (some_nan x)
                 else if (is_infinity x a) then a
                 else if (is_infinity x b) then b
                 else  zerosign x (if (is_zero x a \<and> is_zero x b \<and> (sign a = sign b)) 
                                  then sign a 
                                  else if (m = To_ninfinity) then 1 else 0)
                              (round x m (valof x a + valof x b)))"

definition fsub :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation" where
"fsub x m a b = (if (is_nan x a) \<or> (is_nan x b) \<or> 
                    (is_infinity x a \<and> is_infinity x b \<and> (sign a = sign b))
                 then (some_nan x)
                 else if (is_infinity x a) then a
                 else if (is_infinity x b) then minus x b
                 else  zerosign x (if (is_zero x a \<and> is_zero x b \<and> \<not>(sign a = sign b)) 
                                  then sign a 
                                  else if (m = To_ninfinity) then 1 else 0)
                              (round x m (valof x a - valof x b)))"

definition fmul :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation" where
"fmul x m a b = (if is_nan x a \<or> is_nan x b \<or> 
                    (is_zero x a \<and> is_infinity x b) \<or>
                    (is_infinity x a \<and> is_zero x b)
                 then some_nan x
                 else if is_infinity x a \<or> is_infinity x b
                 then (if sign a = sign b then plus_infinity x else minus_infinity x)
                 else zerosign x (if sign a = sign b 
                                  then 0 else 1 )
                              (round x m (valof x a * valof x b)))"

definition fdiv :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> representation" where
"fdiv x m a b = (if is_nan x a \<or> is_nan x b \<or> 
                    (is_zero x a \<and> is_zero x b) \<or> 
                    (is_infinity x a \<and> is_infinity x b)
                 then some_nan x
                 else if is_infinity x a \<or> is_zero x b
                 then (if sign a = sign b then plus_infinity x else minus_infinity x)
                 else if is_infinity x b
                 then (if sign a = sign b then plus_zero x else minus_zero x)
                 else zerosign x (if sign a = sign b then 0 else 1)
                               (round x m (valof x a / valof x b)))"

definition fsqrt :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation" where
"fsqrt x m a = (if is_nan x a then some_nan x
                else if is_zero x a \<or> is_infinity x a \<and> (sign a = 0) then a
                else if (sign a = 1) then some_nan x
                else zerosign x (sign a) (round x m (sqrt(valof x a))))"

(*Negation*)
definition fneg :: "format \<Rightarrow> roundmode \<Rightarrow> representation \<Rightarrow> representation" where
"fneg x m a = (1 - sign a, exponent a, fraction a )"

(*Comparison*)
datatype ccode = Gt | Lt | Eq | Und 

subsection{*Comparison operation *}
definition fcompare :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> ccode" where
"fcompare x a b = (if is_nan x a \<or> is_nan x b then Und
                   else if (is_infinity x a \<and> (sign a = 1)) 
                   then (if is_infinity x b \<and> (sign b = 1) then Eq else Lt)
                   else if (is_infinity x a \<and> (sign a = 0))
                   then  (if is_infinity x b \<and> (sign b = 0) then Eq else Gt )
                   else if (is_infinity x b \<and> (sign b = 1)) then Gt
                   else if (is_infinity x b \<and> (sign b = 0)) then Lt
                   else if (valof x a < valof x b) then Lt
                   else if (valof x a = valof x b) then Eq
                   else Gt)"

definition flt :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool" where
"flt x a b = (fcompare x a b = Lt)"

declare flt_def [simp]

definition fle :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool" where
"fle x a b = ((fcompare x a b = Lt) \<or> (fcompare x a b = Eq))"

declare fle_def [simp]

definition fgt :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool" where
"fgt x a b = (fcompare x a b = Gt)"

declare fgt_def [simp]

definition fge :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool" where
"fge x a b = ((fcompare x a b = Gt) \<or> (fcompare x a b = Eq))"

declare fge_def [simp]

definition feq :: "format \<Rightarrow> representation \<Rightarrow> representation \<Rightarrow> bool" where
"feq x a b = (fcompare x a b = Eq)"

declare feq_def [simp]


section{*Specify float to be double  precision and round to even*}                                   

(*>*)
definition float_format :: "format" where
"float_format = (11, 52)"

(*Define the float type*)
typedef float = "{a. is_valid float_format a}"
by (rule_tac x = "(0::nat, 0, 0)" in exI) (simp add: is_valid_def) 
(*<*)

definition Val :: "float \<Rightarrow> real" where
"Val a = valof (float_format) (Rep_float a)"

definition Float :: "real \<Rightarrow> float" where
"Float x = Abs_float (round float_format To_nearest x)"

definition Sign :: "float \<Rightarrow> nat" where
"Sign a = sign (Rep_float a)"

definition Exponent :: "float \<Rightarrow> nat" where
"Exponent a = exponent (Rep_float a)"

definition Fraction :: "float \<Rightarrow> nat" where
"Fraction a = fraction (Rep_float a)"

definition Ulp :: "float \<Rightarrow> real" where
"Ulp a = ulp float_format (Rep_float a)"

(*Lifting of the discriminator functions*)
definition Isnan :: "float \<Rightarrow> bool" where
"Isnan a = is_nan float_format (Rep_float a)"

definition Infinity :: "float \<Rightarrow> bool" where
"Infinity a = is_infinity float_format (Rep_float a)"

definition Isnormal :: "float \<Rightarrow> bool" where
"Isnormal a = is_normal float_format (Rep_float a)"

definition Isdenormal :: "float \<Rightarrow> bool" where
"Isdenormal a = is_denormal float_format (Rep_float a)"

definition Iszero :: "float \<Rightarrow> bool" where
"Iszero a = is_zero float_format (Rep_float a)"

definition Finite :: "float \<Rightarrow> bool" where
"Finite a = (Isnormal a \<or> Isdenormal a \<or> Iszero a)"

definition Isintegral :: "float \<Rightarrow> bool" where
"Isintegral a = is_integral float_format (Rep_float a)"

(*Basic operations on floats*)
definition Topfloat :: "float" where
"Topfloat = Abs_float (topfloat float_format)"

definition Bottomfloat :: "float" where
"Bottomfloat = Abs_float (bottomfloat float_format)"

definition Plus_zero :: "float" where
"Plus_zero = Abs_float (plus_zero float_format)"

definition Minus_zero :: "float" where
"Minus_zero = Abs_float (minus_zero float_format)"

definition Minus_infinity :: "float" where
"Minus_infinity = Abs_float (minus_infinity float_format)"

definition Plus_infinity :: "float" where
"Plus_infinity = Abs_float (plus_infinity float_format)"

(*>*)
instantiation float :: plus begin

definition plus_float :: "float \<Rightarrow> float \<Rightarrow> float" where
"a + b = Abs_float (fadd float_format To_nearest (Rep_float a) (Rep_float b))"

instance ..
end
(*<*)
instantiation float :: minus begin

definition minus_float :: "float \<Rightarrow> float \<Rightarrow> float" where
"a - b = Abs_float (fsub float_format To_nearest (Rep_float a) (Rep_float b))"

instance ..
end

instantiation float :: times begin

definition times_float :: "float \<Rightarrow> float \<Rightarrow> float" where
"a * b = Abs_float (fmul float_format To_nearest (Rep_float a) (Rep_float b))"

instance ..
end

instantiation float :: inverse begin

definition divide_float :: "float \<Rightarrow> float \<Rightarrow> float" where
"a div b = Abs_float (fdiv float_format To_nearest (Rep_float a) (Rep_float b))"

definition inverse_float :: "float \<Rightarrow> float" where
"inverse_float a = Float ((1::real) / Val a)"

instance ..
end

definition float_rem :: "float \<Rightarrow> float \<Rightarrow> float" where
"float_rem a b = Abs_float (frem float_format To_nearest (Rep_float a) (Rep_float b))"

definition float_sqrt :: "float \<Rightarrow> float" where
"float_sqrt a = Abs_float (fsqrt float_format To_nearest (Rep_float a))"

definition ROUNDFLOAT :: "float \<Rightarrow> float" where
"ROUNDFLOAT a = Abs_float (fintrnd float_format To_nearest (Rep_float a))"


instantiation float :: ord begin

definition less_float :: "float \<Rightarrow> float \<Rightarrow> bool"  where
"a < b \<equiv> flt float_format (Rep_float a) (Rep_float b)"

definition less_eq_float :: "float \<Rightarrow> float \<Rightarrow> bool" where
"a \<le> b = fle float_format (Rep_float a) (Rep_float b)"


instance ..
end


definition float_gt :: "float \<Rightarrow> float \<Rightarrow> bool" where
"float_gt a b = fgt float_format (Rep_float a) (Rep_float b)"

definition float_ge :: "float \<Rightarrow> float \<Rightarrow> bool" where
"float_ge a b = fge float_format (Rep_float a) (Rep_float b)"

definition float_eq :: "float \<Rightarrow> float \<Rightarrow> bool"  (infixl "\<doteq>" 70 ) where
"float_eq a b = feq float_format (Rep_float a) (Rep_float b)"

definition float_neg :: "float \<Rightarrow> float" where
"float_neg a = Abs_float (fneg float_format To_nearest (Rep_float a))"

definition float_abs :: "float \<Rightarrow> float" where
"float_abs a = (if sign (Rep_float a) = 0 then a else float_neg a)"

(***************"1 + Epsilon" property**************)
definition normalizes :: "real \<Rightarrow> bool" where
"normalizes x = (1/ (2::real)^(bias float_format - 1) \<le> \<bar>x\<bar> \<and> \<bar>x\<bar> < threshold float_format)"

lemmas float_defs = Finite_def Infinity_def Iszero_def Isnan_def Val_def Sign_def
                    Isnormal_def Isdenormal_def Fraction_def Exponent_def float_format_def
                    Plus_zero_def Minus_zero_def
lemma float_cases_finite: "Isnan a \<or> Infinity a \<or> Finite a"
by (cases a) (auto simp: Abs_float_inverse emax_def is_nan_def float_defs
                is_infinity_def is_normal_def is_denormal_def is_zero_def is_valid_def)
(*>*)
section\<open>Additional stuff (not printed)\<close>
(*>*)
(*<*)
(*The types of floating-point numbers are mutually distinct*)
lemma float_distinct: "\<not>(Isnan a \<and> Infinity a)"
                      "\<not>(Isnan a \<and> Isnormal a)"
                      "\<not>(Isnan a \<and> Isdenormal a)"
                      "\<not>(Isnan a \<and> Iszero a)"
                      "\<not>(Infinity a \<and> Isnormal a)"
                      "\<not>(Infinity a \<and> Isdenormal a)"
                      "\<not>(Infinity a \<and> Iszero a)"
                      "\<not>(Isnormal a \<and> Isdenormal a)"
                      "\<not>(Isdenormal a \<and> Iszero a)"
by (auto simp: emax_def float_defs is_nan_def is_infinity_def is_normal_def is_denormal_def is_zero_def)


code_printing constant "float_eq :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.== ((_:real), (_))" and (OCaml) "Pervasives.(=)"
declare float_eq_def[code del]

code_printing constant "Orderings.less_eq :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.<= ((_), (_))" and (OCaml) "Pervasives.(<=)"
declare less_float_def [code del]

code_printing constant "op + :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.+ ((_), (_))" and (OCaml) "Pervasives.( +. )"
declare plus_float_def[code del]

code_printing constant "op * :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.* ((_), (_))" and (OCaml) "Pervasives.( *. )"
declare times_float_def [code del]

code_printing constant "op - :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.- ((_), (_))" and (OCaml) "Pervasives.( -. )"
declare minus_float_def [code del]

code_printing constant "float_neg :: float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.~" and (OCaml) "Pervasives.( ~-. )"
declare float_neg_def [code del]
(*>*)

section\<open>Notation\<close>
text \<open>In theory \<open>IEEE\<close>, the float operations use the \<open>+\<close> and \<open>-\<close> sign via


@{theory_text "instantiation float"}


For this thesis, we want the IEEE-operations to use a different symbol, and reserve the @{text "+"} operator for exact number formats. Fortunately, Isabelle provides spare symbols and the @{command abbreviation} command, which makes sure even the output uses the new notation. We thus state at the beginning of our @{command theory}:\<close>
--\<open>Use another notation for the possibly inexact IEEE-operations.\<close>
abbreviation round_affected_plus :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<oplus>" 65) where
  "round_affected_plus a b \<equiv> a + b"

abbreviation round_affected_minus :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<ominus>" 65) where
  "round_affected_minus a b \<equiv> a - b"

text\<open>Afterwards,\<close>
term "a + (b::float)"
text\<open>outputs\<close>
text\<open>\<open>"a \<oplus> b" :: "IEEE.float"\<close>\<close>

section\<open>Making operations error-free\<close>
text\<open>
The core idea is to provide an error-free form of the basic operations between IEEE floats. Since we want the output to be floats as well, and rounding occurs for almost all input values, the only way to do so is to use the round-affected IEEE operation and then computing the error, also represented as floats. For the basic operations, this will turn out to be exactly another float.\<close>

subsection\<open>Addition\<close>
text\<open>We compute \<open>a \<oplus> b\<close> together with \<open>y\<close> the error value. \<open>y\<close> will have the sign \<open>-\<close> or \<open>+\<close> corresponding to whether \<open>a \<oplus> b\<close> is above resp. below the exact mathematical result of \<open>a + b\<close>. It can be computed by the following sequence, first described by Ole Møller in 1965@{cite moller}:\<close>

definition TwoSum :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "TwoSum a b = (let
    x = a \<oplus> b;
    b\<^sub>v = x \<ominus> a;
    a\<^sub>v = x \<ominus> b\<^sub>v;
    b\<^sub>r = b \<ominus> b\<^sub>v;
    a\<^sub>r = a \<ominus> a\<^sub>v;
    y = a\<^sub>r \<oplus> b\<^sub>r
    in (x, y))"

text\<open>
Here, we compute a value \<open>y\<close> such that \<open>a + b = x + y\<close>, where \<open>x = a \<oplus> b\<close>. The following lemma states the latter:\<close>

lemma TwoSum_correct1: "TwoSum a b = (x, y) \<Longrightarrow> x = a \<oplus> b"
  --\<open>\<open>x\<close> is defined in the first line of @{const TwoSum} and not changed thereafter.\<close>
  by (auto simp: TwoSum_def Let_def)

text\<open>The other property needs the preconditions that both the input and the output represent real numbers (as opposed to the special values \<open>NaN\<close> and \<open>\<plusminus>\<infinity>\<close>). This is checked by the predicate @{const Finite}. We use the exact arithmetic of @{typ Real.real} and the conversion @{const Val}
@{text "::"} @{text "float => real"} from \<open>IEEE_Floating_Point/IEEE\<close>.\<close>

lemma TwoSum_correct2:
  fixes a b x y :: float
  assumes "Finite a"
  assumes "Finite b"
  assumes "Finite (a \<oplus> b)"
  assumes out: "(x, y) = TwoSum a b"
  shows "Val a + Val b = Val x + Val y"
  sorry

text\<open>We assume the lemma by @{command sorry} for this thesis. Notice that a formal proof using the theorem prover Coq@{cite coq} is available online@{cite coqTwoSum}\<close>

subsection\<open>Subtraction\<close>

text\<open>For \<open>a - b\<close>, we can compute:\<close>
definition TwoDiff :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "TwoDiff a b = TwoSum a (float_neg b)"

text\<open>To drop the additional negation step, we could instead perform:\<close>
(*<*)definition TwoDiff' where(*>*)
  "TwoDiff' a b = (let
    x = a \<ominus> b;
    b\<^sub>v = x \<ominus> a;
    a\<^sub>v = x \<oplus> b\<^sub>v;
    b\<^sub>r = b\<^sub>v \<ominus> b;
    a\<^sub>r = a \<ominus> a\<^sub>v;
    y = a\<^sub>r \<oplus> b\<^sub>r
    in (x, y))"

text\<open>according to Shewchuk@{cite "Shewchuk"}. Note that we still need a \<open>+\<close> on the right side of the equation:\<close>

lemma TwoDiff_correct2:
  fixes a b x y :: float
  assumes "Finite a"
  assumes "Finite b"
  assumes "Finite (a \<ominus> b)"
  assumes out: "(x, y) = TwoDiff a b"
  shows "Val a - Val b = Val x + Val y"
  sorry

text\<open>To not further increase the amount of unproven lemmas, we drop this optimization for this thesis.\<close>

section\<open>Code Analysis\<close>
text\<open>The new data format is designed to implement the idea of storing all the errors as an unevaluated sum. It is defined as follows:\<close>
--\<open>Define the "Multiple Precision Float"\<close>
type_synonym mpf = "float \<times> float list"
fun approx :: "mpf \<Rightarrow> float" where
  "approx (a, es) = a"
fun errors :: "mpf \<Rightarrow> float list" where
  "errors (a, es) = es"
text\<open>
where the tuple of a \<open>float\<close> and a \<open>float list\<close> should be seen together as a non-empty float list, ordered by decreasing magnitude. The approximation @{const approx} is just stored separately to avoid having to check for an empty list on access. Its quality depends on the executed algorithms (proofs about it can be found at @{cite "Shewchuk"}).

The mpf's represented value is the infinite precise sum of all its components:\<close>
fun Val_mpf :: "mpf \<Rightarrow> real" where
  "Val_mpf (a, es) = Val a + listsum (map Val es)"

(*
lemma "\<exists>a b. Val_mpf a = Val_mpf b \<and> a \<noteq> b"
  oops
text\<open>Since no facts about @{const Val} are provided for any float, we only be able to prove this once the code generation is set up.\<close> *)
text\<open>Note that multiple @{typ mpf}s can represent the same value. Many of these are invalid if we enforce the "non-overlapping" property proposed by Shewchuk@{cite Shewchuk} on the float list. However, since it needs to read out the bit representation of the IEEE float, there is no easy way to check this condition using the AFP-formalization. We could instead decrease the number of valid representations by not allowing zero components in the list's tail:\<close>

fun valid :: "mpf \<Rightarrow> bool" where
  "valid (a, es) = (case Iszero a of
    True \<Rightarrow> es = [] |
    False \<Rightarrow> Finite a \<and> list_all (\<lambda>f. Isdenormal f \<or> Isnormal f) es)"

text\<open>where @{term "\<lambda>f. Isdenormal f \<or> Isnormal f"} returns @{const False} for zero-floats:\<close>

lemma "Iszero fl \<Longrightarrow> \<not>(\<lambda>f. Isdenormal f \<or> Isnormal f) fl"
  using float_distinct
by (metis Isnormal_def Iszero_def is_normal_def is_zero_def order_less_irrefl)

text\<open>Since zero components don't contribute to the mpf's value, omitting them is an easy way to save storage by decreasing the list size. The problem with this property is that the algorithms don't preserve the constraint by default. As Shewchuk puts it:\<close>

text_raw\<open>\begin{center}\<close>
text\<open>"A complicating characteristic of all the algorithms for manipulating expansions is that there may be spurious zero components scattered throughout the output expansions, even if no zeros were present in the input expansions."\<close>
text_raw\<open>\end{center}\<close>

text\<open>As he shows by an example, they even occur in the middle of output lists that provably have all non-zero-components sorted. He also states:\<close>

text_raw\<open>\begin{center}\<close>
text\<open>"Unfortunately, accounting for these zero components could complicate the correctness proofs significantly."@{cite "Shewchuk"}\<close>
text_raw\<open>\end{center}\<close>

text\<open>In other words: We @{bold \<open>could\<close>} modify the algorithms to drop the zero component on-the-fly, but the extra branch would drastically increase the proof size. We instead settle for an even weaker property:\<close>

fun Finite_mpf :: "mpf \<Rightarrow> bool" where
  "Finite_mpf (a, es) \<longleftrightarrow> Finite a \<and> list_all Finite es"

text\<open>Using this property and the well-known \<open>TwoSum_correct2\<close> property described above (@{thm TwoSum_correct2}, unproven in this thesis), we will be able to prove computations error-free in the next section.

Here is a proof that valid implies Finite:\<close>

lemma valid_finite: "valid (a, es) \<Longrightarrow> Finite_mpf (a, es)"
  apply (simp split: bool.splits)
  using float_cases_finite float_distinct apply fastforce
  by (metis (no_types, lifting) Ball_set Finite_def)

(*
lemma TwoDiff_correct1: "TwoDiff a b = (x, y) \<Longrightarrow> x = a \<ominus> b"
  by (auto simp: TwoDiff_def Let_def)

*)
definition "safe_TwoSum a b =
  (let r = TwoSum a b in
    if Finite (fst r) \<and> Finite (snd r)
    then Some r
    else None)"

definition "safe_TwoDiff a b =
  (let r = TwoDiff a b in
    if Finite (fst r) \<and> Finite (snd r)
    then Some r
    else None)"


lemma safe_TwoSum_finite:
  assumes "safe_TwoSum a b = Some (s, e)"
  shows safe_TwoSum_finite1: "Finite s"
  and safe_TwoSum_finite2: "Finite e"
  using assms
  by (auto simp: safe_TwoSum_def Let_def split: split_if_asm)

lemma safe_TwoSum_correct1:
  "safe_TwoSum a b = Some (x, y) \<Longrightarrow> x = a \<oplus> b"
  by (auto simp: safe_TwoSum_def Let_def TwoSum_correct1 split: split_if_asm)
(*
lemma safe_TwoDiff_finite:
  assumes "safe_TwoDiff a b = Some (s, e)"
  shows safe_TwoDiff_finite1: "Finite s"
  and safe_TwoDiff_finite2: "Finite e"
  using assms
  by (auto simp: safe_TwoDiff_def Let_def split: split_if_asm)

lemma safe_TwoDiff_correct1:
  "safe_TwoDiff a b = Some (x, y) \<Longrightarrow> x = a \<ominus> b"
  by (auto simp: safe_TwoDiff_def Let_def TwoDiff_correct1 split: split_if_asm)
*)
lemma safe_TwoSum_correct2:
  fixes a b x y :: float
  assumes "Finite a" "Finite b" "Finite (a \<oplus> b)"
  assumes out: "safe_TwoSum a b = Some (x, y)"
  shows "Val a + Val b = Val x + Val y"
  using assms
by (auto intro!: TwoSum_correct2 simp: safe_TwoSum_def Let_def split: split_if_asm)
(*
lemma safe_TwoDiff_correct2:
  fixes a b x y :: float
  assumes "Finite a" "Finite b" "Finite (a \<ominus> b)"
  assumes out: "safe_TwoDiff a b = Some (x, y)"
  shows "Val a - Val b = Val x + Val y"
  using assms
by (auto intro!: TwoDiff_correct2 simp: safe_TwoDiff_def Let_def split: split_if_asm)
*)
definition "IsZero_mpf mpf \<longleftrightarrow> Iszero (approx mpf) \<and> errors mpf = []"

lemma float_distinct_10: "\<not> (Isnormal f \<and> Iszero f)"
  by (auto simp add: float_defs is_normal_def is_zero_def)

lemma valid_no_zero_components: "valid (a, es) \<Longrightarrow> list_all (\<lambda>f. \<not>Iszero f) es"
  apply (simp split: bool.splits)
  apply (induction es)
  using float_distinct(9) float_distinct_10
  apply auto
  done

lemma rec_val: "Val_mpf (a, e # es) = Val a + Val_mpf (e, es)"
  by simp
lemma rec_finite: "Finite_mpf (a, e # es) \<longleftrightarrow> Finite a \<and> Finite_mpf (e, es)"
  by simp

fun safe_grow_mpf_rec :: "mpf \<Rightarrow> float \<Rightarrow> mpf option" where
  "safe_grow_mpf_rec (a, []) f =
    do {
      (x, y) \<leftarrow> safe_TwoSum f a;
      Some (x, [y])
    }" |
  "safe_grow_mpf_rec (a, e # es) f =
    do {
      (a', es') \<leftarrow> safe_grow_mpf_rec (e, es) f;
      (x, y) \<leftarrow> safe_TwoSum a' a;
      Some (x, y # es')
    }"
text\<open>At this point, we could implement the zero removal explained before, by modifying the last lines of the blocks:\<close>

fun safe_grow_mpf_rec_no_0 :: "mpf \<Rightarrow> float \<Rightarrow> mpf option" where
  "safe_grow_mpf_rec_no_0 (a, []) f =
    do {
      (x, y) \<leftarrow> safe_TwoSum f a;
      if Iszero y then Some (x, []) else Some (x, [y])
    }" |
  "safe_grow_mpf_rec_no_0 (a, e # es) f =
    do {
      (a', es') \<leftarrow> safe_grow_mpf_rec_no_0 (e, es) f;
      (x, y) \<leftarrow> safe_TwoSum a' a;
      if Iszero y then Some (x, es') else Some (x, y # es')
    }"
text\<open>However, we don't pursue this idea further due to the problems mentioned there.\<close>

text\<open>We rename the induction cases:\<close>
lemmas safe_grow_mpf_induct = safe_grow_mpf_rec.induct[case_names no_error in_between]

lemma preserve_finite:
  assumes "safe_grow_mpf_rec mpf x = Some r"
  assumes "Finite x" "Finite_mpf mpf"
  shows "Finite_mpf r"
using assms
proof (induction mpf x arbitrary: r rule: safe_grow_mpf_induct)
--\<open>The base case is the case where the mpf is a single float with an empty error-list:\<close>
case (no_error a f)
--\<open>We apply the definition of @{const safe_grow_mpf_rec}:\<close>
from no_error.prems(1) have "do {(x, y) \<leftarrow> safe_TwoSum f a; Some (x, [y])} = Some r"
    unfolding safe_grow_mpf_rec.simps(1) .
--\<open>Since we required the result to be some value, we can give it a name:\<close>
  then obtain x y where xy: "safe_TwoSum f a = Some (x, y)" and r: "r = (x, [y])"
    by (auto simp: bind_eq_Some_conv)
--\<open>and then delegate to the corresponding property of @{const safe_TwoSum}:\<close>
  moreover from safe_TwoSum_finite[OF xy]
    have "Finite x" "Finite y".
  ultimately show ?case
    by simp
next
case (in_between a e es f r_full)
  note "in_between.prems"(1)[simplified, unfolded bind_eq_Some_conv, simplified]
  then obtain l r where goal1: "safe_grow_mpf_rec (e, es) f = Some (l, r)"
    and r1: "do {(x, y) \<leftarrow> safe_TwoSum l a; Some (x, y # r)} = Some r_full"
      by blast
  then obtain l2 r2 where l2: "safe_TwoSum l a = Some (l2, r2)" and
     r2: "(l2, r2 # r) = r_full"
     using r1[unfolded bind_eq_Some_conv, simplified] by auto
  from r2 have "?case = Finite_mpf (l2, r2 # r)" by simp
  moreover have "Finite l2"
    using safe_TwoSum_finite1[OF l2].
  moreover have "Finite r2"
    using safe_TwoSum_finite2[OF l2].
  moreover from "in_between.IH"[OF goal1 "in_between.prems"(2)] have "list_all Finite r"
    using "in_between.prems"(3) by auto
  ultimately
    show ?case
    by simp
qed

text\<open>Notice that the "assignments"(@{text \<leftarrow>}) in a Monad like @{typ "mpf option"} can also be written using the @{text \<bind>}-operator (@{text bind}) and @{text \<lambda>}-notation. This is also what Isabelle's state panel will output, e.g.\<close>
text\<open>@{text "do {(x, y) \<leftarrow> safe_TwoSum l a; Some (x, y # r)}"}\<close>
text\<open>becomes\<close>
text\<open>@{term "do {(x, y) \<leftarrow> safe_TwoSum l a; Some (x, y # r)}"}\<close>
text \<open>etc. We perform the next proof using this style:\<close>

lemma preserve_val:
  assumes "safe_grow_mpf_rec mpf x = Some r"
  assumes "Finite x" "Finite_mpf mpf"
  shows "Val_mpf r = Val_mpf mpf + Val x"
using assms
proof (induction mpf x arbitrary: r rule: safe_grow_mpf_induct)
case (no_error a f)
  from no_error.prems(1) have "safe_TwoSum f a \<bind> (\<lambda>(x, y). Some (x, [y])) = Some r"
    unfolding safe_grow_mpf_rec.simps(1) .
  then obtain x y where xy: "safe_TwoSum f a = Some (x, y)" and r: "r = (x, [y])"
    by (auto simp: bind_eq_Some_conv)
  from safe_TwoSum_finite1[OF xy]
  have "Finite x".
  from no_error have an: "Finite a" by simp
  show ?case
    using safe_TwoSum_correct2[OF \<open>Finite f\<close> an _ xy] \<open>Finite x\<close>
      safe_TwoSum_correct1[OF xy]
    by (auto simp: r split: prod.split)
next
case (in_between a e es f r_full)
  note "in_between.prems"(1)[simplified, unfolded bind_eq_Some_conv, simplified]
  then obtain l r where goal1: "safe_grow_mpf_rec (e, es) f = Some (l, r)"
    and r1: "safe_TwoSum l a \<bind> (\<lambda>(x, y). Some (x, y # r)) = Some r_full"
      by blast
  then obtain l2 r2 where l2: "safe_TwoSum l a = Some (l2, r2)" and
     r2: "(l2, r2 # r) = r_full"
     using r1[unfolded bind_eq_Some_conv, simplified] by auto
  then have "Val_mpf r_full = Val_mpf (l2, r2 # r)" by simp
  also have "\<dots> = Val l2 + Val_mpf (r2, r)"
    by (simp add: rec_val)
  also have "\<dots> = Val l2 + Val r2 + listsum(map Val r)"
    by simp
  also have "\<dots> = Val l + Val a + listsum(map Val r)"
    proof -
      from "in_between.prems" have "Finite l"
        using goal1 preserve_finite by auto
      moreover have "Finite a"
        using "in_between.prems"(3) by simp
      moreover have "Finite (l + a)"
        using l2 safe_TwoSum_correct1 safe_TwoSum_finite1 by auto
      moreover have "Val l + Val a = Val l2 + Val r2"
        using safe_TwoSum_correct2[OF calculation l2].
      ultimately show ?thesis
        by simp
    qed
  finally show ?case
    using in_between goal1 rec_finite by auto
qed

text\<open>Note that the proof tactics for @{text preserve_finite} and @{text preserve_val} are very similar (identical up to the @{command obtain} commands in both induction cases). They could be combined by stating\<close>
(*<*)lemma(*>*)
  shows preserve_finite: "Finite_mpf r"
  and preserve_val: "Val_mpf r = Val_mpf mpf + Val x"
(*<*)oops(*>*)
text\<open>in a single lemma with the same assumptions. However, to actually remove redundancy in the proofs, both goals would have to be combined again via\<close>
text\<open>@{theory_text \<open>
  unfolding atomize_conj
\<close>}\<close>
text \<open>Since the second result depends partly on the first one, many fact names (or alternatively: large HOL predicates combining unrelated facts) would accumulate during the proof. To maintain readability, we stick to the two-proof-solution. Instead of stating both goals in one lemma, we collect the results afterwards:\<close>

lemmas safe_grow_mpf_correct =
  preserve_finite
  preserve_val

subsection "Tail recursive version"

text \<open>We can also implement grow-mpf in a tail-recursive way. For simplicity, we drop the overflow-check via the @{type option} monad for now.\<close>

fun grow_mpf_it :: "float list \<Rightarrow> float \<Rightarrow> float list \<Rightarrow> mpf" where (*better name: add*)
  "grow_mpf_it [] f hs = (f, hs)" |
  "grow_mpf_it (e # es) f hs = (let
    (x, y) = TwoSum f e
    in grow_mpf_it es x (y # hs))"

text\<open>This transformation was comparably easy because grow-mpf only needs one linear pass as the graphic shows.\<close>

fun grow_mpf_tr :: "mpf \<Rightarrow> float \<Rightarrow> mpf" where
  "grow_mpf_tr (a, es) f = (let
    (a', es') = grow_mpf_it (rev es) f [];
    (x, y) = TwoSum a' a
    in (x, y # es'))"

text\<open>An interesting realisation is that the list recursion can instead be implemented using fold:\<close>

fun grow_mpf_step :: "float \<Rightarrow> mpf \<Rightarrow> mpf" where
  "grow_mpf_step f (a, es) = (let
    (x, y) = TwoSum a f
  in (x, y # es))"

fun grow_by_fold :: "mpf \<Rightarrow> float \<Rightarrow> mpf" where
  "grow_by_fold (a, es) f = foldr grow_mpf_step (a # es) (f, [])"

text \<open>We prepare an equivalence proof for @{const grow_mpf_tr} and @{const grow_by_fold} by providing some lemmas about @{const grow_mpf_tr} and @{const append}.\<close>

lemma grow_it_append_accumulator:
  "grow_mpf_it as f (hs @ hs') = (let
      (a, es) = grow_mpf_it as f hs
    in (a, es @ hs'))"
  apply (induction as arbitrary: f hs hs')
  apply simp_all
  apply (metis (no_types, lifting) Cons_eq_appendI case_prod_beta)
  done

lemma grow_it_append_expansion:
  "grow_mpf_it (as @ es) f hs = (let
    (a', es') = grow_mpf_it as f hs
  in grow_mpf_it es a' es')"
  apply (induction as arbitrary: f hs)
  by (simp_all add: prod.case_eq_if)

text\<open>Its effect on the wrapper @{const grow_mpf_tr} is\<close>

lemma grow_append_rev:
  "grow_mpf_tr (a, es @ es') f = (let
    (a'', es'') = grow_mpf_it (rev es') f [];
    (a', es') = grow_mpf_it (rev es) a'' es'';
    (x, y) = TwoSum a' a
    in (x, y # es'))"
     by (simp add: case_prod_beta grow_it_append_expansion)

text\<open>In case of an increase by a singleton, this can be simplified:\<close>

lemma grow_snoc_rev:
  "(grow_mpf_tr (a, es @ [h]) f) = (let
      (x, y) = TwoSum f h;
      (a', es') = grow_mpf_it (rev es) x [y];
      (x', y') = TwoSum a' a
    in (x', y' # es'))"
  unfolding grow_append_rev[of a es "[h]" f]
  apply simp
  by (simp add: split_def)

text \<open>The right part of the equation can also be written using @{const grow_mpf_tr}:\<close>

lemma gm_snoc1: "(grow_mpf_tr (a, es @ [h]) f) = (let
        (x, y) = TwoSum f h;
        (a', es') = grow_mpf_tr (a, es) x
       in (a', es' @ [y]))"
       by (induction es arbitrary: a) (simp_all add: case_prod_beta grow_it_append_expansion)

(* todo *)
text\<open>We expect compilers that optimize tail recursion to also optimize @{const foldr}. Thus, it is no longer necessary to make the functions tail recursive if they can be expressed by fold.\<close>

section\<open>Further Operations\<close>

text\<open>With\<close>

fun mpf_neg :: "mpf \<Rightarrow> mpf" where
  "mpf_neg (a, es) = (float_neg a, map float_neg es)"

text\<open>\<close>
(*<*)
text\<open>From CodeFloat\cite{IEEE_Floating_Point-AFP} we use the definition:\<close>
definition One :: float where
"One = Abs_float (0, bias float_format, 0)"
declare One_def[code del]

code_printing constant "One :: float" \<rightharpoonup>
  (SML) "1.0" and (OCaml) "1.0"

definition Plus_zero_mpf :: mpf where
  "Plus_zero_mpf = (Plus_zero, [])"

definition Minus_zero_mpf :: mpf where
  "Minus_zero_mpf = (Minus_zero, [])"

definition One_mpf :: mpf where
  "One_mpf = (One, [])"
(*>*)
(*<*)
(* Mapping natual numbers to floats *)
fun float_of :: "nat \<Rightarrow> float" where
  "float_of 0 = Plus_zero"
| "float_of (Suc n) = float_of n +  One "
lemma float_zero1: "Iszero Plus_zero"
  by (auto simp: float_defs Abs_float_inverse is_zero_def is_valid_def)
lemma float_zero2: "Iszero Minus_zero"
  by (auto simp: float_defs Abs_float_inverse is_zero_def is_valid_def)
(*>*)

lemma valid_zero_mpf:
  shows "valid Plus_zero_mpf"
  and "valid Minus_zero_mpf"
by (simp_all add: Plus_zero_mpf_def Minus_zero_mpf_def float_zero1 float_zero2)

text\<open>One way to inspect which computations will be performed is to define a test mpf with dummy values and then use Isabelle's simplifier to apply the methods simplifications to the desired point:\<close>
definition "a\<^sub>4 = undefined"
definition "a\<^sub>3 = undefined"
definition "a\<^sub>2 = undefined"
definition "a\<^sub>1 = undefined"
definition "a\<^sub>0 = undefined"
definition "test_mpf = (a\<^sub>4, [a\<^sub>3, a\<^sub>2, a\<^sub>1])"
definition "output = grow_by_fold test_mpf a\<^sub>0"

text\<open>To make the simplifier apply the definition, we need to state a lemma:\<close>
lemma "P output" unfolding output_def test_mpf_def grow_by_fold.simps
--\<open>We can now use various proof methods to get a neatly arranged output:\<close>
  apply (clarsimp split: prod.splits) oops

text\<open>where P is an undefined dummy predicate. At the last step, the output is as follows:\<close>
(*<*)term(*>*) "\<And>x1 x2 x1a x2a x1b x2b x1c x2c.
       TwoSum x1b a\<^sub>4 = (x1c, x2c) \<Longrightarrow>
       TwoSum x1a a\<^sub>3 = (x1b, x2b) \<Longrightarrow>
       TwoSum x1 a\<^sub>2 = (x1a, x2a) \<Longrightarrow>
       TwoSum a\<^sub>0 a\<^sub>1 = (x1, x2) \<Longrightarrow>
     P (x1c, [x2c, x2b, x2a, x2])"
text\<open>\<close>
text\<open>To demonstrate the @{const TwoSum} sequence carried out by grow-mpf, we use the following graphic:\<close>
text_raw\<open>
  \vspace{0mm}

  \begin{figure}[h!]
    \centering
    \includegraphics[width=13cm]{fabi}
    \caption[Bildunterschrift]{The float @{text \<open>f\<close>} is added to the mpf (@{text \<open>a\<close>}, @{text \<open>es\<close>}). TwoSum is represented by a box where the larger value, @{text \<open>x\<close>}, is output to the left side and the smaller one, @{text \<open>y\<close>}, to the bottom. On the top, the function call is passed on. The returned mpf (bottom) is built from right to left.}
  \end{figure}
\<close>

text\<open>@{theory_text \<open>value "approx output"\<close>} delivers\<close>
text\<open>@{text \<open>
"Plus_zero \<oplus> One \<oplus> undefined \<oplus> undefined \<oplus> undefined \<oplus> undefined \<oplus> undefined"
  :: "IEEE.float"\<close>}\<close>


chapter\<open>Code generation\<close>
section\<open>Use of SML floats\<close>

text\<open>To enable computation for hardware floats, @{theory_text "theory Code_Float"}\cite{IEEE_Floating_Point-AFP} provides the built-in operators of the target language:\<close>
code_printing constant "op / :: float \<Rightarrow> float \<Rightarrow> float" \<rightharpoonup>
  (SML) "Real.'/ ((_), (_))" and (OCaml) "Pervasives.( '/. )"
declare divide_float_def [code del]

text\<open>The other operations are defined analogously.

Even ML's comparisons can be used (ML's @{ML_type bool} is already defined as translation for HOL's @{typ bool} in the @{theory Main} theory @{theory HOL}):\<close>

code_printing constant "Orderings.less :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.< ((_), (_))" and (OCaml) "Pervasives.(<)"
declare less_eq_float_def[code del]

section\<open>Printing Floats\<close>
text\<open>If we decide that an unchecked code module is safe enough for us, we can use the format @{typ Float.float}\cite{float} from Isabelle's HOL-library.\<close>

text\<open>To enable the conversion from @{text IEEE.float} to @{typ Float.float} in the generated code, we first insert the possibility to produce them from integers:\<close>

definition "float_of_int i = Float (real_of_int i)"
context includes integer.lifting begin
lift_definition float_of_integer::"integer \<Rightarrow> float" is float_of_int .
end

lemma float_of_int[code]:
  "float_of_int i = float_of_integer (integer_of_int i)"
  by (simp add: float_of_integer_def)

code_printing
  constant "float_of_integer :: integer \<Rightarrow> float" \<rightharpoonup> (SML) "Real.fromInt"
declare [[code drop: float_of_integer]]

text\<open>Then, the conversion is possible:\<close>

--\<open>convert hardware floats to Float.float for an exact representation\<close>
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


text\<open>We can now define a test list:\<close>
definition list :: "float list" where
--\<open>Note that floats with magnitude @{text "< 1"} can only be defined via @{const divide}:\<close>
  "list = [
    float_of_int 43,
    float_of_int 34538,
    float_of_int 3 / float_of_int 44,
    float_of_int 0,
    float_of_int 0,
    float_of_int (-348976754389282980)]"

text\<open>To use the ML operators, we have to insert the transformation to a term and back:\<close>

instantiation float::term_of
begin
definition term_of::"float \<Rightarrow> term" where "term_of x = undefined"
instance ..
end

code_printing
code_module "FromManExp" \<rightharpoonup> (SML)
  \<open>fun frommanexp m e = Real.fromManExp {man = Real.fromLargeInt m, exp = e}\<close>
consts frommanexp::"integer \<Rightarrow> integer \<Rightarrow> float"
code_printing constant "frommanexp :: integer \<Rightarrow> integer \<Rightarrow> float" \<rightharpoonup>
  (SML) "frommanexp"

definition of_Float::"Float.float \<Rightarrow> float" where
  "of_Float x = frommanexp (integer_of_int (Float.mantissa x)) (integer_of_int (Float.exponent x))"

lemma [code]: "term_of_class.term_of (x::float) \<equiv>
  Code_Evaluation.App
    (Code_Evaluation.termify of_Float)
    (term_of_class.term_of (normfloat (toFloat x)))"
  by (rule term_of_anything)

text\<open>We can now print the list without an error:\<close>
value "list"
text\<open>produces\<close>
(*<*)term(*>*)"[of_Float 43, of_Float (Float.Float 17269 1),
  of_Float (Float.Float 1228254443828317 (- 54)),
  of_Float (Float.Float 0 0), of_Float (Float.Float 0 0),
  of_Float (Float.Float (- 5452761787332547) 6)]
  :: float list"
text\<open>which is an error-free representation.
\<close>

abbreviation toNF :: "float \<Rightarrow> Float.float" where
  "toNF \<equiv> normfloat o toFloat"
(*
value [code] "toNF (fold op+ (tl list) (hd list))"
value [code] "listsum (map toNF list)"
value [code] "map toNF (let
  mpf = (hd list, tl list);
  (a, es) = mpf_transform mpf in
  a # es)"
value [code] "map toNF (vecSum list)"
value [code] "let
  mpf = (hd list, tl list);
  (a, es) = mpf_transform mpf in
  map toNF (a # es)"
value [code] "map toNF (vecSum list)"
value [code] "let
  mpf = (hd list, tl list);
  (a, es) = mpf_transform mpf in
  map toNF (a # es @ vecSum list)"
*)

(*
text\<open>We can use the grow_mpf procedure to iteratively build an mpf with the exact listsum of a float list as value:\<close>

lemma "listsum (map Val x) = Val_mpf (build_mpf x)"
  oops

text\<open>With the "unsafe" version that does not check for overflow, this can again by done by fold:\<close>
fun build_by_fold :: "float list \<Rightarrow> mpf" where
  "build_by_fold fs = fold (\<lambda>x y. grow_by_fold y x) fs (Plus_zero,[])"
thm build_by_fold.simps [unfolded fold]
lemma "safe_build_mpf testlist = build_by_fold testlist"
  by eval

oops
value [code] "build_mpf [float_of 1]"

fun nbuild_mpf :: "float list \<Rightarrow> mpf option" where
  "nbuild_mpf [] = undefined" |
  "nbuild_mpf [f] = Some (f, [])" |
  "nbuild_mpf (f # fs) = do {
    a \<leftarrow> nbuild_mpf fs;
    ngrow_mpf_slow a f
  }"

fun it_mpf_transform :: "mpf \<Rightarrow> float list \<Rightarrow> mpf" where
  "it_mpf_transform (a, []) bs = (a, rev bs)" |
  "it_mpf_transform (a, (v#vs)) bs = (let (s, e) = twoSum (a, v)
    in it_mpf_transform (s, vs) (e # bs))"

fun mpf_transform :: "mpf \<Rightarrow> mpf" where
  "mpf_transform x = it_mpf_transform x []"

(* ToDos *)
(*
fun mpf_eq :: "mpf \<Rightarrow> mpf \<Rightarrow> bool" where
  "mpf_eq a b \<longleftrightarrow> (let diff = mpf_add a (mpf_neg b)
    in IsZero_mpf diff)"

lemma "Val_mpf (build_mpf fs) = listsum (map Val fs)"
*)
definition "list = l1"

ML \<open>val test_ml = @{code ngrow_mpf_slow}\<close>

--\<open>Beware of the inexact representation\<close>
ML \<open>val timing_test_ml = @{code timing_test}\<close>
ML \<open>val grow_mpf_ml = @{code ngrow_mpf_slow}\<close>
ML \<open>val test =  flat (replicate 100 [12.324245, 234.234, 12.234, 2345.0345])\<close>
ML \<open>grow_mpf_ml (4.34,test) 5664.34\<close>
ML \<open>timing_test_ml ()\<close>

*)

chapter\<open>Results and conclusion\<close>
text\<open>The IEEE 754 floats were already modelled in Isabelle. Using this formalization, this work provides an easy way to use them for fast and error-free addition and subtraction. For these operations, we translated algorithms from the literature and adapted them for our purposes.\<close>

section\<open>Impact\<close>
text\<open>
We give a more practice-oriented analysis of Shewchuk's algorithms and offer explanations for challenges that can arise when implementing them. We also give ideas and solutions for verifying them in a functional setting.
Based on the existing formalization of IEEE-floats, we then specified a data format to provide an easy access to these algorithms. This means that users have a new option for a number format to perform verified computations using fast and error-free addition and subtraction. As results of our thorough testing of generated code, an error in polyML's float handling has been detected and removed. This means the code generated using the AFP-theory @{text \<open>IEEE_Floating_Point/Code_Float\<close>} has now a clearer semantics.\<close>

section\<open>Future Work\<close>
text\<open>A correctness proof for the @{const TwoSum} method needs to be converted to Isabelle's IEEE754 formalization. This will then also enable proofs for Shewchuk's "nonoverlapping" property, which, when implemented, allows more assertions about float expansions to be formally verified, e.g. about the maximum length of a valid @{typ mpf}, or the quality of the approximation stored in the first component.
Another improvement could be made by adapting code generation for IEEE-floats to support more of Isabelle's target languages. This will make our arithmetic library more flexible for use in languages than SML. However, the correct behaviour of floats in the language should be ensured beforehand, to avoid getting wrong results when using the generated code.\<close>

(*<*)
end
(*>*)