(*<*)
theory Snippets
imports
  "../test_utils"
  "../MPF"
begin
(*>*)

paragraph \<open>mpfdef\<close>
(*<*) typ mpf (*>*)
text_raw\<open>\snip{mpfdef}{1}{2}{%\<close>
type_synonym mpf = "float \<times> float list"
text_raw\<open>}%endsnip\<close>
(*<*) hide_type mpf (*>*)

paragraph \<open>typmpf\<close>
text_raw\<open>\snip{typmpf}{1}{2}{%\<close>
text \<open>@{typ mpf}\<close>
text_raw\<open>}%endsnip\<close>

paragraph \<open>approxdef\<close>
(*<*) thm approx.simps (*>*)
text_raw\<open>\snip{approxdef}{1}{2}{%\<close>
fun approx :: "mpf \<Rightarrow> float" where
  "approx (a, es) = a"
text_raw\<open>}%endsnip\<close>
(*<*) hide_const approx (*>*)

paragraph \<open>constapprox\<close>
text_raw\<open>\snip{constapprox}{1}{1}{%\<close>
txt \<open>@{const approx}\<close>
text_raw\<open>}%endsnip\<close>

paragraph \<open>IEEE\<close>
text_raw\<open>\snip{IEEE}{0}{0}{%\<close>
txt \<open>@{theory IEEE}\<close>
text_raw\<open>}%endsnip\<close>

paragraph \<open>HOLreal\<close>
text_raw\<open>\snip{HOLreal}{0}{0}{%\<close>
txt \<open>@{typ real}\<close>
text_raw\<open>}%endsnip\<close>

section \<open>Primary and secondary style\<close>
text \<open>This is the primary style. @{thm float_def}\<close>
txt  \<open>This is the secondary one. @{thm float_def}\<close>

section \<open>Test snippets\<close>

paragraph \<open>float def\<close>
text_raw\<open>\snip{floatdef}{1}{2}{%\<close>
text \<open>definition @{thm float_def}\<close>
definition "float' = {real_of_int m * 2 powr real_of_int e |m e. True}"
text_raw\<open>}%endsnip\<close>

paragraph \<open>float type\<close>
text_raw\<open>\snip{floattype}{1}{2}{%\<close>
text \<open>@{type float}\<close>
text_raw\<open>}%endsnip\<close>

paragraph \<open>float typeof\<close>
text_raw\<open>\snip{floattypeof}{1}{2}{%\<close>
text \<open>@{typeof float}\<close>
text_raw\<open>}%endsnip\<close>

paragraph \<open>float typ\<close>
text_raw\<open>\snip{floattyp}{1}{2}{%\<close>
text \<open>@{typ float}\<close>
text_raw\<open>}%endsnip\<close>

paragraph\<open>MLreal\<close>
text_raw\<open>\snip{MLreal}{1}{2}{%\<close>
text\<open>@{ML_type real}\<close>
text_raw\<open>}%endsnip\<close>

paragraph\<open>prf\<close>
text_raw\<open>\snip{prf}{1}{2}{%\<close>
text\<open>@{prf }\<close>
text_raw\<open>}%endsnip\<close>

paragraph\<open>prft\<close>
text_raw\<open>\snip{prft}{1}{2}{%\<close>
text\<open>@{prf preserve_val}\<close>
text_raw\<open>}%endsnip\<close>

paragraph \<open>TestSnippet\<close>
text_raw\<open>\snip{test}{1}{2}{%\<close>
definition "ym = Plus_zero"
text_raw\<open>}%endsnip\<close>

(*
These are broken:

text \<open>plus zero\<close>
text_raw\<open>\snip{pluszero}{1}{2}{%\<close>
text \<open>@{const Plus_zero}}\<close>
text_raw\<open>}%endsnip\<close>

text\<open>lal\<close>
text_raw\<open>\snip{lal}{1}{2}{%\<close>
text\<open>list_all2_lengthD: @{thm list_all2_lengthD[no_vars]}\<close>
text_raw\<open>}%endsnip\<close>
*)


(*<*)
end
(*>*)
