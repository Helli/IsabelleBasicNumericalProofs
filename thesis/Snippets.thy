(*<*)
theory Snippets
imports
  "../test_utils"
  "../MPF"
begin
(*>*)

section \<open>Test snippets\<close>

text \<open>float def\<close>
text_raw{*\snip{floatdef}{1}{2}{%*}
text \<open>definition @{thm float_def}\<close>
definition "float' = {real_of_int m * 2 powr real_of_int e |m e. True}"
text_raw{*}%endsnip*}

text \<open>float type\<close>
text_raw{*\snip{floattype}{1}{2}{%*}
text \<open>@{type float}\<close>
text_raw{*}%endsnip*}

text \<open>float typeof\<close>
text_raw{*\snip{floattypeof}{1}{2}{%*}
text \<open>@{typeof float}\<close>
text_raw{*}%endsnip*}

text \<open>float typ\<close>
text_raw{*\snip{floattyp}{1}{2}{%*}
text \<open>@{typ float}\<close>
text_raw{*}%endsnip*}

text\<open>MLreal\<close>
text_raw{*\snip{MLreal}{1}{2}{%*}
text\<open>@{ML_type real}\<close>
text_raw{*}%endsnip*}

text\<open>prf\<close>
text_raw{*\snip{prf}{1}{2}{%*}
text\<open>@{prf }\<close>
text_raw{*}%endsnip*}

text\<open>prft\<close>
text_raw{*\snip{prft}{1}{2}{%*}
text\<open>@{prf preserve_val}\<close>
text_raw{*}%endsnip*}
(*
These are broken:

text \<open>plus zero\<close>
text_raw{*\snip{pluszero}{1}{2}{%*}
text \<open>@{const Plus_zero}}\<close>
text_raw{*}%endsnip*}

text\<open>lal\<close>
text_raw{*\snip{lal}{1}{2}{%*}
text\<open>list_all2_lengthD: @{thm list_all2_lengthD[no_vars]}\<close>
text_raw{*}%endsnip*}
*)


(*<*)
end
(*>*)
