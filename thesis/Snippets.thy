(*<*)
theory Snippets
imports "../test_utils"
begin
(*>*)

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
