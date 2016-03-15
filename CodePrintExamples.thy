(*<*)
theory CodePrintExamples
imports test_utils
begin
(*>*)

section \<open>Einleitung hier\<close>

text \<open>
Hallo ich bin generierter Text.
\<close>

text_raw \<open>
\begin{itemize}
\item Punkt 1
\item \[ \int_0^t \pi \]
\item @{thm float_def}
\end{itemize}
\<close>

text \<open>Ich bin ein theorem: @{thm float_of_int_def}.\<close>

subsection \<open>Introduction\<close>

text \<open>
Sugar FTW
\<close>
(*<*)
end
(*>*)
