theory Ausgelagertes
imports
  MPF
begin

primrec foldl_opt :: "('b \<Rightarrow> 'a \<Rightarrow> 'b option) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b option" where
foldl_opt_Nil:  "foldl_opt f a [] = Some a" |
foldl_opt_Cons: "foldl_opt f a (x # xs) = do{
    b \<leftarrow> f a x;
    foldl_opt f b xs
  }"

fun nbuild_mpf :: "float list \<Rightarrow> mpf option" where
  "nbuild_mpf [] = None" |
  "nbuild_mpf (f # fs) = foldl_opt ngrow_mpf_slow (f, []) fs"
thm foldl_Nil foldl_opt_Nil
thm foldl_Cons foldl_opt_Cons

--\<open>ngrow_mpf can't be translated because there is no code equation for Isnormal\<close>
ML \<open>val nb_ml = @{code nbuild_mpf}\<close>
ML \<open>val test_list = [2323.032, 2.342342939E15]\<close>
ML \<open>nb_ml test_list\<close>

end