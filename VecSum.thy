theory VecSum
imports
  Float_twosum
begin

fun vecsum :: "float list \<Rightarrow> float list" where
  "vecsum [] = []"
| "vecsum [a] = [a]"
| "vecsum (a0 # a1 # as) = (let
    (s, e) = twosum (a0, a1) in
    (e # vecsum (s # as)))"

end