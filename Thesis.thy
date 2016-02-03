(*<*)
theory Thesis
imports test_utils
begin
(*>*)

section \<open>Introduction\<close>

text \<open>
The transformation of numerical methods to use machine arithmetic is known to be error-prone.
Therefore it is appropriate and important to exercise care to minimize errors.
Most of the numerical methods implemented in Isabelle had already been proven to be correct
beforehand in Mathematics. While most of these proofs work in a rather general setting, some
require additional assumptions or preconditions that are not necessarily given in the context
of real operational code, even if it uses the well-known IEEE standard of floating point
arithmetic. As a related problem, this standard also introduces a lot of additional cases for
operation results with its special values. In consequence, one might consider working with
arbitrary precision formats that implement the entire number format using only the infinitely
precise integer operations.\<close>

(*<*)
end
(*>*)
