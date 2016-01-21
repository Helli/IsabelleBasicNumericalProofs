theory MPF
imports
  VecSum_tests
  "$AFP/IEEE_Floating_Point/FloatProperty"
begin

type_synonym mpf = "float \<times> float list"

(*
context
  assumes normal: "Isnormal a"
begin
*)

fun approx :: "mpf \<Rightarrow> float" where
  "approx (a, es) = a"

fun errors :: "mpf \<Rightarrow> float list" where
  "errors (a, es) = es"

context
  fixes a b :: float
  assumes ge: "float_abs a \<ge> float_abs b"
begin

  definition FastTwoSum :: "float \<times> float" where
    "FastTwoSum = (let
      x = a + b;
      b\<^sub>v = x - a;
      y = b - b\<^sub>v
      in (x, y))"

  lemma FastTwoSum_correct:
    assumes out: "(x, y) = FastTwoSum"
    shows FastTwoSum_correct1: "x = a + b"
    and FastTwoSum_correct2: "Val a + Val b = Val x + Val y"
    apply (metis FastTwoSum_def fst_conv out)
    sorry

end
thm FastTwoSum_def FastTwoSum_correct

definition TwoSum :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "TwoSum a b = (let
    x = a + b;
    b\<^sub>v = x - a;
    a\<^sub>v = x - b\<^sub>v;
    b\<^sub>r = b - b\<^sub>v;
    a\<^sub>r = a - a\<^sub>v;
    y = a\<^sub>r + b\<^sub>r
    in (x, y))"

lemma TwoSum_correct:
  fixes a b x y :: float
  assumes out: "(x, y) = TwoSum a b"
  shows TwoSum_correct1: "x = a + b"
  and TwoSum_correct2: "Val a + Val b = Val x + Val y"
  apply (metis TwoSum_def fst_conv out)
  sorry

lemma swap: "TwoSum a b = TwoSum b a"
  sorry

subsection \<open>MPF operations\<close>

--\<open>The following operations are correct when their operands are nonoverlapping.
  in this case, the result is nonoverlapping, too.\<close>

fun mpf_neg :: "mpf \<Rightarrow> mpf" where
  "mpf_neg (a, es) = (float_neg a, map float_neg es)"

fun grow_mpf_slow :: "mpf \<Rightarrow> float \<Rightarrow> mpf" where
  "grow_mpf_slow (a, []) f = (let (x, y) = TwoSum f a in (x, [y]))" |
  "grow_mpf_slow (a, e # es) f = (let
    (a', es') = grow_mpf_slow (e, es) f;
    (x, y) = TwoSum a' a
    in (x, y # es'))"

(* alternative version *)
fun gm_step :: "float \<Rightarrow> mpf \<Rightarrow> mpf" where
  "gm_step f (a, es) = (let
    (x, y) = TwoSum a f
  in (x, y # es))"

fun gm_by_fold :: "mpf \<Rightarrow> float \<Rightarrow> mpf" where
  "gm_by_fold (a, es) f = fold gm_step (a # es) (f, [])"

fun grow_mpf_it :: "float list \<Rightarrow> float \<Rightarrow> float list \<Rightarrow> mpf" where (*better name: add*)
  "grow_mpf_it [] f hs = (f, hs)" |
  "grow_mpf_it (e # es) f hs = (let
    (x, y) = TwoSum f e
    in grow_mpf_it es x (y # hs))"
(* store f in one of the lists?*)

lemma it:
  "grow_mpf_it as f (hs @ hs') = (let (a, es) = grow_mpf_it as f hs in (a, es @ hs'))"
  apply (induction as arbitrary: f hs hs')
  apply simp_all
    by (metis (no_types, lifting) Cons_eq_appendI case_prod_beta)

lemma it2:
  "grow_mpf_it (as @ es) f hs = (let
    (a', es') = grow_mpf_it as f hs
    in grow_mpf_it es a' es')"
  apply (induction as arbitrary: f hs)
  by (simp_all add: prod.case_eq_if)

fun grow_mpf :: "mpf \<Rightarrow> float \<Rightarrow> mpf" where
  "grow_mpf (a, es) f = (let
    (a', es') = grow_mpf_it (rev es) f [];
    (x, y) = TwoSum a' a
    in (x, y # es'))"

lemma g2:
  "grow_mpf (a, es @ es') f = (let
    (a'', es'') = grow_mpf_it (rev es') f [];
    (a', es') = grow_mpf_it (rev es) a'' es'';
    (x, y) = TwoSum a' a
    in (x, y # es'))"
     by (simp add: case_prod_beta it2)


lemma gm_eq_gm_it: "(grow_mpf (a, es @ [h]) f) = (let
        (x, y) = TwoSum f h;
        (a', es') = grow_mpf_it (rev es) x [y];
        (x', y') = TwoSum a' a
       in (x', y' # es'))"
       by (smt append_Nil2 grow_mpf.simps grow_mpf_it.simps(2) it2 rev.simps(1) rev_append rev_singleton_conv split_conv split_def)

lemma start: "grow_mpf (a, []) f = (let (x, y) = TwoSum a f in (x, [y]))"
  by (simp add: swap)

lemma gm_snoc1: "(grow_mpf (a, es @ [h]) f) = (let
        (x, y) = TwoSum f h;
        (a', es') = grow_mpf (a, es) x
       in (a', es' @ [y]))"
       by (induction es arbitrary: a) (simp_all add: case_prod_beta it2)

lemma gm_insert:
  "grow_mpf (a, es @ (h # hs)) f = (let
    (a', es') = grow_mpf (h, hs) f;
    (a'', es'') = grow_mpf (a, es) a'
    in (a'', es'' @ es'))"
  apply (induction hs arbitrary: a h f es)
  apply (metis (no_types, lifting) case_prod_beta grow_mpf.simps grow_mpf_it.simps(1) gm_snoc1 rev.simps(1) split_conv)
  unfolding g2
  apply (simp add: prod.case_eq_if it)
  unfolding it
  oops

lemma it:
  "(case grow_mpf_it (rev es @ [e]) f hs of
     (a', es') \<Rightarrow> case TwoSum a' a of (x, y) \<Rightarrow> (x, y # es')) =
    (case case grow_mpf_it (rev es) f hs of (a', es') \<Rightarrow> case TwoSum a' e of (x, y) \<Rightarrow> (x, y # es') of
     (a', es') \<Rightarrow> case TwoSum a' a of (x, y) \<Rightarrow> (x, y # es'))"
  apply (induction hs arbitrary: a e f es)
  apply (simp add: prod.case_eq_if)
  oops

lemma
  "grow_mpf (a, e # es') f = (let
    (a', es') = grow_mpf (e, es') f;
    (x, y) = TwoSum a' a
    in (x, y # es'))"
  apply simp
  apply (induction es' arbitrary: a e f)
  apply simp
  apply (simp add: prod.case_eq_if)
  oops

lemma "let (a', es') = grow_mpf_slow (a, es) f in (a', es' @ hs) = (let
    (a', es') = grow_mpf_it (rev es) f hs;
    (x, y) = TwoSum a' a
    in (x, y # es'))"
  apply (induction es arbitrary: a f hs)
  apply simp_all
  apply (simp add: prod.case_eq_if)
  apply (simp add: prod.case_eq_if)
  oops

subsection \<open>Testing\<close>

definition "sehrgross = undefined"
definition "gross = undefined"
definition "mittel = undefined"
definition "klein = undefined"
definition "sehrklein = undefined"
definition "test_mpf = (sehrgross, [gross, mittel, klein, sehrklein])"

(* generate unfolded view in "output" *)
definition "output = grow_mpf_slow test_mpf (float_of 1)"
lemma "P output" unfolding output_def test_mpf_def grow_mpf_slow.simps
  apply (clarsimp split: prod.splits) oops

definition "output' = grow_mpf test_mpf (float_of 1)"
lemma "P output'" unfolding output'_def test_mpf_def grow_mpf.simps grow_mpf_it.simps
  apply (clarsimp split: prod.splits) oops

value "approx output"

fun build_mpf :: "float list \<Rightarrow> mpf" where
  "build_mpf [] = undefined" |
  "build_mpf (f # fs) = foldl grow_mpf (f,[]) fs"

fun it_mpf_transform :: "mpf \<Rightarrow> float list \<Rightarrow> mpf" where
  "it_mpf_transform (a, []) bs = (a, rev bs)" |
  "it_mpf_transform (a, (v#vs)) bs = (let (s, e) = twoSum (a, v)
    in it_mpf_transform (s, vs) (e # bs))"

fun mpf_transform :: "mpf \<Rightarrow> mpf" where
  "mpf_transform x = it_mpf_transform x []"

(* ToDos *)
fun mpf_eq :: "mpf \<Rightarrow> mpf \<Rightarrow> bool" where
  "mpf_eq a b \<longleftrightarrow> (let diff = mpf_add a (mpf_neg b)
    in Iszero (approx diff) \<and> errors diff = Nil)"

lemma "Val (build_mpf fs) = listsum (map Val fs)"

definition "list = l1"

value "list"
value "fold op+ (tl list) (hd list)"
value "listsum (map toNF list)"
value "let
  mpf = (hd list, tl list);
  (a, es) = mpf_transform mpf in
  a # es"
value "vecSum list"
value "let
  mpf = (hd list, tl list);
  (a, es) = mpf_transform mpf in
  map toNF (a # es)"
value "map toNF (vecSum list)"
value "let
  mpf = (hd list, tl list);
  (a, es) = mpf_transform mpf in
  map toNF (a # es @ vecSum list)"

(*
end
*)

end