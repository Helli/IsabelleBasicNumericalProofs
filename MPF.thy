theory MPF
imports
  "$AFP/IEEE_Floating_Point/FloatProperty"
  "$AFP/IEEE_Floating_Point/Code_Float"
  "~~/src/HOL/Library/Monad_Syntax"
begin

type_synonym mpf = "float \<times> float list"

fun approx :: "mpf \<Rightarrow> float" where
  "approx (a, es) = a"

fun errors :: "mpf \<Rightarrow> float list" where
  "errors (a, es) = es"

lemma "approx = fst" and "errors = snd"
  by auto

--\<open>Use another notation for the possibly inexact IEEE-operations\<close>
abbreviation round_affected_plus :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<oplus>" 65) where
  "round_affected_plus a b \<equiv> a + b"

abbreviation round_affected_minus :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<ominus>" 65) where
  "round_affected_minus a b \<equiv> a - b"

abbreviation round_affected_times :: "float \<Rightarrow> float \<Rightarrow> float" (infixl "\<otimes>" 65) where
  "round_affected_times a b \<equiv> a * b"

context
  fixes a b :: float
  assumes ge: "float_abs a \<ge> float_abs b"
begin

  definition FastTwoSum :: "float \<times> float" where
    "FastTwoSum = (let
      x = a \<oplus> b;
      b\<^sub>v = x \<ominus> a;
      y = b \<ominus> b\<^sub>v
      in (x, y))"
    
  lemma FastTwoSum_correct1: "FastTwoSum = (x, y) \<Longrightarrow> x = a \<oplus> b"
    by (auto simp: FastTwoSum_def Let_def)
  
  lemma FastTwoSum_correct2:
    fixes x y :: float
    assumes "Finite a"
    assumes "Finite b"
    assumes "Finite (a \<oplus> b)"
    assumes out: "(x, y) = FastTwoSum"
    shows "Val a + Val b = Val x + Val y"
    sorry

end
thm FastTwoSum_def FastTwoSum_correct1 FastTwoSum_correct2

definition TwoSum :: "float \<Rightarrow> float \<Rightarrow> float \<times> float" where
  "TwoSum a b = (let
    x = a \<oplus> b;
    b\<^sub>v = x \<ominus> a;
    a\<^sub>v = x \<ominus> b\<^sub>v;
    b\<^sub>r = b \<ominus> b\<^sub>v;
    a\<^sub>r = a \<ominus> a\<^sub>v;
    y = a\<^sub>r \<oplus> b\<^sub>r
    in (x, y))"

lemma TwoSum_correct1: "TwoSum a b = (x, y) \<Longrightarrow> x = a \<oplus> b"
  by (auto simp: TwoSum_def Let_def)

lemma TwoSum_correct2:
  fixes a b x y :: float
  assumes "Finite a"
  assumes "Finite b"
  assumes "Finite (a \<oplus> b)"
  assumes out: "(x, y) = TwoSum a b"
  shows "Val a + Val b = Val x + Val y"
  sorry

lemma swap: "TwoSum a b = TwoSum b a"
  sorry


definition "nTwoSum a b =
  (let r = TwoSum a b in
    if Finite (fst r) \<and> Finite (snd r)
    then Some r
    else None)"

lemma nTwoSum_finite:
  assumes "nTwoSum a b = Some (s, e)"
  shows nTwoSum_finite1: "Finite s"
  and nTwoSum_finite2: "Finite e"
using assms
  by (auto simp: nTwoSum_def Let_def split: split_if_asm)

lemma nTwoSum_correct1:
  "nTwoSum a b = Some (x, y) \<Longrightarrow> x = a \<oplus> b"
  by (auto simp: nTwoSum_def Let_def TwoSum_correct1 split: split_if_asm)

lemma nTwoSum_correct2:
  fixes a b x y :: float
  assumes "Finite a"
  assumes "Finite b"
  assumes "Finite (a \<oplus> b)"
  assumes out: "nTwoSum a b = Some (x, y)"
  shows "Val a + Val b = Val x + Val y"
  using out
  by (auto intro!: TwoSum_correct2 assms simp: nTwoSum_def Let_def split: split_if_asm)

definition "IsZero_mpf mpf \<longleftrightarrow> Iszero (approx mpf) \<and> errors mpf = []"
definition "Val_mpf x = (let (a, es) = x in Val a + listsum (map Val es))"
definition "Finite_mpf mpf \<longleftrightarrow> Finite (fst mpf) \<and> list_all Finite (snd mpf)"

fun valid :: "mpf \<Rightarrow> bool" where
  "valid (a, es) = (case Iszero a of
    True \<Rightarrow> es = [] |
    False \<Rightarrow> Finite a \<and> list_all (\<lambda>f. Isdenormal f \<or> Isnormal f) es)"

lemma float_distinct_10: "\<not> (Isnormal f \<and> Iszero f)"
  by (auto simp add: float_defs is_normal_def is_zero_def)

lemma valid_no_zero_components: "valid (a, es) \<Longrightarrow> list_all (\<lambda>f. \<not>Iszero f) es"
  apply (simp split: bool.splits)
  apply (induction es)
  using float_distinct(9) float_distinct_10
  apply auto
  done

lemma valid_finite: "valid (a, es) \<Longrightarrow> Finite_mpf (a, es)"
  apply (simp split: bool.splits)
  using Finite_mpf_def float_cases_finite float_distinct apply fastforce
  by (metis (no_types, lifting) Ball_set Finite_def Finite_mpf_def fstI sndI)

--\<open>Recursive versions for induction proofs:\<close>
lemma rec_val: "Val_mpf (a, e # es) = Val a + Val_mpf (e, es)"
  unfolding Val_mpf_def Let_def by simp
lemma rec_finite: "Finite_mpf (a, e # es) \<longleftrightarrow> Finite a \<and> Finite_mpf (e, es)"
  unfolding Finite_mpf_def by simp

fun ngrow_mpf_slow :: "mpf \<Rightarrow> float \<Rightarrow> mpf option" where
  no_error: "ngrow_mpf_slow (a, []) f =
    do {
      (x, y) \<leftarrow> nTwoSum f a; (* \<leftarrow> = <. *)
      Some (x, [y])
    }" |
  in_between: "ngrow_mpf_slow (a, e # es) f =
    do {
      (a', es') \<leftarrow> ngrow_mpf_slow (e, es) f;
      (x, y) \<leftarrow> nTwoSum a' a;
      Some (x, y # es')
    }"


lemmas ngrow_mpf_slow_induct = ngrow_mpf_slow.induct[case_names no_error in_between]


lemma preserve_finite:
  assumes "ngrow_mpf_slow mpf x = Some r"
  assumes "Finite x" "Finite_mpf mpf"
  shows "Finite_mpf r"
using assms
proof (induction mpf x arbitrary: r rule: ngrow_mpf_slow_induct)
case (no_error a f)
  from no_error have an: "Finite a" by (simp add: Finite_mpf_def)
  from no_error have "nTwoSum f a \<bind> (\<lambda>(x, y). Some (x, [y])) = Some r"
    by simp
  then obtain x y where xy: "nTwoSum f a = Some (x, y)" and r: "r = (x, [y])"
    by (auto simp: bind_eq_Some_conv)
  moreover from nTwoSum_finite[OF xy]
    have "Finite x" "Finite y".
  ultimately show ?case
    by (simp add: Finite_mpf_def)
next
case (in_between a e es f r_full)
  note "in_between.prems"(1)[simplified, unfolded bind_eq_Some_conv, simplified]
  then obtain l r where goal1: "ngrow_mpf_slow (e, es) f = Some (l, r)"
    and r1: "nTwoSum l a \<bind> (\<lambda>(x, y). Some (x, y # r)) = Some r_full"
      by blast
  then obtain l2 r2 where l2: "nTwoSum l a = Some (l2, r2)" and
     r2: "(l2, r2 # r) = r_full"
     using r1[unfolded bind_eq_Some_conv, simplified] by auto
  from r2 have "?case = Finite_mpf (l2, r2 # r)" by simp
  moreover have "Finite l2"
    using nTwoSum_finite1[OF l2].
  moreover have "Finite r2"
    using nTwoSum_finite2[OF l2].
  moreover from "in_between.IH"[OF goal1 "in_between.prems"(2)] have "list_all Finite r"
    using "in_between.prems"(3) Finite_mpf_def by auto
  ultimately
    show ?case
    by (simp add: Finite_mpf_def)
qed

lemma preserve_val:
  assumes "ngrow_mpf_slow mpf x = Some r"
  assumes "Finite x" "Finite_mpf mpf"
  shows "Val_mpf r = Val_mpf mpf + Val x"
using assms
proof (induction mpf x arbitrary: r rule: ngrow_mpf_slow.induct)
case (1 a f r)
  from 1 have an: "Finite a" by (simp add: Finite_mpf_def)
  from 1 have "nTwoSum f a \<bind> (\<lambda>(x, y). Some (x, [y])) = Some r"
    by simp
  then obtain x y where xy: "nTwoSum f a = Some (x, y)" and r: "r = (x, [y])"
    by (auto simp: bind_eq_Some_conv)
  from nTwoSum_finite1[OF xy]
  have "Finite x".
  show ?case
    using nTwoSum_correct2[OF \<open>Finite f\<close> an _ xy] \<open>Finite x\<close>
      nTwoSum_correct1[OF xy]
    by (auto simp: Val_mpf_def r split: prod.split)
next
case (2 a e es f r_full)
  note "2.prems"(1)[simplified, unfolded bind_eq_Some_conv, simplified]
  then obtain l r where goal1: "ngrow_mpf_slow (e, es) f = Some (l, r)"
    and r1: "nTwoSum l a \<bind> (\<lambda>(x, y). Some (x, y # r)) = Some r_full"
      by blast
  then obtain l2 r2 where l2: "nTwoSum l a = Some (l2, r2)" and
     r2: "(l2, r2 # r) = r_full"
     using r1[unfolded bind_eq_Some_conv, simplified] by auto
  then have "Val_mpf r_full = Val_mpf (l2, r2 # r)" by simp
  also have "... = Val l2 + Val_mpf (r2, r)"
    by (simp add: rec_val)
  also have "... = Val l2 + Val r2 + listsum(map Val r)"
    by (simp add: Val_mpf_def)
  also have "... = Val l + Val a + listsum(map Val r)"
    proof -
      from "2.prems" have "Finite l"
        using Finite_mpf_def goal1 preserve_finite by auto
      moreover have "Finite a"
        using "2.prems"(3) Finite_mpf_def by simp
      moreover have "Finite (l + a)"
        using l2 nTwoSum_correct1 nTwoSum_finite1 by auto
      moreover have "Val l + Val a = Val l2 + Val r2"
        using nTwoSum_correct2[OF calculation l2].
      ultimately show ?thesis
        by simp
    qed
  finally show ?case
    using 2 Val_mpf_def goal1 rec_finite by auto
qed

lemmas ngrow_mpf_correct =
  preserve_finite
  preserve_val


subsection \<open>MPF operations\<close>

fun mpf_neg :: "mpf \<Rightarrow> mpf" where
  "mpf_neg (a, es) = (float_neg a, map float_neg es)"

(* alternative version *)
fun gm_step :: "float \<Rightarrow> mpf \<Rightarrow> mpf" where
  "gm_step f (a, es) = (let
    (x, y) = TwoSum a f
  in (x, y # es))"

fun gm_by_fold :: "mpf \<Rightarrow> float \<Rightarrow> mpf" where
  "gm_by_fold (a, es) f = foldr gm_step (a # es) (f, [])"

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

end