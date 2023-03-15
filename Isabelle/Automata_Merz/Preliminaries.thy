theory Preliminaries
imports Main "HOL-Library.Infinite_Set"
begin

section "Mathematical Preliminaries"

text \<open>
  We begin by proving some general-purpose lemmas that underly our
  developments, but that could also be useful in other contexts.

  The first subsection establishes various random results about
  existing theories of Isabelle/HOL. The second subsection
  introduces general concepts of $\omega$-words (i.e., infinite
  sequences), and $\omega$-dags are formalized in the third subsection.
\<close>

subsection \<open> General-purpose lemmas \<close>

text \<open>
  The standard library contains theorem @{text less_iff_Suc_add}

  @{thm less_iff_Suc_add [no_vars]}

  that can be used to reduce ``less than'' to addition and successor.
  The following lemma is the analogous result for ``less or equal''.
\<close>

lemma le_iff_add:
  "(m::nat) \<le> n = (\<exists> k. n = m+k)"
proof
  assume le: "m \<le> n"
  thus "\<exists> k. n = m+k"
  proof (auto simp add: order_le_less)
    assume "m<n"
    then obtain k where "n = Suc(m+k)"
      by (auto simp add: less_iff_Suc_add)
    thus ?thesis by auto
  qed
next
  assume "\<exists> k. n = m+k"
  thus "m \<le> n" by auto
qed

lemma exists_leI:
  assumes hyp: "(\<forall>n' < n. \<not> P n') \<Longrightarrow> P (n::nat)"
  shows "\<exists>n' \<le> n. P n'"
proof (rule classical)
  assume contra: "\<not> (\<exists>n'\<le>n. P n')"
  hence "\<forall>n' < n. \<not> P n'" by auto
  hence "P n" by (rule hyp)
  thus "\<exists>n'\<le>n. P n'" by auto
qed


text \<open>
  An ``induction'' law for modulus arithmetic: if $P$ holds for some
  $i<p$ and if $P(i)$ implies $P((i+1) \bmod p)$, for all $i<p$, then
  $P(i)$ holds for all $i<p$.
\<close>

lemma mod_induct_0:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p"
  shows "P 0"
proof (rule ccontr)
  assume contra: "\<not>(P 0)"
  from i have p: "0<p" by simp
  have "\<forall>k. 0<k \<longrightarrow> \<not> P (p-k)" (is "\<forall>k. ?A k")
  proof
    fix k
    show "?A k"
    proof (induct k)
      show "?A 0" by simp  \<comment>\<open>by contradiction\<close>
    next
      fix n
      assume ih: "?A n"
      show "?A (Suc n)"
      proof (clarsimp)
	assume y: "P (p - Suc n)"
	have n: "Suc n < p"
	proof (rule ccontr)
	  assume "\<not>(Suc n < p)"
	  hence "p - Suc n = 0"
	    by simp
	  with y contra show "False"
	    by simp
	qed
	hence n2: "Suc (p - Suc n) = p-n" by arith
	from p have "p - Suc n < p" by arith
	with y step have z: "P ((Suc (p - Suc n)) mod p)"
	  by blast
	show "False"
	proof (cases "n=0")
	  case True
	  with z n2 contra show ?thesis by simp
	next
	  case False
	  with p have "p-n < p" by arith
	  with z n2 False ih show ?thesis by simp
	qed
      qed
    qed
  qed
  moreover
  from i obtain k where "0<k \<and> i+k=p"
    by (blast dest: less_imp_add_positive)
  hence "0<k \<and> i=p-k" by auto
  moreover
  note base
  ultimately
  show "False" by blast
qed

lemma mod_induct:
  assumes step: "\<forall>i<p. P i \<longrightarrow> P ((Suc i) mod p)"
  and base: "P i" and i: "i<p" and j: "j<p"
  shows "P j"
proof -
  have "\<forall>j<p. P j"
  proof
    fix j
    show "j<p \<longrightarrow> P j" (is "?A j")
    proof (induct j)
      from step base i show "?A 0"
	by (auto elim: mod_induct_0)
    next
      fix k
      assume ih: "?A k"
      show "?A (Suc k)"
      proof
	assume suc: "Suc k < p"
	hence k: "k<p" by simp
	with ih have "P k" ..
	with step k have "P (Suc k mod p)"
	  by blast
	moreover
	from suc have "Suc k mod p = Suc k"
	  by simp
	ultimately
	show "P (Suc k)" by simp
      qed
    qed
  qed
  with j show ?thesis by blast
qed

text \<open>
  Pairs and functions whose codomains are pairs.
\<close>

lemma img_fst [intro]:
  assumes "(a,b) \<in> S"
  shows "a \<in> fst ` S"
by (rule image_eqI[OF _ assms]) simp

lemma img_snd [intro]:
  assumes "(a,b) \<in> S"
  shows "b \<in> snd ` S"
by (rule image_eqI[OF _ assms]) simp

lemma range_prod:
  "range f \<subseteq> (range (fst \<circ> f)) \<times> (range (snd \<circ> f))"
proof
  fix y
  assume "y \<in> range f"
  then obtain x where y: "y = f x" by auto
  hence "y = (fst(f x), snd(f x))"
    by simp
  thus "y \<in> (range (fst \<circ> f)) \<times> (range (snd \<circ> f))"
    by (fastforce simp add: image_def)
qed

lemma finite_range_prod:
  assumes fst: "finite (range (fst \<circ> f))"
  and     snd: "finite (range (snd \<circ> f))"
  shows "finite (range f)"
proof -
  from fst snd have "finite (range (fst \<circ> f) \<times> range (snd \<circ> f))"
    by (rule finite_SigmaI)
  thus ?thesis
    by (rule finite_subset[OF range_prod])
qed

text \<open>
  Decompose general union over sum types.
\<close>

lemma Union_plus:
  "(\<Union> x \<in> A <+> B. f x) = (\<Union> a \<in> A. f (Inl a)) \<union> (\<Union>b \<in> B. f (Inr b))"
by auto

lemma Union_sum:
  "(\<Union>x. f (x::'a+'b)) = (\<Union>l. f (Inl l)) \<union> (\<Union>r. f (Inr r))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Union>x \<in> UNIV <+> UNIV. f x)"
    by simp
  thus ?thesis
    by (simp only: Union_plus)
qed

lemma card_Plus:
  assumes fina: "finite (A::'a set)" and finb: "finite (B::'b set)"
  shows "card (A <+> B) = (card A) + (card B)"
proof -
  from fina finb
  have "card ((Inl ` A) \<union> (Inr ` B)) =
        (card ((Inl ` A)::('a+'b)set)) + (card ((Inr ` B)::('a+'b)set))"
    by (auto intro: card_Un_disjoint finite_imageI)
  thus ?thesis
    by (simp add: Plus_def card_image inj_on_def)
qed

text \<open>
  The standard library proves that a generalized union is finite
  if the index set is finite and if for every index the component
  set is itself finite. Conversely, we show that every component
  set must be finite when the union is finite.
\<close>
(*
lemma finite_UNION_then_finite:
  assumes hyp: "finite (UNION A B)" and a: "a \<in> A"
  shows "finite (B a)"
proof (rule ccontr)
  assume cc: "infinite (B a)"
  from a have "B a \<subseteq> UNION A B" by auto
  from this cc have "infinite (UNION A B)" by (rule infinite_super)
  from this hyp show "False" ..
qed
*)

lemma finite_UNION_then_finite:
  "finite (\<Union>(B ` A)) \<Longrightarrow> a \<in> A \<Longrightarrow> finite (B a)"
by (metis Set.set_insert UN_insert Un_infinite)

end