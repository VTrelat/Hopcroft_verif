theory Dags
imports Main "~~/src/HOL/Library/Infinite_Set"
begin

subsection {* $\omega$-dags *}

text {*
  Infinite dags are an important tool in the study of
  $\omega$-automata. In particular, they can be used to represent
  all possible runs of an automaton over an input word, and this
  representation underlies a recent technique introduced by
  Kupferman et al.\ for proving closure of B\"uchi automata
  (among others) under complement.

  We formalize an $\omega$-dag over a type @{text 'n} of nodes 
  by indicating a set of root nodes and, for each ``slice'' of
  the dag, a successor relation: the set of nodes reachable
  from a position $(n,i)$ where $n$ is a node and $i$ is a natural
  number.

  Note: the theory of $\omega$-dags is independent of that of
  $\omega$-words.
*}

type_synonym 'n position = "'n * nat"

record 'n dag =
  roots :: "'n set"
  succs :: "'n position \<Rightarrow> 'n set"


subsubsection {* Reachability in dags *}

text {*
  A standard inductive definition characterizes reachability of
  positions in a dag.
*}

(* consts reachable :: "('n,'a) dag_scheme \<Rightarrow> 'n position \<Rightarrow> 'n position set" *)
inductive_set
  reachable :: "('n,'a) dag_scheme \<Rightarrow> 'n position \<Rightarrow> 'n position set"
  for dg :: "('n,'a) dag_scheme" and pos :: "'n position"
  where
    reachable_base [intro,simp]:  "pos \<in> reachable dg pos"
  | reachable_succs [elim]:
    "\<lbrakk>nd'' \<in> succs dg pos'; pos' \<in> reachable dg pos\<rbrakk>
     \<Longrightarrow> (nd'', Suc (snd pos')) \<in> reachable dg pos"

text {*
  The definition is lifted in the canonical way to the set of
  positions reachable from a set of source positions.
*}

definition
  reachables :: "('n,'a) dag_scheme \<Rightarrow> 'n position set \<Rightarrow> 'n position set"
  where "reachables dg S \<equiv> \<Union> pos \<in> S. reachable dg pos"

subsubsection {* Elementary lemmas *}

text {* We restate some of the lemmas in terms of explicit pairs. *}

lemma reachable_succs' [elim]:
  assumes nd'': "nd'' \<in> succs dg (nd',lvl')"
  and nd': "(nd',lvl') \<in> reachable dg pos"
  shows "(nd'', Suc lvl') \<in> reachable dg pos"
proof -
  from nd'' nd' have "(nd'', Suc (snd (nd',lvl'))) \<in> reachable dg pos" ..
  thus ?thesis by simp
qed

text {* Successors of a position are reachable. *}

lemma succs_reachable [elim]:
  assumes n': "n' \<in> succs dg pos"
  shows "(n', Suc(snd pos)) \<in> reachable dg pos"
proof -
  have "pos \<in> reachable dg pos" ..
  with n' show ?thesis ..
qed

lemma succs_reachable' [elim]:
  assumes n': "n' \<in> succs dg (n,l)"
  shows "(n', Suc l) \<in> reachable dg (n,l)"
proof -
  have "(n,l) \<in> reachable dg (n,l)" ..
  with n' show ?thesis ..
qed

text {* A ``reverse'' induction step for reachability. *}

lemma reachable_revI:
  assumes nd': "nd' \<in> succs dg pos"
  and pos'': "pos'' \<in> reachable dg (nd', (Suc (snd pos)))"
  shows "pos'' \<in> reachable dg pos"
using pos''
proof (induct)
  from nd' show "(nd', Suc (snd pos)) \<in> reachable dg pos" ..
next
  fix nd'' pos'
  assume "nd'' \<in> succs dg pos'"
    and  "pos' \<in> reachable dg pos"
  thus "(nd'', Suc (snd pos')) \<in> reachable dg pos" ..
qed

text {* Reachability is transitive. *}

lemma reachable_trans [rule_format, trans]:
  assumes pos': "pos' \<in> reachable dg pos"
  shows "\<forall>pos'' \<in> reachable dg pos'. pos'' \<in> reachable dg pos"
    (is "?P pos pos'")
using pos'
proof (induct)
  show "?P pos pos" ..
next
  fix nd'' pos'
  assume nd'': "nd'' \<in> succs dg pos'"
    and ih: "?P pos pos'"
  show "?P pos (nd'', (Suc (snd pos')))"
  proof (clarify)
    fix nd''' lvl'''
    assume "(nd''',lvl''') \<in> reachable dg (nd'', (Suc (snd pos')))"
    with nd'' have "(nd''',lvl''') \<in> reachable dg pos'"
      by (rule reachable_revI)
    with ih show "(nd''',lvl''') \<in> reachable dg pos" ..
  qed
qed

text {* Only positions of higher levels are reachable. *}

lemma reachable_level:
  assumes pos': "pos' \<in> reachable dg pos"
  shows "snd pos \<le> snd pos'"
using pos'
by (induct, auto)

lemma reachable_level':
  assumes "(nd',lvl') \<in> reachable dg (nd,lvl)"
  shows "lvl \<le> lvl'"
using reachable_level[OF assms] by auto

lemma reachable_same_level_then_equal:
  assumes pos': "pos' \<in> reachable dg pos"
  and lvl: "snd pos' = snd pos"
  shows "pos' = pos"
using pos'
proof (cases)
  fix nd' pos''
  assume nd':  "pos' = (nd', Suc (snd pos''))"
    and pos'': "pos'' \<in> reachable dg pos"
  from pos'' have "snd pos \<le> snd pos''"
    by (rule reachable_level)
  with nd' lvl show ?thesis -- "by contradiction"
    by auto
qed (simp)

lemma reachable_same_level_then_equal':
  assumes pos': "(nd', lvl) \<in> reachable dg (nd, lvl)"
  shows "nd' = nd"
using reachable_same_level_then_equal[OF assms] by auto

lemma mutually_reachable_equal:
  assumes pos': "pos' \<in> reachable dg pos" and pos: "pos \<in> reachable dg pos'"
  shows "pos = pos'"
proof -
  from pos' have "snd pos \<le> snd pos'"
    by (rule reachable_level)
  moreover
  from pos have "snd pos' \<le> snd pos"
    by (rule reachable_level)
  ultimately show ?thesis
    by (auto intro: reachable_same_level_then_equal[OF pos])
qed

lemma reachable_Suc_level:
  assumes pos'': "pos'' \<in> reachable dg pos"
  and "snd pos'' = Suc lvl'"
  and "snd pos \<le> lvl'"
  shows "\<exists>pos' \<in> reachable dg pos. fst pos'' \<in> succs dg pos' \<and> snd pos' = lvl'"
using assms by (cases) auto

lemma reachable_Suc_level':
  assumes pos'': "(nd'', Suc lvl') \<in> reachable dg (nd,lvl)"
  and "lvl \<le> lvl'"
  shows "\<exists>nd'. (nd',lvl') \<in> reachable dg (nd,lvl) \<and> nd'' \<in> succs dg (nd',lvl')"
using assms by (cases) auto

(** lemmas [elim!] = reachable_Suc_level'[THEN exE, rule_format] **)

text {* Reflexivity of @{text reachables} *}

lemma reachables_refl [elim]:
  assumes "pos \<in> S"
  shows "pos \<in> reachables dg S"
using assms by (auto simp add: reachables_def)

text {* Monotonicity of @{text reachables} *}

lemma reachables_mono:
  assumes "S \<subseteq> T"
  and "pos \<in> reachables dg S"
  shows "pos \<in> reachables dg T"
using assms by (auto simp add: reachables_def)

text {* Idempotence of @{text reachables} *}

lemma reachables_idem [simp]:
  "reachables dg (reachables dg S) = reachables dg S"
  (is "?lhs = ?rhs")
by (auto simp add: reachables_def elim: reachable_trans)

lemma reachables_reachable:
  assumes "pos \<in> reachables dg S"
  and "pos' \<in> reachable dg pos"
  shows "pos' \<in> reachables dg S"
using assms by (auto simp add: reachables_def elim: reachable_trans)

lemma reachables_succs [elim]:
  assumes "nd' \<in> succs dg pos"
  and "pos \<in> reachables dg S"
  shows "(nd', Suc (snd pos)) \<in> reachables dg S"
using assms by (auto simp add: reachables_def)

lemma reachables_succs' [elim]:
  assumes "nd' \<in> succs dg (nd,lvl)"
  and "(nd,lvl) \<in> reachables dg S"
  shows "(nd', Suc lvl) \<in> reachables dg S"
using assms by (auto simp add: reachables_def)

text {* Fixpoint characterization of @{text reachable} *}

theorem reachable_rec:
  "reachable dg pos = 
   {pos} \<union> reachables dg (succs dg pos \<times> {Suc (snd pos)})"
  (is "?lhs = ?rhs" is "?lhs = _ \<union> ?rch")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix pos'
    assume pos': "pos' \<in> ?lhs"
    thus "pos' \<in> ?rhs"
    proof (induct)
      show "pos \<in> ?rhs" by simp
    next
      fix nd'' pos''
      assume pos'': "pos'' \<in> ?rhs"
	and nd'': "nd'' \<in> succs dg pos''"
      hence "(nd'', Suc(snd pos'')) \<in> ?rch"
	by (auto simp add: reachables_def)	
      thus "(nd'', Suc(snd pos'')) \<in> ?rhs" ..
    qed
  qed
next
  show "?rhs \<subseteq> ?lhs"
    by (auto simp add: reachables_def elim: reachable_revI)
qed

text {*
  If infinitely many positions are reachable from position @{text pos}
  that has only finitely many successors then @{text pos} must have
  some successor from which infinitely many positions can be reached.
*}

lemma infinite_reachable_succs:
  assumes inf: "infinite (reachable dg pos)"
  and width: "finite (succs dg pos)"
  shows "\<exists>nd \<in> succs dg pos. infinite (reachable dg (nd, Suc(snd pos)))"
proof (rule ccontr)
  assume "\<not> ?thesis"
  with width have "finite (reachable dg pos)"
    by (auto simp add: reachable_rec[of dg pos] reachables_def)
  with inf show "False" ..
qed


subsubsection {* Reachable positions and slices *}

text {*
  We define the set of reachable positions in a dag and the
  slices of a dag, i.e.\ the set of reachable nodes at a given
  level of the dag.
*}

definition
  rch_positions :: "'n dag \<Rightarrow> 'n position set"
  where "rch_positions dg \<equiv> reachables dg (roots dg \<times> {0})"

definition
  slice :: "['n dag, nat] \<Rightarrow> 'n set"
  where "slice dg lvl \<equiv> { nd . (nd, lvl) \<in> rch_positions dg }"

lemma rch_positionsI [intro]:
  "\<lbrakk> rt \<in> roots dg; pos \<in> reachable dg (rt,0) \<rbrakk> \<Longrightarrow> pos \<in> rch_positions dg"
by (auto simp add: rch_positions_def reachables_def)

lemma rch_positionsE [elim]:
  "\<lbrakk> pos \<in> rch_positions dg; 
     \<And>rt. \<lbrakk>rt \<in> roots dg; pos \<in> reachable dg (rt,0)\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (auto simp add: rch_positions_def reachables_def)

lemma rch_positions_reachable [elim]:
  "\<lbrakk> pos \<in> rch_positions dg; pos' \<in> reachable dg pos \<rbrakk> \<Longrightarrow> pos' \<in> rch_positions dg"
by (blast intro: reachable_trans)

lemma rch_positions_succs [elim]:
  "\<lbrakk> nd' \<in> succs dg pos; pos \<in> rch_positions dg \<rbrakk>
   \<Longrightarrow> (nd',Suc (snd pos)) \<in> rch_positions dg"
by auto

lemma rch_positions_succs' [elim]:
  "\<lbrakk> nd' \<in> succs dg (nd,lvl); (nd, lvl) \<in> rch_positions dg \<rbrakk>
   \<Longrightarrow> (nd', Suc lvl) \<in> rch_positions dg"
by auto

text {* The set of reachable positions is the union of all slices. *}

lemma "rch_positions dg = (\<Union> lvl. (slice dg lvl) \<times> {lvl})"
by (auto simp add: slice_def)

text {* Any (reachable) position is in its slice. *}

lemma rch_positions_slice [simp, intro]:
  "pos \<in> rch_positions dg \<Longrightarrow> fst pos \<in> slice dg (snd pos)"
by (auto simp add: slice_def)

lemma rch_positions_slice' [intro]:
  "(nd,lvl) \<in> rch_positions dg \<Longrightarrow> nd \<in> slice dg lvl"
by (auto simp add: slice_def)

lemma slice0 [simp]:
  shows "slice dg 0 = roots dg"
by (auto simp add: slice_def dest: reachable_same_level_then_equal')

lemma slice_Suc [simp]:
  shows "slice dg (Suc lvl) = (\<Union> nd \<in> slice dg lvl. succs dg (nd,lvl))"
by (fastsimp simp add: slice_def dest: reachable_Suc_level')


subsubsection {* Paths in a dag *}

text {*
  We define the set of paths from a given position in a dag and
  the set of paths from the roots of the dag. Paths are sequences
  of nodes related by edges in the dag.
*}

definition
  paths_from :: "('n,'a) dag_scheme \<Rightarrow> 'n position \<Rightarrow> (nat \<Rightarrow> 'n) set"
  where "paths_from dg pos \<equiv> 
         { w . w 0 = fst pos \<and> (\<forall> i. w (Suc i) \<in> succs dg (w i, (snd pos) + i)) }"

definition
  paths :: "('n,'a) dag_scheme \<Rightarrow> (nat \<Rightarrow> 'n) set"
  where "paths dg \<equiv> \<Union> rt \<in> roots dg. paths_from dg (rt, 0)"

lemma path_from_0 [elim]:
  "p \<in> paths_from dg pos \<Longrightarrow> p 0 = fst pos"
by (auto simp add: paths_from_def)

lemma path_from_0' [elim]:
  "p \<in> paths_from dg (q,l) \<Longrightarrow> p 0 = q"
by (auto simp add: paths_from_def)

lemma path_from_Suc [elim]:
  "p \<in> paths_from dg pos \<Longrightarrow> p(Suc n) \<in> succs dg (p n, snd pos + n)"
by (auto simp add: paths_from_def)

lemma path_from_Suc' [elim]:
  "p \<in> paths_from dg (q,l) \<Longrightarrow> p(Suc n) \<in> succs dg (p n, l + n)"
by (auto simp add: paths_from_def)

lemma path_0 [elim]:
  "p \<in> paths dg \<Longrightarrow> p 0 \<in> roots dg"
by (auto simp add: paths_def path_from_0)

lemma path_Suc [elim]:
  "p \<in> paths dg \<Longrightarrow> p(Suc n) \<in> succs dg (p n, n)"
by (auto simp add: paths_def dest: path_from_Suc)

text {* The tail of a path is a path. *}

lemma paths_from_tail:
  assumes p: "p \<in> paths_from dg pos"
  shows "(\<lambda>n. p (k+n)) \<in> paths_from dg (p k, snd pos + k)"
proof (auto simp add: paths_from_def)
  fix i
  from p have "p(Suc(k+i)) \<in> succs dg (p(k+i), snd pos + (k + i))"
    by (auto simp add: paths_from_def)
  thus "p(Suc(k+i)) \<in> succs dg (p(k+i), snd pos + k + i)"
    by (auto simp add: add_ac)
qed

text {* All positions along a path are reachable. *}

lemma path_then_reachable:
  "p \<in> paths_from dg pos \<Longrightarrow> (p i, snd pos + i) \<in> reachable dg pos"
by (induct i, auto simp add: paths_from_def)

lemma path_rch_positions [elim]:
  assumes p: "p \<in> paths dg"
  shows "(p n, n) \<in> rch_positions dg"
proof -
  from p obtain rt where
    rt: "rt \<in> roots dg" and p': "p \<in> paths_from dg (rt,0)"
    by (auto simp add: paths_def)
  from p' have "(p n, n) \<in> reachable dg (rt,0)"
    by (auto dest: path_then_reachable)
  with rt show ?thesis ..
qed

text {*
  Note that the converse is not necessarily true: if position
  @{text pos'} is reachable from position @{text pos} there is
  certainly a finite path, but not necessarily an infinite
  path from @{text pos} to @{text pos'}. The following lemma
  expresses the existence of a finite path.
*}

lemma reachable_then_path:
  assumes nd': "pos' \<in> reachable dg pos"
  shows "\<exists>p. p(snd pos) = fst pos \<and> p(snd pos') = fst pos'
             \<and> (\<forall>k \<in> {snd pos ..< snd pos'}. p (Suc k) \<in> succs dg (p k, k))"
    (is "\<exists>p. ?path p pos'")
using nd'
proof (induct)
  have "?path (\<lambda>k. if k = snd pos then fst pos else arbitrary) pos" by fastsimp
  thus "\<exists>p. ?path p pos" by (intro exI)
next
  fix nd pos''
  assume ih: "\<exists>p. ?path p pos''"
    and suc: "nd \<in> succs dg pos''"
    and rch: "pos'' \<in> reachable dg pos"
  from ih obtain p where p: "?path p pos''" ..
  from rch have "snd pos \<le> snd pos''"
    by (rule reachable_level)
  with p suc have "?path (\<lambda>k. if k = Suc(snd pos'') then nd else p k) (nd, Suc (snd pos''))"
    by fastsimp
  thus "\<exists>p. ?path p (nd, Suc (snd pos''))" by (intro exI)
qed

text {* Paths go through successive slices. *}

lemma paths_from_slice:
  assumes "p \<in> paths_from dg pos"
  and "pos \<in> rch_positions dg"
  shows "p k \<in> slice dg (snd pos + k)"
using assms by (induct k) (auto simp add: paths_from_def)

text {*
  We prove a version of König's lemma: given a position @{text pos}
  from which an infinite set of positions is reachable but where
  any position reachable from @{text pos} only has a finite set
  of successors, there exists an infinite path from @{text pos}.
*}

theorem koenig:
  assumes fin: "\<And>pos'. pos' \<in> reachable dg pos \<Longrightarrow> finite (succs dg pos')"
  and reach: "infinite (reachable dg pos)"
  shows "\<exists> p. p \<in> paths_from dg pos"
proof -
  txt {*
    The idea is to choose a path consisting of nodes that have each
    an infinite set of reachable nodes, and that are related by dag edges.
    *}
  let "?inf pp" = "infinite (reachable dg pp)"
  let "?suc_inf pp n" = "n \<in> succs dg pp \<and> ?inf (n, Suc (snd pp))"
  def p \<equiv> "nat_rec (fst pos) (\<lambda>i pnd. \<some> n. ?suc_inf (pnd, snd pos + i) n)"
  have "\<forall>i. (p i, snd pos + i) \<in> reachable dg pos
          \<and> ?inf (p i, snd pos + i)
          \<and> (\<forall>j. i = Suc j \<longrightarrow> p i \<in> succs dg (p j, snd pos + j))"
       (is "\<forall>i. ?P i")
  proof
    fix i
    show "?P i"
    proof (induct i)
      from reach show "?P 0"
	by (auto simp add: p_def)
    next
      fix k
      assume ih: "?P k"
      have "\<exists> n. ?suc_inf (p k, snd pos + k) n"
      proof (rule ccontr)
	assume contra: "\<not> ?thesis"
	from ih have "finite (succs dg (p k, snd pos + k))"
	  by (auto intro: fin)
	with contra have "finite (reachables dg (succs dg (p k, snd pos + k)
                                                 \<times> {Suc(snd pos + k)}))"
	  by (simp add: reachables_def)
	hence "finite (reachable dg (p k, snd pos + k))"
	  by (simp add: reachable_rec)
	with ih show "False" by simp
      qed
      hence "?suc_inf (p k, snd pos + k) (\<some> n. ?suc_inf (p k, snd pos + k) n)"
	by (rule someI_ex)
      with ih show "?P (Suc k)"
	by (force simp add: p_def)
    qed
  qed
  hence "p \<in> paths_from dg pos"
    by (auto simp add: p_def paths_from_def)
  thus ?thesis by blast
qed


subsubsection {* Sub-dags and removal of nodes *}

text {*
  We occasionally need to consider sub-dags of a given dag, and
  in particular construct a sub-dag by removing some nodes (and
  the corresponding edges).
*}

definition       -- {* dg is a sub-dag of dg' *}
  subdag :: "[('n,'a) dag_scheme, ('n,'b) dag_scheme] \<Rightarrow> bool"
  where "subdag dg dg' \<equiv>
            roots dg \<subseteq> roots dg'
         \<and> (\<forall>pos. succs dg pos \<subseteq> succs dg' pos)"

definition
  dag_minus :: "('n,'a) dag_scheme \<Rightarrow> 'n position set \<Rightarrow> ('n,'a) dag_scheme"
  where "dag_minus dg S \<equiv> 
         dg\<lparr>roots :=  (roots dg) - {n . (n,0) \<in> S}, 
            succs := (\<lambda>pos. (succs dg pos) - {n . (n, Suc(snd pos)) \<in> S})
           \<rparr>"

lemma subdag_root [elim]:
  "\<lbrakk> subdag dg dg'; rt \<in> roots dg \<rbrakk> \<Longrightarrow> rt \<in> roots dg'"
by (auto simp add: subdag_def)

lemma subdag_succs [elim]:
  "\<lbrakk>subdag dg dg'; nd \<in> succs dg pos\<rbrakk> \<Longrightarrow> nd \<in> succs dg' pos"
by (unfold subdag_def, blast)

lemma subdag_refl [simp]: "subdag dg dg"
by (simp add: subdag_def)

lemma subdag_trans [trans]:
  "\<lbrakk> subdag dg dg'; subdag dg' dg'' \<rbrakk> \<Longrightarrow> subdag dg dg''"
by (fastsimp simp add: subdag_def)

text {*
  Without any assumptions about the ``more'' fields, we cannot prove
  anti-symmetry of the subdag relation.
*}

text {* Reachability in subdag implies reachability in superdag. *}

lemma subdag_reachable [elim]:
  assumes dg': "subdag dg' dg"
  and pos': "pos' \<in> reachable dg' pos"
  shows "pos' \<in> reachable dg pos"
using pos'
proof (induct)
  show "pos \<in> reachable dg pos" ..
next
  fix nd'' pos'
  assume ih:  "pos' \<in> reachable dg pos"
    and nd'': "nd'' \<in> succs dg' pos'"
  from dg' nd'' have "nd'' \<in> succs dg pos'" ..
  from this ih show "(nd'', Suc(snd pos')) \<in> reachable dg pos" ..
qed

lemma subdag_reachables [elim]:
  "\<lbrakk> subdag dg' dg; pos \<in> reachables dg' S \<rbrakk> \<Longrightarrow> pos \<in> reachables dg S"
by (auto simp add: reachables_def)

lemma subdag_rch_positions [elim]:
  assumes dg': "subdag dg' dg"
  and pos: "pos \<in> rch_positions dg'"
  shows "pos \<in> rch_positions dg"
proof -
  from dg' have "roots dg' \<subseteq> roots dg"
    by (auto simp add: subdag_def)
  hence "(roots dg') \<times> {0} \<subseteq> (roots dg \<times> {0})"
    by auto
  thus ?thesis using assms
    by (auto simp add: rch_positions_def elim: reachables_mono)
qed

lemma subdag_path_from [elim]:
  "\<lbrakk> subdag dg' dg; p \<in> paths_from dg' pos \<rbrakk> \<Longrightarrow> p \<in> paths_from dg pos"
by (fastsimp simp add: paths_from_def subdag_def)

lemma subdag_paths [elim]:
  assumes dg': "subdag dg' dg"
  and p: "p \<in> paths dg'"
  shows "p \<in> paths dg"
proof -
  from p obtain rt where
    rt: "rt \<in> roots dg'" and prt: "p \<in> paths_from dg' (rt,0)"
    by (auto simp add: paths_def)
  from dg' rt have "rt \<in> roots dg" ..
  moreover
  from dg' prt have "p \<in> paths_from dg (rt,0)" ..
  ultimately show ?thesis
    by (auto simp add: paths_def)
qed

lemma subdag_slice [elim]:
  "\<lbrakk> subdag dg dg'; nd \<in> slice dg lvl \<rbrakk> \<Longrightarrow> nd \<in> slice dg' lvl"
by (auto simp add: slice_def)


lemma dag_minus_is_subdag [simp, intro]:
  "subdag (dag_minus dg S) dg"
by (auto simp add: subdag_def dag_minus_def)

text {*
  The representation that we have chosen for dags does not include
  the set of positions of the dag, and thus we cannot assert that 
  the positions in $S$ are no longer present after removing $S$
  from a dag. However, they are no longer reachable. More
  precisely, positions in $S$ can only be reached from themselves,
  and they are not reachable from the roots of the dag.
*}

lemma dag_minus_reachable:
  assumes pin: "pos \<in> S"
  and rch: "pos \<in> reachable (dag_minus dg S) pos'"
  shows "pos = pos'"
using pin by (rule_tac reachable.cases[OF rch]) (auto simp add: dag_minus_def)

lemma dag_minus_reachables [elim]:
  assumes "pos \<in> S" and "pos \<in> reachables (dag_minus dg S) S'"
  shows "pos \<in> S'"
using assms by (auto simp add: reachables_def dest: dag_minus_reachable)

lemma dag_minus_rch_positions [dest]:
  assumes pos: "pos \<in> rch_positions (dag_minus dg S)"
  shows "pos \<in> (rch_positions dg) - S"
proof
  have "subdag (dag_minus dg S) dg" ..
  from this pos show "pos \<in> rch_positions dg" ..
next
  show "pos \<notin> S"
  proof
    assume contra: "pos \<in> S"
    with pos have "pos \<in> roots (dag_minus dg S) \<times> {0}"
      by (auto simp add: rch_positions_def)
    with contra show "False"
      by (auto simp add: dag_minus_def)
  qed
qed

end
