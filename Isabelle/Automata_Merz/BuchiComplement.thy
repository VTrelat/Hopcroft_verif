theory BuchiComplement
imports Buchi Parity
begin

section {* Closure under complement of Büchi automata *}

text {*
  We now prove that the class of Büchi automata is closed under
  complement, i.e.\ that for every Büchi automaton $\mathcal{A}$
  there exists a Büchi automaton $comp(\mathcal{A})$ that
  accepts precisely those words rejected by $\mathcal{A}$.

  Unlike the case of finite automata over finite words, one cannot
  proceed by determinizing $\mathcal{A}$ and then complementing a
  deterministic Büchi automaton because deterministic Büchi
  automata are strictly weaker than non-deterministic ones.
  The complementation theorem was originally proved in a non-constructive 
  way by Büchi in 1962. It was subsequently reproved many times,
  based on different kinds of determinizable $\omega$-automata,
  culminating in a celebrated construction by Safra (1988).
  We formalize here a more recent approach discovered by Kupferman
  and Vardi that is related to the complementation proof for weak
  alternating automata and that appears to extend well to other
  classes of $\omega$-automata. It is based on a study of the
  run dag of a Büchi automaton over an input word.
*}

subsection {* Rankings and odd rankings *}

text {*
  A ranking of a run dag of a Büchi automaton is a function that
  associates a natural number (the rank) to each position such that
  the two following conditions hold:
  \begin{itemize}
  \item The rank of a child is at most the rank of the parent.
  \item Positions built from accepting states have even rank.
  \end{itemize}
  Our definition of rankings takes the acceptance set of the automaton
  as an extra parameter.
*}

type_synonym 'n ranking = "'n position \<Rightarrow> nat"

definition
  rankings :: "'n dag \<Rightarrow> 'n set \<Rightarrow> 'n ranking set" where
  "rankings dg ac \<equiv> 
   { r . \<forall>pos \<in> rch_positions dg.
               (fst pos \<in> ac \<longrightarrow> even (r pos))
            \<and> (\<forall>nd \<in> succs dg pos. r (nd, Suc(snd pos)) \<le> r pos) }"

lemma rank_nonincr [elim]:
  assumes "r \<in> rankings dg ac"
  and "pos \<in> rch_positions dg" and "nd \<in> succs dg pos"
  shows "r(nd, Suc(snd pos)) \<le> r pos"
using assms by (auto simp add: rankings_def)

lemma rank_nonincr' [elim]:
  "\<lbrakk>r \<in> rankings dg ac; (q,l) \<in> rch_positions dg; nd \<in> succs dg (q,l) \<rbrakk>
   \<Longrightarrow> r(nd, Suc l) \<le> r (q,l)"
by (auto dest: rank_nonincr)

lemma rank_nonincr_path [elim]:
  assumes r: "r \<in> rankings dg ac" and p: "p \<in> paths dg"
  shows "r(p (Suc n), Suc n) \<le> r(p n, n)"
using assms by auto

lemma rank_accept_even [elim]:
  assumes "r \<in> rankings dg ac" and "(nd,lvl) \<in> rch_positions dg" and "nd \<in> ac"
  shows "even (r(nd,lvl))"
using assms by (auto simp add: rankings_def)

text {*
  Because ranks are non-increasing along a path, they must eventually
  stabilize: from some point onward, all ranks are equal, and this
  is the least rank that occurs along the path.
*}

definition
  stable_rank :: "'q word \<Rightarrow> 'q ranking \<Rightarrow> nat" where
  "stable_rank path r  \<equiv> LEAST rk. \<exists> i. rk = r(path i, i)"

lemma stable_rank_exists:
  "\<exists>i. stable_rank path r = r (path i, i)"
by (auto simp add: stable_rank_def intro: LeastI)

lemma stable_rank_le_rank:
  shows "stable_rank p r \<le> r (p i, i)"
by (auto simp add: stable_rank_def intro: Least_le)

lemma stable_rank_is_stable:
assumes path: "path \<in> paths dg" and rk: "r \<in> rankings dg ac"
shows "\<exists>n. \<forall>m. r (path (n+m), n+m) = stable_rank path r"
proof -
  from stable_rank_exists obtain k where k: "stable_rank path r = r (path k, k)" ..
  have "\<forall>i. r (path(k+i), k+i) = stable_rank path r"
  proof
    fix i
    show "r (path(k+i), k+i) = stable_rank path r"
    proof (induct i)
      case 0
      from k show ?case	by simp
    next
      case (Suc i)
      from path rk have "r (path(k + Suc i), k+Suc i) \<le> r (path(k+i), k+i)"
	(is "?rSuc \<le> _")
	by (auto simp add: rank_nonincr_path)
      with Suc have "?rSuc \<le> stable_rank path r" by simp
      moreover
      have "stable_rank path r \<le> ?rSuc"
	by (auto simp add: stable_rank_def intro: Least_le)
      ultimately show ?case by simp
    qed
  qed
  thus ?thesis ..
qed

text {*
  An \emph{odd ranking} of a dag is a ranking such that the stable
  rank of each path in the dag is odd.
*}

definition
  odd_rankings :: "'q dag \<Rightarrow> 'q set \<Rightarrow> 'q ranking set" where
  "odd_rankings dg ac \<equiv> 
   { r. r \<in> rankings dg ac \<and>
        (\<forall> path \<in> paths dg. odd (stable_rank path r)) }"

text {*
  We will prove that a Büchi
  automaton $\mathcal{A}$ does not accept word $w$ iff the run dag
  for $\mathcal{A}$ and $w$ admits an odd ranking (w.r.t. the set
  of accepting states of $\mathcal{A}$).
*}

subsection {* Existence of odd ranking implies non-acceptance *}

text {*
  The ``if'' direction is easy: suppose there is an odd ranking
  for the run dag for $\mathcal{A}$ and $w$, and consider any run
  of $\mathcal{A}$ over $w$. We have already seen that to this run
  corresponds some path in the run dag, and by assumption the stable
  rank of that path must be odd. In particular, the run visits only
  finitely many accepting states of $\mathcal{A}$. Because this holds
  of any run of $\mathcal{A}$ over $w$, the word is not accepted.
*}

lemma odd_ranking_then_finite_accepts:
  assumes r: "r \<in> odd_rankings dg ac"
  and path: "path \<in> paths dg"
  shows "finite {m. path m \<in> ac}"
proof -
  from r path have odd: "odd (stable_rank path r)"
    by (simp add: odd_rankings_def)
  from r path
  obtain n where "\<forall>m. r (path(n+m), n+m) = stable_rank path r"
    by (auto simp add: odd_rankings_def dest: stable_rank_is_stable)
  with odd have "\<forall>m. n \<le> m \<longrightarrow> odd (r (path m, m))"
    by (auto simp add: le_iff_add)
  hence "\<forall>\<^sub>\<infinity>m. odd (r (path m, m))"
    by (auto simp add: MOST_nat_le)
  hence "finite {m. even (r (path m, m))}"
    by (simp add: MOST_iff_finiteNeg)
  moreover
  from r path
  have "{m. path m \<in> ac} \<subseteq> {m. even (r (path m, m))}"
    by (auto simp add: odd_rankings_def)
  ultimately
  show ?thesis
    by (elim finite_subset)
qed

theorem odd_ranking_then_naccept:
  assumes r: "r \<in> odd_rankings (run_dag auto w) (accept auto)"
  shows "w \<notin> buchi_language auto"
proof (simp add: buchi_language_def, clarify)
  fix run
  assume run: "nd_run auto w run"
    and  acc: "buchi_accepting (accept auto) run"
  from run r have "finite {m. run m \<in> accept auto}"
    by (elim odd_ranking_then_finite_accepts, simp add: path_iff_run)
  moreover from acc have "\<exists>\<^sub>\<infinity> n. run n \<in> accept auto"
    by (auto simp add: buchi_accepting_def limit_inter_INF)
  ultimately show "False"
    by (simp add: Inf_many_def)
qed

subsection {* Non-acceptance implies existence of odd ranking *}

text {*
  The other direction is more complicated: assuming that $w$ is not
  accepted by $\mathcal{A}$, we must construct an odd ranking.
  Kupferman et al. introduce an inductive construction that successively
  eliminates parts of the run dag.

  A position $pos$ of a dag is called
  \begin{itemize}
  \item \emph{endangered} if the set of positions reachable from $pos$
    is finite,
  \item \emph{safe} if no accepting position is reachable from $pos$.
  \end{itemize}
*}

definition
  endangereds :: "'n dag \<Rightarrow> 'n position set" where
  "endangereds dg \<equiv> { pos . finite (reachable dg pos) }"

definition
  safes :: "'n dag \<Rightarrow> 'n set \<Rightarrow> 'n position set" where
  "safes dg ac \<equiv> { pos . (reachable dg pos) \<inter> (ac \<times> UNIV) = {} }"

text {*
  These definitions imply that every node reachable from an
  endangered (resp., safe) node is again endangered (resp., safe).
*}

lemma safes_trans:
  assumes pos: "pos \<in> safes dg ac" and pos': "pos' \<in> reachable dg pos"
  shows "pos' \<in> safes dg ac"
proof -
  from pos' have "reachable dg pos' \<subseteq> reachable dg pos"
    by (auto elim: reachable_trans)
  with pos show ?thesis
    by (auto simp add: safes_def)
qed

lemma endangereds_trans:
  assumes pos: "pos \<in> endangereds dg" and pos': "pos' \<in> reachable dg pos"
  shows "pos' \<in> endangereds dg"
proof -
  from pos' have "reachable dg pos' \<subseteq> reachable dg pos"
    by (auto elim: reachable_trans)
  with pos show ?thesis
    by (auto simp add: endangereds_def elim: finite_subset)
qed

text {*
  The following is a key lemma: a dag without safe positions, and
  that contains positions at each level, contains an accepting path.
  The technical formulation concerns the subdag reachable from some root,
  in order to exclude junk nodes.
*}

lemma no_safes_then_accept:
  assumes rt: "rt \<in> roots dg"
  and safes: "reachable dg (rt,0) \<inter> safes dg ac = {}"
  and succs: "\<forall>pos \<in> reachable dg (rt,0). succs dg pos \<noteq> {}"
  shows "\<exists>p \<in> paths dg. \<exists>\<^sub>\<infinity> n. p n \<in> ac"
proof -
  txt {*
    First, construct a sequence $\pi$ of accepting nodes reachable from $(rt,0)$
    such that $\pi_{i+1}$ is reachable from some successor of $\pi_i$.
  *}
  let "?rsuc pos" = "reachables dg (succs dg pos \<times> {Suc (snd pos)}) \<inter> (ac \<times> UNIV)"
  have rsuc: "\<And>pos. pos \<in> reachable dg (rt,0) \<Longrightarrow> ?rsuc pos \<noteq> {}"
  proof -
    fix pos
    assume pos: "pos \<in> reachable dg (rt,0)"
    with succs obtain nd where nd: "nd \<in> succs dg pos" by blast
    from this pos have "(nd, Suc(snd pos)) \<in> reachable dg (rt,0)"
      by (rule reachable_succs)
    with safes have "(nd, Suc(snd pos)) \<notin> safes dg ac" by blast
    then obtain pos'
      where "pos' \<in> reachable dg (nd, Suc(snd pos)) \<inter> (ac \<times> UNIV)"
      by (fastsimp simp add: safes_def)
    with nd show "?rsuc pos \<noteq> {}"
      by (auto simp add: reachables_def)
  qed
  def pi \<equiv> "nat_rec (rt, 0) (\<lambda> n pos. \<some> pos'. pos' \<in> ?rsuc pos)"
  have pi: "\<And> n. pi n \<in> reachable dg (rt,0) \<and> pi (Suc n) \<in> ?rsuc (pi n)"
       (is "\<And> n. ?rch n \<and> ?suc n")
  proof -
    fix n
    have rch_suc: "\<And> m. ?rch m \<Longrightarrow> ?suc m"
    proof -
      fix m
      assume "?rch m"
      then obtain pos where pos: "pos \<in> ?rsuc (pi m)" by (blast dest: rsuc)
      have "pi (Suc m) = (\<some> pos'. pos' \<in> ?rsuc (pi m))" by (simp add: pi_def)
      also from pos have "\<dots> \<in> ?rsuc (pi m)" by (rule someI)
      finally show "?suc m" .
    qed
    have "?rch n"
    proof (induct n)
      show "?rch 0" by (simp add: pi_def)
    next
      fix n
      assume ih: "?rch n"
      hence "?suc n" by (rule rch_suc)
      hence "pi(Suc n) \<in> reachable dg (pi n)"
	by (simp add: reachable_rec)
      with ih show "?rch (Suc n)"
	by (rule reachable_trans)
    qed
    with rch_suc show "?rch n \<and> ?suc n" by blast
  qed

  txt {*
    The levels of the positions in $\pi$ form an index sequence.
  *}
  have idx: "idx_sequence (\<lambda>n. snd(pi n))"
  proof (auto simp add: idx_sequence_def)
    show "snd(pi 0) = 0" by (simp add: pi_def)
  next
    fix n
    from pi have "pi(Suc n) \<in> ?rsuc (pi n)" by auto
    hence "Suc(snd(pi n)) \<le> snd(pi(Suc n))"
      by (auto simp add: reachables_def reachable_level')
    thus "snd(pi n) < snd(pi(Suc n))" by simp
  qed

  txt {*
    Any two successive positions of $\pi$ are linked by a finite path
    in the dag.
  *}
  let "?path p pos pos'" = 
    "p (snd pos) = fst pos \<and> p (snd pos') = fst pos' \<and>
     (\<forall>k \<in> {snd pos ..< snd pos'}. p (Suc k) \<in> succs dg (p k, k))"
  have "\<forall>n. \<exists>p. ?path p (pi n) (pi (Suc n))"
  proof
    fix n
    from pi have "?suc n" by simp
    hence "pi (Suc n) \<in> reachable dg (pi n)"
      by (simp add: reachable_rec)
    thus "\<exists>p. ?path p (pi n) (pi (Suc n))"
      by (rule reachable_then_path)
  qed
  then obtain ps where
    ps: "\<forall>n. ?path (ps n) (pi n) (pi (Suc n))"
    by (auto dest: choice)

  txt {*
    Finally, obtain the desired path by concatenating these finite paths.
  *}
  have "merge ps (\<lambda>n. snd(pi n)) \<in> paths dg" (is "?mrg \<in> paths dg")
  proof (auto simp add: paths_def paths_from_def)
    from idx have "?mrg 0 = ps 0 (snd (pi 0))"
      by (simp add: merge0 pi_def)
    also from ps have "\<dots> = fst (pi 0)"
      by simp
    also from rt have "\<dots> \<in> roots dg"
      by (simp add: pi_def)
    finally show "?mrg 0 \<in> roots dg" .
  next
    fix i
    from idx obtain k where k: "i \<in> {snd(pi k) ..< snd(pi (Suc k))}"
      by (blast dest: idx_sequence_interval)
    with ps have suc: "ps k (Suc i) \<in> succs dg (ps k i, i)"
      by blast
    from k idx have "?mrg i = ps k i"
      by (simp add: merge)
    with k idx show "?mrg (Suc i) \<in> succs dg (?mrg i, i)"
    proof (auto simp add: merge_Suc)
      assume suci: "Suc i = snd(pi(Suc k))"
      from ps have "ps (Suc k) (snd(pi(Suc k))) = ps k (snd(pi(Suc k)))"
	by auto
      also from suci have "\<dots> = ps k (Suc i)"
	by simp
      finally show "ps (Suc k) (snd(pi(Suc k))) \<in> succs dg (ps k i, i)"
	by (simp add: suc)
    qed (rule suc) -- {* takes care of the other case *}
  qed
  moreover
  have "\<exists>\<^sub>\<infinity> n. (merge ps (\<lambda>n. snd(pi n)) n) \<in> ac"
  proof (auto simp add: INFM_nat)
    fix m
    from idx obtain k where k: "m \<in> {snd(pi k) ..< snd(pi(Suc k))}"
      by (blast dest: idx_sequence_interval)
    let ?n = "snd(pi(Suc k))"
    from idx have "?n \<in> {snd(pi(Suc k)) ..< snd(pi(Suc(Suc k)))}"
      by (rule idx_sequence_idx)
    with idx have "?mrg ?n = ps (Suc k) ?n"
      by (simp add: merge)
    with ps have "?mrg ?n = fst(pi(Suc k))"
      by simp
    moreover from pi have "pi(Suc k) \<in> ac \<times> UNIV"
      by simp
    ultimately have "?mrg ?n \<in> ac"
      by auto
    with k show "\<exists>n. m < n \<and> ?mrg n \<in> ac"
      by auto
  qed
  ultimately
  show ?thesis by blast
qed

text {*
  Clearly, endangered or safe positions cannot appear in an accepting
  path in the run dag. We successively prune the run dag of the
  sets of endangered and safe sets of positions, obtaining a sequence
  of dags.
*}

definition
  elim_positions :: "['n dag, 'n set, nat] \<Rightarrow> 'n position set" where
  "elim_positions dg ac n \<equiv> if even n then endangereds dg else safes dg ac"

lemma elim_positions_trans:
  assumes "pos \<in> elim_positions dg ac n" and "pos' \<in> reachable dg pos"
  shows "pos' \<in> elim_positions dg ac n"
using assms by (auto simp add: elim_positions_def elim: endangereds_trans safes_trans)

primrec dag_seq :: "['n dag, 'n set, nat] \<Rightarrow> 'n dag"
where
  "dag_seq dg ac 0 = dg"
| "dag_seq dg ac (Suc n) = 
   dag_minus (dag_seq dg ac n) (elim_positions (dag_seq dg ac n) ac n)"

lemma dag_seq_subdag: "subdag (dag_seq dg ac (n+k)) (dag_seq dg ac n)"
  (is "?sub k")
proof (induct k)
  show "?sub 0" by simp
next
  fix k
  assume ih: "?sub k"
  have "subdag (dag_seq dg ac (n + Suc k)) (dag_seq dg ac (n+k))"
    by simp
  from this ih show "?sub (Suc k)"
    by (rule subdag_trans)
qed

lemma dag_seq_subdag' [intro]: "subdag (dag_seq dg ac n) dg"
proof -
  have "subdag (dag_seq dg ac (0+n)) (dag_seq dg ac 0)" by (rule dag_seq_subdag)
  thus ?thesis by simp
qed

text {*
  (Reachable) positions from the original dag that have not yet been
  eliminated are still reachable in the $n$-th dag of the sequence.
*}

lemma dag_seq_roots [rule_format]:
  assumes rt: "rt \<in> roots dg"
  shows "(\<forall>k<n. (rt,0) \<notin> elim_positions (dag_seq dg ac k) ac k)
         \<longrightarrow> rt \<in> roots (dag_seq dg ac n)"
using assms by (induct n) (auto simp add: dag_minus_def)

lemma dag_seq_succs [rule_format]:
  assumes "nd' \<in> succs dg pos"
  shows "(\<forall>k<n. (nd', Suc(snd pos)) \<notin> elim_positions (dag_seq dg ac k) ac k)
         \<longrightarrow> nd' \<in> succs (dag_seq dg ac n) pos"
using assms by (induct n) (auto simp add: dag_minus_def)

lemma dag_seq_reachable [rule_format]:
  assumes rch: "pos' \<in> reachable dg pos"
  shows "(\<forall>k<n. pos' \<notin> elim_positions (dag_seq dg ac k) ac k)
         \<longrightarrow> pos' \<in> reachable (dag_seq dg ac n) pos" (is "?P pos'")
using rch proof induct
  show "?P pos" by auto
next
  fix nd pos''
  assume nd: "nd \<in> succs dg pos''" and ih: "?P pos''"
  show "?P (nd, Suc(snd pos''))"
  proof
    let "?elim k" = "elim_positions (dag_seq dg ac k) ac k"
    let ?rch = "reachable (dag_seq dg ac n) pos"
    assume nelim: "\<forall>k<n. (nd, Suc(snd pos'')) \<notin> ?elim k"
    have "\<forall>k<n. pos'' \<notin> ?elim k"
    proof (clarify)
      fix k
      assume k: "k<n" and elim: "pos'' \<in> ?elim k"
      from nd have "nd \<in> succs (dag_seq dg ac k) pos''"
      proof (rule dag_seq_succs)
	fix k'
	assume "k'<k"
	with k nelim show "(nd, Suc(snd pos'')) \<notin> ?elim k'" by auto
      qed
      with elim have "(nd, Suc(snd pos'')) \<in> ?elim k"
	by (auto elim: elim_positions_trans)
      with nelim k show "False" by blast
    qed
    with ih have "pos'' \<in> ?rch" ..
    moreover
    from nd nelim have "nd \<in> succs (dag_seq dg ac n) pos''"
      by (auto elim: dag_seq_succs)
    ultimately show "(nd, Suc(snd pos'')) \<in> ?rch"
      by (elim reachable_succs)
  qed
qed

lemma dag_seq_rch_positions:
  assumes pos: "pos \<in> rch_positions dg"
  and nelim: "\<forall>k<n. pos \<notin> elim_positions (dag_seq dg ac k) ac k"
  shows "pos \<in> rch_positions (dag_seq dg ac n)"
proof -
  from pos obtain rt where
    rt: "rt \<in> roots dg" and rch: "pos \<in> reachable dg (rt,0)" ..
  from rch nelim have rch': "pos \<in> reachable (dag_seq dg ac n) (rt,0)"
    by (auto elim: dag_seq_reachable)
  from rt have "rt \<in> roots (dag_seq dg ac n)"
  proof (rule dag_seq_roots, clarify)
    let "?elim k" = "elim_positions (dag_seq dg ac k) ac k"
    fix k
    assume k: "k<n" and elim: "(rt,0) \<in> ?elim k"
    from k nelim have "\<forall>k'<k. pos \<notin> ?elim k'" by auto
    with rch have "pos \<in> reachable (dag_seq dg ac k) (rt,0)"
      by (auto elim: dag_seq_reachable)
    with elim have "pos \<in> ?elim k"
      by (rule elim_positions_trans)
    with k nelim show "False" by blast
  qed
  from this rch' show ?thesis ..
qed

lemma dag_seq_paths_from:
  assumes p: "p \<in> paths_from dg pos"
  and nelim: "\<forall>k<n. \<forall>i. (p i, snd pos + i) \<notin> elim_positions (dag_seq dg ac k) ac k"
  shows "p \<in> paths_from (dag_seq dg ac n) pos"
proof (auto simp add: paths_from_def)
  from p show "p 0 = fst pos"
    by (auto simp add: paths_from_def)
next
  let "?dg k" = "dag_seq dg ac k"
  fix i
  from p have "p (Suc i) \<in> succs dg (p i, snd pos + i)"
    by (auto simp add: paths_from_def)
  thus "p (Suc i) \<in> succs (?dg n) (p i, snd pos + i)"
  proof (rule dag_seq_succs)
    fix k
    assume "k < n"
    with nelim have "(p(Suc i), snd pos + (Suc i)) \<notin> elim_positions (?dg k) ac k"
      by blast
    thus "(p (Suc i), Suc(snd(p i, snd pos + i))) \<notin> elim_positions (?dg k) ac k"
      by auto
  qed
qed

lemma dag_seq_paths:
  assumes p: "p \<in> paths dg"
  and nelim: "\<forall>k<n. \<forall>i. (p i, i) \<notin> elim_positions (dag_seq dg ac k) ac k"
  shows "p \<in> paths (dag_seq dg ac n)"
proof -
  let ?dg = "dag_seq dg ac"
  from p obtain rt where
    rt: "rt \<in> roots dg" and p': "p \<in> paths_from dg (rt,0)"
    by (auto simp add: paths_def)
  from p' nelim have "p \<in> paths_from (?dg n) (rt,0)"
    by (auto elim: dag_seq_paths_from)
  moreover
  from rt have "rt \<in> roots (?dg n)"
  proof (rule dag_seq_roots)
    fix k
    assume "k < n"
    with nelim have "(p 0, 0) \<notin> elim_positions (?dg k) ac k"
      by blast
    with p' show "(rt,0) \<notin> elim_positions (?dg k) ac k"
      by (simp add: paths_from_def)
  qed
  ultimately show ?thesis
    by (auto simp add: paths_def)
qed


text {*
  From a position that has been eliminated, no position except
  itself is reachable in the resulting dag.
*}

lemma dag_seq_elim_reachable:
  assumes elim: "pos \<in> elim_positions (dag_seq dg ac n) ac n"
  and nd': "pos' \<in> reachable (dag_seq dg ac (Suc n)) pos"
  shows "pos' = pos"
using nd'
proof (induct)
  fix nd pos''
  assume ih: "pos'' = pos"
    and suc: "nd \<in> succs (dag_seq dg ac (Suc n)) pos''"
  hence "nd \<in> succs (dag_seq dg ac n) pos"
    by (simp add: dag_minus_def)
  with elim have "(nd, Suc(snd pos)) \<in> elim_positions (dag_seq dg ac n) ac n"
    by (elim elim_positions_trans succs_reachable)
  with suc ih have "False"
    by (simp add: dag_minus_def)
  thus "(nd, Suc(snd pos'')) = pos" ..
qed (simp) -- {* base case is trivial *}

text {*
  With every position of a dag we associate a set of possible ranks:
  the set of numbers for which the position is eliminated.
  We define the ranking function as assigning each position its least
  possible rank, and we will show that this yields an odd ranking of
  a run dag for an automaton $\mathcal{A}$ and a word rejected by
  $\mathcal{A}$. In fact, the hard part of the proof is to show that
  every position has some rank.
*}

definition
  ranks :: "['n dag, 'n set, 'n position] \<Rightarrow> nat set" where
  "ranks dg ac pos \<equiv>
   { n . pos \<in> elim_positions (dag_seq dg ac n) ac n }"

definition
  ranking :: "['n dag, 'n set, 'n position] \<Rightarrow> nat" where
  "ranking dg ac pos \<equiv> LEAST r. r \<in> ranks dg ac pos"

text {*
  Children have smaller possible ranks than their parents.
*}

lemma ranks_succs:
  assumes nd: "nd \<in> succs dg pos"
  and rk: "r \<in> ranks dg ac pos"
  shows "\<exists>r' \<le> r. r' \<in> ranks dg ac (nd, Suc(snd pos))"
proof (rule exists_leI)
  assume "\<forall>r'<r. r' \<notin> ranks dg ac (nd, Suc(snd pos))"
  hence "\<forall>r'<r. (nd, Suc(snd pos)) \<notin> elim_positions (dag_seq dg ac r') ac r'"
    by (auto simp add: ranks_def)
  with nd have "nd \<in> succs (dag_seq dg ac r) pos"
    by (auto elim: dag_seq_succs)
  hence "(nd, Suc(snd pos)) \<in> reachable (dag_seq dg ac r) pos"
    by (rule succs_reachable)
  with rk show "r \<in> ranks dg ac (nd, Suc(snd pos))"
    by (auto simp add: ranks_def elim: elim_positions_trans)
qed

lemma ranking_succs:
  assumes nd: "nd \<in> succs dg pos"
  and rk: "r \<in> ranks dg ac pos"
  shows "ranking dg ac (nd, Suc(snd pos)) \<le> ranking dg ac pos"
proof -
  from rk have "ranking dg ac pos \<in> ranks dg ac pos"
    by (unfold ranking_def, rule LeastI)
  with nd obtain r' where
    r': "r' \<le> ranking dg ac pos" and rk': "r' \<in> ranks dg ac (nd, Suc(snd pos))"
    by (blast dest: ranks_succs)
  from rk' have "ranking dg ac (nd, Suc(snd pos)) \<le> r'"
    by (unfold ranking_def, rule Least_le)
  with r' show ?thesis by auto
qed

text {*
  An accepting position can only have an even rank.
*}

lemma ranks_acc_even:
  assumes pos: "q \<in> ac" and r: "r \<in> ranks dg ac (q,l)"
  shows "even (ranking dg ac (q,l))" (is "even ?rank")
proof (rule ccontr)
  assume cc: "odd(?rank)"
  let ?rdg = "dag_seq dg ac ?rank"
  from r have "?rank \<in> ranks dg ac (q,l)" 
    by (unfold ranking_def, rule LeastI)
  hence "(q,l) \<in> elim_positions ?rdg ac ?rank" by (simp add: ranks_def)
  with cc have "reachable ?rdg (q,l) \<inter> (ac \<times> UNIV) = {}"
    by (auto simp add: elim_positions_def safes_def)
  moreover
  from pos have "(q,l) \<in> reachable ?rdg (q,l) \<inter> (ac \<times> UNIV)" by auto
  ultimately show "False" by auto
qed

text {*
  Our next goal is to prove that in a dag of bounded width that contains
  no accepting path, every position has some rank.

  Assume that $dg$ is a dag of width $N$ that contains no accepting path.
  Then for all $i$, there is some level such that all slices of the
  $2i$-th dag in the dag sequence constructed for $dg$ from that level
  onward contain at most $N-i$ nodes.
*}

lemma naccept_then_bounded_width:
  assumes fin: "\<forall>k. finite (slice dg k)"
  and card: "\<forall>k. card (slice dg k) \<le> N"
  and nacc: "\<not> (\<exists>p \<in> paths dg. \<exists>\<^sub>\<infinity> n. p n \<in> ac)"
  shows "\<exists> lvl. \<forall>k. card (slice (dag_seq dg ac (i+i)) (lvl+k)) \<le> N - i"
    (is "?P i" is "\<exists> lvl. ?wdth i lvl")
proof (induct i)
  from card have "?wdth 0 0" by auto
  thus "?P 0" ..
next
  txt {* preparation of induction step *}
  let "?dg i" = "dag_seq dg ac i"
  let "?rch i" = "rch_positions (?dg i)"

  txt {* All slices of all dags in the sequence are finite. *}
  have fin_slice: "\<And>i k. finite (slice (?dg i) k)"
  proof (rule finite_subset)
    fix i k
    from fin show "finite (slice dg k)" ..
  next
    fix i k
    have "subdag (?dg i) dg" by (rule  dag_seq_subdag')
    thus "slice (?dg i) k \<subseteq> slice dg k" by auto
  qed

  txt {* All reachable positions have finite sets of successors. *}
  have fin_succs: "\<And>i pos. pos \<in> ?rch i \<Longrightarrow> finite (succs (?dg i) pos)"
  proof -
    fix i pos
    assume pos: "pos \<in> ?rch i"
    hence "fst pos \<in> slice (?dg i) (snd pos)" ..
    hence "succs (?dg i) pos \<subseteq> slice (?dg i) (Suc(snd pos))" by auto
    from this fin_slice show "finite (succs (?dg i) pos)"
      by (rule finite_subset)
  qed

  txt {* induction step *}
  fix i
  assume ih: "?P i" show "?P (Suc i)"
  proof (cases "finite (?rch (i+i))")
    txt {*
      We distinguish two cases: if the $2i$-th dag is finite then every
      position is endangered, hence the $2i+1$-st dag is empty, and so
      is the $2i+2$-nd dag.
      *}
    case True
    have "(roots (?dg (i+i)) \<times> {0}) \<subseteq> endangereds (?dg (i+i))"
    proof (clarsimp simp add: endangereds_def)
      fix rt
      assume rt: "rt \<in> roots (?dg (i+i))"
      hence "reachable (?dg (i+i)) (rt,0) \<subseteq> ?rch (i+i)" by auto
      from this True show "finite (reachable (?dg (i+i)) (rt,0))"
	by (rule finite_subset)
    qed
    hence "roots (?dg (Suc(i+i))) = {}"
      by (auto simp add: elim_positions_def dag_minus_def)
    hence "roots (?dg (Suc(Suc(i+i)))) = {}"
      by (auto simp add: dag_minus_def)
    hence "?rch (Suc(Suc(i+i))) = {}" 
      by auto
    hence "?wdth (Suc i) 0"
      by (auto simp add: slice_def)
    thus ?thesis ..

  next

    case False
    let ?odg = "?dg (Suc(i+i))"

    txt {*
      Since dag $2i+1$ contains infinitely many (reachable) nodes,
      it must have a root.
    *}
    have "\<exists>rt. rt \<in> roots ?odg"
    proof -
      have "\<exists>rt \<in> roots (?dg(i+i)). infinite (reachable (?dg(i+i)) (rt,0))"
      proof (rule ccontr)
	assume contra: "\<not> ?thesis"
	from fin_slice have "finite (slice (?dg(i+i)) 0)" .
	hence "finite (roots (?dg(i+i)))" by simp
	with contra have "finite (?rch (i+i))"
	  by (auto simp add: rch_positions_def reachables_def)
	with False -- {* use case assumption to obtain contradiction *}
	show False ..
      qed
      thus ?thesis
	by (auto simp add: elim_positions_def endangereds_def dag_minus_def)
    qed
    then obtain rt where rt: "rt \<in> roots ?odg" ..

    txt {*
      From any position in dag $2i+1$, infinitely many positions 
      are reachable (because all endangered positions have been removed).
      In particular, all positions have at least one successor.
    *}
    have succs: "\<forall>pos \<in> rch_positions ?odg. succs ?odg pos \<noteq> {}"
    proof
      fix pos
      assume pos: "pos \<in> rch_positions ?odg"
      from pos have
	posii: "pos \<in> rch_positions (?dg(i+i))"	and ndgr: "infinite (reachable (?dg(i+i)) pos)"
	by (auto simp add: elim_positions_def endangereds_def)
      let ?succs = "succs (?dg(i+i)) pos"
      from ndgr have "\<exists>nd \<in> ?succs. infinite (reachable (?dg(i+i)) (nd, Suc(snd pos)))"
      proof (rule infinite_reachable_succs)
	from posii show "finite ?succs"
	  by (rule fin_succs)
      qed
      thus "succs ?odg pos \<noteq> {}"
	by (auto simp add: dag_minus_def elim_positions_def endangereds_def)
    qed

    txt {*
      Dag $2i+1$ contains some safe position, otherwise it would contain
      an accepting path, using lemma @{text no_safes_then_accept}
      (and a fortiori so would the original dag).
    *}
    have "?rch (Suc(i+i)) \<inter> safes ?odg ac \<noteq> {}"
    proof
      assume nosafe: "?rch (Suc(i+i)) \<inter> safes ?odg ac = {}"
      with rt have rts: "reachable ?odg (rt,0) \<inter> safes ?odg ac = {}"
	by auto
      from succs rt
      have "\<forall>pos \<in> reachable ?odg (rt,0). succs ?odg pos \<noteq> {}"
	by auto
      with rt rts have "\<exists>p \<in> paths ?odg. \<exists>\<^sub>\<infinity>n. p n \<in> ac"
	by (rule no_safes_then_accept)
      then obtain p where p: "p \<in> paths ?odg" and pacc: "\<exists>\<^sub>\<infinity>n. p n \<in> ac" ..
      have "subdag ?odg dg" ..
      from this p have "p \<in> paths dg"
	by (rule subdag_paths)
      with nacc pacc show "False" by blast
    qed
    then obtain pos
      where pos: "pos \<in> ?rch (Suc(i+i))" and safe: "pos \<in> safes ?odg ac"
      by blast

    txt {*
      Because this position is contained in dag $2i+1$, it is not
      endangered in dag $2i$. Hence, there exists an infinite path 
      from that position in dag $2i$, using König's lemma.
    *}
    from pos have ndgr: "pos \<in> ?rch(i+i) - endangereds (?dg(i+i))"
      by (auto simp add: elim_positions_def)
    have "\<exists> p. p \<in> paths_from (?dg(i+i)) pos"
    proof (rule koenig)
      from ndgr show "infinite (reachable (?dg(i+i)) pos)"
	by (simp add: endangereds_def)
    next
      fix pos'
      assume "pos' \<in> reachable (?dg(i+i)) pos"
      with ndgr have "pos' \<in> ?rch (i+i)"
	by (auto elim: rch_positions_reachable)
      thus "finite (succs (?dg(i+i)) pos')"
	by (rule fin_succs)
    qed
    then obtain p where p: "p \<in> paths_from (?dg(i+i)) pos" ..

    txt {*
      None of the positions on this path can be endangered in dag $2i$,
      so the path continues to exist in dag $2i+1$.
    *}
    let "?ppos n" = "(p n, snd pos + n)"
    have p_ndgr: "\<forall>k. ?ppos k \<notin> endangereds (?dg(i+i))"
    proof
      fix k
      let ?pp = "\<lambda>n. (p (k+n), snd pos + k + n)"
      from p have "(\<lambda>n. p(k+n)) \<in> paths_from (?dg(i+i)) (?ppos k)"
	by (rule paths_from_tail)
      hence "range ?pp \<subseteq> reachable (?dg(i+i)) (?ppos k)"
	by (auto dest: path_then_reachable)
      moreover
      have "inj ?pp" by (auto intro: inj_onI)
      hence "infinite (range ?pp)" by (rule range_inj_infinite)
      ultimately
      have "infinite (reachable (?dg(i+i)) (?ppos k))"
	by (rule infinite_super)
      thus "?ppos k \<notin> endangereds (?dg(i+i))"
	by (simp add: endangereds_def)
    qed
    have p': "p \<in> paths_from ?odg pos"
    proof (auto simp add: paths_from_def simp del: dag_seq.simps)
      from p show "p 0 = fst pos"
	by (simp add: paths_from_def)
    next
      fix k
      from p_ndgr have "?ppos (Suc k) \<notin> endangereds (?dg(i+i))" ..
      with p show "p (Suc k) \<in> succs ?odg (?ppos k)"
	by (auto simp add: dag_minus_def elim_positions_def paths_from_def)
    qed

    txt {*
      All of the positions along $p$ are safe in dag $2i+1$, since
      they are reachable from (safe) position $pos$. They will therefore
      not belong to dag $2i+2$, which proves the assertion.
    *}
    have p_safe: "\<forall>n. ?ppos n \<in> ?rch(Suc(i+i)) \<inter> safes ?odg ac" (is "\<forall>n. ?P n")
    proof
      fix n
      show "?P n"
      proof (induct n)
	from p' safe pos show "?P 0" by (simp add: paths_from_def)
      next
	fix n
	assume pn: "?P n"
	from p' have succ: "p (Suc n) \<in> succs ?odg (?ppos n)"
	  by (auto simp add: paths_from_def)
	with pn show "?P (Suc n)"
	  by (auto elim: safes_trans)
      qed
    qed

    from ih obtain lvl where
      lvl: "\<forall>k. card (slice (?dg (i+i)) (lvl+k)) \<le> N-i" ..
    let ?lv = "max lvl (snd pos)"
    have "lvl \<le> ?lv"
      by (rule le_maxI1)
    then obtain d where d: "?lv = lvl + d"
      by (auto simp add: le_iff_add)
    have "snd pos \<le> ?lv"
      by (rule le_maxI2)
    then obtain d' where d': "?lv = snd pos + d'"
      by (auto simp add: le_iff_add)
    have lv: "\<forall>k. card (slice (?dg (i+i)) (?lv+k)) \<le> N-i"
    proof
      fix k
      from d have "card (slice (?dg (i+i)) (?lv+k)) = card (slice (?dg (i+i)) (lvl + (d+k)))"
	by (simp add: add_ac)
      with lvl show "card (slice (?dg (i+i)) (?lv+k)) \<le> N-i"
	by auto
    qed
    have "?wdth (Suc i) ?lv"
    proof
      fix k
      let "?sl i" = "slice (?dg(i+i)) (?lv + k)"
      have sub: "?sl (Suc i) \<subseteq> ?sl i - {p (d'+k)}"
      proof (auto simp del: dag_seq.simps)
	fix nd
	assume nd: "nd \<in> slice (?dg (Suc(Suc(i+i)))) (?lv + k)"
	have "subdag (?dg ((i+i)+2)) (?dg (i+i))"
	  by (rule dag_seq_subdag)
	hence "subdag (?dg (Suc(Suc(i+i)))) (?dg (i+i))"
	  by simp
	with nd	show "nd \<in> slice (?dg (i+i)) (?lv + k)"
	  by (elim subdag_slice)
      next
	assume "p (d'+k) \<in> slice (?dg (Suc(Suc(i+i)))) (?lv + k)"
	hence rch: "?ppos (d'+k) \<in> ?rch (Suc(Suc(i+i)))"
	  by (auto simp add: slice_def d' add_ac)
	from p_safe have "?ppos (d'+k) \<in> safes (?dg (Suc(i+i))) ac"
	  by auto
	hence "?ppos (d'+k) \<in> elim_positions (?dg (Suc(i+i))) ac (Suc(i+i))"
	  by (simp add: elim_positions_def)
	with rch show "False" by auto
      qed
      have "finite (?sl i - {p (d'+k)})"
	by (auto intro: fin_slice)
      from this sub have "card (?sl (Suc i)) \<le> card (?sl i - {p (d'+k)})"
	by (rule card_mono)
      also have "\<dots> < card (?sl i)"
      proof (rule card_Diff1_less)
	show "finite (?sl i)" by (rule fin_slice)
      next
	from p ndgr show "p (d'+k) \<in> ?sl i"
	  by (auto simp add: d' add_ac dest: paths_from_slice[where k="d'+k"])
      qed
      also from lv have "\<dots> \<le> N - i" ..
      finally show "card (?sl (Suc i)) \<le> N - Suc i"
	by arith
    qed
    thus ?thesis ..
  qed
qed

text {*
  In particular, given the hypotheses of the previous lemma, the
  dags eventually become empty, and thus every position in the
  original rank is assigned some rank.
*}

lemma naccept_then_ranks:
  assumes fin: "\<forall>k. finite (slice dg k)"
  and card: "\<forall>k. card (slice dg k) \<le> N"
  and nacc: "\<not> (\<exists>p \<in> paths dg. \<exists>\<^sub>\<infinity> n. p n \<in> ac)"
  and pos: "pos \<in> rch_positions dg"
  shows "\<exists>r \<le> N+N. r \<in> ranks dg ac pos"
proof -
  let ?dg2n = "dag_seq dg ac (N+N)"

  txt {* All (reachable) positions of dag $2N$ are endangered *}
  from fin card nacc
  have "\<exists>lvl. \<forall>k. card (slice ?dg2n (lvl+k)) \<le> N-N"
    by (rule naccept_then_bounded_width)
  then obtain lvl where
    lvl: "\<forall>k. lvl \<le> k \<longrightarrow> card (slice ?dg2n k) = 0"
    by (auto simp add: le_iff_add)
  have fin2n: "\<forall>k. finite (slice ?dg2n k)"
  proof
    fix k
    have "subdag ?dg2n dg" ..
    hence "slice ?dg2n k \<subseteq> slice dg k" by auto
    with fin show "finite (slice ?dg2n k)"
      by (auto elim: finite_subset)
  qed
  have "rch_positions ?dg2n = (\<Union> k \<in> {0 ..< lvl}. (slice ?dg2n k) \<times> {k})"
    (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
    proof
      fix pos
      assume "pos \<in> ?lhs"
      hence fst: "fst pos \<in> slice ?dg2n (snd pos)" ..
      with lvl fin2n have "\<not>(lvl \<le> snd pos)" by auto
      with fst show "pos \<in> ?rhs" by (cases pos) auto
    qed
  next
    show "?rhs \<subseteq> ?lhs" by (auto simp add: slice_def)
  qed
  with fin2n have frch: "finite (rch_positions ?dg2n)" by auto
  have dgr: "rch_positions ?dg2n \<subseteq> endangereds ?dg2n"
  proof
    fix pos
    assume "pos \<in> rch_positions ?dg2n"
    hence "reachable ?dg2n pos \<subseteq> rch_positions ?dg2n" by auto
    from this frch have "finite (reachable ?dg2n pos)" by (rule finite_subset)
    thus "pos \<in> endangereds ?dg2n" by (simp add: endangereds_def)
  qed

  txt {* 
    Therefore all reachable positions of the original dag must be
    eliminated, at the latest at step $2N$.
  *}
  let "?elim k" = "elim_positions (dag_seq dg ac k) ac k"
  show ?thesis
  proof (rule exists_leI, clarsimp simp add: ranks_def)
    assume nelim: "\<forall>r < N+N. pos \<notin> ?elim r"
    with pos have "pos \<in> rch_positions ?dg2n"
      by (rule dag_seq_rch_positions)
    with dgr show "pos \<in> ?elim (N+N)"
      by (auto simp add: elim_positions_def)
  qed
qed

text {* The same lemma rewritten for Büchi automata. *}

(* could be generalized to bounded_nondet instead of finite_state
   provided Buchi acceptance were defined by saying that infinitely
   often a run passes through some accepting state *)
lemma auto_naccept_then_ranks:
  assumes inp: "inp \<notin> buchi_language auto"
  and fin: "finite_state auto"
  and pos: "pos \<in> rch_positions (run_dag auto inp)"
  shows "\<exists>r \<le> card (states_of auto) + card (states_of auto). 
            r \<in> ranks (run_dag auto inp) (accept auto) pos"
proof (rule naccept_then_ranks)
  show "\<forall>k. finite (slice (run_dag auto inp) k)" using assms by (auto elim: finite_state_finite_slice finite_state_card_slice)
next
  show "\<forall>k. card (slice (run_dag auto inp) k) \<le> card (states_of auto)" using assms by (auto elim: finite_state_finite_slice finite_state_card_slice)
next
  show "\<not> (\<exists>p\<in>paths (run_dag auto inp). \<exists>\<^sub>\<infinity>n. p n \<in> accept auto)"
  proof (auto simp add: path_iff_run)
    fix run
    assume run: "nd_run auto inp run"
    thus "\<forall>\<^sub>\<infinity>n. run n \<notin> accept auto"
    proof (rule_tac ccontr, auto)
      assume "\<exists>\<^sub>\<infinity>n. run n \<in> accept auto"
      hence "\<exists>q. q \<in> limit run \<inter> accept auto"
      proof (rule_tac INF_limit_inter)
        from fin run have "finite (range run)"
          by (rule finite_state_run)
        thus "finite (accept auto \<inter> range run)"
          by (auto elim: finite_subset)
      qed
      with inp run show "False"
        by (simp add: buchi_language_def buchi_accepting_def)
    qed
  qed
next
  show "pos \<in> rch_positions (run_dag auto inp)" using assms by auto
qed

text {*
  The function @{text ranking} is therefore an admissible ranking
  for a run dag for a word not accepted by a finite-state
  Büchi automaton.
*}

abbreviation
  "aranking auto inp \<equiv> ranking (run_dag auto inp) (accept auto)"

lemma naccept_then_odd_ranking:
  assumes inp: "inp \<notin> buchi_language auto"
  and fin: "finite_state auto"
  shows "aranking auto inp \<in> odd_rankings (run_dag auto inp) (accept auto)"
    (is "?rk \<in> odd_rankings ?rdg ?acc")
proof -
  have rk: "?rk \<in> rankings ?rdg ?acc"
  proof (auto simp add: rankings_def)
    fix q l
    assume pos: "(q,l) \<in> rch_positions ?rdg" and  acc: "q \<in> ?acc"
    from inp fin pos have "\<exists>r. r \<in> ranks ?rdg ?acc (q,l)"
      by (blast dest: auto_naccept_then_ranks)
    with acc show "even (?rk (q,l))"
      by (auto elim: ranks_acc_even)
  next
    fix q l q'
    assume pos: "(q,l) \<in> rch_positions ?rdg" and q': "q' \<in> succs ?rdg (q,l)"
    from inp fin pos have "\<exists>r. r \<in> ranks ?rdg ?acc (q,l)"
      by (blast dest: auto_naccept_then_ranks)
    with q' show "?rk (q', Suc l) \<le> ?rk (q,l)"
      by (auto dest: ranking_succs)
  qed
  have "\<forall>p \<in> paths ?rdg. odd (stable_rank p ?rk)"
  proof
    fix p
    assume p: "p \<in> paths ?rdg"
    with rk obtain n where
      n: "\<forall>m. ?rk (p(n+m), n+m) = stable_rank p ?rk"
      by (auto dest: stable_rank_is_stable)
    from n have lst: "\<forall>m. stable_rank p ?rk = (LEAST r. r \<in> ranks ?rdg ?acc (p(n+m), n+m))"
      by (auto simp add: ranking_def)
    have is_rank: "\<forall>m. stable_rank p ?rk \<in> ranks ?rdg ?acc (p (n+m), n+m)"
    proof
      fix m
      from p have "(p(n+m), n+m) \<in> rch_positions ?rdg"
	by (auto simp add: paths_def path_rch_positions)
      with inp fin have "\<exists>r. r \<in> ranks ?rdg ?acc (p(n+m), n+m)"
	by (blast dest: auto_naccept_then_ranks)
      with spec[OF lst, of m] show "stable_rank p ?rk \<in> ranks ?rdg ?acc (p (n+m), n+m)"
	by (auto intro: LeastI)
    qed

    txt {*
      The path @{text p} exists in the $r$-th dag of the sequence
      (where $r$ is the stable rank of @{text p}).
    *}
    let ?lim_dg = "dag_seq ?rdg ?acc (stable_rank p ?rk)"
    from p have p': "p \<in> paths ?lim_dg"
    proof (rule dag_seq_paths, clarify)
      fix k i
      assume k: "k < stable_rank p ?rk"
	and elim: "(p i, i) \<in> elim_positions (dag_seq ?rdg ?acc k) ?acc k"
      from elim have k': "k \<in> ranks ?rdg ?acc (p i, i)"
	by (auto simp add: ranks_def)
      have "stable_rank p ?rk \<le> ?rk (p i, i)"
	by (rule stable_rank_le_rank)
      with k have "k < (LEAST r. r \<in> ranks ?rdg ?acc (p i, i))"
	by (auto simp add: ranking_def)
      hence "k \<notin> ranks ?rdg ?acc (p i, i)"
	by (rule not_less_Least)
      from this k' show "False" ..
    qed

    txt {*
      In particular, infinitely many positions are accessible from
      the $n$-th state along the path.
    *}
    from p' have "(\<lambda>m. p(n+m)) \<in> paths_from ?lim_dg (p n, n)"
      by (auto simp add: paths_def dest: paths_from_tail)
    hence "range (\<lambda>m. (p(n+m), n+m)) \<subseteq> reachable ?lim_dg (p n, n)"
      by (auto dest: path_then_reachable)
    hence inf: "infinite (reachable (dag_seq ?rdg ?acc (stable_rank p ?rk)) (p n, n))"
    proof (rule infinite_super)
      show "infinite (range (\<lambda>m. (p (n + m), n + m)))"
	by (rule range_inj_infinite, auto intro: inj_onI)
    qed

    txt {* Therefore, the stable rank must be odd. *}
    show "odd (stable_rank p ?rk)"
    proof (rule ccontr)
      assume even: "\<not> odd (stable_rank p ?rk)"
      from is_rank have "stable_rank p ?rk \<in> ranks ?rdg ?acc (p (n+0), n+0)" ..
      with even inf show "False"
	by (auto simp add: ranks_def elim_positions_def endangereds_def)
    qed
  qed
  with rk show ?thesis
    by (auto simp add: odd_rankings_def)
qed


theorem naccept_iff_odd_ranking:
  assumes "finite_state auto"
  shows "(inp \<notin> buchi_language auto) 
         = (\<exists>r. r \<in> odd_rankings (run_dag auto inp) (accept auto))"
using assms by (blast dest: odd_ranking_then_naccept naccept_then_odd_ranking)


(****
subsection {* Construction of the complement automaton *}

text {*
  The complement automaton guesses an odd ranking while reading
  the temporal structure.
*}

types
  'q levelranking = "'q \<Rightarrow> nat option"

constdefs
  buchi_complement: "('q,'a) ndbuchi \<Rightarrow> ('q levelranking \<times> 'q set,'a) ndbuchi"
  buchi_complement auto =
    \<lparr> initial = {(r,{}) | r. \<forall>q \<in> initial auto. \<exists>n. r q = Some n},
      trans 


****)

end
