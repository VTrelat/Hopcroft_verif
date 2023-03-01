theory GBuchi
imports Buchi
begin

section "Generalized non-deterministic Büchi automata"

subsection "Generalized Büchi automata and their languages"

text {*
  Generalized Büchi automata have several acceptance sets 
  instead of a single one, as ordinary Büchi automata. A run
  is accepting iff it passes infinitely often through each of
  the acceptance sets.
*}

record ('q,'a) ndgbuchi = "('q ,'a) ndtable" +
  accept :: "'q set list"  -- "collection of set of accepting states"

definition
 gbuchi_accepting :: "['q set list, 'q word] \<Rightarrow> bool" where
 "gbuchi_accepting FF run \<equiv> 
  \<forall>s < length FF. buchi_accepting (FF!s) run"
 
definition
 gbuchi_accepting' :: "['q set list, 'q word] \<Rightarrow> bool" where
 "gbuchi_accepting' FF run \<equiv> 
  \<forall>s < length FF. buchi_accepting' (FF!s) run"

lemma gbuchi_accepting_accepting' [elim]:
  assumes "gbuchi_accepting FF run"
  shows "gbuchi_accepting' FF run"
using assms by (force simp add: gbuchi_accepting_def gbuchi_accepting'_def)

lemma gbuchi_accepting'_accepting [elim]:
  assumes "gbuchi_accepting' FF run"
  and "\<forall>s < length FF. finite ((FF!s) \<inter> range run)"
  shows "gbuchi_accepting FF run"
using assms by (force simp add: gbuchi_accepting_def gbuchi_accepting'_def)

 
text {*
  The language of a Generalized Büchi automaton is again
  the set of words for which there exists some accepting run
  (w.r.t.\ either acceptance condition).
*}

definition
  gbuchi_language where
  "gbuchi_language auto \<equiv>
   { inp . \<exists>run. nd_run auto inp run \<and> gbuchi_accepting (accept auto) run }"

definition
  gbuchi_language' where
  "gbuchi_language' auto \<equiv>
   { inp . \<exists>run. nd_run auto inp run \<and> gbuchi_accepting' (accept auto) run }"

lemma gbuchi_language_language':
  assumes "x \<in> gbuchi_language auto"
  shows "x \<in> gbuchi_language' auto"
using assms by (auto simp add: gbuchi_language_def gbuchi_language'_def)

lemma gbuchi_language'_language:
  assumes x: "x \<in> gbuchi_language' auto" and fin: "finite_state auto"
  shows "x \<in> gbuchi_language auto"
proof -
  from x obtain run where
    run: "nd_run auto x run" and acc: "gbuchi_accepting' (accept auto) run"
    by (auto simp add: gbuchi_language'_def)
  from fin run have "finite (range run)"
    by (rule finite_state_run)
  with acc have "gbuchi_accepting (accept auto) run"
    by auto
  with run show ?thesis
    by (auto simp add: gbuchi_language_def)
qed

lemma language'_language_bis:
  assumes x: "x \<in> gbuchi_language' auto"
  and fin: "\<forall>s < length (accept auto).finite ((accept auto)!s)"
  shows "x \<in> gbuchi_language auto"
proof -
  from x obtain run where
    run: "nd_run auto x run" and acc: "gbuchi_accepting' (accept auto) run"
    by (auto simp add: gbuchi_language'_def)
  from acc fin have "gbuchi_accepting (accept auto) run"
    by auto
  with run show ?thesis
    by (auto simp add: gbuchi_language_def)
qed


subsection "Closure under intersection"

subsubsection "Product construction"

text {*
  Let $A$ and $B$ be Generalized Büchi automata. Then there is a 
  Generalized Büchi automaton $C$ such as $\LL(C) = \LL(A) \cap \LL(B)$.
  The automaton $C$ is obtained by a standard product construction.
  The list of accepting sets of $C$ is the concatenation of the corresponding
  lists of $A$ and $B$ (after lifting to the product state space).
*}

definition
  gbuchi_inter :: "[('q,'a) ndgbuchi, ('r,'a) ndgbuchi] \<Rightarrow> ('q\<times>'r,'a) ndgbuchi"
  where
   "gbuchi_inter auta autb \<equiv> 
    \<lparr> initial = initial auta \<times> initial autb,
      trans = \<lambda> (qa,qb) a. (trans auta qa a) \<times> (trans autb qb a),
      accept = (map (\<lambda> F. F \<times> (UNIV:: 'r set)) (accept auta)) @ 
               (map (\<lambda> F. (UNIV:: 'q set) \<times> F) (accept autb))
    \<rparr>"

lemma gbuchi_inter_initial [simp]:
  "initial (gbuchi_inter auta autb) = initial auta \<times> initial autb"
by (simp add: gbuchi_inter_def)

lemma gbuchi_inter_trans [simp]:
  "q' \<in> trans (gbuchi_inter auta autb) q a =
   (fst q' \<in> trans auta (fst q) a \<and> snd q' \<in> trans autb (snd q) a)"
by (auto simp add: gbuchi_inter_def split_def intro: PairE[of q'])

lemma gbuchi_inter_accept:
  "accept (gbuchi_inter auta autb) =
   (map (\<lambda> F. F \<times> (UNIV:: 'r set)) (accept auta)) @ 
   (map (\<lambda> F. (UNIV:: 'q set) \<times> F) (accept autb))"
by (simp add: gbuchi_inter_def)

lemma gbuchi_inter_states_of:
  "states_of (gbuchi_inter auta autb) \<subseteq> (states_of auta) \<times> (states_of autb)"
by (auto simp add: gbuchi_inter_def states_of_def)

text {*
  In particular, the product automaton obtained from two
  finite-state automata is again finite-state.
*}

theorem gbuchi_inter_finite_state:
  assumes fina: "finite_state auta" and finb: "finite_state autb"
  shows "finite_state (gbuchi_inter auta autb)"
proof -
  from fina have "finite (states_of auta)"
    by (unfold finite_state_def)
  moreover
  from finb have "finite (states_of autb)"
    by (unfold finite_state_def)
  ultimately
  have "finite ((states_of auta) \<times> (states_of autb))"
    by (rule finite_cartesian_product)
  hence "finite (states_of (gbuchi_inter auta autb))"
    by (rule finite_subset[OF gbuchi_inter_states_of])
  thus ?thesis
    by (unfold finite_state_def)
qed

subsection "Correctness of the product automaton"

text {*
  It is easy to prove that the executions of the product automaton
  project to executions of the component automata. Moreover, any
  accepting run of the product automaton is accepted by the
  component automata (w.r.t.\ the similar acceptance condition).
*}

lemma gbuchi_inter_run_left:
  "nd_execution (gbuchi_inter auta autb) inp run
   \<Longrightarrow> nd_execution auta inp (fst \<circ> run)"
by (rule, auto)

lemma gbuchi_inter_accept_left:
  assumes acc: "gbuchi_accepting (accept (gbuchi_inter auta autb)) run"
  shows "gbuchi_accepting (accept auta) (fst \<circ> run)"
proof (auto simp add: gbuchi_accepting_def)
  fix s
  assume s: "s < length (accept auta)"
  with acc have "buchi_accepting ((accept auta)!s \<times> UNIV) run"
    by (force simp add: gbuchi_accepting_def gbuchi_inter_accept nth_append
              split: split_if_asm)
  thus "buchi_accepting ((accept auta)!s) (fst \<circ> run)"
    by (auto simp add: buchi_accepting_def dest: limit_o)
qed

lemma gbuchi_inter_accept'_left:
  assumes acc: "gbuchi_accepting' (accept (gbuchi_inter auta autb)) run"
  shows "gbuchi_accepting' (accept auta) (fst \<circ> run)"
proof (auto simp add: gbuchi_accepting'_def)
  fix s
  assume s: "s < length (accept auta)"
  with acc have "buchi_accepting' ((accept auta)!s \<times> UNIV) run"
    by (force simp add: gbuchi_accepting'_def gbuchi_inter_accept nth_append
              split: split_if_asm)
  thus "buchi_accepting' ((accept auta)!s) (fst \<circ> run)"
    by (auto simp add: buchi_accepting'_def elim: INFM_mono)
qed

lemma gbuchi_inter_run_right:
  "nd_execution (gbuchi_inter auta autb) inp run
   \<Longrightarrow> nd_execution autb inp (snd \<circ> run)"
by (rule, auto)

lemma gbuchi_inter_accept_right:
  assumes acc: "gbuchi_accepting (accept (gbuchi_inter auta autb)) run"
  shows "gbuchi_accepting (accept autb) (snd \<circ> run)"
proof (auto simp add: gbuchi_accepting_def)
  fix s
  assume s: "s < length (accept autb)"
  with acc have "buchi_accepting (accept (gbuchi_inter auta autb) ! (length (accept auta) + s)) run"
    by (auto simp add: gbuchi_accepting_def gbuchi_inter_accept)
  with s have "buchi_accepting (UNIV \<times> (accept autb)!s) run"
    by (auto simp add: gbuchi_inter_accept nth_append)
  thus "buchi_accepting ((accept autb)!s) (snd \<circ> run)"
    by (auto simp add: buchi_accepting_def dest: limit_o)
qed

lemma gbuchi_inter_accept'_right:
  assumes acc: "gbuchi_accepting' (accept (gbuchi_inter auta autb)) run"
  shows "gbuchi_accepting' (accept autb) (snd \<circ> run)"
proof (auto simp add: gbuchi_accepting'_def)
  fix s
  assume s: "s < length (accept autb)"
  with acc have "buchi_accepting' (accept (gbuchi_inter auta autb) ! (length (accept auta) + s)) run"
    by (auto simp add: gbuchi_accepting'_def gbuchi_inter_accept)
  with s have "buchi_accepting' (UNIV \<times> (accept autb)!s) run"
    by (auto simp add: gbuchi_inter_accept nth_append)
  thus "buchi_accepting' ((accept autb)!s) (snd \<circ> run)"
    by (auto simp add: buchi_accepting'_def elim: INFM_mono)
qed

text {*
  On the other hand, given two executions of the component automata,
  an execution of the product automaton is just the pointwise product
  of the two executions. The product run is accepted by the product
  automaton. Depending on the type of acceptance condition, this may
  require a finiteness assumption.
*}

lemma gbuchi_inter_prod:
  "\<lbrakk> nd_execution auta inp runa; nd_execution autb inp runb \<rbrakk>
   \<Longrightarrow> nd_execution (gbuchi_inter auta autb) inp (\<lambda> n. (runa n, runb n))"
by (rule, auto)

lemma gbuchi_inter_accept'_inter:
  assumes "gbuchi_accepting' (accept auta) runa" and "gbuchi_accepting' (accept autb) runb"
  shows "gbuchi_accepting' (accept (gbuchi_inter auta autb)) (\<lambda>n. (runa n, runb n))"
using assms by (auto simp add: gbuchi_inter_accept gbuchi_accepting'_def buchi_accepting'_def nth_append elim: INFM_mono)

lemma gbuchi_inter_accept_inter:
  assumes acca: "gbuchi_accepting (accept auta) runa" 
  and accb: "gbuchi_accepting (accept autb) runb"
  and fina: "finite (range runa)"
  and finb: "finite (range runb)"
  shows "gbuchi_accepting (accept (gbuchi_inter auta autb)) (\<lambda>n. (runa n, runb n))"
    (is "gbuchi_accepting ?pacc ?prun")
proof -
  from acca have "gbuchi_accepting' (accept auta) runa" ..
  moreover
  from accb have "gbuchi_accepting' (accept autb) runb" ..
  ultimately have "gbuchi_accepting' ?pacc ?prun"
    by (rule gbuchi_inter_accept'_inter)
  moreover
  from fina finb have "finite (range ?prun)"
    by (intro finite_range_prod, auto simp add: image_def)
  ultimately show ?thesis
    by (auto simp add: gbuchi_inter_accept)
qed

(*** 
  original, direct proof with slightly different hypotheses --
  note that runx and finx imply finite (range runx)

lemma gbuchi_inter_accept_inter:
  assumes hypa: "gbuchi_accepting (accept auta) runa" 
  and hypb: "gbuchi_accepting (accept autb) runb"
  and runa: "nd_run auta inpa runa"
  and runb: "nd_run autb inpb runb"
  and fina: "finite_state auta"
  and finb: "finite_state autb"
  shows "gbuchi_accepting (accept (gbuchi_inter auta autb)) (\<lambda>n. (runa n, runb n))"
    (is "gbuchi_accepting ?pacc ?prun")
proof (auto simp add: gbuchi_accepting_def)
  fix s
  assume s: "s < length ?pacc"
    and contra: "limit ?prun \<inter> ?pacc ! s = {}"
  show "False"
  proof (cases "s < length (accept auta)")
    case True
    with hypa have lim: "limit runa \<inter> (accept auta)!s \<noteq> {}"
      by (simp add:  gbuchi_accepting_def)
    then obtain q where q: "q \<in> limit runa \<inter> (accept auta)!s "
      by blast
    from contra True have "limit ?prun \<inter> ((accept auta)!s \<times> UNIV) = {}"
      by (auto simp add:  gbuchi_inter_accept nth_append)
    with q have "\<forall>r. (q,r) \<notin> limit ?prun"
      by auto
    hence fin: "\<forall>r \<in> range runb. finite {n. (runa n, runb n) = (q,r)}"
      by (simp add: limit_def Inf_many_def)
    hence "finite (\<Union>r \<in> range runb. {n. runa n = q \<and> runb n = r})"
      (is "finite ?S")
      by (intro finite_UN_I, auto simp add: finite_state_run[OF finb runb])
    moreover have "?S = {n. runa n = q \<and> (\<exists>r. runb n = r)}"
      by auto
    ultimately have "finite {n. runa n = q}"
      by simp
    with q show ?thesis
      by (simp add: limit_def Inf_many_def)
  next
    case False
    let ?s = "s - length (accept auta)"
    from s have "s < length (accept auta) + length (accept autb)"
      by (simp add: gbuchi_inter_def)
    with False have vs: "?s < length (accept autb)"
      by arith
    with hypb have lim: "limit runb \<inter> (accept autb)!(?s) \<noteq> {}"
      by (simp add:  gbuchi_accepting_def)
    then obtain r where r: "r \<in> limit runb \<inter> (accept autb)!(?s)"
      by blast
    from contra False vs have "limit ?prun \<inter> (UNIV \<times> (accept autb)!(?s)) = {}"
      by (auto simp add:  gbuchi_inter_accept nth_append)
    with r have "\<forall>q. (q,r) \<notin> limit ?prun"
      by auto
    hence fin: "\<forall>q \<in> range runa. finite {n. (runa n, runb n) = (q,r)}"
      by (simp add: limit_def Inf_many_def)
    hence "finite (\<Union>q \<in> range runa. {n. runa n = q \<and> runb n = r})"
      (is "finite ?S")
      by (intro finite_UN_I, auto simp add: finite_state_run[OF fina runa])
    moreover have "?S = {n. (\<exists>q. runa n = q) \<and>  runb n = r}"
      by auto
    ultimately have "finite {n. runb n = r}"
      by simp
    with r show ?thesis
      by (simp add: limit_def Inf_many_def)
  qed
qed
***)

text {*
  The correctness of the product construction is a direct consequence
  of the preceding lemmas.
*}

theorem gbuchi_inter':
  "gbuchi_language' (gbuchi_inter auta autb) = 
   (gbuchi_language' auta) \<inter> (gbuchi_language' autb)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix inp
    assume "inp \<in> ?lhs"
    then obtain run 
      where run: "nd_run (gbuchi_inter auta autb) inp run"
      and   acc: "gbuchi_accepting' (accept (gbuchi_inter auta autb)) run"
      by (auto simp add: gbuchi_language'_def)
    show "inp \<in> ?rhs"
    proof -
      from run have "fst (run 0) \<in> initial auta"
	by (auto simp add: nd_run_def)
      with run have "nd_run auta inp (fst \<circ> run)"
	by (auto simp add: gbuchi_inter_run_left nd_run_def)
      with acc have "inp \<in> gbuchi_language' auta"
	by (auto simp add: gbuchi_language'_def gbuchi_inter_accept'_left)

      moreover
      from run have "snd (run 0) \<in> initial autb"
	by (auto simp add: nd_run_def)
      with run have "nd_run autb inp (snd \<circ> run)"
	by (auto simp add: gbuchi_inter_run_right nd_run_def)
      with acc have "inp \<in> gbuchi_language' autb"
	by (auto simp add: gbuchi_language'_def gbuchi_inter_accept'_right)

      ultimately
      show ?thesis ..
    qed
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix inp assume "inp \<in> ?rhs"
    thus "inp \<in> ?lhs"
    proof
      assume inpa: "inp \<in> gbuchi_language' auta"
         and inpb: "inp \<in> gbuchi_language' autb"
      then obtain runa runb
	where runa: "nd_run auta inp runa" 
	and   acca: "gbuchi_accepting' (accept auta) runa" 
	and   runb: "nd_run autb inp runb" 
	and   accb:  "gbuchi_accepting' (accept autb) runb" 
	by (auto simp add: gbuchi_language'_def)
      let ?prun = "(\<lambda> n. (runa n, runb n))"
      from runa runb 
      have init: "(runa 0, runb 0) \<in> initial (gbuchi_inter auta autb)"
	by (simp add: nd_run_def)
      with runa runb 
      have run: "nd_run (gbuchi_inter auta autb) inp ?prun"
	by (simp add: gbuchi_inter_prod nd_run_def)
      from acca accb
      have "gbuchi_accepting' (accept (gbuchi_inter auta autb)) ?prun"
	by (simp add: gbuchi_inter_accept'_inter)
      with run init show "?thesis"
	by (auto simp add: gbuchi_language'_def)
    qed
  qed
qed

theorem gbuchi_inter :
  assumes fina: "finite_state auta" and finb: "finite_state autb"
  shows "gbuchi_language (gbuchi_inter auta autb)
         = (gbuchi_language auta) \<inter> (gbuchi_language autb)"
proof -
  let ?prod = "gbuchi_inter auta autb"
  from fina finb have "finite_state ?prod"
    by (rule gbuchi_inter_finite_state)
  hence "gbuchi_language ?prod = gbuchi_language' ?prod"
    by (auto elim: gbuchi_language_language' gbuchi_language'_language)
  also have "\<dots> = (gbuchi_language' auta) \<inter> (gbuchi_language' autb)"
    by (rule gbuchi_inter')
  also from fina finb have "\<dots> = (gbuchi_language auta) \<inter> (gbuchi_language autb)"
    by (auto elim: gbuchi_language_language' gbuchi_language'_language)
  finally show ?thesis .
qed


subsubsection "Run dag of the product automaton"

text {*
  The run dag of the product automaton for an input word is the
  ``product'' of the two run dags for the component automata.
*}

lemma gbuchi_inter_run_dag:
  "run_dag (gbuchi_inter auta autb) inp =
   \<lparr> roots = roots (run_dag auta inp) \<times> roots (run_dag autb inp),
     succs = \<lambda>((qa,qb),l). succs (run_dag auta inp) (qa,l) \<times> succs (run_dag autb inp) (qb,l)
   \<rparr>"
by (auto simp add: run_dag_def gbuchi_inter_def split_def)

lemma roots_inter:
  "roots (run_dag (gbuchi_inter auta autb) inp) = roots (run_dag auta inp) \<times> roots (run_dag autb inp)"
by (simp add: gbuchi_inter_run_dag)

lemma reachable_inter_then_left:
  assumes hyp: "pos' \<in> reachable (run_dag (gbuchi_inter auta autb) inp) pos"
  shows "(fst(fst pos'), snd pos') \<in> reachable (run_dag auta inp) (fst(fst pos), snd pos)"
using hyp 
by (induct, auto simp add: gbuchi_inter_run_dag)

lemma reachable_inter_then_left':
  assumes "((qa',qb'),l') \<in> reachable (run_dag (gbuchi_inter auta autb) inp) ((qa,qb),l)"
  shows "(qa',l') \<in> reachable (run_dag auta inp) (qa,l)"
using assms by (fastsimp dest: reachable_inter_then_left)

lemma reachable_inter_then_right:
  assumes hyp: "pos' \<in> reachable (run_dag (gbuchi_inter auta autb) inp) pos"
  shows "(snd(fst pos'), snd pos') \<in> reachable (run_dag autb inp) (snd(fst pos), snd pos)"
using hyp 
by (induct, auto simp add: gbuchi_inter_run_dag)

lemma reachable_inter_then_right':
  assumes "((qa',qb'),l') \<in> reachable (run_dag (gbuchi_inter auta autb) inp) ((qa,qb),l)"
  shows "(qb',l') \<in> reachable (run_dag autb inp) (qb,l)"
using assms by (fastsimp dest: reachable_inter_then_right)

lemma reachable_left_right_then_inter:
  assumes hypa: "posa' \<in> reachable (run_dag auta inp) posa" (is "?arch posa posa'")
  and hypb: "posb' \<in> reachable (run_dag autb inp) posb" (is "?brch posb posb'")
  and pos: "snd posb = snd posa" and pos': "snd posb' = snd posa'"
  shows "((fst posa', fst posb'), snd posa') \<in>
         reachable (run_dag (gbuchi_inter auta autb) inp) ((fst posa, fst posb), snd posa)"
    (is "?irch posa posb posa' posb'")
proof - -- {* need to generalize the induction hypothesis *}
  from hypa
  have "\<forall>posb posb'. snd posb = snd posa \<and> snd posb' = snd posa' \<and> ?brch posb posb'
                     \<longrightarrow> ?irch posa posb posa' posb'"
    (is "?P posa posa'")
  proof (induct)
    show "?P posa posa"
      by (auto dest: reachable_same_level_then_equal')
  next
    let ?adg = "run_dag auta inp"
    let ?bdg = "run_dag autb inp"
    let ?idg = "run_dag (gbuchi_inter auta autb) inp"
    fix nda' posa''
    assume nda': "nda' \<in> succs ?adg posa''"
      and posa'': "posa'' \<in> reachable ?adg posa"
      and ih: "?P posa posa''"
    from posa'' have lvl'': "snd posa \<le> snd posa''"
      by (rule reachable_level)
    show "?P posa (nda', Suc(snd posa''))"
    proof (clarsimp)
      fix ndb' ndb
      assume "?brch (ndb, snd posa) (ndb', Suc(snd posa''))"
      from this lvl''
      have "\<exists>ndb''. (ndb'', snd posa'') \<in> reachable ?bdg (ndb, snd posa)
                     \<and> ndb' \<in> succs ?bdg (ndb'', snd posa'')"
	by (cases, auto)
      then obtain ndb''
	where ndb'': "(ndb'', snd posa'') \<in> reachable ?bdg (ndb, snd posa)"
	and ndb': "ndb' \<in> succs ?bdg (ndb'', snd posa'')"
	by blast
      from ndb'' ih 
      have "((fst posa'', ndb''), snd posa'') \<in> reachable ?idg ((fst posa, ndb), snd posa)"
	by fastsimp
      with nda' ndb'
      show "((nda',ndb'), Suc(snd posa'')) \<in> reachable ?idg ((fst posa, ndb), snd posa)"
	by (intro reachable_succs', auto simp add: gbuchi_inter_run_dag)
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma reachable_left_right_then_inter':
  assumes hypa: "(qa',l') \<in> reachable (run_dag auta inp) (qa,l)"
  and hypb: "(qb',l') \<in> reachable (run_dag autb inp) (qb,l)"
  shows "((qa',qb'),l') \<in> reachable (run_dag (gbuchi_inter auta autb) inp) ((qa,qb),l)"
by (rule reachable_left_right_then_inter[OF hypa hypb, simplified])

theorem rch_positions_inter:
  "rch_positions (run_dag (gbuchi_inter auta autb) inp) =
   {((qa,qb),l) | qa qb l . (qa,l) \<in> rch_positions (run_dag auta inp)
                         \<and> (qb,l) \<in> rch_positions (run_dag autb inp)}"
  (is "?lhs = ?rhs")
proof -
  let ?adg = "run_dag auta inp"
  let ?bdg = "run_dag autb inp"
  let ?idg = "run_dag (gbuchi_inter auta autb) inp"
  have sub: "?lhs \<subseteq> ?rhs"
  proof (clarsimp)
    fix qa qb l
    assume "((qa,qb),l) \<in> ?lhs"
    then obtain rta rtb 
      where "rta \<in> roots ?adg" and rtb: "rtb \<in> roots ?bdg"
      and "((qa,qb),l) \<in> reachable ?idg ((rta,rtb), 0)"
      by (auto simp add: rch_positions_def reachables_def roots_inter)
    thus "(qa,l) \<in> rch_positions ?adg \<and> (qb,l) \<in> rch_positions ?bdg"
      by (auto simp add: rch_positions_def reachables_def
	       elim: reachable_inter_then_left' reachable_inter_then_right')
  qed
  have super: "?rhs \<subseteq> ?lhs"
  proof (clarsimp)
    fix qa qb l
    assume "(qa,l) \<in> rch_positions ?adg" and "(qb,l) \<in> rch_positions ?bdg"
    then obtain rta rtb
      where rta: "rta \<in> roots ?adg" and rtb: "rtb \<in> roots ?bdg"
      and qa: "(qa,l) \<in> reachable ?adg (rta,0)" and qb: "(qb,l) \<in> reachable ?bdg (rtb,0)"
      by (auto simp add: rch_positions_def reachables_def)
    from qa qb have "((qa,qb),l) \<in> reachable ?idg ((rta,rtb),0)"
      by (rule reachable_left_right_then_inter')
    with rta rtb show "((qa,qb),l) \<in> ?lhs"
      by (auto simp add: rch_positions_def reachables_def roots_inter)
  qed
  from sub super show ?thesis ..
qed

corollary gbuchi_inter_slice:
  "slice (run_dag (gbuchi_inter auta autb) inp) lvl =
   (slice (run_dag auta inp) lvl) \<times> (slice (run_dag autb inp) lvl)"
by (simp add: slice_def rch_positions_inter)

(**** 
  From there, derive finiteness of product automaton w.r.t. old
  definition of finiteness.

proof (clarsimp simp add: finite_state_def)
  fix inp
  let ?adg = "run_dag auta inp"
  let ?bdg = "run_dag autb inp"
  let ?idg = "run_dag (gbuchi_inter auta autb) inp"
  have "(fst ` rch_positions ?idg) \<subseteq> (fst ` rch_positions ?adg) \<times> (fst ` rch_positions ?bdg)"
    -- expand "Bex_def" because there is no counterpart for split_paired_Ex
    -- for bounded existential
    by (auto simp add: rch_positions_inter image_def Bex_def)
  with fina finb show "finite (fst ` rch_positions ?idg)"
    by (auto simp add: finite_state_def elim: finite_subset)
qed
****)

text {*
  The product automaton construction therefore preserves bounded
  non-determinism.
*}

theorem gbuchi_inter_bounded_nondet:
  assumes fina: "bounded_nondet auta m" and finb: "bounded_nondet autb n"
  shows "bounded_nondet (gbuchi_inter auta autb) (m*n)"
using assms by (auto simp add: bounded_nondet_def gbuchi_inter_slice mult_le_mono)


subsection {* Equivalence of Büchi and Generalized Büchi automata *}

text {*
  Every Büchi automaton can be viewed as a Generalized Büchi
  automaton with a singleton acceptance condition.
*}

definition
 buchi_gbuchi where (* :: "('q,'a) ndbuchi \<Rightarrow> ('q,'a) ndgbuchi " *)
  "buchi_gbuchi auto \<equiv> 
   \<lparr> initial = initial auto,
     trans =  trans auto, 
     accept = [ndbuchi.accept auto]
   \<rparr>"

lemma buchi_gbuchi_run:
  "nd_run (buchi_gbuchi auto) inp run = nd_run auto inp run"
by (auto simp add: buchi_gbuchi_def nd_run_def nd_execution_def)

lemma buchi_gbuchi_accept:
  "gbuchi_accepting (ndgbuchi.accept (buchi_gbuchi auto)) run = 
   buchi_accepting (ndbuchi.accept auto) run"
by (auto simp add: gbuchi_accepting_def buchi_accepting_def buchi_gbuchi_def)

lemma buchi_gbuchi_accept':
  "gbuchi_accepting' (ndgbuchi.accept (buchi_gbuchi auto)) run = 
   buchi_accepting' (ndbuchi.accept auto) run"
by (auto simp add: gbuchi_accepting'_def buchi_accepting'_def buchi_gbuchi_def)

theorem buchi_gbuchi:
  "gbuchi_language (buchi_gbuchi auto) = buchi_language auto"
by (auto simp add: gbuchi_language_def buchi_language_def
         buchi_gbuchi_run buchi_gbuchi_accept)

theorem buchi_gbuchi':
  "gbuchi_language' (buchi_gbuchi auto) = buchi_language' auto"
by (auto simp add: gbuchi_language'_def buchi_language'_def
         buchi_gbuchi_run buchi_gbuchi_accept')

theorem buchi_gbuchi_finite_state:
  "finite_state auto \<Longrightarrow> finite_state (buchi_gbuchi auto)"
by (auto simp add: finite_state_def states_of_def buchi_gbuchi_def)


text {*
  Generalized Büchi automata recognize the same class of languages
  as standard Büchi automata. In fact, we now show that given a
  generalized Büchi automaton $A$ one can construct a Büchi
  automaton $B$ that accepts the same language. The states of
  $B$ are pairs $(q,n)$ where $q$ is a state of $A$ and $n$
  is a natural number that indicates the index of the accepting set
  of $A$ that $B$ expects to visit next. The transition relation
  of $B$ follows that of $A$ concerning the first component,
  while the second component is incremented by $1$ (modulo the length
  of the list of accepting sets) whenever a state of the accepting
  set designated by the counter is visited. The acceptance condition
  of $B$ requires to infinitely often visit some state $(q,0)$,
  for states $q$ in the $0$-th accepting set of $A$. Due to the
  condition on handling the counter, this implies that all other
  accepting sets will also be visited infinitely often.

  The function @{text gbuchi_buchi} realizes the translation
  described above. A second function, @{text gbuchi_buchi_run},
  is introduced to compute a run of the Büchi automaton $B$
  that corresponds to a given run of the generalized Büchi
  automaton $A$. Moreover, the Büchi automaton obtained from
  a finite-state generalized Büchi automaton is again finite-state.

  Another detail to notice is that this translation does not
  work for generalized Büchi automata with an empty list of
  acceptance sets. In effect, the acceptance condition is trivial
  in that case whereas the translated (Büchi) acceptance
  condition is empty. One could handle this case separately by
  defining the acceptance set of the resulting Büchi automaton
  to be the universal set.
*}


definition
gbuchi_buchi :: "('q,'a) ndgbuchi \<Rightarrow> ('q \<times> nat,'a) ndbuchi " where
  "gbuchi_buchi auto \<equiv> 
   \<lparr> initial = (initial auto) \<times> {0::nat},
     trans = \<lambda>q a. (trans auto (fst q) a) \<times>
                   (if (fst q) \<in> (accept auto)!(snd q)
                    then {(Suc (snd q)) mod length (accept auto)}
                    else {(snd q) mod length (accept auto)}),
     ndbuchi.accept = ((ndgbuchi.accept auto)!0) \<times> {0::nat}
   \<rparr>"

lemma gbuchi_buchi_suc_accept:
  assumes run: "nd_execution (gbuchi_buchi auto) inp run"
  and acc: "fst(run n) \<in> accept auto ! (snd(run n))"
  shows "snd(run(Suc n)) = Suc (snd(run n)) mod length (accept auto)"
proof -
  from run have "run(Suc n) \<in> trans (gbuchi_buchi auto) (run n) (inp n)" ..
  with acc show ?thesis
    by (auto simp add: gbuchi_buchi_def)
qed
                      
lemma gbuchi_buchi_suc_naccept:
  assumes run: "nd_execution (gbuchi_buchi auto) inp run"
  and acc: "fst(run n) \<notin> ndgbuchi.accept auto ! (snd(run n))"
  shows "snd(run(Suc n)) = (snd(run n)) mod length (accept auto)"
proof -
  from run have "run(Suc n) \<in> trans (gbuchi_buchi auto) (run n) (inp n)" ..
  with acc show ?thesis
    by (auto simp add: gbuchi_buchi_def)
qed

lemma gbuchi_buchi_counter:
  assumes "0 < length (accept auto)" and "q' \<in> trans (gbuchi_buchi auto) q a"
  shows "snd q' < length (accept auto)"
using assms by (auto simp add: gbuchi_buchi_def split: split_if_asm)

lemma gbuchi_buchi_counter':
  assumes len: "0 < length (accept auto)"
  and trn: "(q',c') \<in> trans (gbuchi_buchi auto) q a"
  shows "c' < length (accept auto)"
by (rule gbuchi_buchi_counter[OF len trn, simplified])

lemma gbuchi_buchi_states_of:
  assumes "0 < length (accept auto)"
  shows "states_of (gbuchi_buchi auto) \<subseteq> (states_of auto) \<times> {0 ..< length(accept auto)}"
using assms by (auto simp add: states_of_def gbuchi_buchi_def split: split_if_asm)

corollary gbuchi_buchi_finite_state:
  assumes "finite_state auto" and "0 < length (accept auto)"
  shows "finite_state (gbuchi_buchi auto)"
using assms by (auto simp add: finite_state_def finite_subset[OF gbuchi_buchi_states_of])

text {*
  We now study the run dag of the Büchi automaton that results
  from the translation: for any reachable position, the state component
  corresponds to a reachable position of the Generalized Büchi automaton,
  while the counter is bounded by the length of the list of accepting sets.
*}

lemma gbuchi_buchi_run_dag_state:
  assumes hyp: "pos \<in> rch_positions (run_dag (gbuchi_buchi auto) inp)"
  shows "(fst(fst pos), snd pos) \<in> rch_positions (run_dag auto inp)" (is "?rch pos")
proof -
  let ?dg = "run_dag (gbuchi_buchi auto) inp"
  let ?adg = "run_dag auto inp"
  from hyp obtain rt where
    rt: "rt \<in> roots ?adg" and rch: "pos \<in> reachable ?dg ((rt,0),0)"
    by (auto simp add: rch_positions_def reachables_def gbuchi_buchi_def run_dag_def)
  from rch show ?thesis
  proof induct
    from rt show "?rch ((rt,0),0)"
      by (auto simp add: rch_positions_def reachables_def)
  next
    fix nd pos'
    assume nd: "nd \<in> succs ?dg pos'" and ih: "?rch pos'"
    from nd have "fst nd \<in> succs ?adg (fst(fst pos'), snd pos')"
      by (auto simp add: gbuchi_buchi_def run_dag_def)
    with ih show "?rch (nd, Suc(snd pos'))"
      by (auto simp add: rch_positions_def reachables_def)
  qed
qed

corollary gbuchi_buchi_run_dag_state':
  assumes hyp: "((q,n),l) \<in> rch_positions (run_dag (gbuchi_buchi auto) inp)"
  shows "(q,l) \<in> rch_positions (run_dag auto inp)"
by (rule gbuchi_buchi_run_dag_state[OF hyp, simplified])

lemma gbuchi_buchi_run_dag_counter:
  assumes hyp: "pos \<in> rch_positions (run_dag (gbuchi_buchi auto) inp)"
  and len: "0 < length (accept auto)"
  shows "snd(fst pos) < length (accept auto)" (is "?cnt pos")
proof -
  let ?dg = "run_dag (gbuchi_buchi auto) inp"
  let ?adg = "run_dag auto inp"
  from hyp obtain rt where
    rt: "rt \<in> roots ?adg" and rch: "pos \<in> reachable ?dg ((rt,0),0)"
    by (auto simp add: rch_positions_def reachables_def gbuchi_buchi_def run_dag_def)
  from rch show ?thesis
  proof (cases)
    assume "pos = ((rt, 0), 0)"
    with len show "?cnt pos" by simp
  next
    fix nd pos'
    assume "pos = (nd, Suc (snd pos'))" and "nd \<in> succs ?dg pos'"
    with len show "?cnt pos"
      by (auto simp add: run_dag_def gbuchi_buchi_def split: split_if_asm)
  qed
qed

corollary gbuchi_buchi_run_dag_counter':
  assumes hyp: "((q,n),l) \<in> rch_positions (run_dag (gbuchi_buchi auto) inp)"
  and len: "0 < length (accept auto)"
  shows "n < length (accept auto)"
by (rule gbuchi_buchi_run_dag_counter[OF hyp len, simplified])

corollary gbuchi_buchi_slice:
  assumes "0 < length (accept auto)"
  shows "slice (run_dag (gbuchi_buchi auto) inp) lvl \<subseteq>
         (slice (run_dag auto inp) lvl) \<times> {0 ..< length (accept auto)}"
using assms by (auto simp add: slice_def gbuchi_buchi_run_dag_state' gbuchi_buchi_run_dag_counter')

lemma gbuchi_buchi_bounded_nondet:
  assumes len: "0 < length (accept auto)" and fin: "bounded_nondet auto n"
  shows "bounded_nondet (gbuchi_buchi auto) (n * length (accept auto))"
proof (clarsimp simp add: bounded_nondet_def)
  fix inp lvl
  let ?slgb = "slice (run_dag auto inp) lvl"
  let ?slb = "slice (run_dag (gbuchi_buchi auto) inp) lvl"
  from fin have slgb: "finite ?slgb"
    by (simp add: bounded_nondet_def)
  with len have slb: "finite ?slb"
    by (auto intro: finite_subset[OF gbuchi_buchi_slice])
  from fin have cgb: "card ?slgb \<le> n"
    by (simp add: bounded_nondet_def)
  from len slgb have "card ?slb \<le> card (?slgb \<times> {0 ..< length (accept auto)})"
    by (intro card_mono, auto simp add: gbuchi_buchi_slice)
  also have "\<dots> = (card ?slgb) * length (accept auto)"
    by (simp add: card_cartesian_product)
  also from cgb have "\<dots> \<le> n * length (accept auto)"
    by (simp add: mult_le_mono)
  finally show "finite ?slb \<and> card ?slb \<le> n * length (accept auto)"
    by (simp add: slb)
qed

(**** finite-state proof for old definition of finite_state
text {*
  It follows that the Büchi automaton obtained from a finite-state
  Generalized Büchi automaton is again finite-state (although this
  is not obvious from looking just at its type, which includes the
  natural numbers).
*}

theorem gbuchi_buchi_finite_state:
  assumes fin: "finite_state auto"
  and len: "0 < length (accept auto)"
  shows "finite_state (gbuchi_buchi auto)"
proof (clarsimp simp add: finite_state_def)
  fix inp
  let ?adg = "run_dag auto inp"
  let ?bdg = "run_dag (gbuchi_buchi auto) inp"
  have "fst ` (rch_positions ?bdg) \<subseteq> (fst ` (rch_positions ?adg)) \<times> {..< length (accept auto)}"
  proof auto
    fix q n l
    assume "((q,n),l) \<in> rch_positions ?bdg"
    hence "(q,l) \<in> rch_positions ?adg"
      by (rule gbuchi_buchi_run_dag_state')
    hence "fst(q,l) \<in> fst ` (rch_positions ?adg)"
      by (rule imageI)
    thus "q \<in> fst ` (rch_positions ?adg)"
      by simp
  next
    fix q n l
    assume "((q,n),l) \<in> rch_positions ?bdg"
    from this len show "n < length (accept auto)"
      by (rule gbuchi_buchi_run_dag_counter')
  qed
  with fin show "finite (fst ` (rch_positions ?bdg))"
    by (auto elim: finite_subset simp add: finite_state_def)
qed
****)

 
text {*
  We now turn to the executions of the two automata.
  From the definition of the translation it follows immediately
  that for any execution of the translated automaton, the projection
  to the first component is an execution of the original (generalized
  Büchi) automaton, while the second component (the ``counter'')
  is bounded by the length of the list of acceptance sets.
*}

lemma  gbuchi_buchi_exec_fst:
  assumes run: "nd_execution (gbuchi_buchi auto) inp run"
  shows "nd_execution auto inp (fst \<circ> run)"
proof (rule, simp)
  fix n
  from run
  have "run (Suc n) \<in> trans (gbuchi_buchi auto) (run n) (inp n)" ..
  thus "fst (run (Suc n)) \<in> trans auto (fst (run n)) (inp n)"
    by (auto simp add: gbuchi_buchi_def)
qed

lemma gbuchi_buchi_run_fst:
  assumes run: "nd_run (gbuchi_buchi auto) inp run"
  shows "nd_run auto inp (fst \<circ> run)"
proof
  from run show "(fst \<circ> run) 0 \<in> initial auto"
    by (auto simp add: nd_run_def gbuchi_buchi_def)
next
  from run show "nd_execution auto inp (fst \<circ> run)"
    by (simp add: nd_run_def gbuchi_buchi_exec_fst)
qed

lemma gbuchi_buchi_run_snd:
  assumes run: "nd_run (gbuchi_buchi auto) inp run"
  and nzero: "0 < length (accept auto)"
  shows "snd(run n) < length (accept auto)"
    (is "?P n")
proof (cases n)
  case 0
  with run nzero show "?thesis"
    by (auto simp add: nd_run_def gbuchi_buchi_def)
next
  case Suc
  with run nzero show ?thesis
    by (auto simp add: nd_run_def nd_execution_def intro: gbuchi_buchi_counter)
qed
  
text {*
  In any run of the translated Büchi automaton, the ``counter''
  (i.e., the second component of the state) will be stuck for
  as long as no accepting state for the current counter value
  has been entered.
*}

lemma gbuchi_buchi_counter_stable [rule_format]:
  assumes run: "nd_execution (gbuchi_buchi auto) inp run"
  and cnt: "snd (run n) < length (accept auto)"
  shows "(\<forall>i<k. fst(run(n+i)) \<notin> accept auto ! (snd(run n))) \<longrightarrow>
         snd (run (n+k)) = snd (run n)"
        (is "(\<forall>i<k. ?nacc i) \<longrightarrow> ?cnt (n+k) = ?cnt n"
	 is "?P k")
proof (induct k)
  show "?P 0" by simp
next
  fix k
  assume ih: "?P k"
  show "?P (Suc k)"
  proof
    assume nacc: "\<forall>i<Suc k. ?nacc i"
    hence "\<forall>i<k. ?nacc i" by auto
    with ih have "?cnt (n+k) = ?cnt n" ..
    moreover
    from nacc have "?nacc k" by auto
    moreover
    note run cnt
    ultimately
    show "?cnt (n+Suc k) = ?cnt n"
      by (auto simp add: gbuchi_buchi_suc_naccept)
  qed
qed

text {*
  The following definition is intended to compute a run of the
  translated (Büchi) automaton from that of the original
  (generalized Büchi) automaton.
*}

primrec gbuchi_buchi_run :: "'q word \<Rightarrow> 'q set list \<Rightarrow> ('q  \<times> nat) word"
where
  "gbuchi_buchi_run run FS 0 = (run 0, 0)"
| "gbuchi_buchi_run run FS (Suc n) =
      (let cnt = snd (gbuchi_buchi_run run FS n)
       in  (run (Suc n), 
            (if run n \<in> (FS!cnt) then Suc cnt else cnt) mod length FS))"

text {*
  Again, the first component of a state of the translated run
  is just the state of the original run, while the second
  component always points to an element of the list of acceptance sets.
*}

lemma fst_gbuchi_buchi_run [simp]:
  "fst (gbuchi_buchi_run run Fs n) = run n"
by (induct n, auto simp add: Let_def)

lemma snd_gbuchi_buchi_run:
  "0 < length Fs \<Longrightarrow> snd (gbuchi_buchi_run run Fs n) < length Fs"
by (cases n, auto simp add: Let_def)

lemma gbuchi_buchi_run_finite:
  assumes fin: "finite (range run)"
  and nzero: "0 < length Fs"
  shows "finite (range (gbuchi_buchi_run run Fs))"
proof (rule finite_range_prod)
  from fin show "finite (range (fst \<circ> gbuchi_buchi_run run Fs))"
    by (auto simp add: image_def)
next
  from nzero
  have "range (snd \<circ> gbuchi_buchi_run run Fs) \<subseteq> {..< length Fs}"
    by (auto simp add: snd_gbuchi_buchi_run)
  moreover have "finite {..< length Fs}"
    by simp
  ultimately
  show "finite (range (snd \<circ> gbuchi_buchi_run run Fs))"
    by (rule finite_subset)
qed

text {*
  We now prove that given an execution of the generalized Büchi
  automaton, the translated execution is indeed an execution of
  the translated automaton.
*}

lemma gbuchi_buchi_run:
  assumes run: "nd_execution auto inp run"
  shows "nd_execution (gbuchi_buchi auto) inp
                      (gbuchi_buchi_run run (accept auto))"
  (is "nd_execution ?tauto inp ?trun")
proof
  fix n
  from run have "run (Suc n) \<in> trans auto (run n) (inp n)" ..
  thus "?trun (Suc n) \<in> trans ?tauto (?trun n) (inp n)"
    by (auto simp add: gbuchi_buchi_def Let_def)
qed

text {*
  Moreover, if the original run is accepting according to the
  generalized Büchi condition, the translated run will be
  accepted by the translated automaton (in the Büchi sense).
  Here we require the collection of acceptance sets to be
  non-empty. We first prove acceptance w.r.t. the alternative
  condition @{text buchi_accepting'} and then derive the
  condition @{text buchi_accepting} for finite-state automata.
*}

lemma gbuchi_buchi_run_accept':
  assumes acc: "gbuchi_accepting' (ndgbuchi.accept auto) run"
  and  len: "0 < length (accept auto)" 
  shows "buchi_accepting' (ndbuchi.accept (gbuchi_buchi auto))
                          (gbuchi_buchi_run run (ndgbuchi.accept auto))"
proof -
  let ?long = "length (ndgbuchi.accept auto)"
  let ?gbrun = "gbuchi_buchi_run run (ndgbuchi.accept auto)"
  txt {*
    The following step contains the central idea of the proof.
    It shows that every state $(q,i)$ is eventually followed by some
    state $(q',i)$ such that $q'$ belongs to the $i$-th acceptance set
    of the generalized Büchi automaton. It follows that the counter
    will be incremented infinitely often.
  *}
  have ind:
    "\<forall>m. \<exists>n. m \<le> n 
           \<and> fst(?gbrun n) \<in> accept auto ! (snd(?gbrun m)) 
           \<and> snd(?gbrun n) = snd(?gbrun m)"
    (is "\<forall>m. ?A m")
  proof
    fix m
    show "?A m"
    proof (rule ccontr)
      -- "if the generalized Büchi automaton contains at least one acceptance"
      assume contra: "\<not> (?A m)"
      let ?s = "snd (?gbrun m)"
      have "\<forall>k. snd(?gbrun(m+k)) = ?s" (is "\<forall>k. ?P k")
      proof
	fix k
	show "?P k"
	proof (induct k)
	  show "?P 0" by simp
	next
	  fix k
	  assume ih: "?P k"
	  with contra
	  have "run(m+k) \<notin> accept auto ! (?s)"
	    by fastsimp
	  with ih len show "?P (Suc k)"
	    by (simp add: snd_gbuchi_buchi_run Let_def)
	qed
      qed
      with contra
      have "\<forall>k. run(m+k) \<notin> accept auto ! (?s)"
	by fastsimp

      moreover
      from len have "?s < ?long"
	by (rule snd_gbuchi_buchi_run)
      with acc have "\<exists>\<^sub>\<infinity> n. run n \<in> accept auto!(?s)"
	by (simp add: gbuchi_accepting'_def buchi_accepting'_def)
      then obtain n where mn: "m<n" and nacc: "run n \<in> (accept auto)!(?s)"
	by (auto simp add: INFM_nat)
      from mn obtain k where "n = m + (Suc k)"
	by (auto simp add: less_iff_Suc_add)
      with nacc have "\<exists>k. run (m+k) \<in> (accept auto)!(?s)"
	by blast

      ultimately show False
	by blast
    qed
  qed

  txt {* We now prove that infinitely often the counter will be $0$. *}
  have inf0: "\<forall>m. \<exists>n. m\<le>n \<and> snd (?gbrun n) = 0"
  proof
    fix m
    show "\<exists>n. m \<le> n \<and> snd (?gbrun n) = 0"
    proof (rule mod_induct_0)
      show "\<forall>i. i<?long \<longrightarrow>
	        (\<exists>n. m \<le> n \<and> snd (?gbrun n) = i) \<longrightarrow>
                (\<exists>n. m \<le> n \<and> snd (?gbrun n) = (Suc i) mod ?long)"
      proof (clarify)
	fix n
	assume n: "m \<le> n"
	from ind obtain p where p: "n \<le> p"
	  and fstp: "fst(?gbrun p) \<in> (accept auto)!(snd(?gbrun n))"
	  and sndp: "snd(?gbrun p) = snd(?gbrun n)"
	  by blast
	hence "snd(?gbrun (Suc p)) = Suc (snd(?gbrun n)) mod ?long"
	  by (simp add: Let_def)
	moreover
	from n p have "m \<le> Suc p" by simp
	ultimately show "\<exists>p. m \<le> p \<and> snd(?gbrun p) = Suc (snd (?gbrun n)) mod ?long"
	  by blast
      qed
    next
      from len show "snd (?gbrun m) < ?long"
	by (rule snd_gbuchi_buchi_run)
    qed (auto)
  qed

  txt {*
    Applying once again $ind$, we show that infinitely many states
    are accepting for the $0$-th acceptance set when the counter
    is at $0$, thus proving acceptance.
  *}
  have "\<exists>\<^sub>\<infinity>n. ?gbrun n \<in> (accept auto)!0 \<times> {0}"
  proof (auto simp add: INFM_nat_le)
    fix m
    from inf0 obtain n where mn: "m \<le> n" and sndn: "snd (?gbrun n) = 0"
      by blast
    from ind obtain p where np: "n \<le> p"
        and "fst(?gbrun p) \<in> (accept auto)!(snd(?gbrun n))"
        and "snd(?gbrun p) = snd(?gbrun n)"
      by blast
    with sndn have "?gbrun p \<in> (accept auto)!0 \<times> {0}"
      by (subst surjective_pairing, simp)
    with mn np show "\<exists>p. m \<le> p \<and> ?gbrun p \<in> (accept auto)!0 \<times> {0}"
      by (auto elim: le_trans)
  qed
  thus ?thesis
    by (simp add: gbuchi_buchi_def buchi_accepting'_def)
qed

lemma gbuchi_buchi_run_accept:
  assumes acc: "gbuchi_accepting (ndgbuchi.accept auto) run"
  and  len: "0 < length (accept auto)" 
  and fin: "finite (range run)"
  shows "buchi_accepting (ndbuchi.accept (gbuchi_buchi auto))
                         (gbuchi_buchi_run run (ndgbuchi.accept auto))"
proof -
  let ?gbrun = "gbuchi_buchi_run run (ndgbuchi.accept auto)"
  from acc have "gbuchi_accepting' (accept auto) run" ..
  from this len have "buchi_accepting' (ndbuchi.accept (gbuchi_buchi auto)) ?gbrun"
    by (rule gbuchi_buchi_run_accept')
  moreover from fin len have "finite (range ?gbrun)" 
    by (rule gbuchi_buchi_run_finite)
  ultimately show ?thesis by auto
qed

text {*
  Our next goal is to prove that (the projection of) every execution
  that is accepted by the translated automaton satisfies the
  acceptance condition of the original (generalized Büchi) automaton.
*}

lemma gbuchi_buchi_accept'_fst:
  assumes acc: "buchi_accepting' (ndbuchi.accept (gbuchi_buchi auto)) run" 
  and run: "nd_execution (gbuchi_buchi auto) inp run"
  shows "gbuchi_accepting' (ndgbuchi.accept auto) (fst \<circ> run)"
proof (clarsimp simp add: gbuchi_accepting'_def buchi_accepting'_def)
  let ?long = "length (accept auto)"
  fix s
  assume s: "s < ?long"
  from acc have inf0: "\<exists>\<^sub>\<infinity>n. run n \<in> (accept auto)!0 \<times> {0}"
    by (simp add: buchi_accepting'_def gbuchi_buchi_def)
  have "\<exists>\<^sub>\<infinity>n. run n \<in> (accept auto)!s \<times> {s}"
  proof (cases s)
    case 0 with inf0 show ?thesis
      by simp
  next
    fix n
    assume ss: "s = Suc n"
    with s have len1: "1 < ?long"
      by simp
    show ?thesis
    proof (rule ccontr)
      assume "\<not>(\<exists>\<^sub>\<infinity>n. run n \<in> accept auto ! s \<times> {s})" (is "\<not>(Inf_many ?P)")
      with Alm_all_def[of ?P] have  "\<forall>\<^sub>\<infinity>n. run n \<notin> accept auto ! s \<times> {s}" by simp
      then obtain m  where m: "\<forall>n. m<n \<longrightarrow> run n \<notin> accept auto ! s \<times> {s}"
	by (auto simp add: MOST_nat)
      from inf0 obtain k where k: "m<k \<and> run k \<in> (accept auto)!0 \<times> {0::nat}"
	by (fastsimp simp add: INFM_nat)
      txt {*
	We show that the counter will stay between $1$ and $s$,
	contradicting the assumption that it is infinitely $0$.
      *}
      have cnt: "\<forall>p. snd (run (Suc (p+k))) \<in> {1..s}"
      proof
	fix p
	show "snd (run (Suc (p+k))) \<in> {1..s}"
	proof (induct p)
	  case 0
	  from k run len1 ss show ?case
	    by (auto simp add: gbuchi_buchi_suc_accept)
	next
	  case (Suc i)
	  let ?cnt = "snd (run (Suc i+k))"
	  from len1 run have cnt: "?cnt < ?long"
	    by (auto intro: gbuchi_buchi_counter)
	  show ?case
	  proof (cases "fst(run(Suc i + k)) \<in> accept auto ! ?cnt")
	    case False
	    with run Suc cnt show ?thesis
	      by (simp add: gbuchi_buchi_suc_naccept)
	  next
	    case True
	    have "?cnt \<noteq> s"
	    proof
	      assume "?cnt = s"
	      with True have "run(Suc i + k) \<in> accept auto ! s \<times> {s}"
		by (subst surjective_pairing, simp)
	      moreover
	      from k have "m < Suc i + k"
		by auto
	      moreover
	      note m
	      ultimately
	      show "False"
		by auto
	    qed
	    with Suc have cnts: "?cnt \<in> {1 ..< s}"
	      by auto
	    with s have "Suc ?cnt < ?long"
	      by auto
	    with True run cnts show ?thesis
	      by (auto simp add: gbuchi_buchi_suc_accept)
	  qed
	qed
      qed
      from inf0 obtain l
	where l: "k<l" and acc0: "run l \<in> (accept auto)!0 \<times> {0::nat}"
	by (fastsimp simp add: INFM_nat)
      from l obtain p where p: "l = Suc(p+k)"
	by (auto simp add: less_iff_Suc_add)
      from acc0 have "snd(run l) = 0"
	by auto
      moreover
      from p cnt have "snd(run l) \<in> {1..s}"
	by simp
      ultimately
      show "False"
	by simp
    qed
  qed
  thus "\<exists>\<^sub>\<infinity>n. fst (run n) \<in> (accept auto)!s"
    by (auto elim: INFM_mono)
qed

lemma gbuchi_buchi_accept_fst:
  assumes acc: "buchi_accepting (ndbuchi.accept (gbuchi_buchi auto)) run" 
  and run: "nd_execution (gbuchi_buchi auto) inp run"
  and fin: "finite (range run)"
  shows "gbuchi_accepting (ndgbuchi.accept auto) (fst \<circ> run)"
proof -
  from acc have "buchi_accepting' (ndbuchi.accept (gbuchi_buchi auto)) run" ..
  from this run have "gbuchi_accepting' (accept auto) (fst \<circ> run)"
    by (rule gbuchi_buchi_accept'_fst)

  moreover from finite_range_imageI[OF fin] have "finite (range (fst \<circ> run))  " by (auto simp add: comp_def)
  ultimately show ?thesis by auto
qed


text {*
  Finally, we show the correctness of the translation: the language
  defined by the Büchi automaton is the same as that of the original,
  generalized Büchi automaton. As explained above, this is true only
  if the generalized Büchi automaton contains at least one acceptance
  set (and if it is finite-state, depending on the definition of the
  acceptance condition).
*}

theorem gbuchi_buchi':
  assumes len: "0 < length (accept auto)"
  shows   "buchi_language' (gbuchi_buchi auto) = gbuchi_language' auto"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix inp assume inp: "inp \<in> ?lhs"
    then obtain run
      where run: "nd_run (gbuchi_buchi auto) inp run"
      and   acc: "buchi_accepting' (ndbuchi.accept (gbuchi_buchi auto)) run"
      by (auto simp add: buchi_language'_def)
    from run have fst: "nd_run auto inp (fst \<circ> run)"
      by (rule gbuchi_buchi_run_fst)
    with acc run have "gbuchi_accepting' (ndgbuchi.accept auto) (fst \<circ> run)"
      by (auto intro: gbuchi_buchi_accept'_fst simp add: nd_run_def)
    with fst show "inp \<in> ?rhs"
      by (auto simp add: gbuchi_language'_def)
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix inp
    assume "inp \<in> ?rhs"
    then obtain run 
      where run: "nd_run auto inp run"
      and   acc: "gbuchi_accepting' (accept auto) run"   
      by (auto simp add: gbuchi_language'_def)
    let ?gbrun = "gbuchi_buchi_run run (accept auto)"
    from run
    have exec: "nd_execution (gbuchi_buchi auto) inp ?gbrun"
      by (fastsimp intro: gbuchi_buchi_run simp add: nd_run_def)
    from run
    have init: "?gbrun 0 \<in> initial (gbuchi_buchi auto)"
      by (simp add: gbuchi_buchi_def nd_run_def)
    from acc len
    have "buchi_accepting' (ndbuchi.accept (gbuchi_buchi auto)) ?gbrun"
      by (rule gbuchi_buchi_run_accept')
    with exec init show "inp \<in> ?lhs"
      by (auto simp add: buchi_language'_def nd_run_def)
  qed
qed

theorem gbuchi_buchi :
  assumes fin: "finite_state auto"
  and     len: "0 < length (accept auto)"
  shows   "buchi_language (gbuchi_buchi auto) = gbuchi_language auto"
  (is "?lhs = ?rhs")
proof -
  from fin len have "finite_state (gbuchi_buchi auto)"
    by (rule gbuchi_buchi_finite_state)
  hence "?lhs = buchi_language' (gbuchi_buchi auto)"
    by (auto elim: language_language' language'_language)
  also from len have "\<dots> = gbuchi_language' auto"
    by (rule gbuchi_buchi')
  also from fin have "\<dots> = gbuchi_language auto"
    by (auto elim: gbuchi_language_language' gbuchi_language'_language)
  finally show ?thesis .
qed


subsection "Closure of Büchi automata under intersection"

text {*
  Assembling the results, it follows that the class of languages
  defined by (finite-state) Büchi automata is also closed unter
  intersection: we can just translate to generalized Büchi automata,
  apply the product construction, and translate back.
*}

theorem buchi_inter':
  "buchi_language'
     (gbuchi_buchi (gbuchi_inter (buchi_gbuchi auta) (buchi_gbuchi autb)))
   = buchi_language' auta \<inter> buchi_language' autb"
  (is "?lhs = ?rhs")
proof -
  let ?gba = "buchi_gbuchi auta"
  let ?gbb = "buchi_gbuchi autb"
  let ?gbi = "gbuchi_inter ?gba ?gbb"
  have "0 < length (accept ?gbi)"
    by (simp add: buchi_gbuchi_def gbuchi_inter_def)
  hence "?lhs = gbuchi_language' ?gbi"
    by (rule gbuchi_buchi')
  also have "\<dots> = (gbuchi_language' ?gba) \<inter> (gbuchi_language' ?gbb)"
    by (rule gbuchi_inter')
  finally show ?thesis
    by (simp add: buchi_gbuchi')
qed

theorem buchi_inter:
  assumes fina: "finite_state auta" and finb: "finite_state autb"
  shows "buchi_language
          (gbuchi_buchi (gbuchi_inter (buchi_gbuchi auta) (buchi_gbuchi autb)))
         = buchi_language auta \<inter> buchi_language autb"
  (is "?lhs = ?rhs")
proof -
  let ?gba = "buchi_gbuchi auta"
  let ?gbb = "buchi_gbuchi autb"
  let ?gbi = "gbuchi_inter ?gba ?gbb"
  from fina have fingba: "finite_state ?gba"
    by (rule buchi_gbuchi_finite_state)
  from finb have fingbb: "finite_state ?gbb"
    by (rule buchi_gbuchi_finite_state)
  from fingba fingbb have fingbi: "finite_state ?gbi"
    by (rule gbuchi_inter_finite_state)
  have nzero: "0 < length (accept ?gbi)"
    by (simp add: buchi_gbuchi_def gbuchi_inter_def)
  from fingbi nzero
  have "?lhs = gbuchi_language ?gbi"
    by (rule gbuchi_buchi)
  also from fingba fingbb
  have "\<dots> = (gbuchi_language ?gba) \<inter> (gbuchi_language ?gbb)"
    by (rule gbuchi_inter)
  finally show ?thesis
    by (simp add: buchi_gbuchi)
qed

end
