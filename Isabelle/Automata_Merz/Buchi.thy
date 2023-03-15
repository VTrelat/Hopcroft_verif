theory Buchi
imports NDTable
begin

section {* Non-deterministic Büchi automata *}

subsection {* Büchi automata and their languages *}

text {*
  Non-deterministic Büchi automata extend non-deterministic
  transition tables by an acceptance condition defined in
  terms of a set of accepting states. A run is accepting iff
  it passes infinitely often through some accepting state.

  This informal requirement can be interpreted in two different
  ways:
  \begin{enumerate}
  \item There should be some accepting state that appears
    infinitely often in a run for that run to be accepted.
  \item There should be infinitely many positions in the run
    that correspond to accepting states.
  \end{enumerate}
  These two interpretations agree for finite-state automata,
  but not necessarily for infinite-state ones. We formalize
  both interpretations and study their impact on the
  subsequent theory.
*}

record ('q,'a) ndbuchi = "('q,'a) ndtable" +
  accept :: "'q set"  -- "set of accepting states"

definition
  buchi_accepting :: "['q set, 'q word] \<Rightarrow> bool" where
  "buchi_accepting F run \<equiv> (limit run) \<inter> F \<noteq> {}"

definition
  buchi_accepting' :: "['q set, 'q word] \<Rightarrow> bool" where
  "buchi_accepting' F run \<equiv> \<exists>\<^sub>\<infinity>n. run n \<in> F"

lemma accepting_accepting' [elim]:
  assumes acc: "buchi_accepting F run"
  shows "buchi_accepting' F run"
proof -
  from acc obtain q where "q \<in> F" and  "\<exists>\<^sub>\<infinity>n. run n = q"
    by (auto simp add: buchi_accepting_def limit_def)
  thus ?thesis
    by (auto simp add: buchi_accepting'_def elim:INFM_mono)
qed

text {*
  The reverse implication is true under some finiteness condition;
  for example, if $F$ is finite or if the run contains only
  finitely many states. The following lemma states the precise condition.
*}

lemma accepting'_accepting [elim]:
  assumes acc': "buchi_accepting' F run" and fin: "finite (F \<inter> range run)"
  shows "buchi_accepting F run"
proof (rule ccontr)
  assume contr: "\<not>?thesis"
  hence "\<forall>q \<in> F. finite (run -` {q})"
    by (auto simp add: buchi_accepting_def limit_vimage)
  hence "\<forall>q \<in> F \<inter> range run. finite (run -` {q})"
    by blast
  with fin have "finite (\<Union>q \<in> F \<inter> range run. run -` {q})"
    by auto
  with acc' show "False"
    by (auto simp add: buchi_accepting'_def Inf_many_def vimage_def UNION_eq)
qed

text {*
  The language of a B\"uchi automaton is the set of words
  for which there exists some accepting run (under either
  interpretation).
*}

definition
  buchi_language where
  "buchi_language auto \<equiv>
   { inp . \<exists>run. nd_run auto inp run 
               \<and> buchi_accepting (accept auto) run }"

definition
  buchi_language' where
  "buchi_language' auto \<equiv>
   { inp . \<exists>run. nd_run auto inp run 
               \<and> buchi_accepting' (accept auto) run }"

lemma language_language':
  assumes "x \<in> buchi_language auto"
  shows "x \<in> buchi_language' auto"
using assms by (auto simp add: buchi_language_def buchi_language'_def)

lemma language'_language:
  assumes x: "x \<in> buchi_language' auto" and fin: "finite_state auto"
  shows "x \<in> buchi_language auto"
proof -
  from x obtain run where
    run: "nd_run auto x run" and acc: "buchi_accepting' (accept auto) run"
    by (auto simp add: buchi_language'_def)
  from fin run have "finite (range run)"
    by (rule finite_state_run)
  with acc have "buchi_accepting (accept auto) run"
    by auto
  with run show ?thesis
    by (auto simp add: buchi_language_def)
qed

lemma language'_language_bis:
  assumes x: "x \<in> buchi_language' auto" and fin: "finite (accept auto)"
  shows "x \<in> buchi_language auto"
proof -
  from x obtain run where
    run: "nd_run auto x run" and acc: "buchi_accepting' (accept auto) run"
    by (auto simp add: buchi_language'_def)
  from acc fin have "buchi_accepting (accept auto) run"
    by auto
  with run show ?thesis
    by (auto simp add: buchi_language_def)
qed

text {*
  The following theorem shows that the language of a Büchi
  automaton is non-empty if and only if there exist an initial state $q$
  and an accepting state $q'$ such that $q'$ is reachable from both $q$
  and (non-trivially) from itself. This result underlies the implementation
  of model checkers for linear-time temporal logic.
*}

lemma buchi_loop_nonempty:
  assumes ini: "q \<in> initial auto"
  and acc: "q' \<in> accept auto"
  and q: "q - auto \<rightarrow>\<^sup>* q'"
  and q': "q' - auto \<rightarrow>\<^sup>+ q'"
  shows "buchi_language auto \<noteq> {}"
proof -
  from q obtain w rw
    where rw: "nd_exec_fragment auto w rw"
    and rw0:  "rw!0 = q" and rwn: "rw ! length w = q'"
    by (blast dest: acc_star_exec)
  from q' obtain x rx
    where rx: "nd_exec_fragment auto x rx"
    and rx0: "rx!0 = q'" and rxn: "rx ! length x = q'"
    and lenx: "0 < length x"
    by (blast dest: acc_plus_exec)

  -- "abbreviations that make the following proof more readable"
  let ?rxm = "take (length x) rx"
  let ?loop = "?rxm\<^sup>\<omega>"
  let ?run = "rw \<frown> (suffix 1 ?loop)"

  from lenx rx have lenrxm: "0 < length ?rxm"
    by (simp add: nd_exec_fragment_length)

  -- "first goal: @{text ?run} is an execution"
  from rx rx0 rxn lenx have "nd_execution auto x\<^sup>\<omega> ?loop"
    by (auto elim: loop_execution)
  moreover
  from lenrxm rx0 have "?loop 0 = q'"
    by simp
  moreover note rw rwn
  ultimately
  have run_ex: "nd_execution auto (w \<frown> x\<^sup>\<omega>) ?run"
    by (fastsimp elim: exec_conc)

  -- "moreover, it is a run (starting in initial state)"
  from rw have "?run 0 = rw!0"
    by (simp add: nd_exec_fragment_length conc_fst)
  with rw0 ini have "?run 0 \<in> initial auto"
    by simp
  with run_ex have run: "nd_run auto (w \<frown> x\<^sup>\<omega>) ?run"
    by blast

  -- "finally, @{text ?run} is accepting"
  from lenrxm have "limit ?run = set ?rxm"
    by simp
  moreover
  from lenrxm lenx have "rx!0 = ?rxm!0"
    by auto
  with lenrxm have "rx!0 \<in> set ?rxm"
    by (simp only: nth_mem)
  moreover
  note rx0
  ultimately
  have "q' \<in> limit ?run"
    by simp
  with acc have "buchi_accepting (accept auto) ?run"
    by (auto simp add: buchi_accepting_def)

  with run show ?thesis
    by (auto simp add: buchi_language_def)
qed

lemma buchi_nonempty_loop:
  assumes nempty: "buchi_language auto \<noteq> {}"
  shows "\<exists>p q. p \<in> initial auto \<and> q \<in> accept auto
              \<and> p - auto \<rightarrow>\<^sup>* q \<and> q - auto \<rightarrow>\<^sup>+ q"
proof -
  from nempty obtain inp run
    where run: "nd_run auto inp run"
      and acc: "buchi_accepting (accept auto) run"
    by (auto simp add: buchi_language_def)
  from run have initial: "run 0 \<in> initial auto" ..
  from acc obtain q
    where q_lim: "q \<in> limit run" and q_acc: "q \<in> accept auto"
    by (auto simp add: buchi_accepting_def)

  -- "$q$ is in the limit: fix two occurrences of $q$ in $run$"
  from q_lim obtain i where i: "run i = q"
    by (auto simp add: limit_def INFM_nat)
  from q_lim obtain j where j: "i<j \<and> run j = q"
    by (auto simp add: limit_def INFM_nat)

  from run have reach1: "run 0 - auto \<rightarrow>\<^sup>* run i"
    by (auto intro: nd_execution_acc_star)
  from run j have reach2: "run i - auto \<rightarrow>\<^sup>+ run j"
    by (auto intro: nd_execution_acc_plus)

  from initial q_acc i j reach1 reach2
  show ?thesis by auto
qed

theorem buchi_nonempty_iff_loop:
  "(buchi_language auto \<noteq> {}) =
   (\<exists>p q. p \<in> initial auto \<and> q \<in> accept auto
          \<and> p - auto \<rightarrow>\<^sup>* q \<and> q - auto \<rightarrow>\<^sup>+ q)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs thus ?rhs
    by (rule buchi_nonempty_loop)
next
  assume ?rhs thus ?lhs
    by (blast intro: buchi_loop_nonempty del: notI)
qed

text {*
  For the alternative definition of Büchi acceptance, the analogous
  theorem is true only for finite-state automata.
*}

theorem buchi'_nonempty_iff_loop:
  assumes fin: "finite_state auto"
  shows "(buchi_language' auto \<noteq> {}) =
   (\<exists>p q. p \<in> initial auto \<and> q \<in> accept auto
          \<and> p - auto \<rightarrow>\<^sup>* q \<and> q - auto \<rightarrow>\<^sup>+ q)"
  (is "?lhs = ?rhs")
proof -
  from fin have "buchi_language' auto = buchi_language auto"
    by (auto elim: language_language' language'_language)
  thus ?thesis
    by (simp add: buchi_nonempty_iff_loop)
qed


subsection {* Union of Büchi automata *}

text {*
  The class of languages definable by Büchi automata is closed
  under set operations. Here we cover the case of set union;
  intersection and complement are harder and will be proven in
  separate theories. The idea is to take the (disjoint)
  union of the two automata to obtain an automaton accepting the
  union of two languages.
*}

definition
  buchi_union where
  "buchi_union auta autb \<equiv>
   \<lparr> initial = initial auta <+> initial autb,
     trans = \<lambda> src a. case src of Inl x \<Rightarrow> Inl ` (trans auta x a)
                                | Inr y \<Rightarrow> Inr ` (trans autb y a),
     accept = accept auta <+> accept autb
   \<rparr>"

lemma buchi_union_states_of:
  "states_of (buchi_union auta autb) = (states_of auta) <+> (states_of autb)"
  (is "?lhs = ?rhs")
proof -
  let ?un = "buchi_union auta autb"
  have init: "initial ?un = (initial auta) <+> (initial autb)"
    by (simp add: buchi_union_def)
  have "(\<Union> qr a. trans ?un qr a) = 
        (\<Union>q a. trans ?un (Inl q) a) \<union> (\<Union>r a. trans ?un (Inr r) a)"
    by (simp add: Union_sum)
  also have "\<dots> = (\<Union>q a. Inl ` (trans auta q a)) \<union> (\<Union>r a. Inr ` (trans autb r a))"
    by (simp add: buchi_union_def)
  finally show ?thesis
    by (auto simp add: init states_of_def image_def)
qed


text {*
  To prove the correctness of this construction, we first show that
  any run of one of the component automata can be lifted to a
  run of the union. Second, we'll show that any run of the union
  is in fact of this form.
*}

lemma buchi_union_lift_left:
  assumes run: "nd_execution auta inp run"
  shows "nd_execution (buchi_union auta autb) inp (Inl \<circ> run)"
proof (rule, simp)
  fix n
  from run
  have "run (Suc n) \<in> trans auta (run n) (inp n)" ..
  thus "Inl (run (Suc n)) 
        \<in> trans (buchi_union auta autb) (Inl (run n)) (inp n)"
    by (simp add: buchi_union_def)
qed

lemma buchi_union_lift_right:
  assumes run: "nd_execution autb inp run"
  shows "nd_execution (buchi_union auta autb) inp (Inr \<circ> run)"
proof (rule, simp)
  fix n
  from run
  have "run (Suc n) \<in> trans autb (run n) (inp n)" ..
  thus "Inr (run (Suc n)) 
        \<in> trans (buchi_union auta autb) (Inr (run n)) (inp n)"
    by (simp add: buchi_union_def)
qed

lemma buchi_union_run_left:
  assumes run: "nd_execution (buchi_union auta autb) inp run"
  and start: "run 0 \<in> range Inl"
  shows "\<exists>runa. nd_execution auta inp runa \<and> run = Inl \<circ> runa"
proof -
  let ?ra = "\<lambda>n. THE q. run n = Inl q"
  have inl: "\<forall>n. run n = Inl (?ra n)"
  proof
    fix n
    show "run n = Inl (?ra n)"
    proof (induct n)
      from start show "run 0 = Inl (?ra 0)" by auto
    next
      fix m
      assume ih: "run m = Inl (?ra m)"
      from run
      have "run (Suc m) \<in> trans (buchi_union auta autb) (run m) (inp m)" ..
      with ih show "run (Suc m) = Inl (?ra (Suc m))"
	by (auto simp add: buchi_union_def split add: sum.splits)
    qed
  qed
  moreover 
  have "\<forall>n. ?ra (Suc n) \<in> trans auta (?ra n) (inp n)"
  proof
    fix n
    from run
    have "run (Suc n) \<in> trans (buchi_union auta autb) (run n) (inp n)" ..
    also from inl obtain x where "run n = Inl x" by blast
    hence "run n \<notin> range Inr" by auto
    ultimately show "?ra (Suc n) \<in> trans auta (?ra n) (inp n)"
      by (auto simp add: buchi_union_def split add: sum.splits)
  qed
  ultimately have "nd_execution auta inp ?ra \<and> run = Inl \<circ> ?ra"
    by (auto intro: ext)
  thus ?thesis by blast
qed

lemma buchi_union_run_right:
  assumes run: "nd_execution (buchi_union auta autb) inp run"
  and start: "run 0 \<in> range Inr"
  shows "\<exists>runb. nd_execution autb inp runb \<and> run = Inr \<circ> runb"
proof -
  let ?rb = "\<lambda>n. THE q. run n = Inr q"
  have inl: "\<forall>n. run n = Inr (?rb n)"
  proof
    fix n
    show "run n = Inr (?rb n)"
    proof (induct n)
      from start show "run 0 = Inr (?rb 0)" by auto
    next
      fix m
      assume ih: "run m = Inr (?rb m)"
      from run
      have "run (Suc m) \<in> trans (buchi_union auta autb) (run m) (inp m)" ..
      with ih show "run (Suc m) = Inr (?rb (Suc m))"
	by (auto simp add: buchi_union_def split add: sum.splits)
    qed
  qed
  moreover 
  have "\<forall>n. ?rb (Suc n) \<in> trans autb (?rb n) (inp n)"
  proof
    fix n
    from run
    have "run (Suc n) \<in> trans (buchi_union auta autb) (run n) (inp n)" ..
    also from inl obtain x where "run n = Inr x" by blast
    hence "run n \<notin> range Inl" by auto
    ultimately show "?rb (Suc n) \<in> trans autb (?rb n) (inp n)"
      by (auto simp add: buchi_union_def split add: sum.splits)
  qed
  ultimately have "nd_execution autb inp ?rb \<and> run = Inr \<circ> ?rb"
    by (auto intro: ext)
  thus ?thesis by blast
qed

text {*
  Moreover, the acceptance conditions are transferred appropriately.
  (Because of the above lemmas, it is enough to show this for
  ``lifted'' runs.)
*}

lemma buchi_union_accept_left:
  "buchi_accepting (accept (buchi_union auta autb)) (Inl \<circ> run)
   = buchi_accepting (accept auta) run"
by (auto simp add: inj_Inl buchi_accepting_def buchi_union_def)

lemma buchi_union_accept_right:
  "buchi_accepting (accept (buchi_union auta autb)) (Inr \<circ> run)
   = buchi_accepting (accept autb) run"
by (auto simp add: inj_Inr buchi_accepting_def buchi_union_def)

lemma buchi_union_accept'_left:
  "buchi_accepting' (accept (buchi_union auta autb)) (Inl \<circ> run)
   = buchi_accepting' (accept auta) run"
by (auto simp add: inj_Inl buchi_accepting'_def buchi_union_def
         elim: INFM_mono)

lemma buchi_union_accept'_right:
  "buchi_accepting' (accept (buchi_union auta autb)) (Inr \<circ> run)
   = buchi_accepting' (accept autb) run"
by (auto simp add: inj_Inr buchi_accepting'_def buchi_union_def
         elim: INFM_mono)

text {*
  The correctness of the construction of the union automaton
  follows, under either acceptance condition.
*}

theorem buchi_union:
  "buchi_language (buchi_union auta autb)
   = (buchi_language auta) \<union> (buchi_language autb)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix inp
    assume "inp \<in> ?lhs"
    then obtain run 
      where run: "nd_run (buchi_union auta autb) inp run
                  \<and> buchi_accepting (accept (buchi_union auta autb)) run"
      by (auto simp add: buchi_language_def)
    from run have "run 0 \<in> (initial auta <+> initial autb)"
      by (simp add: nd_run_def buchi_union_def)
    hence "run 0 \<in> Inl ` (initial auta) \<or> run 0 \<in> Inr ` (initial autb)"
      by auto
    thus "inp \<in> ?rhs"
    proof
      assume start: "run 0 \<in> Inl ` (initial auta)"
      with run obtain runa
	where runa: "nd_execution auta inp runa \<and> run = Inl \<circ> runa"
	by (fastsimp intro: buchi_union_run_left simp add: nd_run_def)
      with start have aini: "runa 0 \<in> initial auta" by auto
      from run runa have "buchi_accepting (accept auta) runa"
	by (simp add: buchi_union_accept_left)
      with runa aini
      have "inp \<in> buchi_language auta"
	by (auto simp add: buchi_language_def nd_run_def)
      thus ?thesis ..
    next
      assume start: "run 0 \<in> Inr ` (initial autb)"
      with run obtain runb
	where runb: "nd_execution autb inp runb \<and> run = Inr \<circ> runb"
	by (fastsimp intro: buchi_union_run_right simp add: nd_run_def)
      with start have bini: "runb 0 \<in> initial autb" by auto
      from run runb have "buchi_accepting (accept autb) runb"
	by (simp add: buchi_union_accept_right)
      with runb bini
      have "inp \<in> buchi_language autb"
	by (auto simp add: buchi_language_def nd_run_def)
      thus ?thesis ..
    qed
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix inp assume "inp \<in> ?rhs"
    thus "inp \<in> ?lhs"
    proof
      assume "inp \<in> buchi_language auta"
      then obtain run
	where run: "nd_run auta inp run \<and> buchi_accepting (accept auta) run"
	by (auto simp add: buchi_language_def)
      from run have "run 0 \<in> initial auta"
	by (simp add: nd_run_def)
      hence "Inl (run 0) \<in> initial (buchi_union auta autb)"
	by (auto simp add: buchi_union_def)
      with run 
      have exec: "nd_run (buchi_union auta autb) inp (Inl \<circ> run)"
	by (simp add: nd_run_def buchi_union_lift_left)
      moreover from run 
      have "buchi_accepting (accept (buchi_union auta autb)) (Inl \<circ> run)"
	by (simp add: buchi_union_accept_left)
      ultimately show "inp \<in> ?lhs"
	by (auto simp add: buchi_language_def)
    next
      assume "inp \<in> buchi_language autb"
      then obtain run
	where run: "nd_run autb inp run \<and> buchi_accepting (accept autb) run"
	by (auto simp add: buchi_language_def)
      from run have "run 0 \<in> initial autb"
	by (simp add: nd_run_def)
      hence "Inr (run 0) \<in> initial (buchi_union auta autb)"
	by (auto simp add: buchi_union_def)
      with run 
      have exec: "nd_run (buchi_union auta autb) inp (Inr \<circ> run)"
	by (simp add: nd_run_def buchi_union_lift_right)
      moreover from run 
      have "buchi_accepting (accept (buchi_union auta autb)) (Inr \<circ> run)"
	by (simp add: buchi_union_accept_right)
      ultimately show "inp \<in> ?lhs"
	by (auto simp add: buchi_language_def)
    qed
  qed
qed

theorem buchi_union':
  "buchi_language' (buchi_union auta autb)
   = (buchi_language' auta) \<union> (buchi_language' autb)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix inp
    assume "inp \<in> ?lhs"
    then obtain run 
      where run: "nd_run (buchi_union auta autb) inp run"
        and acc: "buchi_accepting' (accept (buchi_union auta autb)) run"
      by (auto simp add: buchi_language'_def)
    from run have "run 0 \<in> (initial auta <+> initial autb)"
      by (simp add: nd_run_def buchi_union_def)
    hence "run 0 \<in> Inl ` (initial auta) \<or> run 0 \<in> Inr ` (initial autb)"
      by auto
    thus "inp \<in> ?rhs"
    proof
      assume start: "run 0 \<in> Inl ` (initial auta)"
      with run obtain runa
	where runa: "nd_execution auta inp runa \<and> run = Inl \<circ> runa"
	by (fastsimp intro: buchi_union_run_left simp add: nd_run_def)
      with start have aini: "runa 0 \<in> initial auta" by auto
      from runa acc have "buchi_accepting' (accept auta) runa"
	by (simp add: buchi_union_accept'_left)
      with runa aini
      have "inp \<in> buchi_language' auta"
	by (auto simp add: buchi_language'_def nd_run_def)
      thus ?thesis ..
    next
      assume start: "run 0 \<in> Inr ` (initial autb)"
      with run obtain runb
	where runb: "nd_execution autb inp runb \<and> run = Inr \<circ> runb"
	by (fastsimp intro: buchi_union_run_right simp add: nd_run_def)
      with start have bini: "runb 0 \<in> initial autb" by auto
      from runb acc have "buchi_accepting' (accept autb) runb"
	by (simp add: buchi_union_accept'_right)
      with runb bini
      have "inp \<in> buchi_language' autb"
	by (auto simp add: buchi_language'_def nd_run_def)
      thus ?thesis ..
    qed
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof
    fix inp assume "inp \<in> ?rhs"
    thus "inp \<in> ?lhs"
    proof
      assume "inp \<in> buchi_language' auta"
      then obtain run
	where run: "nd_run auta inp run" and acc:"buchi_accepting' (accept auta) run"
	by (auto simp add: buchi_language'_def)
      from run have "run 0 \<in> initial auta"
	by (simp add: nd_run_def)
      hence "Inl (run 0) \<in> initial (buchi_union auta autb)"
	by (auto simp add: buchi_union_def)
      with run have exec: "nd_run (buchi_union auta autb) inp (Inl \<circ> run)"
	by (simp add: nd_run_def buchi_union_lift_left)
      moreover from acc
      have "buchi_accepting' (accept (buchi_union auta autb)) (Inl \<circ> run)"
	by (simp add: buchi_union_accept'_left)
      ultimately show "inp \<in> ?lhs"
	by (auto simp add: buchi_language'_def)
    next
      assume "inp \<in> buchi_language' autb"
      then obtain run
	where run: "nd_run autb inp run" and acc:"buchi_accepting' (accept autb) run"
	by (auto simp add: buchi_language'_def)
      from run have "run 0 \<in> initial autb"
	by (simp add: nd_run_def)
      hence "Inr (run 0) \<in> initial (buchi_union auta autb)"
	by (auto simp add: buchi_union_def)
      with run have exec: "nd_run (buchi_union auta autb) inp (Inr \<circ> run)"
	by (simp add: nd_run_def buchi_union_lift_right)
      moreover from acc
      have "buchi_accepting' (accept (buchi_union auta autb)) (Inr \<circ> run)"
	by (simp add: buchi_union_accept'_right)
      ultimately show "inp \<in> ?lhs"
	by (auto simp add: buchi_language'_def)
    qed
  qed
qed

text {*
  The run dag of the union automaton is obtained as the ``disjoint
  union'' of the corresponding run dags of the component automata.
*}

lemma buchi_union_run_dag:
  "run_dag (buchi_union auta autb) inp =
   \<lparr> roots = (roots (run_dag auta inp)) <+> (roots (run_dag autb inp)),
     succs = \<lambda>(q,l). case q of Inl x \<Rightarrow> Inl ` (succs (run_dag auta inp) (x,l))
                             | Inr y \<Rightarrow> Inr ` (succs (run_dag autb inp) (y,l))
  \<rparr>"
by (auto simp add: buchi_union_def run_dag_def cong del: sum.weak_case_cong)


lemma reachable_left_then_union:
  assumes hyp: "pos' \<in> reachable (run_dag auta inp) pos"
  shows "(Inl (fst pos'), snd pos') \<in> 
         reachable (run_dag (buchi_union auta autb) inp) (Inl (fst pos), snd pos)"
    (is "?rch pos pos'")
using hyp proof induct
  show "?rch pos pos" ..
next
  fix nd pos''
  assume pos'': "?rch pos pos''"
    and nd: "nd \<in> succs (run_dag auta inp) pos''"
  from nd have "Inl nd \<in> succs (run_dag (buchi_union auta autb) inp) (Inl(fst pos''), snd pos'')"
    by (auto simp add: buchi_union_run_dag)
  with pos'' show "?rch pos (nd, Suc(snd pos''))"
    by auto
qed

lemma reachable_left_then_union':
  assumes hyp: "(q',l') \<in> reachable (run_dag auta inp) (q,l)"
  shows "(Inl q', l') \<in> reachable (run_dag (buchi_union auta autb) inp) (Inl q, l)"
proof -
  from reachable_left_then_union[OF hyp] show ?thesis by auto
qed

lemma reachable_right_then_union:
  assumes hyp: "pos' \<in> reachable (run_dag autb inp) pos"
  shows "(Inr (fst pos'), snd pos') \<in> 
         reachable (run_dag (buchi_union auta autb) inp) (Inr (fst pos), snd pos)"
    (is "?rch pos pos'")
using hyp proof induct
  show "?rch pos pos" ..
next
  fix nd pos''
  assume pos'': "?rch pos pos''"
    and nd: "nd \<in> succs (run_dag autb inp) pos''"
  from nd have "Inr nd \<in> succs (run_dag (buchi_union auta autb) inp) (Inr(fst pos''), snd pos'')"
    by (auto simp add: buchi_union_run_dag)
  with pos'' show "?rch pos (nd, Suc(snd pos''))"
    by auto
qed

lemma reachable_right_then_union':
  assumes hyp: "(q',l') \<in> reachable (run_dag autb inp) (q,l)"
  shows "(Inr q', l') \<in> reachable (run_dag (buchi_union auta autb) inp) (Inr q, l)"
proof -
  from reachable_right_then_union[OF hyp] show ?thesis by auto
qed

lemma reachable_union_then_left:
  assumes hyp: "pos' \<in> reachable (run_dag (buchi_union auta autb) inp) (Inl q, l)"
  shows "\<exists>q' l'. pos' = (Inl q', l') \<and> (q',l') \<in> reachable (run_dag auta inp) (q,l)"
    (is "\<exists>q' l'. ?rch pos' q' l'")
using hyp proof induct
  have "?rch (Inl q, l) q l" by simp
  thus "\<exists>q' l'. ?rch (Inl q, l) q' l'" by blast
next
  fix nd pos''
  assume pos'': "\<exists>q'' l''. ?rch pos'' q'' l''"
    and nd: "nd \<in> succs (run_dag (buchi_union auta autb) inp) pos''"
  from pos'' obtain q'' l'' where q'': "?rch pos'' q'' l''" by blast
  with pos'' nd obtain q' where "nd = Inl q' \<and> q' \<in> succs (run_dag auta inp) (q'',l'')"
    by (auto simp add: buchi_union_run_dag)
  with q'' have "?rch (nd, Suc(snd pos'')) q' (Suc l'')" by auto
  thus "\<exists>q' l'. ?rch (nd, Suc(snd pos'')) q' l'" by blast
qed

lemma reachable_union_then_right:
  assumes hyp: "pos' \<in> reachable (run_dag (buchi_union auta autb) inp) (Inr q, l)"
  shows "\<exists>q' l'. pos' = (Inr q', l') \<and> (q',l') \<in> reachable (run_dag autb inp) (q,l)"
    (is "\<exists>q' l'. ?rch pos' q' l'")
using hyp proof induct
  have "?rch (Inr q, l) q l" by simp
  thus "\<exists>q' l'. ?rch (Inr q, l) q' l'" by blast
next
  fix nd pos''
  assume pos'': "\<exists>q'' l''. ?rch pos'' q'' l''"
    and nd: "nd \<in> succs (run_dag (buchi_union auta autb) inp) pos''"
  from pos'' obtain q'' l'' where q'': "?rch pos'' q'' l''" by blast
  with pos'' nd obtain q' where "nd = Inr q' \<and> q' \<in> succs (run_dag autb inp) (q'',l'')"
    by (auto simp add: buchi_union_run_dag)
  with q'' have "?rch (nd, Suc(snd pos'')) q' (Suc l'')" by auto
  thus "\<exists>q' l'. ?rch (nd, Suc(snd pos'')) q' l'" by blast
qed

lemma reachable_union_left:
  "reachable (run_dag (buchi_union auta autb) inp) (Inl q, l)
   = {(Inl q', l') | q' l' . (q',l') \<in> reachable (run_dag auta inp) (q,l)}"
by (auto dest: reachable_left_then_union reachable_union_then_left)

lemma reachable_union_right:
  "reachable (run_dag (buchi_union auta autb) inp) (Inr q, l)
   = {(Inr q', l') | q' l' . (q',l') \<in> reachable (run_dag autb inp) (q,l)}"
by (auto dest: reachable_right_then_union reachable_union_then_right)

theorem rch_positions_union:
  "rch_positions (run_dag (buchi_union auta autb) inp) =
   {(Inl q', l') | q' l' . (q',l') \<in> rch_positions (run_dag auta inp)} \<union>
   {(Inr q', l') | q' l' . (q',l') \<in> rch_positions (run_dag autb inp)}"
  (is "?lhs = ?left \<union> ?right")
proof -
  let ?undg = "run_dag (buchi_union auta autb) inp"
  let ?ldg = "run_dag auta inp"
  let ?rdg = "run_dag autb inp"
  have sub: "?lhs \<subseteq> ?left \<union> ?right"
  proof
    fix pos
    assume pos: "pos \<in> rch_positions ?undg"
    then obtain rt 
      where rt: "rt \<in> roots ?undg" and rtpos: "pos \<in> reachable ?undg (rt,0)"
      by (auto simp add: rch_positions_def reachables_def)
    from rt have "rt \<in> roots ?ldg <+> roots ?rdg"
      by (auto simp add: buchi_union_run_dag)
    thus "pos \<in> ?left \<union> ?right"
    proof -- {* case distinction on ``left'' or ``right'' root *}
      fix lrt
      assume lrt: "lrt \<in> roots ?ldg"
	and rt: "rt = Inl lrt"
      from rt rtpos obtain q l 
	where "pos = (Inl q, l)" and "(q,l) \<in> reachable ?ldg (lrt, 0)"
	by (blast dest: reachable_union_then_left)
      with lrt show ?thesis
	by (auto simp add: rch_positions_def reachables_def)
    next
      fix rrt
      assume rrt: "rrt \<in> roots ?rdg"
	and rt: "rt = Inr rrt"
      from rt rtpos obtain q l 
	where "pos = (Inr q, l)" and "(q,l) \<in> reachable ?rdg (rrt, 0)"
	by (blast dest: reachable_union_then_right)
      with rrt show ?thesis
	by (auto simp add: rch_positions_def reachables_def)
    qed
  qed
  have sup1: "?left \<subseteq> ?lhs"
  proof clarsimp
    fix q l
    assume q: "(q,l) \<in> rch_positions ?ldg"
    then obtain rt where
      rt: "rt \<in> roots ?ldg" and rch: "(q,l) \<in> reachable ?ldg (rt,0)"
      by (auto simp add: rch_positions_def reachables_def)
    from rt have "Inl rt \<in> roots ?undg"
      by (auto simp add: buchi_union_run_dag)
    moreover
    from rch have "(Inl q, l) \<in> reachable ?undg (Inl rt, 0)"
      by (rule reachable_left_then_union')
    ultimately show "(Inl q, l) \<in> rch_positions ?undg"
      by (auto simp add: rch_positions_def reachables_def)
  qed
  have sup2: "?right \<subseteq> ?lhs"
  proof clarsimp
    fix q l
    assume q: "(q,l) \<in> rch_positions ?rdg"
    then obtain rt where
      rt: "rt \<in> roots ?rdg" and rch: "(q,l) \<in> reachable ?rdg (rt,0)"
      by (auto simp add: rch_positions_def reachables_def)
    from rt have "Inr rt \<in> roots ?undg"
      by (auto simp add: buchi_union_run_dag)
    moreover
    from rch have "(Inr q, l) \<in> reachable ?undg (Inr rt, 0)"
      by (rule reachable_right_then_union')
    ultimately show "(Inr q, l) \<in> rch_positions ?undg"
      by (auto simp add: rch_positions_def reachables_def)
  qed
  from sub sup1 sup2 show ?thesis by blast
qed

corollary slice_union:
  "slice (run_dag (buchi_union auta autb) inp) lvl =
   slice (run_dag auta inp) lvl <+> slice (run_dag autb inp) lvl"
by (auto simp add: slice_def rch_positions_union)


text {*
  The union of two finite-state Büchi automata is again finite-state.
*}

theorem buchi_union_finite_state:
  assumes fina: "finite_state auta" and finb: "finite_state autb"
  shows "finite_state (buchi_union auta autb)"
using assms by (auto simp add: finite_state_def buchi_union_states_of finite_Plus)

(**** proof for old definition of finiteness
proof (auto simp add: finite_state_def)
  fix inp
  from fina have "finite (fst ` rch_positions (run_dag auta inp))"
    by (simp add: finite_state_def)
  hence "finite (Inl ` (fst ` rch_positions (run_dag auta inp)))"
    by (rule finite_imageI)
  moreover
  have "(fst ` {(Inl q,l) | q l . (q,l) \<in> rch_positions (run_dag auta inp)})
        \<subseteq> Inl ` (fst ` rch_positions (run_dag auta inp))"
    by (auto simp add: image_def)
  ultimately
  have lt: "finite (fst ` {(Inl q,l) | q l . (q,l) \<in> rch_positions (run_dag auta inp)})"
    by (auto elim: finite_subset)

  from finb have "finite (fst ` rch_positions (run_dag autb inp))"
    by (simp add: finite_state_def)
  hence "finite (Inr ` (fst ` rch_positions (run_dag autb inp)))"
    by (rule finite_imageI)
  moreover
  have "(fst ` {(Inr q,l) | q l . (q,l) \<in> rch_positions (run_dag autb inp)})
        \<subseteq> Inr ` (fst ` rch_positions (run_dag autb inp))"
    by (auto simp add: image_def)
  ultimately
  have rt: "finite (fst ` {(Inr q,l) | q l . (q,l) \<in> rch_positions (run_dag autb inp)})"
    by (auto elim: finite_subset)

  from lt rt show "finite (fst ` rch_positions (run_dag (buchi_union auta autb) inp))"
    by (auto simp add: rch_positions_union image_Un)
qed
****)

theorem buchi_union_bounded_nondet:
  assumes fina: "bounded_nondet auta m" and finb: "bounded_nondet autb n"
  shows "bounded_nondet (buchi_union auta autb) (m+n)"
proof (clarsimp simp add: bounded_nondet_def)
  fix inp lvl
  let ?slice = "slice (run_dag (buchi_union auta autb) inp) lvl"
  let ?sla = "slice (run_dag auta inp) lvl"
  let ?slb = "slice (run_dag autb inp) lvl"
  from fina have sla: "finite ?sla"
    by (simp add: bounded_nondet_def)
  from finb have slb: "finite ?slb"
    by (simp add: bounded_nondet_def)
  from fina have carda: "card ?sla \<le> m"
    by (simp add: bounded_nondet_def)
  from finb have cardb: "card ?slb \<le> n"
    by (simp add: bounded_nondet_def)
  have "card ?slice = card (?sla <+> ?slb)"
    by (simp add: slice_union)
  also from sla slb have "\<dots> = (card ?sla) + (card ?slb)"
    by (rule card_Plus)
  also from carda cardb have "\<dots> \<le> m + n"
    by auto
  finally show "finite ?slice \<and> card ?slice \<le> m+n"
    by (auto simp add: sla slb slice_union finite_Plus)
qed

end
