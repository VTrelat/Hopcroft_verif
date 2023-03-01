theory NDTable
imports Words Dags
begin

text {*
  The following rule was already deactivated in theory Words, but it
  creeps back in when combining theories.
*}

declare upt_Suc [simp del]

section {* Non-deterministic transition tables *}

subsection {* Definition *}

text {*
  Non-deterministic transition tables underly non-deterministic
  $\omega$-automata. They are parameterized by two sorts
  that represent the sort of states and the input alphabet.
  Transition tables are defined by the set of their initial states
  and their transition relation, formalized here as a function
  that maps a source state and input letter to the set of
  potential successor states. Different classes of non-deterministic
  automata can simply be represented as (record) extensions of this
  basic table structure.

  Observe in particular that the set of automaton states is not
  represented explicitly (but see definition of function
  @{text states} below). The main reason for this design
  decision is that otherwise one would require a well-formedness
  predicate that states that initial states and target states
  of transitions belong to the set of states. Most theorems
  would then require an extra hypothesis stating that the
  automata are well-formed.
*}

record ('q,'a) ndtable =
  initial   :: "'q set"     -- "set of initial states"
  trans     :: "'q \<Rightarrow> 'a \<Rightarrow> 'q set"

text {*
  A deterministic table contains at most one initial state
  and has at most one successor state per source state and
  alphabet letter. Observe that the definitions and theorems
  in this section are all defined for @{text ndtable_scheme}
  so that they apply to all future extensions of 
  non-deterministic tables.
*}

definition
  det_table :: "('q,'a,'b) ndtable_scheme \<Rightarrow> bool"
  where "det_table tbl \<equiv> 
         atmost_one (initial tbl) \<and> 
         (\<forall>q a. atmost_one (trans tbl q a))"

lemma det_table_initial:
  "\<lbrakk> det_table tbl; q \<in> initial tbl; r \<in> initial tbl \<rbrakk> \<Longrightarrow> q=r"
by (auto simp add: det_table_def)

lemma det_table_trans:
  "\<lbrakk> det_table tbl; r \<in> trans tbl q a; r' \<in> trans tbl q a \<rbrakk> \<Longrightarrow> r'=r"
by (fastsimp simp add: det_table_def)


text {*
  The following function can be used to approximate the set of
  states of a transition table as the union of the initial
  states and the targets of the transition relation. For
  concrete tables, the transition relation should be defined
  such that elements of the state type that are not automaton
  states are assigned the empty set of successors.
*}

definition
  states_of :: "('q,'a,'b) ndtable_scheme \<Rightarrow> 'q set"
  where "states_of tbl = (initial tbl) \<union> (\<Union> q a. trans tbl q a)"

lemma initial_states_of [elim]:
  assumes "q \<in> initial tbl"
  shows "q \<in> states_of tbl"
using assms by (simp add: states_of_def)

lemma trans_states_of [elim]:
  assumes "q' \<in> trans tbl q a"
  shows "q' \<in> states_of tbl"
using assms by (auto simp add: states_of_def)


subsection {* Execution fragments, executions, and runs *}

text {*
  A run of a table over a word is an infinite sequence of
  states such that the first state is initial and all states
  are related by the transition relation, for the corresponding
  input letter. We also define (finite and infinite) executions
  starting from arbitrary states.
*}

definition
  -- "finite executions (from arbitrary state)"
  nd_exec_fragment :: "[('q,'a,'b) ndtable_scheme, 'a list, 'q list] \<Rightarrow> bool"
  where 
   "nd_exec_fragment tbl inp run \<equiv>
    length run = Suc (length inp) \<and>
    (\<forall>n < length inp. run!(Suc n) \<in> trans tbl (run!n) (inp!n))"

definition
  -- "infinite executions (from arbitrary state)"
  nd_execution :: "[('q,'a,'b) ndtable_scheme, 'a word, 'q word] \<Rightarrow> bool"
  where  
   "nd_execution tbl inp run \<equiv>
    \<forall>n. run (Suc n) \<in> trans tbl (run n) (inp n)"

definition
  -- "infinite runs (from initial state)"
  nd_run :: "[('q,'a,'b) ndtable_scheme, 'a word, 'q word] \<Rightarrow> bool"
  where 
    "nd_run tbl inp run \<equiv>
    nd_execution tbl inp run \<and> run 0 \<in> initial tbl"

lemma [intro]:
  "\<lbrakk> length run = Suc (length inp);
     \<And>n. n < length inp \<Longrightarrow> run!(Suc n) \<in> trans tbl (run!n) (inp!n)
   \<rbrakk> \<Longrightarrow> nd_exec_fragment tbl inp run"
by (simp add: nd_exec_fragment_def)

lemma nd_exec_fragment_length [elim]:
  "nd_exec_fragment tbl inp run \<Longrightarrow> length run = Suc (length inp)"
by (simp add: nd_exec_fragment_def)

lemma nd_exec_fragment_inp_less_run [elim]:
  "nd_exec_fragment tbl inp run \<Longrightarrow> length inp < length run"
by (simp add: nd_exec_fragment_def)

lemma nd_exec_fragment_nempty [elim]:
  "nd_exec_fragment tbl inp [] \<Longrightarrow> R"
by (simp add: nd_exec_fragment_def)

lemma nd_exec_fragment_succ [elim]:
  "\<lbrakk> nd_exec_fragment tbl inp run; n < length inp \<rbrakk>
   \<Longrightarrow> run!(Suc n) \<in> trans tbl (run!n) (inp!n)"
by (simp add: nd_exec_fragment_def)

lemma [intro]:
  "\<lbrakk> \<And>n. run (Suc n) \<in> trans tbl (run n) (inp n) \<rbrakk>
   \<Longrightarrow> nd_execution tbl inp run"
by (simp add: nd_execution_def)

lemma nd_execution_succ [elim_format,elim]:
  "nd_execution tbl inp run
   \<Longrightarrow> run (Suc n) \<in> trans tbl (run n) (inp n)"
by (simp add: nd_execution_def)

lemma [intro]:
  "\<lbrakk> run 0 \<in> initial tbl; nd_execution tbl inp run \<rbrakk>
   \<Longrightarrow> nd_run tbl inp run"
by (simp add: nd_run_def)

lemma nd_run_initial [elim_format,elim]:
  "nd_run tbl inp run \<Longrightarrow> run 0 \<in> initial tbl"
by (simp add: nd_run_def)

lemma nd_run_trans [elim_format,elim]:
  "nd_run tbl inp run \<Longrightarrow> run (Suc n) \<in> trans tbl (run n) (inp n)"
by (simp add: nd_run_def nd_execution_def)

lemma nd_run_execution [elim]:
  "nd_run tbl inp run \<Longrightarrow> nd_execution tbl inp run"
by (simp add: nd_run_def)

text {*
  Finite and infinite executions remain within the state set of
  the transition table.
*}

lemma nd_exec_fragment_states [elim]:
  assumes "nd_exec_fragment tbl inp run"
  and "run!0 \<in> states_of tbl"
  and "k < length run"
  shows "run!k \<in> states_of tbl"
using assms by (cases k) (auto simp add: nd_exec_fragment_def)

lemma nd_execution_states [elim]:
  assumes "nd_execution tbl inp run"
  and "run 0 \<in> states_of tbl"
  shows "run k \<in> states_of tbl"
using assms by (cases k) auto

lemma nd_run_states [elim]:
  assumes "nd_run tbl inp run"
  shows "run k \<in> states_of tbl"
using assms by (cases k) auto

text {*
  A deterministic table admits at most one execution (fragment)
  for a given input.
*}

theorem det_exec_fragment_unique:
  assumes det: "det_table tbl"
  and runa: "nd_exec_fragment tbl inp runa"
  and runb: "nd_exec_fragment tbl inp runb"
  and start: "runb!0 = runa!0"
  shows "runb = runa"
proof (rule nth_equalityI)
  from runa runb show "length runb = length runa"
    by (simp add: nd_exec_fragment_length)
next
  show "\<forall>i. i < length runb \<longrightarrow> runb ! i = runa ! i"
  proof
    fix n
    show "n < length runb \<longrightarrow> runb!n = runa!n" (is "?P n")
    proof (induct n)
      from start show "?P 0" by simp
    next
      fix k
      assume ih: "?P k"
      show "?P (Suc k)"
      proof
	assume k: "Suc k < length runb"
	with ih have eqk: "runb!k = runa!k" by simp
	from k runb have kinp: "k < length inp"
	  by (simp add: nd_exec_fragment_length)
	from runa kinp
	have a: "runa!(Suc k) \<in> trans tbl (runa!k) (inp!k)" ..
	from runb kinp
	have "runb!(Suc k) \<in> trans tbl (runb!k) (inp!k)" ..
	with eqk
	have b: "runb!(Suc k) \<in> trans tbl (runa!k) (inp!k)" by simp
	from det a b show "runb!(Suc k) = runa!(Suc k)"
	  by (rule det_table_trans)
      qed
    qed
  qed
qed

theorem det_execution_unique:
  assumes det: "det_table tbl"
  and runa: "nd_execution tbl inp runa"
  and runb: "nd_execution tbl inp runb"
  and start: "runb 0 = runa 0"
  shows "runb = runa"
proof
  fix n
  show "runb n = runa n"
  proof (induct n)
    from start show "runb 0 = runa 0" .
  next
    fix k
    assume ih: "runb k = runa k"
    from runa have a: "runa (Suc k) \<in> trans tbl (runa k) (inp k)" ..
    from runb have "runb (Suc k) \<in> trans tbl (runb k) (inp k)" ..
    with ih have b: "runb (Suc k) \<in> trans tbl (runa k) (inp k)" by simp
    from det a b show "runb (Suc k) = runa (Suc k)"
      by (rule det_table_trans)
  qed
qed

theorem det_table_run_unique:
  assumes det: "det_table tbl"
  and runa: "nd_run tbl inp runa"
  and runb: "nd_run tbl inp runb"
  shows "runa = runb"
using det
proof (rule det_execution_unique)
  from runa show "nd_execution tbl inp runa" ..
next
  from runb show "nd_execution tbl inp runb" ..
next
  from runa have "runa 0 \<in> initial tbl" ..
  moreover
  from runb have "runb 0 \<in> initial tbl" ..
  moreover note det
  ultimately show "runa 0 = runb 0"
    by (simp add: det_table_initial)
qed

text {*
  Non-empty subsequences of an execution (fragment)
  are executions (or execution fragments).
*}

lemma nd_exec_frag_take:
  assumes run: "nd_exec_fragment tbl inp run"
  shows "nd_exec_fragment tbl (take k inp) (take (Suc k) run)"
    (is "nd_exec_fragment tbl ?tinp ?trun")
proof
  from run have "length run = Suc (length inp)"
    by (simp add: nd_exec_fragment_length)
  thus "length ?trun = Suc (length ?tinp)"
    by simp
next
  fix n
  assume n: "n < length ?tinp"
  with run have sucn: "Suc n < length ?trun"
    by (simp add: nd_exec_fragment_length)
  from n sucn run
  show "?trun ! (Suc n) \<in> trans tbl (?trun!n) (?tinp!n)"
    by auto
qed

lemma nd_exec_frag_drop:
  assumes run: "nd_exec_fragment tbl inp run"
  and k: "k \<le> length inp"
  shows "nd_exec_fragment tbl (drop k inp) (drop k run)"
    (is "nd_exec_fragment tbl ?dinp ?drun")
proof
  from run have "length run = Suc (length inp)"
    by (simp add: nd_exec_fragment_length)
  with k show "length ?drun = Suc (length ?dinp)"
    by (simp add: Suc_diff_le)
next
  fix n
  assume n: "n < length ?dinp"
  with k have kn: "k+n < length inp"
    by simp
  from n run k have "Suc n < length ?drun"
    by (simp add: nd_exec_fragment_length Suc_diff_le)
  hence sucn: "k+Suc n < length run"
    by simp
  from kn sucn run
  show "?drun!(Suc n) \<in> trans tbl (?drun!n) (?dinp!n)"
    by auto
qed

lemma nd_execution_suffix:
  "nd_execution tbl inp run
   \<Longrightarrow> nd_execution tbl (suffix k inp) (suffix k run)"
by (rule, auto)

lemma nd_execution_sub:
  assumes run: "nd_execution tbl inp run"
  and nempty: "k \<le> m"
  shows "nd_exec_fragment tbl (map inp [k ..< m]) (map run [k ..< Suc m])"
    (is "nd_exec_fragment tbl ?sinp ?srun")
proof
  from nempty show "length ?srun = Suc (length ?sinp)"
    by (simp add: upt_Suc)
next
  fix n
  assume n: "n < length ?sinp"
  hence "k+n < m"
    by simp
  with n have inpn: "?sinp!n = inp (k+n)"
    by simp
  from n nempty have ksucn: "k + Suc n < Suc m"
    by simp
  hence runn: "?srun!n = run (k+n)"
    by (intro nth_map_upt, arith)
  from ksucn have "?srun!(Suc n) = run (k + Suc n)"
    by (intro nth_map_upt, arith)
  also from run
  have "\<dots> \<in> trans tbl (run (k+n)) (inp (k+n))"
    by auto
  also from inpn runn
  have "\<dots> = trans tbl (?srun!n) (?sinp!n)"
    by simp
  finally show "?srun!(Suc n) \<in> trans tbl (?srun!n) (?sinp!n)" .
qed

text {*
  Execution fragments can be concatenated to produce longer
  fragments.
*}

lemma exec_frag_append:
  assumes runa: "nd_exec_fragment tbl inpa runa"
  and runb: "nd_exec_fragment tbl inpb runb"
  and eq: "runa!(length inpa) = runb!0"
  shows "nd_exec_fragment tbl (inpa @ inpb) (runa @ (drop 1 runb))"
    (is "nd_exec_fragment tbl ?linp ?lrun")
proof
  from runa runb
  show "length ?lrun = Suc (length ?linp)"
    by (simp add: nd_exec_fragment_length)
next
  fix n
  assume n: "n < length ?linp"
  {
    assume left: "n < length inpa"
    with runa have suc: "Suc n < length runa"
      by (simp add: nd_exec_fragment_length)
    hence "?lrun ! (Suc n) = runa ! (Suc n)"
      by (simp add: nth_append)
    also from runa left
    have "\<dots> \<in> trans tbl (runa!n) (inpa!n)" ..
    also from suc left
    have "\<dots> = trans tbl (?lrun!n) (?linp!n)"
      by (simp add: nth_append)
    finally
    have "?lrun ! (Suc n) \<in> trans tbl (?lrun ! n) (?linp ! n)" .
  }
  moreover
  {
    assume middle: "length inpa = n"
    with n have lb: "0 < length inpb"
      by simp
    from middle runa have suc: "length runa = Suc n"
      by (simp add: nd_exec_fragment_length)
    with runb have "?lrun ! (Suc n) = runb ! 1"
      by (simp add: nth_append nd_exec_fragment_length)
    also from runb lb
    have "\<dots> \<in> trans tbl (runb!0) (inpb!0)"
      by (simp add: nd_exec_fragment_succ)
    also from eq middle suc
    have "\<dots> = trans tbl (?lrun!n) (?linp!n)"
      by (simp add: nth_append)
    finally 
    have "?lrun ! (Suc n) \<in> trans tbl (?lrun ! n) (?linp ! n)" .
  }
  moreover
  {
    assume right: "length inpa < n"
    with n
    have lb: "n - length inpa < length inpb"
         (is "n - ?la < ?lb")
      by simp
    with runb
    have nla: "n - ?la \<le> length runb"
      by (simp add: nd_exec_fragment_length)
    from right
    have sucn: "Suc (n - Suc ?la) = n - ?la"
      by arith
    from lb runa runb right
    have "?lrun ! (Suc n) = runb ! (Suc (n - ?la))"
      by (simp add: nth_append nd_exec_fragment_length)
    also from runb lb
    have "\<dots> \<in> trans tbl (runb!(n - ?la)) (inpb!(n - ?la))" ..
    also from right sucn nla runa
    have "\<dots> = trans tbl (?lrun!n) (?linp!n)"
      by (simp add: nth_append nd_exec_fragment_length)
    finally
    have "?lrun ! (Suc n) \<in> trans tbl (?lrun ! n) (?linp ! n)" .
  }
  ultimately
  show "?lrun ! (Suc n) \<in> trans tbl (?lrun ! n) (?linp ! n)"
    by arith
qed

lemma exec_conc:
  assumes runa: "nd_exec_fragment tbl inpa runa"
  and runb: "nd_execution tbl inpb runb"
  and eq: "runa!(length inpa) = runb 0"
  shows "nd_execution tbl (inpa \<frown> inpb) (runa \<frown> (suffix 1 runb))"
    (is "nd_execution tbl ?linp ?lrun")
proof
  fix n
  {
    assume left: "n < length inpa"
    with runa have suc: "Suc n < length runa"
      by (simp add: nd_exec_fragment_length)
    hence "?lrun (Suc n) = runa ! (Suc n)"
      by (simp add: conc_def)
    also from runa left
    have "\<dots> \<in> trans tbl (runa!n) (inpa!n)" ..
    also from suc left
    have "\<dots> = trans tbl (?lrun n) (?linp n)"
      by (simp add: conc_def)
    finally
    have "?lrun (Suc n) \<in> trans tbl (?lrun n) (?linp n)" .
  }
  moreover
  {
    assume middle: "length inpa = n"
    from middle runa have suc: "length runa = Suc n"
      by (simp add: nd_exec_fragment_length)
    hence "?lrun (Suc n) = runb 1"
      by (simp add: conc_def)
    also from runb
    have "\<dots> \<in> trans tbl (runb 0) (inpb 0)"
      by auto
    also from eq middle suc
    have "\<dots> = trans tbl (?lrun n) (?linp n)"
      by (simp add: conc_def)
    finally
    have "?lrun (Suc n) \<in> trans tbl (?lrun n) (?linp n)" .
  }
  moreover
  {
    assume right: "length inpa < n"
    let ?la = "length inpa"
    from right
    have sucn: "Suc (n - Suc ?la) = n - ?la"
      by (arith)
    from runa right
    have "?lrun (Suc n) = runb (Suc (n - ?la))"
      by (simp add: conc_def nd_exec_fragment_length)
    also from runb
    have "\<dots> \<in> trans tbl (runb (n - ?la)) (inpb (n - ?la))" ..
    also from right sucn runa
    have "\<dots> = trans tbl (?lrun n) (?linp n)"
      by (simp add: conc_def nd_exec_fragment_length)
    finally
    have "?lrun (Suc n) \<in> trans tbl (?lrun n) (?linp n)" .
  }
  ultimately
  show "?lrun (Suc n) \<in> trans tbl (?lrun n) (?linp n)"
    by arith
qed

text {*
  From a finite and non-empty loop through the table, 
  an infinite execution can be obtained by $\omega$-iteration.
  This is useful to prove the non-emptiness of languages
  defined by $\omega$-automata from the existence of suitable
  finite executions.
*}

theorem loop_execution:
  assumes run: "nd_exec_fragment tbl inp run"
  and loop: "run!(length inp) = run!0"
  and nempty: "0 < length inp"
  shows "nd_execution tbl inp\<^sup>\<omega> (take (length inp) run)\<^sup>\<omega>"
    (is "nd_execution tbl ?linp ?lrun")
proof
  -- "some preparatory calculation"
  let ?l = "length inp"
  from nempty obtain k where k: "?l = Suc k"
    by (auto simp add: gr0_conv_Suc)
  from run
  have "length (take ?l run) = ?l"
    by (simp add: nd_exec_fragment_length)
  with run nempty
  have ridx: "\<And>i. ?lrun i = run ! (i mod ?l)"
    by (simp add: nd_exec_fragment_length)
  from nempty
  have iidx: "\<And>i. ?linp i = inp ! (i mod ?l)"
    by simp
  -- "now for the main proof"
  fix n
  show "?lrun (Suc n) \<in> trans tbl (?lrun n) (?linp n)"
  proof (cases "Suc (n mod ?l) = ?l")
    case True
    with ridx have "?lrun (Suc n) = run!0"
      by (simp add: mod_Suc)
    also from loop k have "\<dots> = run ! (Suc k)"
      by simp
    also from run k
    have "\<dots> \<in> trans tbl (run!k) (inp!k)"
      by auto
    also from ridx iidx k True
    have "\<dots> = trans tbl (?lrun n) (?linp n)"
      by (simp add: mod_Suc)
    finally show ?thesis .
  next
    case False
    with ridx have "?lrun (Suc n) = run ! (Suc (n mod ?l))"
      by (simp add: mod_Suc)
    also from run k
    have "\<dots> \<in> trans tbl (run ! (n mod ?l)) (inp ! (n mod ?l))"
      by auto
    also from iidx ridx False
    have "\<dots> = trans tbl (?lrun n) (?linp n)"
      by (simp add: mod_Suc)
    finally show ?thesis .
  qed
qed

text {*
  We define one- and multi-step accessibility between automaton 
  states and prove some obvious lemmas.
*}

definition
  one_step :: "('q,'a,'b) ndtable_scheme \<Rightarrow> ('q \<times> 'q) set"
  where "one_step tbl \<equiv> { (q,q') . \<exists>a. q' \<in> trans tbl q a }"

syntax
  "_acc_one"  :: "['q, ('q,'a,'b) ndtable_scheme, 'q] \<Rightarrow> bool"  
                                             ("_ - _ -> _" [65,65,65] 100)
  "_acc_star" :: "['q, ('q,'a,'b) ndtable_scheme, 'q] \<Rightarrow> bool"  
                                             ("_ - _ ->^* _" [65,65,65] 100)
  "_acc_plus" :: "['q, ('q,'a,'b) ndtable_scheme, 'q] \<Rightarrow> bool"  
                                             ("_ - _ ->^+ _" [65,65,65] 100)
syntax (xsymbols)
  "_acc_one"  :: "['q, ('q,'a,'b) ndtable_scheme, 'q] \<Rightarrow> bool"
                                             ("_ - _ \<rightarrow> _" [65,65,65] 100)
  "_acc_star" :: "['q, ('q,'a,'b) ndtable_scheme, 'q] \<Rightarrow> bool"
                                             ("_ - _ \<rightarrow>\<^sup>* _" [65,65,65] 100)
  "_acc_plus" :: "['q, ('q,'a,'b) ndtable_scheme, 'q] \<Rightarrow> bool"
                                             ("_ - _ \<rightarrow>\<^sup>+ _" [65,65,65] 100)
translations
  "q - tbl \<rightarrow> q'" \<rightleftharpoons> "(q,q') \<in> (CONST one_step tbl)"
  "q - tbl \<rightarrow>\<^sup>* q'" \<rightleftharpoons> "(q,q') \<in> (CONST one_step tbl)\<^sup>*"
  "q - tbl \<rightarrow>\<^sup>+ q'" \<rightleftharpoons> "(q,q') \<in> (CONST one_step tbl)\<^sup>+"


lemma exec_acc_star:
  assumes run: "nd_exec_fragment tbl inp run"   (is "?exe inp run")
  shows "(run!0) - tbl \<rightarrow>\<^sup>* (run ! length inp)"  (is "?acc inp run")
proof -
  have "\<forall>run. ?exe inp run \<longrightarrow> ?acc inp run"
  proof (induct inp)
    show "\<forall>run. ?exe [] run \<longrightarrow> ?acc [] run" by auto
  next
    fix a inp
    assume ih: "\<forall>run. ?exe inp run \<longrightarrow> ?acc inp run"
    show "\<forall>run. ?exe (a # inp) run \<longrightarrow> ?acc (a # inp) run"
    proof (clarify)
      fix run
      assume r: "nd_exec_fragment tbl (a # inp) run"
      -- {* first show that $run!1$ is accessible from $run!0$ *}
      from r have "(run!0) - tbl \<rightarrow> (run!1)"
	by (auto simp add: one_step_def)
      -- {* now use the induction hypothesis to show accessibility for the tail *}
      moreover
      from r have "nd_exec_fragment tbl (drop 1 (a # inp)) (drop 1 run)"
	by (rule nd_exec_frag_drop, simp)
      hence "nd_exec_fragment tbl inp (drop 1 run)" by simp
      with ih have "((drop 1 run)!0) - tbl \<rightarrow>\<^sup>* ((drop 1 run)!(length inp))"
	by blast
      with r have "(run!1) - tbl \<rightarrow>\<^sup>* (run ! length(a # inp))"
	by (simp add: nd_exec_fragment_length)
      ultimately
      show "run!0 - tbl \<rightarrow>\<^sup>* (run ! length (a # inp))"
	by (rule converse_rtrancl_into_rtrancl)
    qed
  qed
  with run show ?thesis by blast
qed

lemma acc_star_exec:
  assumes acc: "q - tbl \<rightarrow>\<^sup>* q'"  (is "?acc q q'")
  shows "\<exists>inp run. nd_exec_fragment tbl inp run
                   \<and> run!0 = q \<and> run!(length inp) = q'"
        (is "\<exists>inp run. ?exec inp run q q'")
using acc
proof (induct)
  have "?exec [] [q] q q" by auto
  thus "\<exists>inp run. ?exec inp run q q" by blast
next
  fix q' q''
  assume q'': "q' - tbl \<rightarrow> q''"
    and  ih:  "\<exists>inp run. ?exec inp run q q'"
  from q'' obtain a where "q'' \<in> trans tbl q' a"
    by (auto simp add: one_step_def)
  hence a_run: "nd_exec_fragment tbl [a] [q',q'']" by auto
  from ih obtain inp run where run: "?exec inp run q q'"
    by blast
  from run a_run
  have "nd_exec_fragment tbl (inp @ [a]) (run @ [q''])"
    by (auto dest: exec_frag_append)
  moreover
  from run have "(run @ [q'']) ! 0 = q"
    by (auto simp add: nth_append)
  moreover
  from run have "length run = Suc (length inp)"
    by (auto simp add: nd_exec_fragment_length)
  with run have "(run @ [q'']) ! (Suc (length inp)) = q''"
    by (simp add: nth_append)
  ultimately
  have "?exec (inp @ [a]) (run @ [q'']) q q''" by simp
  thus "\<exists>inp run. ?exec inp run q q''" by blast
qed

text {*
  Therefore, multi-step accessibility of a state by another one
  is equivalent to the existence of an input word and a
  finite execution linking the two states.
*}

theorem acc_star_iff_exec:
  "q - tbl \<rightarrow>\<^sup>* q'
   = (\<exists>inp run. nd_exec_fragment tbl inp run
                 \<and> run!0 = q \<and> run!(length inp) = q')"
by (blast intro: acc_star_exec exec_acc_star)

text {*
  As a corollary, establish reachability from infinite executions.
*}

lemma nd_execution_acc_star:
  assumes exe: "nd_execution tbl inp run"
  and leq: "i \<le> j"
  shows "(run i) - tbl \<rightarrow>\<^sup>* (run j)"
proof -
  let ?w = "map inp [i ..< j]" and ?rw = "map run [i ..< Suc j]"
  from exe leq have "nd_exec_fragment tbl ?w ?rw"
    by (rule nd_execution_sub)
  hence "(?rw ! 0) - tbl \<rightarrow>\<^sup>* (?rw ! length ?w)"
    by (rule exec_acc_star)
  moreover
  from leq have "?rw ! 0 = run i"
    by simp
  moreover
  from leq have "j-i < length [i ..< Suc j]"
    by simp
  with leq have "?rw ! (length ?w) = run j"
    by simp
  ultimately
  show ?thesis by simp
qed

text {*
  Multi-step reachability remains within state set.
*}

lemma acc_star_states:
  assumes acc: "q - tbl \<rightarrow>\<^sup>* q'" and q: "q \<in> states_of tbl"
  shows "q' \<in> states_of tbl"
using acc q proof (auto simp add: acc_star_iff_exec)
  fix inp run
  assume init: "run!0 \<in> states_of tbl" and exec: "nd_exec_fragment tbl inp run"
  from exec have "length inp < length run" ..
  with init exec show "run!(length inp) \<in> states_of tbl"
    by auto
qed

text {*
  Similar lemmas for the transitive closure.
*}

lemma acc_plus_exec:
  assumes acc: "q - tbl \<rightarrow>\<^sup>+ q'"
  shows "\<exists>inp run. nd_exec_fragment tbl inp run
                 \<and> run!0 = q \<and> run!(length inp) = q' \<and> 0 < length inp"
        (is "\<exists>inp run. ?exe inp run")
proof -
  from acc obtain q'' 
    where q: "q - tbl \<rightarrow> q''" and q': "q'' - tbl \<rightarrow>\<^sup>* q'"
    by (auto dest: tranclD)
  from q obtain a where "q'' \<in> trans tbl q a"
    by (auto simp add: one_step_def)
  hence a: "nd_exec_fragment tbl [a] [q,q'']" by auto
  from q' obtain inp run
    where run: "nd_exec_fragment tbl inp run"
      and run0: "run!0 = q''" and runn: "run!(length inp) = q'"
    by (blast dest: acc_star_exec)
  from a run run0
  have "nd_exec_fragment tbl ([a] @ inp) ([q,q''] @ (drop 1 run))"
    by (auto dest: exec_frag_append)
  moreover
  from run have "0 < length run"
    by (simp add: nd_exec_fragment_length)
  hence lrun: "length (q'' # (drop (Suc 0) run)) = length run"
    (is "length ?lhs = length ?rhs")
    by simp
  hence "q'' # (drop (Suc 0) run) = run"
  proof (rule nth_equalityI, clarify)
    fix i
    assume i: "i < length ?lhs"
    show "?lhs ! i = ?rhs ! i"
    proof (cases i)
      case 0
      with run0 show ?thesis by simp
    next
      fix n
      assume n: "i = Suc n"
      with i lrun show ?thesis by simp
    qed
  qed
  moreover note runn
  ultimately
  have "?exe (a # inp) (q # run)"
    by simp
  thus ?thesis by blast
qed

lemma exec_acc_plus:
  assumes run: "nd_exec_fragment tbl inp run"
  and len: "0 < length inp"
  shows "(run!0) - tbl \<rightarrow>\<^sup>+ (run ! length inp)"
proof -
  from len obtain k where k: "length inp = Suc k" 
    by (auto simp add: gr0_conv_Suc)
  with run have fst: "(run!0) - tbl \<rightarrow> (run!1)"
    by (auto simp add: nd_exec_fragment_def one_step_def)
  from run k
  have "nd_exec_fragment tbl (drop 1 inp) (drop 1 run)"
    (is "nd_exec_fragment tbl ?dinp ?drun")
    by (auto elim: nd_exec_frag_drop)
  hence "(?drun!0) - tbl \<rightarrow>\<^sup>* (?drun ! length ?dinp)"
    by (rule exec_acc_star)
  with run k
  have "(run!1) - tbl \<rightarrow>\<^sup>* (run ! length inp)"
    by (simp add: nd_exec_fragment_length)
  with fst show ?thesis
    by (rule rtrancl_into_trancl2)
qed

theorem acc_plus_iff_exec:
  "q - tbl \<rightarrow>\<^sup>+ q'
   = (\<exists>inp run. nd_exec_fragment tbl inp run
                 \<and> run!0 = q \<and> run!(length inp) = q' \<and> 0 < length inp)"
by (blast intro: acc_plus_exec exec_acc_plus)


lemma nd_execution_acc_plus:
  assumes exe: "nd_execution tbl inp run"
  and lt: "i < j"
  shows "(run i) - tbl \<rightarrow>\<^sup>+ (run j)"
proof -
  let ?w = "map inp [i ..< j]" and ?rw = "map run [i ..< Suc j]"
  from lt have lenw: "0 < length ?w"
    by simp
  from exe lt have "nd_exec_fragment tbl ?w ?rw"
    by (auto elim: nd_execution_sub)
  with lenw have "(?rw ! 0) - tbl \<rightarrow>\<^sup>+ (?rw ! length ?w)"
    by (blast intro: exec_acc_plus)
  moreover
  from lt have "?rw ! 0 = run i"
    by simp
  moreover
  from lt have "j-i < length [i ..< Suc j]"
    by simp
  with lt have "?rw ! (length ?w) = run j"
    by simp
  ultimately
  show ?thesis by simp
qed

lemma acc_plus_states:
  assumes acc: "q - tbl \<rightarrow>\<^sup>+ q'" and q: "q \<in> states_of tbl"
  shows "q' \<in> states_of tbl"
using acc q proof (auto simp add: acc_plus_iff_exec)
  fix inp run
  assume init: "run!0 \<in> states_of tbl" and exec: "nd_exec_fragment tbl inp run"
  from exec have "length inp < length run" ..
  with init exec show "run!(length inp) \<in> states_of tbl"
    by auto
qed


subsection {* Run dags of transition tables *}

text {*
  The run dag for a transition table and an input word is an infinite 
  dag over the automaton states as follows: the roots of the dag are
  the initial states, and the successors of a node $q$ at level $l$
  are the possible automaton successor states for $q$ and the
  $l$-th letter of the input word.
*}

definition
run_dag :: " [('q,'a,'b) ndtable_scheme, 'a word] \<Rightarrow> 'q dag"
 where 
  "run_dag tbl inp \<equiv> 
   \<lparr> roots = initial tbl,
     succs = \<lambda>(q,l). trans tbl q (inp l)
   \<rparr>"

text {*
  The paths in the dag for an automaton and an input word
  correspond precisely to the runs of the automaton over that input.
*}

theorem path_iff_run:
  "(run \<in> paths (run_dag tbl inp)) = nd_run tbl inp run"
by (auto simp add: paths_def paths_from_def run_dag_def)

lemma reachable_exec_fragment:
  assumes pos': "pos' \<in> reachable (run_dag tbl inp) pos"
  shows "\<exists>run. nd_exec_fragment tbl (map inp [snd pos ..< snd pos']) run
               \<and> hd run = fst pos \<and> run ! (snd pos' - snd pos) = fst pos'"
    (is "\<exists>run. ?exec run pos pos'")
using pos'
proof (induct)
  have "?exec [fst pos] pos pos" by auto
  thus "\<exists>run. ?exec run pos pos" ..
next
  fix nd pos''
  assume nd: "nd \<in> succs (run_dag tbl inp) pos''"
    and pos'': "pos'' \<in> reachable (run_dag tbl inp) pos"
    and ih: "\<exists>run. ?exec run pos pos''"
  from ih obtain run where run: "?exec run pos pos''" ..
  from pos'' have sndpos: "snd pos \<le> snd pos''"
    by (rule reachable_level)
  hence Sucsndpos: "Suc (snd pos'' - snd pos) = Suc (snd pos'') - snd pos"
    by arith
  let ?inp = "map inp [snd pos ..< snd pos'']"
  let ?inp' = "map inp [snd pos ..< Suc(snd pos'')]"
  have "?exec (run @ [nd]) pos (nd, Suc(snd pos''))"
  proof auto
    show "nd_exec_fragment tbl ?inp' (run @ [nd])"
    proof
      from run show "length (run @ [nd]) = Suc (length ?inp')"
	by (auto simp add: nd_exec_fragment_def Sucsndpos)
    next
      fix n
      assume n: "n < length ?inp'"
      show "(run @ [nd]) ! (Suc n) \<in> trans tbl ((run @ [nd])!n) (?inp' ! n)"
      proof (cases "n < length ?inp")
	case True
	with run sndpos show ?thesis
	  by (auto simp add: nd_exec_fragment_def nth_append upt_Suc_append)
      next
	case False
	with n sndpos have n': "n = snd pos'' - snd pos"
	  by simp
	with nd run sndpos show ?thesis
	  by (auto simp add: nd_exec_fragment_def run_dag_def 
			     nth_append upt_Suc_append)
      qed
    qed
  next
    from run have "run \<noteq> []" by auto
    with run show "hd (run @ [nd]) = fst pos" by auto
  next
    from run show "(run @ [nd]) ! (Suc (snd pos'') - snd pos) = nd"
      by (auto simp add: nd_exec_fragment_def nth_append Sucsndpos)
  qed
  thus "\<exists>run. ?exec run pos (nd, Suc(snd pos''))" ..
qed

text {*
  Reachability is closed under positions corresponding to automaton
  states. Slices of the run dag are subsets of automaton states.
*}

lemma reachable_states_of [elim]:
  assumes pos': "pos' \<in> reachable (run_dag tbl inp) pos"
  and pos: "fst pos \<in> states_of tbl"
  shows "fst pos' \<in> states_of tbl"
using assms by (induct) (auto simp add: run_dag_def)

lemma reachable_states_of' [elim]:
  assumes q': "(q',lvl') \<in> reachable (run_dag tbl inp) (q,lvl)"
  and q: "q \<in> states_of tbl"
  shows "q' \<in> states_of tbl"
proof -
  from q have "fst (q,lvl) \<in> states_of tbl" by simp
  with q' have "fst (q',lvl') \<in> states_of tbl" by (rule reachable_states_of)
  thus ?thesis by simp
qed

lemma roots_states_of:
  "roots (run_dag tbl inp) \<subseteq> states_of tbl"
by (auto simp add: run_dag_def)

lemmas roots_states_ofE [elim] = roots_states_of[THEN subsetD]

lemma rch_positions_states_of [elim]:
  assumes pos: "pos \<in> rch_positions (run_dag tbl inp)"
  shows "fst pos \<in> states_of tbl"
using pos
proof
  fix rt
  assume rt: "rt \<in> roots (run_dag tbl inp)"
  and prt: "pos \<in> reachable (run_dag tbl inp) (rt, 0)"
  from rt have "fst (rt, 0) \<in> states_of tbl" by auto
  with prt show "fst pos \<in> states_of tbl" ..
qed

lemma rch_positions_states_of' [elim]:
  assumes q: "(q,lvl) \<in> rch_positions (run_dag tbl inp)"
  shows "q \<in> states_of tbl"
proof -
  from q have "fst (q,lvl) \<in> states_of tbl" ..
  thus ?thesis by simp
qed

lemma slice_states_of:
  "slice (run_dag tbl inp) n \<subseteq> states_of tbl"
by (auto simp add: slice_def)

lemmas slice_states_ofE [elim] = slice_states_of[THEN subsetD]


subsection {* Finite-state transition tables *}

text {*
  A table is finite-state iff its set of states, as defined by the
  @{text states_of} function, is finite. Observe that this function
  in general computes an approximation (superset) of the precise set
  of states. We have to pay this price for not including the precise
  set of states as a record component.

  We also study a somewhat weaker notion that only requires any run
  dag of the automaton to be of bounded width. That is, for any given
  input and at any given position of the input we can determine the
  automaton state at that position up to a bounded degree of
  uncertainty, although the automaton might still have infinitely
  many states overall. It turns out that many automaton constructions
  remain applicable under this weaker hypothesis.
*}


(*** OLD DEFINITIONS, TOO WEAK FOR COMPLEMENT
constdefs
  finite_state :: "('q,'a,'b) ndtable_scheme \<Rightarrow> bool"
  "finite_state tbl \<equiv>
   \<forall>inp run. nd_run tbl inp run \<longrightarrow> finite (range run)"

constdefs
  finite_state :: "('q,'a,'b) ndtable_scheme \<Rightarrow> bool"
  "finite_state tbl \<equiv> \<forall>inp. finite (fst ` (rch_positions (run_dag tbl inp)))"
***)

definition
  finite_state where (* :: "('q,'a,'b) ndtable_scheme \<Rightarrow> bool" *)
  "finite_state tbl \<equiv> finite (states_of tbl)"

definition
  bounded_nondet where (* :: "[('q,'a,'b) ndtable_scheme, nat] \<Rightarrow> bool" *)
  "bounded_nondet tbl n \<equiv>
   \<forall>inp lvl. finite (slice (run_dag tbl inp) lvl) \<and>
             card (slice (run_dag tbl inp) lvl) \<le> (n::nat)"

text {*
  In particular, the set of states that occur in any run of
  a finite-state automaton is finite.
*}

lemma finite_state_run:
  assumes fin: "finite_state tbl" and run: "nd_run tbl inp run"
  shows "finite (range run)"
proof (rule finite_subset)
  from run show "range run \<subseteq> states_of tbl"
    by auto
next
  from fin show "finite (states_of tbl)"
    by (unfold finite_state_def)
qed

lemma finite_state_finite_slice:
  assumes fin: "finite_state tbl"
  shows "finite (slice (run_dag tbl inp) l)"
proof (rule finite_subset)
  show "slice (run_dag tbl inp) l \<subseteq> states_of tbl"
    by (rule slice_states_of)
next
  from fin show "finite (states_of tbl)"
    by (unfold finite_state_def)
qed

lemma finite_state_card_slice:
  assumes fin: "finite_state tbl"
  shows "card (slice (run_dag tbl inp) lvl) \<le> card (states_of tbl)"
proof (rule card_mono)
  from fin show "finite (states_of tbl)"
    by (unfold finite_state_def)
next
  show "slice (run_dag tbl inp) lvl \<subseteq> states_of tbl"
    by (rule slice_states_of)
qed

lemma finite_state_bounded_nondet:
  assumes fin: "finite_state tbl"
  shows "bounded_nondet tbl (card (states_of tbl))"
using assms by (auto simp add: bounded_nondet_def finite_state_finite_slice finite_state_card_slice)

end

