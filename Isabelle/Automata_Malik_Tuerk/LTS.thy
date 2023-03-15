(*  Title:       Labelled Transition Systems
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
                 Petra Dietrich <petra@ecs.vuw.ac.nz>

    using Peter Lammich <peter.lammich@uni-muenster.de> work on
    Finite state machines
*)

section \<open> Labeled transition systems \<close>

theory LTS
imports Main "../Automata_Merz/Words"
begin

declare upt_Suc[simp del]

text \<open> This theory defines labeled transition systems (LTS). \<close>

subsection \<open> Auxiliary Definitions \<close>
lemma lists_product : 
  "w \<in> lists (\<Sigma>1 \<times> \<Sigma>2) \<longleftrightarrow> (map fst w) \<in> lists \<Sigma>1 \<and>  (map snd w) \<in> lists \<Sigma>2"
by (induct w, auto)

lemma lists_inter : "w \<in> lists (\<Sigma>1 \<inter> \<Sigma>2) = (w \<in> lists \<Sigma>1 \<and> w \<in> lists \<Sigma>2)"
  by (simp add: lists_eq_set)

lemma lists_rev [simp] :
  "(rev w) \<in> lists \<Sigma> \<longleftrightarrow> w \<in> lists \<Sigma>"
by auto

lemma rev_image_lists [simp] :
  "rev ` (lists A) = lists A"
proof (rule set_eqI)
  fix xs
  have "xs \<in> rev ` (lists A) \<longleftrightarrow> rev xs \<in> lists A"
    apply (simp add: image_iff Bex_def)
    apply (metis rev_swap lists_rev)
  done
  thus "xs \<in> rev ` lists A \<longleftrightarrow> xs \<in> lists A"
    by simp
qed


subsection \<open> Basic Definitions \<close>
subsubsection \<open> Transition Relations \<close>

text \<open> Given a set of states $\mathcal{Q}$ and an alphabet $\Sigma$,
a labeled transition system is a subset of $\mathcal{Q} \times \Sigma
\times \mathcal{Q}$.  Given such a relation $\Delta \subseteq
\mathcal{Q} \times \Sigma \times \mathcal{Q}$, a triple $(q, \sigma,
q')$ is an element of $\Delta$ iff starting in state $q$ the state
$q'$ can be reached reading the label $\sigma$.\<close>

type_synonym ('q,'a) LTS = "('q * 'a * 'q) set"

lemma LTS_image_finiteI [intro]:
  assumes "finite \<Delta>"
  shows "finite {(f q,a,f q') | q a q'. (q,a,q') \<in> \<Delta>}" (is "finite ?\<Delta>")
proof -
  have "?\<Delta> = (\<lambda>(q,a,q'). (f q,a,f q')) ` \<Delta>"
    by (fastforce split: prod.split)
  with assms show ?thesis by simp
qed

subsubsection \<open> Finite Runs \<close>

definition LTS_is_fin_run :: "('q,'a) LTS \<Rightarrow> 'a list \<Rightarrow> 'q list \<Rightarrow> bool" where
  "LTS_is_fin_run \<Delta> w r \<longleftrightarrow> 
     ((length r = Suc (length w)) \<and>
      (\<forall>i < length w. (r ! i, w ! i, r ! (Suc i)) \<in> \<Delta>))"

lemma LTS_is_fin_run_D1 :
  "LTS_is_fin_run \<Delta> w r \<Longrightarrow> (length r = Suc (length w))"
   unfolding LTS_is_fin_run_def by simp

lemma LTS_is_fin_run_D2 :
  "LTS_is_fin_run \<Delta> w r \<Longrightarrow> 
   i < length w \<Longrightarrow>
   (r ! i, w ! i, r ! (Suc i)) \<in> \<Delta>"
   unfolding LTS_is_fin_run_def by simp

lemma LTS_is_fin_run_I[intro!] :
  "\<lbrakk>length r = Suc (length w);
    \<And>i. i < length w \<Longrightarrow> (r ! i, w ! i, r ! (Suc i)) \<in> \<Delta>\<rbrakk> \<Longrightarrow>
   LTS_is_fin_run \<Delta> w r"
   unfolding LTS_is_fin_run_def by blast

lemma LTS_is_fin_run_simps[simp] :
  "LTS_is_fin_run \<Delta> w [] = False" (is ?T1)
  "LTS_is_fin_run \<Delta> w [q] = (w = [])" (is ?T2)
  "LTS_is_fin_run \<Delta> [] r = (length r = 1)" (is ?T3)
  "LTS_is_fin_run \<Delta> (a # w) (q1 # q2 # r) = 
     ((q1, a, q2) \<in> \<Delta> \<and> LTS_is_fin_run \<Delta> w (q2 # r))" (is ?T4)
proof -
  show ?T1 ?T2 ?T3 unfolding LTS_is_fin_run_def by auto
next
  show "?T4" (is "?T4_l \<longleftrightarrow> ?T4_r")
  proof (rule iffI)
    assume l: "?T4_l"
    show "?T4_r"
    proof (intro conjI LTS_is_fin_run_I)
      from LTS_is_fin_run_D1[OF l]
      show "length (q2 # r) = Suc (length w)" by simp
    next
      note l_simp = LTS_is_fin_run_D2[OF l]
      
      from l_simp[of 0] show "(q1, a, q2) \<in> \<Delta>" by simp

      fix i
      assume "i < length w"
      with l_simp[of "Suc i"] show "((q2 # r) ! i, w ! i, (q2 # r) ! Suc i) \<in> \<Delta>" 
        by simp
    qed
  next
    assume r: "?T4_r"
    hence r0: "(q1, a, q2) \<in> \<Delta>" and r_run:"LTS_is_fin_run \<Delta> w (q2 # r)" by simp_all

    show "?T4_l"
    proof (intro LTS_is_fin_run_I)
      from LTS_is_fin_run_D1[OF r_run] 
      show "length (q1 # q2 # r) = Suc (length (a # w))" by simp
    next
      fix i
      assume i_less: "i < length (a # w)"
      
      show "((q1 # q2 # r) ! i, (a # w) ! i, (q1 # q2 # r) ! Suc i) \<in> \<Delta>"
      proof (cases i)
        case 0 with r0 show ?thesis by simp
      next
        case (Suc i') with i_less LTS_is_fin_run_D2[OF r_run, of i']
        show ?thesis by simp
      qed
    qed
  qed
qed

lemma LTS_is_fin_run_expand_r2 :
  "LTS_is_fin_run \<Delta> (a # w) r =
    (\<exists>q1 q2 r'. r = (q1 # q2 # r') \<and> (q1, a, q2) \<in> \<Delta> \<and> LTS_is_fin_run \<Delta> w (q2 # r'))"
apply (cases r, simp, rename_tac q1 r')
apply (case_tac r', simp_all)
done

lemma LTS_is_fin_run_expand_r :
  "LTS_is_fin_run \<Delta> (a # w) r =
    (\<exists>q r'. r = (q # r') \<and> (q, a, hd r') \<in> \<Delta> \<and> LTS_is_fin_run \<Delta> w r')"
apply (cases r, simp, rename_tac q1 r')
apply (case_tac r', simp_all)
done

lemma LTS_is_fin_run_expand_r1 :
  "LTS_is_fin_run \<Delta> w r =
    (\<exists>q r'. r = (q # r') \<and> LTS_is_fin_run \<Delta> w (q # r'))"
by (cases r, auto)

lemma LTS_is_fin_run_expand_w :
  "LTS_is_fin_run \<Delta> w (q1 # q2 # r) =
    (\<exists>a w'. w = (a # w') \<and> (q1, a, q2) \<in> \<Delta> \<and> LTS_is_fin_run \<Delta> w' (q2 # r))"
by (cases w, simp_all)


subsubsection \<open> Infinite Runs \<close>

definition LTS_is_inf_run :: "('q,'a) LTS \<Rightarrow> 'a word \<Rightarrow> 'q word \<Rightarrow> bool" where
  "LTS_is_inf_run \<Delta> w r \<longleftrightarrow> (\<forall>i. (r i, w i, r (Suc i)) \<in> \<Delta>)"

lemma LTS_is_inf_run_D :
  "LTS_is_inf_run \<Delta> w r \<Longrightarrow> 
   (r i, w i, r (Suc i)) \<in> \<Delta>"
   unfolding LTS_is_inf_run_def by simp

lemma LTS_is_inf_run_I[intro!] :
  "\<lbrakk>\<And>i. (r i, w i, r (Suc i)) \<in> \<Delta>\<rbrakk> \<Longrightarrow>
   LTS_is_inf_run \<Delta> w r"
   unfolding LTS_is_inf_run_def by blast

text \<open> Every suffix of infinite run is an infinite run \<close>

lemma LTS_is_inf_run___suffix :
assumes inf_run: "LTS_is_inf_run \<Delta> w r"
shows "LTS_is_inf_run \<Delta> (suffix k w) (suffix k r)"
using inf_run unfolding LTS_is_inf_run_def suffix_def by simp

text \<open> Every finite chunk of an infinite run is a finite run \<close>

lemma LTS_is_inf_run___extract_fin_run :
assumes inf_run: "LTS_is_inf_run \<Delta> w r"
    and i_le: "i \<le> j"
shows "LTS_is_fin_run \<Delta> (map w [i..<j]) (map r [i..<Suc j])"
using inf_run i_le
unfolding LTS_is_fin_run_def LTS_is_inf_run_def
by simp

lemma LTS_is_inf_run___prefix :
assumes inf_run: "LTS_is_inf_run \<Delta> w r"
shows "LTS_is_fin_run \<Delta> (map w [0..<i]) (map r [0..<Suc i])"
using LTS_is_inf_run___extract_fin_run[OF inf_run, of 0 i] by simp

subsubsection \<open> Reachability \<close>

text \<open> Often it is enough to consider just the first and last state of
a run. This leads to the following definition of reachability. Notice, 
that @{term "LTS_is_reachable \<Delta>"} is the reflexive, transitive closure of @{term \<Delta>}. \<close>

fun LTS_is_reachable :: "('q, 'a) LTS \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q \<Rightarrow> bool" where
   "LTS_is_reachable \<Delta> q [] q' = (q = q')"
 | "LTS_is_reachable \<Delta> q (\<sigma> # w) q' = 
      (\<exists>q''. (q, \<sigma>, q'') \<in> \<Delta> \<and> LTS_is_reachable \<Delta> q'' w q')"

text \<open> Let's show the connection with @{term LTS_is_fin_run}.\<close>
lemma LTS_is_reachable_alt_def :
  "LTS_is_reachable \<Delta> q w q' \<longleftrightarrow> 
   (\<exists>r. LTS_is_fin_run \<Delta> w r \<and> hd r = q \<and> last r = q')"
proof (induct w arbitrary: q)
  case Nil thus ?case by (auto simp add: length_Suc_conv)
next
  case (Cons \<sigma> w) thus ?case
    using LTS_is_fin_run_expand_r[of \<Delta> \<sigma> w ]
    apply (simp del: ex_simps add: ex_simps[symmetric])
    apply (metis LTS_is_fin_run_simps(1))
  done
qed

lemma LTS_is_reachable_concat :
   "LTS_is_reachable \<Delta> q (w @ w') q' = 
    (\<exists>q''. LTS_is_reachable \<Delta> q w q'' \<and> LTS_is_reachable \<Delta> q'' w' q')"
by (induct w arbitrary: q, auto)

lemma LTS_is_reachable_snoc [simp] :
   "LTS_is_reachable \<Delta> q (w @ [\<sigma>]) q' = 
    (\<exists>q''. LTS_is_reachable \<Delta> q w q'' \<and> (q'', \<sigma>, q') \<in> \<Delta>)"
by (simp add: LTS_is_reachable_concat)

text \<open> Connection with infinite runs \<close>

lemma LTS_is_inf_run___is_reachable :
assumes inf_run: "LTS_is_inf_run \<Delta> w r"
    and i_le: "i \<le> j"
shows "LTS_is_reachable \<Delta> (r i) (map w [i..<j]) (r j)"
using LTS_is_inf_run___extract_fin_run[OF inf_run i_le] i_le
unfolding LTS_is_reachable_alt_def
  apply (rule_tac exI[where x = "map r [i..<Suc j]"])
  apply (simp add: hd_map last_map)
done

text \<open> Unreachability is often interesting as well. \<close>
definition LTS_is_unreachable where
   "LTS_is_unreachable \<Delta> q q' \<longleftrightarrow> \<not>(\<exists>w. LTS_is_reachable \<Delta> q w q')"

lemma LTS_is_unreachable_not_refl [simp] :
   "\<not>(LTS_is_unreachable \<Delta> q q)"
proof -
  have "LTS_is_reachable \<Delta> q [] q" by simp
  thus "\<not>(LTS_is_unreachable \<Delta> q q)"
    by (metis LTS_is_unreachable_def)
qed

lemma LTS_is_inf_run___is_unreachable :
assumes inf_run: "LTS_is_inf_run \<Delta> w r"
    and i_le: "i \<le> j"
shows "\<not>(LTS_is_unreachable \<Delta> (r i) (r j))"
using LTS_is_inf_run___is_reachable[OF inf_run i_le] 
unfolding LTS_is_unreachable_def
  apply (simp add: Bex_def)
  apply (rule_tac exI[where x = "map w [i..< j]"])
  apply (simp)
done

lemma LTS_is_unreachable_reachable_start :
assumes unreach_q_q': "LTS_is_unreachable \<Delta> q q'" 
    and reach_q_q'': "LTS_is_reachable \<Delta> q w q''" 
shows "LTS_is_unreachable \<Delta> q'' q'"
proof (rule ccontr)
  assume "\<not> (LTS_is_unreachable \<Delta> q'' q')"
  then obtain w' where reach_q''_q': "LTS_is_reachable \<Delta> q'' w' q'"
    by (auto simp add: LTS_is_unreachable_def)
  
  from reach_q_q'' reach_q''_q' have
    reach_q_q' : "LTS_is_reachable \<Delta> q (w @ w') q'" by (auto simp add: LTS_is_reachable_concat)
  
  from reach_q_q' unreach_q_q' show "False"
    by (metis LTS_is_unreachable_def)
qed
      
lemma LTS_is_unreachable_reachable_end :
   "\<lbrakk>LTS_is_unreachable \<Delta> q q'; LTS_is_reachable \<Delta> q'' w q'; w \<in> lists \<Sigma>\<rbrakk> \<Longrightarrow>
    LTS_is_unreachable \<Delta> q q''"
by (metis LTS_is_unreachable_def LTS_is_unreachable_reachable_start)

subsection \<open> Efficient way of computing reachability \<close>

fun LTS_is_reachable_fun where
   "LTS_is_reachable_fun \<Delta> [] Q = Q"
 | "LTS_is_reachable_fun \<Delta> (a # as) Q = 
    LTS_is_reachable_fun \<Delta> as {q'. \<exists>q\<in>Q. (q, a, q') \<in> \<Delta>}"

lemma LTS_is_reachable_fun_alt_def :
  "LTS_is_reachable_fun \<Delta> w Q = {q'. \<exists>q \<in> Q. LTS_is_reachable \<Delta> q w q'}"
by (induct w arbitrary: Q) auto

subsection \<open> Deterministic Transition Relations \<close>

text \<open> Often, one is interested in deterministic transition
 systems. There are several slightly different notions of
 deterministic transitions systems in literature. In the following,
 we consider transition systems that are complete as well.
 This allows to represent determistic transition systems as functions.
\<close>

definition LTS_is_deterministic :: "('q, 'a) LTS \<Rightarrow> bool" where
  "LTS_is_deterministic \<Delta> = (\<forall>q \<sigma> q1' q2'. ((q, \<sigma>, q1') \<in> \<Delta> \<and> (q, \<sigma>, q2') \<in> \<Delta>) \<longrightarrow> (q1' = q2'))"

lemma LTS_is_deterministic_I[intro] :
  "\<lbrakk>\<And>q \<sigma> q1' q2'. \<lbrakk>(q, \<sigma>, q1') \<in> \<Delta>; (q, \<sigma>, q2') \<in> \<Delta>\<rbrakk> \<Longrightarrow> (q1' = q2')\<rbrakk> \<Longrightarrow>
   LTS_is_deterministic \<Delta>"
unfolding LTS_is_deterministic_def by auto

definition LTS_is_complete :: "'q set \<Rightarrow> 'a set \<Rightarrow> ('q, 'a) LTS \<Rightarrow> bool" where
  "LTS_is_complete \<Q> \<Sigma> \<Delta> = (\<forall>q\<in>\<Q>. \<forall>\<sigma>\<in>\<Sigma>. \<exists>q'\<in>\<Q>. (q, \<sigma>, q') \<in> \<Delta>)"

definition LTS_is_complete_deterministic :: "'q set \<Rightarrow> 'a set \<Rightarrow> ('q, 'a) LTS \<Rightarrow> bool" where
  "LTS_is_complete_deterministic \<Q> \<Sigma> \<Delta> \<equiv> (LTS_is_deterministic \<Delta> \<and> LTS_is_complete \<Q> \<Sigma> \<Delta>)"

type_synonym ('q,'a) DLTS = "'q * 'a \<Rightarrow> 'q option"

definition DLTS_to_LTS :: "('q, 'a) DLTS \<Rightarrow> ('q, 'a) LTS" 
where "DLTS_to_LTS \<delta> \<equiv> {(q, \<sigma>, q') | q \<sigma> q'. \<delta>(q, \<sigma>) = Some q'}"

lemma DLTS_to_LTS_alt_def [simp]:
  "(q, \<sigma>, q') \<in> DLTS_to_LTS \<delta> \<longleftrightarrow> (\<delta>(q, \<sigma>) = Some q')"
by (auto simp add: DLTS_to_LTS_def)

lemma DLTS_to_LTS___LTS_is_deterministic [simp] :
  "LTS_is_deterministic (DLTS_to_LTS \<delta>)"
by (auto simp add: LTS_is_deterministic_def)

lemma DLTS_to_LTS___LTS_is_complete_deterministic :
  "\<lbrakk>\<And>q \<sigma>. \<lbrakk>q \<in> \<Q>; \<sigma> \<in> \<Sigma>\<rbrakk> \<Longrightarrow> \<exists>q'\<in>\<Q>. (\<delta> (q, \<sigma>) = Some q')\<rbrakk> \<Longrightarrow>
   LTS_is_complete_deterministic \<Q> \<Sigma> (DLTS_to_LTS \<delta>)"
by (auto simp add: LTS_is_complete_deterministic_def LTS_is_complete_def)

definition LTS_to_DLTS :: "('q, 'a) LTS \<Rightarrow> ('q, 'a) DLTS" where
  "LTS_to_DLTS \<Delta> \<equiv> (\<lambda>(q,\<sigma>). if (\<exists>q'. (q,\<sigma>,q') \<in> \<Delta>) then Some (SOME q'. (q, \<sigma>, q') \<in> \<Delta>) else None)"

lemma LTS_to_DLTS_in : 
  "(q, \<sigma>, q') \<in> \<Delta> \<Longrightarrow> (\<exists>q''. LTS_to_DLTS \<Delta> (q,\<sigma>) = Some q'' \<and> (q, \<sigma>, q'') \<in> \<Delta>)"
by (auto simp add: LTS_to_DLTS_def,
    rule someI2, simp_all)

lemma split_if_eq1:
  "((if Q then x else y) = b) = ((Q --> x = b) & (\<not> Q --> y = b))"
  by simp

lemma LTS_to_DLTS_is_some : 
  "LTS_to_DLTS \<Delta> (q,\<sigma>) = Some q' \<Longrightarrow> (q, \<sigma>, q') \<in> \<Delta>"
apply (auto simp add: LTS_to_DLTS_def split_if_eq1)
apply (rule_tac someI_ex)
apply auto
done

lemma LTS_to_DLTS_is_none : 
  "(LTS_to_DLTS \<Delta> (q,\<sigma>) = None) \<longleftrightarrow> (\<forall>q'. (q, \<sigma>, q') \<notin> \<Delta>)"
by (simp add: LTS_to_DLTS_def split_if_eq1)

lemma LTS_to_DLTS_is_some_det :
  "LTS_is_deterministic \<Delta> \<Longrightarrow>
   ((LTS_to_DLTS \<Delta> (q, \<sigma>) = Some q') \<longleftrightarrow> (q, \<sigma>, q') \<in> \<Delta>)"
by (metis LTS_to_DLTS_in LTS_is_deterministic_def LTS_to_DLTS_is_some)

lemma DLTS_to_LTS_inv [simp] :
   "LTS_to_DLTS (DLTS_to_LTS \<delta>) = \<delta>"
apply (subst fun_eq_iff, clarify)
apply (auto simp add: DLTS_to_LTS_def LTS_to_DLTS_def)
done

lemma LTS_to_DLTS_inv :
   "LTS_is_deterministic \<Delta> \<Longrightarrow>
    DLTS_to_LTS (LTS_to_DLTS \<Delta>) = \<Delta>"
by (simp add: DLTS_to_LTS_def LTS_to_DLTS_is_some_det, auto)

subsubsection \<open> Unique Runs \<close>

text \<open> In deterministic transition systems, there is at most one run. \<close>
lemma DLTS_is_fin_run_unique :
assumes det_\<Delta>: "LTS_is_deterministic \<Delta>"
    and run_r1: "LTS_is_fin_run \<Delta> w r1"
    and run_r2: "LTS_is_fin_run \<Delta> w r2"
    and start_eq: "hd r1 = hd r2"
shows "r1 = r2"
using assms
  apply (induct w arbitrary: r1 r2)
  apply (auto simp add: length_Suc_conv)[]
  apply (simp add: LTS_is_fin_run_expand_r)
  apply clarify
  apply (simp add: LTS_is_deterministic_def)
done

lemma DLTS_is_inf_run_unique :
assumes det_\<Delta>: "LTS_is_deterministic \<Delta>"
    and run_r1: "LTS_is_inf_run \<Delta> w r1"
    and run_r2: "LTS_is_inf_run \<Delta> w r2"
    and start_eq: "r1 0 = r2 0"
shows "r1 = r2"
proof
  fix i
  show "r1 i = r2 i"
  proof (induct i)
    case 0 with start_eq show ?case by simp
  next
    case (Suc i) note indhyp = this

    from LTS_is_inf_run_D[OF run_r1, of i]
    have r1_next: "(r1 i, w i, r1 (Suc i)) \<in> \<Delta>" .

    from LTS_is_inf_run_D[OF run_r2, of i]
    have r2_next: "(r2 i, w i, r2 (Suc i)) \<in> \<Delta>" .

    from det_\<Delta> r1_next r2_next indhyp
    show ?case unfolding LTS_is_deterministic_def by metis
  qed
qed

lemma LTS_is_reachable___LTS_is_deterministic :
assumes det_\<Delta>: "LTS_is_deterministic \<Delta>"
shows  "\<lbrakk>LTS_is_reachable \<Delta> q w q'; LTS_is_reachable \<Delta> q w q''\<rbrakk> \<Longrightarrow> (q' = q'')"
using DLTS_is_fin_run_unique[OF det_\<Delta>, of w]
unfolding LTS_is_reachable_alt_def
by blast

definition LTS_image_filter_inj_on where
  "LTS_image_filter_inj_on f A = 
    (\<forall>x\<in>A. \<forall>y\<in>A. (\<lambda>(v,e,v'). (v, e)) (f x) = (\<lambda>(v,e,v'). (v, e)) (f y) \<longrightarrow> 
                             (\<lambda>(v,e,v'). (v, e)) x = (\<lambda>(v,e,v'). (v, e)) y)" 

lemma LTS_image_filter_inj_on_id:
  "LTS_image_filter_inj_on id S"
  unfolding LTS_image_filter_inj_on_def by auto

lemma lts_image_filter_inj_on_implies_deterministic :   
  "LTS_is_deterministic A \<Longrightarrow> 
   LTS_image_filter_inj_on f A \<Longrightarrow> LTS_is_deterministic (f ` A)"
  unfolding LTS_image_filter_inj_on_def LTS_is_deterministic_def
  apply (simp split: prod.splits add: Ball_def image_iff Bex_def)
  apply auto 
  apply (metis Pair_inject)
done

text \<open> In complete transition systems, there is a run. \<close>

primrec CLTS_fin_run where
   "CLTS_fin_run \<Q> \<Delta> q [] = [q]"
 | "CLTS_fin_run \<Q> \<Delta> q (a # w) =
    (q # (CLTS_fin_run \<Q> \<Delta> (SOME q'. (q, a, q') \<in> \<Delta> \<and> q' \<in> \<Q>) w))"

lemma hd_CLTS_fin_run [simp] :
 "hd (CLTS_fin_run \<Q> \<Delta> q w) = q"
by (cases w, simp_all)

lemma CLTS_fin_run_correct :
assumes complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
    and w_OK: "w \<in> lists \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "LTS_is_fin_run \<Delta> w (CLTS_fin_run \<Q> \<Delta> q w) \<and>
       (CLTS_fin_run \<Q> \<Delta> q w) \<in> lists \<Q>"
using w_OK q_OK
proof (induct w arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons a w q1)
  note a_in_\<Sigma> = Cons(1)
  note w_in_\<Sigma> = Cons(2)
  note indhyp = Cons(3)
  note q1_in_\<Q> = Cons(4)

  define q2 where "q2 \<equiv> SOME q'. (q1, a, q') \<in> \<Delta> \<and> q' \<in> \<Q>"

  from complete_\<Delta> q1_in_\<Q> a_in_\<Sigma> have 
     q2_in_\<Q>: "q2 \<in> \<Q>" and
     step: "(q1, a, q2) \<in> \<Delta>" unfolding LTS_is_complete_def q2_def
     using someI_ex[where P = "\<lambda>q'. (q1, a, q') \<in> \<Delta> \<and> q' \<in> \<Q>"]
     by auto

  from indhyp[OF q2_in_\<Q>] have
     run': "LTS_is_fin_run \<Delta> w (CLTS_fin_run \<Q> \<Delta> q2 w)" and
     run_in_Q: "CLTS_fin_run \<Q> \<Delta> q2 w \<in> lists \<Q>" by simp_all

  obtain r' where r'_intro: "(CLTS_fin_run \<Q> \<Delta> q2 w) = q2 # r'"
    by (cases w) auto

  from run' step run_in_Q
  show ?case
    by (simp add: q2_def[symmetric] r'_intro q1_in_\<Q>)
qed

lemma CLTS_is_fin_run_exists :
assumes complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
    and w_OK: "w \<in> lists \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "\<exists>r. LTS_is_fin_run \<Delta> w (q # r)"
using CLTS_fin_run_correct[OF assms]
by (cases w) auto

lemma CLTS_is_reachable_exists :
assumes complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
    and w_OK: "w \<in> lists \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "\<exists>q'. LTS_is_reachable \<Delta> q w q'"
proof -
  from CLTS_is_fin_run_exists[OF complete_\<Delta> w_OK q_OK]
  obtain r where run_r: "LTS_is_fin_run \<Delta> w (q # r)" by blast
 
  have "LTS_is_reachable \<Delta> q w (last (q # r))"
    unfolding LTS_is_reachable_alt_def
    apply (rule exI[where x = "q # r"]) 
    apply (simp add: run_r)
  done
  thus ?thesis by blast
qed

lemma word_with_props_exists :
assumes q0_OK: "P_q q0"
    and ind: "\<And>q i. P_q q \<Longrightarrow> \<exists>q'. P_q q' \<and> P_qaq q (w i) q'"
shows "\<exists>r. r 0 = q0 \<and> (\<forall>i. P_q (r i) \<and> P_qaq (r i) (w i) (r (Suc i)))"
proof -
  define PP where "PP \<equiv> \<lambda>i q q'. (P_q q' \<and> P_qaq q (w i) q')"
  define rr where "rr \<equiv> rec_nat q0 (\<lambda>i q. (SOME q'. PP i q q'))"

  have rr_0: "rr 0 = q0"
    unfolding rr_def by simp

  { fix i
    have "PP i (rr i) (rr (Suc i))"
    proof (induct i)
      case 0
      show ?case 
        apply (simp add: rr_def q0_OK)
        apply (rule someI_ex)
        apply (simp add: PP_def)
        apply (intro ind q0_OK)
      done
    next
      case (Suc i)
      note indhyp = this

      have rr_Suc_Suc_eq: "rr (Suc (Suc i)) = (SOME q'. (PP (Suc i) (rr (Suc i)) q'))"
        unfolding rr_def by simp

      show ?case
        apply (simp add: rr_Suc_Suc_eq)
        apply (rule someI_ex)
        apply (simp add: PP_def)
        apply (intro ind)
        apply (insert indhyp)
        apply (simp add: PP_def)
      done
    qed
  } note PP_prop = this

  { fix i
    from PP_prop rr_0
    have "P_q (rr i)"
      by (cases i) (simp_all add: q0_OK PP_def)
  } note P_q_prop = this

  from PP_prop P_q_prop
  show ?thesis
    apply (rule_tac exI[where x = rr])
    apply (simp_all add: PP_def rr_0)
  done
qed

primrec CLTS_inf_run where
   "CLTS_inf_run \<Q> \<Delta> q w 0 = q"
 | "CLTS_inf_run \<Q> \<Delta> q w (Suc i) =
    (SOME q'. (CLTS_inf_run \<Q> \<Delta> q w i, w i, q') \<in> \<Delta> \<and> q' \<in> \<Q>)"

lemma CLTS_inf_run_correct :
assumes complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
    and w_OK: "\<And>i. w i \<in> \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "LTS_is_inf_run \<Delta> w (CLTS_inf_run \<Q> \<Delta> q w)" (is ?T1)
      "\<And>i. (CLTS_inf_run \<Q> \<Delta> q w) i \<in> \<Q>" (is "\<And>i. ?T2 i")
proof -
  have step: "\<And>i. CLTS_inf_run \<Q> \<Delta> q w i \<in> \<Q> \<Longrightarrow>
      (CLTS_inf_run \<Q> \<Delta> q w (Suc i) \<in> \<Q>) \<and>
      (CLTS_inf_run \<Q> \<Delta> q w i, w i, CLTS_inf_run \<Q> \<Delta> q w (Suc i)) \<in> \<Delta>"
  proof -
    fix i
    assume q1_in: "CLTS_inf_run \<Q> \<Delta> q w i \<in> \<Q>"
    with complete_\<Delta> w_OK[of i]
    show "(CLTS_inf_run \<Q> \<Delta> q w (Suc i) \<in> \<Q>) \<and>
      (CLTS_inf_run \<Q> \<Delta> q w i, w i, CLTS_inf_run \<Q> \<Delta> q w (Suc i)) \<in> \<Delta>"
       unfolding LTS_is_complete_def
       using someI_ex[where P = "\<lambda>q'. (CLTS_inf_run \<Q> \<Delta> q w i, w i, q') \<in> \<Delta> \<and> q' \<in> \<Q>"]
       by auto
  qed

  { fix i 
    have "(CLTS_inf_run \<Q> \<Delta> q w i \<in> \<Q>) \<and>
      (CLTS_inf_run \<Q> \<Delta> q w i, w i, CLTS_inf_run \<Q> \<Delta> q w (Suc i)) \<in> \<Delta>"
    proof (induct i)
      case 0 with step[of 0] q_OK show ?case by simp
    next
      case (Suc i)
      with step[of i] step[of "Suc i"] show ?case by auto
    qed
  }
  thus ?T1 "\<And>i. ?T2 i" by (simp_all add: LTS_is_inf_run_def)
qed

lemma CLTS_is_inf_run_exists :
assumes complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
    and w_OK: "\<And>i. w i \<in> \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "\<exists>r. LTS_is_inf_run \<Delta> w r \<and> r 0 = q"
using CLTS_inf_run_correct[OF complete_\<Delta>, of w q, OF w_OK q_OK]
by (rule_tac exI [where x = "CLTS_inf_run \<Q> \<Delta> q w"]) simp


text \<open> In complete, determistic transition systems, a unique run exists. \<close>

lemma CDLTS_fin_run_correct :
assumes complete_det_\<Delta>: "LTS_is_complete_deterministic \<Q> \<Sigma> \<Delta>"
    and w_OK: "w \<in> lists \<Sigma>"
    and q_OK: "hd r \<in> \<Q>"
shows "LTS_is_fin_run \<Delta> w r \<longleftrightarrow>
       r = CLTS_fin_run \<Q> \<Delta> (hd r) w"
proof -
  from complete_det_\<Delta> 
  have det_\<Delta>: "LTS_is_deterministic \<Delta>"
   and complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
     unfolding LTS_is_complete_deterministic_def by simp_all
  
  from CLTS_fin_run_correct[OF complete_\<Delta> w_OK q_OK]
       DLTS_is_fin_run_unique[OF det_\<Delta>, of w]
  show ?thesis by (metis hd_CLTS_fin_run)+
qed

lemma CDLTS_is_fin_run_exists_unique :
assumes complete_det_\<Delta>: "LTS_is_complete_deterministic \<Q> \<Sigma> \<Delta>"
    and w_OK: "w \<in> lists \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "\<exists>!r. LTS_is_fin_run \<Delta> w (q # r)"
using CDLTS_fin_run_correct[OF complete_det_\<Delta> w_OK] q_OK
by (cases w) simp_all

lemma CDLTS_is_reachable_exists_unique :
assumes complete_det_\<Delta>: "LTS_is_complete_deterministic \<Q> \<Sigma> \<Delta>"
    and w_OK: "w \<in> lists \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "\<exists>!q'. LTS_is_reachable \<Delta> q w q'"
proof -
  from CDLTS_is_fin_run_exists_unique[OF complete_det_\<Delta> w_OK q_OK]
  show ?thesis 
    unfolding LTS_is_reachable_alt_def
    apply (auto)
    apply (metis list.sel(1))
    apply (metis LTS_is_fin_run_expand_r1 list.sel(1))
  done
qed

lemma CDLTS_inf_run_correct :
assumes complete_det_\<Delta>: "LTS_is_complete_deterministic \<Q> \<Sigma> \<Delta>"
    and w_OK: "\<And>i. w i \<in> \<Sigma>"
    and q_OK: "r 0 \<in> \<Q>"
shows "LTS_is_inf_run \<Delta> w r \<longleftrightarrow>
       r = CLTS_inf_run \<Q> \<Delta> (r 0) w"
proof -
  from complete_det_\<Delta> 
  have det_\<Delta>: "LTS_is_deterministic \<Delta>"
   and complete_\<Delta>: "LTS_is_complete \<Q> \<Sigma> \<Delta>"
     unfolding LTS_is_complete_deterministic_def by simp_all
  
  from CLTS_inf_run_correct[OF complete_\<Delta>, of w, OF w_OK q_OK]
       DLTS_is_inf_run_unique[OF det_\<Delta>, of w] q_OK
  show ?thesis by (rule_tac iffI) simp_all
qed

lemma CDLTS_is_inf_run_exists_unique :
assumes complete_det_\<Delta>: "LTS_is_complete_deterministic \<Q> \<Sigma> \<Delta>"
    and w_OK: "\<And>i. w i \<in> \<Sigma>"
    and q_OK: "q \<in> \<Q>"
shows "\<exists>!r. LTS_is_inf_run \<Delta> w r \<and> r 0 = q"
by (metis CLTS_is_inf_run_exists DLTS_is_inf_run_unique 
          LTS_is_complete_deterministic_def complete_det_\<Delta> 
          q_OK w_OK)


subsubsection \<open> Basic Definitions for DLTSs \<close>

fun DLTS_fin_run_of :: "('q,'a) DLTS \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> ('q list) option" where
  "DLTS_fin_run_of \<delta> q [] = Some [q]"
| "DLTS_fin_run_of \<delta> q (\<sigma> # w) = 
   Option.bind (\<delta> (q, \<sigma>)) (\<lambda>q'. map_option (\<lambda>r. q  # r) (DLTS_fin_run_of \<delta> q' w))"

lemma DLTS_fin_run_of_hd :
assumes r_eq: "DLTS_fin_run_of \<delta> q w = Some r"
shows "\<exists>r'. r = q # r'"
proof (cases w)
  case Nil with r_eq show ?thesis by auto
next
  case (Cons a w') 
  note w_eq = Cons(1)

  from r_eq
  show ?thesis 
    by (cases "\<delta>(q, a)", auto simp add: w_eq)
qed

lemma LTS_is_fin_run___DLTS_fin_run_of :
shows "LTS_is_fin_run (DLTS_to_LTS \<delta>) w (q # r) =
       (DLTS_fin_run_of \<delta> q w = Some (q # r))"
proof (induct w arbitrary: q r)
  case Nil thus ?case by auto
next
  case (Cons a w q r)
  note ind_hyp = this

  show ?case 
  proof (cases "\<delta> (q, a)")
    case None thus ?thesis by (simp add: LTS_is_fin_run_expand_r)
  next
    case (Some q'')
    with ind_hyp DLTS_fin_run_of_hd[of \<delta> q'' w r]
    show ?thesis
      apply (simp add: LTS_is_fin_run_expand_r)
      apply (cases r)
      apply auto
    done
  qed
qed


fun DLTS_reach :: "('q, 'a) DLTS \<Rightarrow> 'q \<Rightarrow> 'a list \<Rightarrow> 'q option" where
    "DLTS_reach \<delta> q [] = Some q"
  | "DLTS_reach \<delta> q (\<sigma> # w) = 
     Option.bind (\<delta> (q, \<sigma>)) (\<lambda>q'. DLTS_reach \<delta> q' w)"

lemma DLTS_reach_Concat [simp] : 
  "DLTS_reach \<delta> q (w @ w') = Option.bind (DLTS_reach \<delta> q w) (\<lambda>q'. DLTS_reach \<delta> q' w')"
by (induct w arbitrary: q, auto)

lemma DLTS_reach_alt_def : 
  "DLTS_reach \<delta> q w = map_option (\<lambda>wl. last wl) (DLTS_fin_run_of \<delta> q w)"
proof (induct w arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> w q)
  note ind_hyp = this

  show ?case
  proof (cases "\<delta> (q, \<sigma>)")
    case None thus ?thesis by simp
  next
    case (Some q') 
    thus ?thesis 
      apply (simp add: ind_hyp option.map_comp o_def)
      apply (cases "DLTS_fin_run_of \<delta> q' w")
      apply (simp_all)
      apply (metis DLTS_fin_run_of_hd list.simps(3))
    done
  qed
qed

lemma LTS_is_reachable_determistic :
assumes det_\<Delta>: "LTS_is_deterministic \<Delta>"
shows "LTS_is_reachable \<Delta> q w q' \<longleftrightarrow>
       DLTS_reach (LTS_to_DLTS \<Delta>) q w = Some q'"
proof (induct w arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons \<sigma> w) 
  note ind_hyp = this 
  note in_\<Delta> = LTS_to_DLTS_is_some_det [OF det_\<Delta>, symmetric]
  
  show ?case
  proof (cases "LTS_to_DLTS \<Delta> (q, \<sigma>)")
    case None thus ?thesis by (simp add: in_\<Delta>)
  next
    case (Some q') thus ?thesis by (simp add: ind_hyp in_\<Delta>)
  qed
qed

lemma LTS_is_reachable_DLTS_to_LTS [simp] :
 "LTS_is_reachable (DLTS_to_LTS \<delta>) q w q' =
  (DLTS_reach \<delta> q w = Some q')"
by (metis LTS_is_reachable_determistic DLTS_to_LTS_inv
          DLTS_to_LTS___LTS_is_deterministic)


subsection \<open> Reachablity on Graphs \<close>

definition LTS_forget_labels_pred :: "('a \<Rightarrow> bool) \<Rightarrow> ('q, 'a) LTS \<Rightarrow> ('q \<times> 'q) set" where
  "LTS_forget_labels_pred P \<Delta> = {(q, q') . \<exists>\<sigma>. (q, \<sigma>, q') \<in> \<Delta> \<and> P \<sigma>}"

definition LTS_forget_labels :: "('q, 'a) LTS \<Rightarrow> ('q \<times> 'q) set" where
  "LTS_forget_labels \<Delta> = {(q, q') . \<exists>\<sigma>. (q, \<sigma>, q') \<in> \<Delta>}"

lemma LTS_forget_labels_alt_def :
  "LTS_forget_labels \<Delta> = LTS_forget_labels_pred (\<lambda>\<sigma>. True) \<Delta>"
unfolding LTS_forget_labels_def LTS_forget_labels_pred_def
by simp

lemma rtrancl_LTS_forget_labels_pred :
  "rtrancl (LTS_forget_labels_pred P \<Delta>) =
   {(q, q'). (\<exists>w. LTS_is_reachable \<Delta> q w q' \<and> w \<in> lists {\<sigma>. P \<sigma>})}"
  (is "?ls = ?rs")
proof (intro set_eqI)
  fix qq' :: "('a \<times> 'a)"
  obtain q q' where qq'_eq : "qq' = (q, q')" by (cases qq', auto)

  have imp1 : "(q, q') \<in> ?ls \<Longrightarrow> (q,q') \<in> ?rs" 
  proof (induct rule: rtrancl_induct)
    case base thus ?case 
      apply simp
      apply (rule exI [where x = "[]"])
      apply simp
    done
  next
    case (step q' q'')
    then obtain w \<sigma> where
      qq'_ind : "LTS_is_reachable \<Delta> q w q'" and
      w_in: "w \<in> lists {\<sigma>. P \<sigma>}" and
      q'q''_ind: "(q', \<sigma>, q'') \<in> \<Delta>" and
      \<sigma>_in: "P \<sigma>" unfolding LTS_forget_labels_pred_def by auto
    hence "LTS_is_reachable \<Delta> q (w @ [\<sigma>]) q'' \<and> (w @ [\<sigma>]) \<in> lists {\<sigma>. P \<sigma>}" by auto
    hence "\<exists>w. LTS_is_reachable \<Delta> q w q'' \<and> w \<in> lists {\<sigma>. P \<sigma>}" by blast
    thus ?case by simp
  qed

  have imp2 : "\<And>w. \<lbrakk>LTS_is_reachable \<Delta> q w q'; w \<in> lists {\<sigma>. P \<sigma>}\<rbrakk> \<Longrightarrow> (q,q') \<in> ?ls" 
  proof -
    fix w show "\<lbrakk>LTS_is_reachable \<Delta> q w q'; w \<in> lists {\<sigma>. P \<sigma>}\<rbrakk> \<Longrightarrow> (q,q') \<in> ?ls"
    proof (induct w arbitrary: q)
      case Nil thus ?case by simp
    next
      case (Cons \<sigma> w)
      then obtain q'' where
         in_D: "(q, \<sigma>, q'') \<in> \<Delta>" and
         \<sigma>_P: "P \<sigma>" and
         in_trcl: "(q'', q') \<in> rtrancl (LTS_forget_labels_pred P \<Delta>)"
        by auto

      from in_D \<sigma>_P have in_D': "(q, q'') \<in> (LTS_forget_labels_pred P \<Delta>)" 
        unfolding LTS_forget_labels_pred_def by auto

      note converse_rtrancl_into_rtrancl [OF in_D' in_trcl]
      thus ?case by auto
    qed
  qed

  from imp1 imp2 qq'_eq show "(qq' \<in> ?ls) = (qq' \<in> ?rs)" by auto
qed


lemma rtrancl_LTS_forget_labels :
  "rtrancl (LTS_forget_labels \<Delta>) =
   {(q, q'). (\<exists>w. LTS_is_reachable \<Delta> q w q')}"
by (simp add: LTS_forget_labels_alt_def
              rtrancl_LTS_forget_labels_pred)

lemma trancl_LTS_forget_labels_pred:
  fixes \<Delta>
  shows "(LTS_forget_labels_pred P \<Delta>)\<^sup>+ 
  = {(q, q'). (\<exists>w. LTS_is_reachable \<Delta> q w q' \<and> w\<noteq>[] \<and> w \<in> lists {\<sigma>. P \<sigma>})}"
  apply (simp add: trancl_unfold_left rtrancl_LTS_forget_labels_pred)
  apply (auto simp: LTS_forget_labels_pred_def)
  apply (rule_tac x="\<sigma>#w" in exI)
  apply auto []
  apply (case_tac w)
  apply auto
  done
lemma trancl_LTS_forget_labels:
  fixes \<Delta>
  shows "(LTS_forget_labels \<Delta>)\<^sup>+ 
  = {(q, q'). \<exists>w. LTS_is_reachable \<Delta> q w q' \<and> w\<noteq>[]}"
  using trancl_LTS_forget_labels_pred[of "\<lambda>_. True" \<Delta>]
  by (simp add: LTS_forget_labels_alt_def)

definition LTS_rename_forget_labels :: "('q \<Rightarrow> 'q2) \<Rightarrow> ('q, 'a) LTS \<Rightarrow> 
   ('q2 \<times> 'q2) set" where
"LTS_rename_forget_labels f \<Delta> = {(f q, f q') | q \<sigma> q'. (q, \<sigma>, q') \<in> \<Delta>}"

lemma LTS_rename_forget_labels_alt_def :
  "LTS_rename_forget_labels f \<Delta> =
   {(f q, f q') | q q'. (q, q') \<in> LTS_forget_labels \<Delta>}"
unfolding LTS_forget_labels_def LTS_rename_forget_labels_def
by auto

subsection \<open> Restricting and extending the transition relation \<close>

lemma LTS_is_fin_run_mono : 
  "\<lbrakk>\<Delta> \<subseteq> \<Delta>'; LTS_is_fin_run \<Delta> q r\<rbrakk> \<Longrightarrow> LTS_is_fin_run \<Delta>' q r"
unfolding LTS_is_fin_run_def by auto

lemma LTS_is_inf_run_mono : 
  "\<lbrakk>\<Delta> \<subseteq> \<Delta>'; LTS_is_inf_run \<Delta> q r\<rbrakk> \<Longrightarrow> LTS_is_inf_run \<Delta>' q r"
unfolding LTS_is_inf_run_def by auto

lemma LTS_is_reachable_mono : 
  "\<lbrakk>\<Delta> \<subseteq> \<Delta>'; LTS_is_reachable \<Delta> q w q'\<rbrakk> \<Longrightarrow> LTS_is_reachable \<Delta>' q w q'"
by (induct w arbitrary: q, auto)


subsection \<open> Products \<close>

definition LTS_product :: "('p,'a) LTS \<Rightarrow> ('q,'a) LTS \<Rightarrow> ('p*'q,'a) LTS" where
  "LTS_product \<Delta>1 \<Delta>2 = {((p,q), \<sigma>, (p',q')) | p p' \<sigma> q q'. (p, \<sigma>, p') \<in> \<Delta>1 \<and> (q, \<sigma>, q') \<in> \<Delta>2}"

lemma LTS_product_elem :
  "((p,q), \<sigma>, (p',q')) \<in> LTS_product \<Delta>1 \<Delta>2 = ((p,\<sigma>,p') \<in> \<Delta>1 \<and> (q,\<sigma>,q') \<in> \<Delta>2)"
by (simp add: LTS_product_def)

lemma LTS_product_alt_def [simp] :
  "x \<in> LTS_product \<Delta>1 \<Delta>2 = 
   ((fst (fst x),fst (snd x), fst (snd (snd x))) \<in> \<Delta>1 \<and> 
    (snd (fst x),fst (snd x), snd (snd (snd x))) \<in> \<Delta>2)"
by (cases x, case_tac a, simp add: LTS_product_elem)

lemma LTS_product_finite:
  assumes "finite \<Delta>1" and "finite \<Delta>2"
  shows "finite (LTS_product \<Delta>1 \<Delta>2)"
proof -
  let ?prod = "{((p,a,p'),q,b,q'). (p,a,p') \<in> \<Delta>1 \<and> (q,b,q') \<in> \<Delta>2 \<and> a = b}"
  let ?f = "\<lambda>((p,a,p'),q,a,q'). ((p,q),a,(p',q'))"

  have "?prod \<subseteq> \<Delta>1 \<times> \<Delta>2" by auto
  with assms have "finite ?prod" by (blast intro: finite_subset)
  moreover have "LTS_product \<Delta>1 \<Delta>2 = ?f ` ?prod" by (auto simp: LTS_product_def image_Collect)
  ultimately show ?thesis by simp
qed

lemma LTS_is_fin_run_product_iff: "LTS_is_fin_run (LTS_product \<Delta>1 \<Delta>2) w r \<longleftrightarrow>
  LTS_is_fin_run \<Delta>1 w (map fst r) \<and> LTS_is_fin_run \<Delta>2 w (map snd r)"
unfolding LTS_is_fin_run_def by auto

lemma LTS_is_inf_run_product_iff: "LTS_is_inf_run (LTS_product \<Delta>1 \<Delta>2) w r \<longleftrightarrow>
  LTS_is_inf_run \<Delta>1 w (fst \<circ> r) \<and> LTS_is_inf_run \<Delta>2 w (snd \<circ> r)"
unfolding LTS_is_inf_run_def by auto

lemma LTS_is_reachable_product :
   "LTS_is_reachable (LTS_product \<Delta>1 \<Delta>2) pq w pq' \<longleftrightarrow>
    (LTS_is_reachable \<Delta>1 (fst pq) w (fst pq') \<and>
     LTS_is_reachable \<Delta>2 (snd pq) w (snd pq'))"
by (induct w arbitrary: pq, auto)

lemma LTS_product_LTS_is_deterministic :
  "\<lbrakk>LTS_is_deterministic \<Delta>1; LTS_is_deterministic \<Delta>2 \<rbrakk> \<Longrightarrow>
   LTS_is_deterministic (LTS_product \<Delta>1 \<Delta>2)"
unfolding LTS_is_deterministic_def LTS_product_def by fast

lemma LTS_product_LTS_is_complete :
  "\<lbrakk>LTS_is_complete \<Q>1 \<Sigma>1 \<Delta>1; LTS_is_complete \<Q>2 \<Sigma>2 \<Delta>2 \<rbrakk> \<Longrightarrow>
   LTS_is_complete (\<Q>1 \<times> \<Q>2) (\<Sigma>1 \<inter> \<Sigma>2) (LTS_product \<Delta>1 \<Delta>2)"
unfolding LTS_is_complete_def LTS_product_def 
  by auto

lemma LTS_product_LTS_is_complete_deterministic :
  "\<lbrakk>LTS_is_complete_deterministic \<Q>1 \<Sigma>1 \<Delta>1; LTS_is_complete_deterministic \<Q>2 \<Sigma>2 \<Delta>2 \<rbrakk> \<Longrightarrow>
   LTS_is_complete_deterministic (\<Q>1 \<times> \<Q>2) (\<Sigma>1 \<inter> \<Sigma>2) (LTS_product \<Delta>1 \<Delta>2)"
unfolding LTS_is_complete_deterministic_def 
by (simp add: LTS_product_LTS_is_complete LTS_product_LTS_is_deterministic) 


subsection \<open> Combination \<close>

definition LTS_comb :: "('p,'a) LTS \<Rightarrow> ('q,'a) LTS \<Rightarrow> ('p + 'q,'a) LTS" where
  "LTS_comb \<Delta>1 \<Delta>2 = {(Inl q1, a, Inl q2) |q1 a q2. (q1, a, q2) \<in> \<Delta>1} \<union>
                     {(Inr q1, a, Inr q2) |q1 a q2. (q1, a, q2) \<in> \<Delta>2}"

lemma LTS_comb_alt_def :
  "(Inl q1, a, Inl q1') \<in> LTS_comb \<Delta>1 \<Delta>2 \<longleftrightarrow> (q1, a, q1') \<in> \<Delta>1"
  "(Inr q2, a, Inr q2') \<in> LTS_comb \<Delta>1 \<Delta>2 \<longleftrightarrow> (q2, a, q2') \<in> \<Delta>2"
  "(Inl q1, a, Inr q2') \<in> LTS_comb \<Delta>1 \<Delta>2 \<longleftrightarrow> False"
  "(Inr q2, a, Inl q1') \<in> LTS_comb \<Delta>1 \<Delta>2 \<longleftrightarrow> False"
unfolding LTS_comb_def
by simp_all

lemma LTS_comb_finite:
  "\<lbrakk> finite \<Delta>1; finite \<Delta>2 \<rbrakk> \<Longrightarrow> finite (LTS_comb \<Delta>1 \<Delta>2)"
by (auto simp: LTS_comb_def)

lemma LTS_comb_alt2_def :
  "(q, a, q') \<in> LTS_comb \<Delta>1 \<Delta>2 \<longleftrightarrow> 
   (\<exists>q1 q1'. q = Inl q1 \<and> q' = Inl q1' \<and> (q1, a, q1') \<in> \<Delta>1) \<or>
   (\<exists>q2 q2'. q = Inr q2 \<and> q' = Inr q2' \<and> (q2, a, q2') \<in> \<Delta>2)"
  apply (cases q)
  apply (cases q') apply (simp_all add: LTS_comb_alt_def)
  apply (cases q') apply (simp_all add: LTS_comb_alt_def)
done

lemma LTS_is_fin_run_LTS_comb :
  "LTS_is_fin_run (LTS_comb \<Delta>1 \<Delta>2) w r \<longleftrightarrow> 
   (\<exists>r1. map Inl r1 = r \<and> LTS_is_fin_run \<Delta>1 w r1) \<or>
   (\<exists>r2. map Inr r2 = r \<and> LTS_is_fin_run \<Delta>2 w r2)"
proof (induct w arbitrary: r)
  case (Nil r)
  show ?case
  proof (cases "\<exists>q. r = [q]")
    case False thus ?thesis by (auto simp add: length_Suc_conv)
  next
    case True
    then obtain q where r_eq: "r = [q]" by auto
    thus ?thesis 
      apply (cases q) 
      apply (simp_all add: length_Suc_conv ex_simps[symmetric] del: ex_simps)
    done
  qed
next
  case (Cons a w r)
  note indhyp = Cons(1)
 
  show ?case 
  proof (cases "length r < 2")
    case True thus ?thesis by (cases r, auto)
  next
    case False
    then obtain q1 q2 r' where r_eq: "r = q1 # q2 # r'"
      by (cases r, simp, rename_tac q1 r'', case_tac r'', auto)

    show ?thesis
      apply (simp add: r_eq indhyp LTS_comb_alt2_def map_eq_Cons_conv)
      apply auto
    done
  qed
qed

lemma LTS_is_reachable_comb :
  "LTS_is_reachable (LTS_comb \<Delta>1 \<Delta>2) q w q' \<longleftrightarrow> 
   (\<exists>q1 q1'. q = Inl q1 \<and> q' = Inl q1' \<and> LTS_is_reachable \<Delta>1 q1 w q1') \<or>
   (\<exists>q2 q2'. q = Inr q2 \<and> q' = Inr q2' \<and> LTS_is_reachable \<Delta>2 q2 w q2')"
unfolding LTS_is_reachable_alt_def LTS_is_fin_run_LTS_comb
apply (auto simp add: LTS_is_fin_run_expand_r)
apply (metis LTS_is_fin_run_simps(1) hd_map last_map)+
done

lemma LTS_comb_LTS_is_deterministic :
  "\<lbrakk>LTS_is_deterministic \<Delta>1; LTS_is_deterministic \<Delta>2 \<rbrakk> \<Longrightarrow>
   LTS_is_deterministic (LTS_comb \<Delta>1 \<Delta>2)"
unfolding LTS_is_deterministic_def LTS_comb_def 
by auto

lemma LTS_comb_LTS_is_complete :
  "\<lbrakk>LTS_is_complete \<Q>1 \<Sigma>1 \<Delta>1; LTS_is_complete \<Q>2 \<Sigma>2 \<Delta>2 \<rbrakk> \<Longrightarrow>
   LTS_is_complete (\<Q>1 <+> \<Q>2) (\<Sigma>1 \<inter> \<Sigma>2) (LTS_comb \<Delta>1 \<Delta>2)"
unfolding LTS_is_complete_def Ball_def LTS_comb_def  Bex_def
apply (auto)
apply (metis InlI)
apply (metis InrI)
done

lemma LTS_comb_LTS_is_complete_deterministic :
  "\<lbrakk>LTS_is_complete_deterministic \<Q>1 \<Sigma>1 \<Delta>1; LTS_is_complete_deterministic \<Q>2 \<Sigma>2 \<Delta>2 \<rbrakk> \<Longrightarrow>
   LTS_is_complete_deterministic (\<Q>1 <+> \<Q>2) (\<Sigma>1 \<inter> \<Sigma>2) (LTS_comb \<Delta>1 \<Delta>2)"
unfolding LTS_is_complete_deterministic_def 
by (simp add: LTS_comb_LTS_is_complete  LTS_comb_LTS_is_deterministic) 

end
