(*  Title:       Labelled Transition Systems
    Authors:     Thomas Tuerk <tuerk@in.tum.de>
*)

header {* Labeled transition systems implementation *}

theory LTS_Impl
imports Main "../LTS" "LTSSpec"
        "../../General/Accessible"
begin

subsubsection {* Reachability *}

fun (in StdCommonLTS) is_reachable_impl where
   "is_reachable_impl l q [] Q = Q q"
 | "is_reachable_impl l q (\<sigma> # w) Q = 
      (succ_bex l (\<lambda>q''. is_reachable_impl l q'' w Q) q \<sigma>)"

lemma (in StdCommonLTS) is_reachable_impl_correct :
  "invar l \<Longrightarrow>
   is_reachable_impl l q w Q =
   (\<exists>q'. Q q' \<and> LTS_is_reachable (\<alpha> l) q w q')"
apply (induct w arbitrary: q)
apply (auto simp add: correct_common)
done

text {* The definition above is very simple, but inefficient.
 If a state is reachable via several paths all paths starting at this node
 are searched multiple times. The following definition solves this problem by
 replacing the depth first search with a breath first one. *}

fun is_reachable_breath_impl where
   "is_reachable_breath_impl s_emp s_insert s_it succ_it l [] Q = Q"
 | "is_reachable_breath_impl s_emp s_insert s_it succ_it l (a # as) Q =
    is_reachable_breath_impl s_emp s_insert s_it succ_it l as
    (s_it Q (\<lambda>_. True) (\<lambda>q Q'. 
       succ_it l q a (\<lambda>_. True) (\<lambda>q' Q'. s_insert q' Q') Q') (s_emp ()))"

lemma is_reachable_breath_impl_alt_def :
  "is_reachable_breath_impl s_emp s_insert s_it succ_it l w Q =
   foldl (\<lambda>Q a. (s_it Q (\<lambda>_. True) (\<lambda>q Q'. 
       succ_it l q a (\<lambda>_. True) (\<lambda>q' Q'. s_insert q' Q') Q') (s_emp ()))) Q w"
by (induct w arbitrary: Q) simp_all

lemma is_reachable_breath_impl_correct :
 fixes Q :: 's
 fixes l :: 'l
 fixes w :: "'a list"
 fixes \<alpha> :: "'s \<Rightarrow> 'q set"
 assumes s_emp_OK: "set_empty \<alpha> invar s_emp"
     and s_ins_OK: "set_ins \<alpha> invar s_insert"
     and s_it_OK: "set_iteratei \<alpha> invar s_it"
     and succ_it_OK: "lts_succ_it l_\<alpha> l_invar succ_it"
     and invar_l: "l_invar l"
     and invar_Q: "invar Q"
  defines "Q' \<equiv> is_reachable_breath_impl s_emp s_insert s_it succ_it l w Q"
  shows "invar Q' \<and> \<alpha> Q' = LTS_is_reachable_fun (l_\<alpha> l) w (\<alpha> Q)"
  unfolding Q'_def
  using invar_Q
  proof (induct w arbitrary: Q)
    case Nil thus ?case by simp
  next
    case (Cons a as) 
    note ind_hyp = Cons(1)
    note invar_Q = Cons(2)

    def Q'' \<equiv> "s_it Q (\<lambda>_. True) (\<lambda>q. succ_it l q a (\<lambda>_. True) s_insert) (s_emp ())"

    have Q''_props: "invar Q'' \<and> \<alpha> Q'' = {q'. \<exists>q \<in> \<alpha> Q. (q, a, q') \<in> l_\<alpha> l}" 
    unfolding Q''_def
    proof (rule set_iteratei.iterate_rule_insert_P [OF s_it_OK, where 
        I = "\<lambda>QQ Q''. invar Q'' \<and> \<alpha> Q'' = {q'. \<exists>q \<in> QQ. (q, a, q') \<in> l_\<alpha> l}"])
      case (goal3 q QQ Q'')
      note pre = this

      from lts_succ_it.lts_succ_it_correct [OF succ_it_OK, OF invar_l, of q a]
      have it_OK: "set_iterator (succ_it l q a) {q'. (q, a, q') \<in> l_\<alpha> l}" by simp

      show ?case 
        apply (rule set_iterator_no_cond_rule_insert_P [OF it_OK, where
                I = "\<lambda>QQ Q'''. invar Q''' \<and> \<alpha> Q''' = \<alpha> Q'' \<union> QQ"])
        apply (auto simp add: pre set_ins.ins_correct[OF s_ins_OK])
      done
    qed (simp_all add: invar_Q set_empty.empty_correct[OF s_emp_OK])
    with ind_hyp[of Q'']
    show ?case by (simp add: Q''_def[symmetric] Bex_def set_eq_iff) 
  qed

text {* For deterministic transition systems, it is easier *}

fun (in StdCommonLTS) DLTS_reach_impl where
   "DLTS_reach_impl l q [] = Some q"
 | "DLTS_reach_impl l q (\<sigma> # w) = 
    (case succ l q \<sigma> of None \<Rightarrow> None | Some q' \<Rightarrow>
     DLTS_reach_impl l q' w)"

lemma (in StdCommonLTS) DLTS_reach_impl_alt_def :
  "DLTS_reach_impl l q w =
   foldli w (\<lambda>q_opt. q_opt \<noteq> None) (\<lambda>\<sigma> q_opt. succ l (the q_opt) \<sigma>) (Some q)"
by (induct w arbitrary: q) (simp_all split: option.split)

lemma (in StdCommonLTS) DLTS_reach_impl_correct :
assumes inv_l: "invar l"
    and det_l: "LTS_is_deterministic (\<alpha> l)"
shows "DLTS_reach_impl l q w = DLTS_reach (LTS_to_DLTS (\<alpha> l)) q w"
proof (induct w arbitrary: q)
  case Nil thus ?case by simp
next
  case (Cons a as q)  note ind_hyp = this

  note succ_simps = lts_succ_det_correct [OF inv_l det_l]
  have succ_eq: "LTS_to_DLTS (\<alpha> l) (q, a) = succ l q a"
    apply (cases "succ l q a")
    apply (simp_all)
    apply (simp_all add: succ_simps LTS_to_DLTS_is_none LTS_to_DLTS_is_some_det[OF det_l])
  done

  show ?case
    by (simp add: succ_eq ind_hyp split: option.split)
qed
    

subsection {* Determinism check *}

definition LTS_is_complete_deterministic_impl where
  "LTS_is_complete_deterministic_impl Q_ball A_ball succ_it l \<equiv>
   Q_ball (\<lambda>q. A_ball (\<lambda>a. (iterate_is_sng (succ_it l q a))))"

lemma LTS_is_complete_deterministic_impl_correct :
assumes Q_ball_OK: "\<And>P. Q_ball P \<longleftrightarrow> (\<forall>q \<in> Q. P q)" 
    and A_ball_OK: "\<And>P. A_ball P \<longleftrightarrow> (\<forall>a \<in> A. P a)" 
    and succ_it_OK: "lts_succ_it \<alpha> invar succ_it"
    and Q_A_OK: "\<And>q a q'. (q, a, q') \<in> \<alpha> l \<Longrightarrow> q \<in> Q \<and> a \<in> A \<and> q' \<in> Q" 
    and invar_l: "invar l"
shows "LTS_is_complete_deterministic_impl Q_ball A_ball succ_it l \<longleftrightarrow>
       LTS_is_complete_deterministic Q A (\<alpha> l)"
proof -
  have "(\<forall>q\<in>Q. \<forall>a\<in>A. card {v'. (q, a, v') \<in> \<alpha> l} = Suc 0) =
        (LTS_is_deterministic (\<alpha> l) \<and> LTS_is_complete Q A (\<alpha> l))"
        (is "?ls = ?rs")
  proof -
    have ls_eq: "?ls \<longleftrightarrow> (\<forall>q\<in>Q. \<forall>a\<in>A. \<exists>!q'. (q, a, q') \<in> \<alpha> l)"
      apply (simp add: card_Suc_eq Ball_def)
      apply (unfold set_eq_iff)
      apply auto 
      apply metis+
    done
 
    show "?ls = ?rs"
        unfolding ls_eq LTS_is_deterministic_def LTS_is_complete_def Bex_def 
      apply (rule_tac iffI)
      apply (metis Q_A_OK)
      apply metis
    done       
  qed
  moreover
  { fix q a
    note succ_it_l_OK = lts_succ_it.lts_succ_it_correct [OF succ_it_OK, OF invar_l, of q a]
    note iterate_is_sng_correct[of "succ_it l q a", OF succ_it_l_OK]
  }
  ultimately show ?thesis
    unfolding LTS_is_complete_deterministic_impl_def LTS_is_complete_deterministic_def
      by (simp add: Q_ball_OK A_ball_OK)
qed

end


