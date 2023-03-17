section "Implementing Labelled Transition Systems using a deterministic and a nondeterministic
  datastructure and choosing the right one automatically"
theory LTSByLTS_DLTS
imports LTSSpec LTSGA
begin

datatype ('a, 'b) LTS_choice = LTS 'a | DLTS 'b

find_consts name: LTS_choice

locale ltsbc_defs = 
  l: lts l_\<alpha> l_invar +
  d: dlts d_\<alpha> d_invar 
  for l_\<alpha> l_invar d_\<alpha> d_invar +
  constrains l_\<alpha> :: "'lts \<Rightarrow> ('Q \<times> 'A \<times> 'Q) set" and 
             d_\<alpha> :: "'dlts \<Rightarrow> ('Q \<times> 'A \<times> 'Q) set"
begin

  definition ltsbc_\<alpha> :: "('Q,'A,('lts,'dlts) LTS_choice) lts_\<alpha>" where
     "ltsbc_\<alpha> =  case_LTS_choice l_\<alpha> d_\<alpha>"

  definition ltsbc_invar where
     "ltsbc_invar =  case_LTS_choice l_invar d_invar"

  definition (in -) ltsbc_emp_lts where
    "ltsbc_emp_lts l_emp = (\<lambda>_::unit. LTS (l_emp ()))"

  definition (in -) ltsbc_emp_dlts where
    "ltsbc_emp_dlts d_emp = (\<lambda>_::unit. DLTS (d_emp ()))"

  lemma ltsbc_empty_correct_dlts: 
    "lts_empty d_\<alpha> d_invar d_emp \<Longrightarrow>
     lts_empty ltsbc_\<alpha> ltsbc_invar (ltsbc_emp_dlts d_emp)"    
    unfolding lts_empty_def ltsbc_emp_dlts_def ltsbc_\<alpha>_def ltsbc_invar_def
    by simp

  lemma ltsbc_empty_correct_lts: 
    "lts_empty l_\<alpha> l_invar l_emp \<Longrightarrow>
     lts_empty ltsbc_\<alpha> ltsbc_invar (ltsbc_emp_lts l_emp)"    
    unfolding lts_empty_def ltsbc_emp_lts_def ltsbc_\<alpha>_def ltsbc_invar_def
    by simp

  lemma ltsbc_memb_correct:
    "lts_memb l_\<alpha> l_invar l_memb \<Longrightarrow>
     lts_memb d_\<alpha> d_invar d_memb \<Longrightarrow>
     lts_memb ltsbc_\<alpha> ltsbc_invar (case_LTS_choice l_memb d_memb)"
  unfolding lts_memb_def ltsbc_invar_def ltsbc_\<alpha>_def 
  by (simp add: image_iff Bex_def split: LTS_choice.split)

  primrec (in -) ltsbc_add where 
    "ltsbc_add l_add d_add d_succ copy (q::'Q) (a::'A) (q'::'Q) (LTS (l::'lts)) = LTS ((l_add q a q' l)::'lts)"
  | "ltsbc_add l_add d_add d_succ copy q a q' (DLTS d) = 
     (case d_succ d q a of None \<Rightarrow> DLTS (d_add q a q' d)
                         | Some q'' \<Rightarrow> (if q'' = q' then DLTS d else
       LTS (l_add q a q' (copy (d::'dlts)))))"

  lemma ltsbc_add_correct:
    assumes l_add_OK: "lts_add l_\<alpha> l_invar l_add"
        and d_add_OK: "dlts_add d_\<alpha> d_invar d_add"
        and d_succ_OK: "dlts_succ d_\<alpha> d_invar d_succ"
        and copy_OK: "lts_copy d_\<alpha> d_invar l_\<alpha> l_invar copy"
    shows "lts_add ltsbc_\<alpha> ltsbc_invar (ltsbc_add l_add d_add d_succ copy)"
  proof (intro lts_add.intro)
    fix dl q a q'
    
    assume invar_dl: "ltsbc_invar dl"
    have "ltsbc_invar (ltsbc_add l_add d_add d_succ copy q a q' dl) \<and>
          ltsbc_\<alpha> (ltsbc_add l_add d_add d_succ copy q a q' dl) = insert (q, a, q') (ltsbc_\<alpha> dl)" 
    proof (cases dl)
      case (LTS l)
      with lts_add.lts_add_correct[OF l_add_OK, of l q a q'] invar_dl
      show ?thesis by (simp add: ltsbc_\<alpha>_def ltsbc_invar_def)
    next
      case (DLTS d) note dl_eq[simp] = this

      from invar_dl have invar_d: "d_invar d" unfolding ltsbc_invar_def by simp

      note succ_eq = dlts_succ.dlts_succ_correct[OF d_succ_OK, OF invar_d, of q a]
      note d_add_props = dlts_add.dlts_add_correct[OF d_add_OK, OF invar_d, of q' q a]

      show ?thesis
      proof (cases "d_succ d q a")
        case None with d_add_props succ_eq show ?thesis
          by (simp add: ltsbc_invar_def ltsbc_\<alpha>_def)
      next
        case (Some q'') note succ_eq_q'' = this
        have in_D: "(q, a, q'') \<in> d_\<alpha> d" using succ_eq succ_eq_q'' by metis

        show ?thesis
        proof (cases "q'' = q'")
          case True with in_D show ?thesis
            by (auto simp add: invar_d ltsbc_invar_def ltsbc_\<alpha>_def succ_eq_q'' )        
        next
          case False note q''_neq = this 

          from lts_copy.copy_correct[OF copy_OK, OF invar_d]
               lts_add.lts_add_correct[OF l_add_OK, of "copy d" q a q']
          show ?thesis
            by (simp add: invar_d ltsbc_invar_def succ_eq_q'' ltsbc_\<alpha>_def q''_neq)
        qed
      qed
    qed
    thus "ltsbc_invar (ltsbc_add l_add d_add d_succ copy q a q' dl)"
         "ltsbc_\<alpha> (ltsbc_add l_add d_add d_succ copy q a q' dl) = insert (q, a, q') (ltsbc_\<alpha> dl)" 
      by simp_all
  qed

  primrec (in -) ltsbc_add_simple :: "_ \<Rightarrow> _ \<Rightarrow> 'Q \<Rightarrow> 'A \<Rightarrow> 'Q \<Rightarrow> ('lts, 'dlts) LTS_choice \<Rightarrow> ('lts, 'dlts) LTS_choice" where 
    "ltsbc_add_simple l_add copy q a q' (LTS l) = LTS ((l_add q a q' l))"
  | "ltsbc_add_simple l_add copy q a q' (DLTS d) = LTS (l_add q a q' (copy d))"

  lemma ltsbc_add_correct_simple:
    assumes l_add_OK: "lts_add l_\<alpha> l_invar l_add"
        and copy_OK: "lts_copy d_\<alpha> d_invar l_\<alpha> l_invar copy"
    shows "lts_add ltsbc_\<alpha> ltsbc_invar (ltsbc_add_simple l_add copy)"
  proof (intro lts_add.intro)
    fix dl q a q'
    
    assume invar_dl: "ltsbc_invar dl"
    have "ltsbc_invar (ltsbc_add_simple l_add copy q a q' dl) \<and>
          ltsbc_\<alpha> (ltsbc_add_simple l_add copy q a q' dl) = insert (q, a, q') (ltsbc_\<alpha> dl)" 
    proof (cases dl)
      case (LTS l)
      with lts_add.lts_add_correct[OF l_add_OK, of l q a q'] invar_dl
      show ?thesis by (simp add: ltsbc_\<alpha>_def ltsbc_invar_def)
    next
      case (DLTS d)
      with lts_add.lts_add_correct[OF l_add_OK, of "copy d" q a q'] invar_dl
           lts_copy.copy_correct[OF copy_OK, of d]
      show ?thesis 
        by (simp add: ltsbc_\<alpha>_def ltsbc_invar_def)
    qed
    thus "ltsbc_invar (ltsbc_add_simple l_add copy q a q' dl)"
         "ltsbc_\<alpha> (ltsbc_add_simple l_add copy q a q' dl) = insert (q, a, q') (ltsbc_\<alpha> dl)" 
      by simp_all
  qed

  primrec (in -) ltsbc_add_succs :: "_ \<Rightarrow> _ \<Rightarrow> 'Q \<Rightarrow> 'A \<Rightarrow> 'Q list \<Rightarrow> ('lts, 'dlts) LTS_choice \<Rightarrow> ('lts, 'dlts) LTS_choice" where 
    "ltsbc_add_succs l_add_succs copy q a qs (LTS l) = LTS ((l_add_succs q a qs l))"
  | "ltsbc_add_succs l_add_succs copy q a qs (DLTS d) = LTS (l_add_succs q a qs (copy d))"

  lemma ltsbc_add_succs_correct:
    assumes l_add_OK: "lts_add_succs l_\<alpha> l_invar l_add_succs"
        and copy_OK: "lts_copy d_\<alpha> d_invar l_\<alpha> l_invar copy"
    shows "lts_add_succs ltsbc_\<alpha> ltsbc_invar (ltsbc_add_succs l_add_succs copy)"
  proof (intro lts_add_succs.intro)
    fix dl q a qs
    
    assume invar_dl: "ltsbc_invar dl"
    have "ltsbc_invar (ltsbc_add_succs l_add_succs copy q a qs dl) \<and>
          ltsbc_\<alpha> (ltsbc_add_succs l_add_succs copy q a qs dl) = 
               ltsbc_\<alpha> dl \<union> {(q, a, q') |q'. q' \<in> set qs}" 
    proof (cases dl)
      case (LTS l)
      with lts_add_succs.lts_add_succs_correct[OF l_add_OK, of l q a qs] invar_dl
      show ?thesis by (simp add: ltsbc_\<alpha>_def ltsbc_invar_def)
    next
      case (DLTS d)
      with lts_add_succs.lts_add_succs_correct[OF l_add_OK, of "copy d" q a qs] invar_dl
           lts_copy.copy_correct[OF copy_OK, of d]
      show ?thesis 
        by (simp add: ltsbc_\<alpha>_def ltsbc_invar_def)
    qed
    thus "ltsbc_invar (ltsbc_add_succs l_add_succs copy q a qs dl)"
         "ltsbc_\<alpha> (ltsbc_add_succs l_add_succs copy q a qs dl) = 
               ltsbc_\<alpha> dl \<union> {(q, a, q') |q'. q' \<in> set qs}" 
      by simp_all
  qed

  primrec (in -) dltsbc_add where 
    "dltsbc_add l_add d_add (q::'Q) (a::'A) (q'::'Q) (LTS (l::'lts)) = LTS ((l_add q a q' l)::'lts)"
  | "dltsbc_add l_add d_add q a q' (DLTS (d::'dlts)) = DLTS ((d_add q a q' d)::'dlts)"

  lemma dltsbc_add_correct:
    assumes l_add_OK: "dlts_add l_\<alpha> l_invar l_add"
        and d_add_OK: "dlts_add d_\<alpha> d_invar d_add"
    shows "dlts_add ltsbc_\<alpha> ltsbc_invar (dltsbc_add l_add d_add)"
  using assms
  unfolding dlts_add_def ltsbc_\<alpha>_def ltsbc_invar_def dltsbc_add_def
  by (simp split: LTS_choice.split)

  primrec (in -) ltsbc_delete where
     "ltsbc_delete l_del d_del (q::'Q) (a::'A) (q'::'Q) (LTS (l::'lts)) = LTS ((l_del q a q' l)::'lts)"
   | "ltsbc_delete l_del d_del q a q' (DLTS (d::'dlts)) = DLTS ((d_del q a q' d)::'dlts)"
   
  lemma ltsbc_delete_correct:
    "lts_delete l_\<alpha> l_invar l_del \<Longrightarrow>
     lts_delete d_\<alpha> d_invar d_del \<Longrightarrow>
     lts_delete ltsbc_\<alpha> ltsbc_invar (ltsbc_delete l_del d_del)"
    unfolding lts_delete_def ltsbc_delete_def ltsbc_\<alpha>_def ltsbc_invar_def 
    by (simp split: LTS_choice.split)

  lemma ltsbc_succ_it_correct :
    assumes "lts_succ_it l_\<alpha> l_invar l_it"
        and "lts_succ_it d_\<alpha> d_invar d_it"
    shows "lts_succ_it ltsbc_\<alpha> ltsbc_invar (case_LTS_choice l_it d_it)"
  using assms
  unfolding lts_succ_it_def ltsbc_invar_def ltsbc_\<alpha>_def
  by (simp split: LTS_choice.split)

  lemma ltsbc_succ_label_it_correct :
    assumes "lts_succ_label_it l_\<alpha> l_invar l_it"
    assumes "lts_succ_label_it d_\<alpha> d_invar d_it"
    shows "lts_succ_label_it ltsbc_\<alpha> ltsbc_invar (case_LTS_choice l_it d_it)"
  using assms
  unfolding lts_succ_label_it_def ltsbc_invar_def ltsbc_\<alpha>_def
  by (simp split: LTS_choice.split)

  primrec (in -) ltsbc_filter_it :: "('Q,'A,'\<sigma>,'lts) lts_filter_it \<Rightarrow> ('Q,'A,'\<sigma>,'dlts) lts_filter_it \<Rightarrow>
    _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _" where
     "ltsbc_filter_it l_it d_it P_q P_a P_q' P (LTS (l::'lts)) = (l_it P_q P_a P_q' P l)"
   | "ltsbc_filter_it l_it d_it P_q P_a P_q' P (DLTS (d::'dlts)) = (d_it P_q P_a P_q' P d)"

  lemma ltsbc_filter_it_correct :
    assumes "lts_filter_it l_\<alpha> l_invar l_it"
    assumes "lts_filter_it d_\<alpha> d_invar d_it"
    shows "lts_filter_it ltsbc_\<alpha> ltsbc_invar (ltsbc_filter_it l_it d_it)"
    using assms
    unfolding lts_filter_it_def ltsbc_filter_it_def ltsbc_invar_def ltsbc_\<alpha>_def
    by (simp split: LTS_choice.split)

  lemma ltsbc_it_correct :
    assumes "lts_iterator l_\<alpha> l_invar l_it"
        and "lts_iterator d_\<alpha> d_invar d_it"
    shows "lts_iterator ltsbc_\<alpha> ltsbc_invar (case_LTS_choice l_it d_it)"
    using assms
    unfolding lts_iterator_def ltsbc_filter_it_def ltsbc_invar_def ltsbc_\<alpha>_def
    by (simp split: LTS_choice.split)

  lemma ltsbc_pre_it_correct :
    assumes "lts_pre_it l_\<alpha> l_invar l_it"
        and "lts_pre_it d_\<alpha> d_invar d_it"
    shows "lts_pre_it ltsbc_\<alpha> ltsbc_invar (case_LTS_choice l_it d_it)"
  using assms
  unfolding lts_pre_it_def ltsbc_invar_def ltsbc_\<alpha>_def
  by (simp split: LTS_choice.split)

  lemma ltsbc_pre_label_it_correct :
    assumes "lts_pre_label_it l_\<alpha> l_invar l_it"
    assumes "lts_pre_label_it d_\<alpha> d_invar d_it"
    shows "lts_pre_label_it ltsbc_\<alpha> ltsbc_invar (case_LTS_choice l_it d_it)"
  using assms
  unfolding lts_pre_label_it_def ltsbc_invar_def ltsbc_\<alpha>_def
  by (simp split: LTS_choice.split)
end

end
