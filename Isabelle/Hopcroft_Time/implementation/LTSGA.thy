theory LTSGA
  imports LTSSpec
  "../..//Collections/Refine_Dflt"
  "../../Collections/ICF/CollectionsV1"
begin

subsection \<open> Copy \<close>

  definition ltsga_copy ::
     "('V,'W,_,'L) lts_it \<Rightarrow> ('V,'W,'L2) lts_empty \<Rightarrow> ('V,'W,'L2) lts_add \<Rightarrow> 'L \<Rightarrow> 'L2"
  where
    "ltsga_copy it emp add l =
     it l (\<lambda>_. True) (\<lambda>(q, a, q') l. add q a q' l)  (emp ())"

  lemma ltsga_copy_correct:
    assumes it_OK: "lts_iterator \<alpha> invar it"
        and emp_OK: "lts_empty \<alpha>2 invar2 emp"
        and add_OK: "lts_add \<alpha>2 invar2 add"
    shows "lts_copy \<alpha> invar \<alpha>2 invar2 (ltsga_copy it emp add)"
  proof (intro lts_copy.intro)
    fix l
    assume invar_l: "invar l"
    
    have it_OK': "set_iterator (it l) (\<alpha> l)" 
      using lts_iterator.lts_it_correct[OF it_OK, OF invar_l] by simp

    note rule = set_iterator_no_cond_rule_insert_P[OF it_OK']

    have "\<alpha>2 (ltsga_copy it emp add l) = \<alpha> l \<and>
          invar2 (ltsga_copy it emp add l)"
      unfolding ltsga_copy_def
    proof (rule rule [where ?I = "\<lambda>L l. L = (\<alpha>2 l) \<and> invar2 l"])
      from lts_empty.lts_empty_correct[OF emp_OK]
      show "{} = \<alpha>2 (emp ()) \<and> invar2 (emp ())" by simp
    next
       fix L l' qaq
       assume "L = \<alpha>2 l' \<and> invar2 l'"
       with lts_add.lts_add_correct[OF add_OK, of l']
       show "insert qaq L = \<alpha>2 ((\<lambda>(q, a, q'). add q a q') qaq l') \<and>
             invar2 ((\<lambda>(q, a, q'). add q a q') qaq l')"
         by (cases qaq) simp
    qed simp
    thus "\<alpha>2 (ltsga_copy it emp add l) = \<alpha> l"
         "invar2 (ltsga_copy it emp add l)" by simp_all
  qed

subsection\<open> get successor \<close>

  definition ltsga_succ where
    "ltsga_succ it l q a = iterate_sel_no_map (it l q a) (\<lambda>_. True)"
 
  lemma ltsga_succ_alt_def :
     "ltsga_succ it = (\<lambda>l q a. it l q a (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. Some x) None)"
    unfolding ltsga_succ_def[abs_def] iterate_sel_no_map_alt_def by simp

  lemma ltsga_succ_correct :
    assumes succ_it: "lts_succ_it \<alpha> invar it"
    shows "lts_succ \<alpha> invar (ltsga_succ it)"
    proof
      fix l v w
      assume inv_l: "invar l"

      note it_OK = lts_succ_it.lts_succ_it_correct [OF succ_it, OF inv_l]
      note succ_OK = iterate_sel_no_map_correct [OF it_OK, where P = "\<lambda>_. True", folded ltsga_succ_def]

      from succ_OK
      show "ltsga_succ it l v w = None \<Longrightarrow> \<forall>v'. (v, w, v') \<notin> \<alpha> l" by simp

      fix v'
      from succ_OK
      show "ltsga_succ it l v w = Some v' \<Longrightarrow> (v, w, v') \<in> \<alpha> l" by simp
    qed
  
subsection\<open> add successors \<close>

  lemma ltsga_it_implies_finite :
    "lts_iterator \<alpha> invar it \<Longrightarrow>
     finite_lts \<alpha> invar"
    unfolding finite_lts_def lts_iterator_def
    by (metis set_iterator_finite)

  definition ltsga_add_succs ::
    "('V,'W,'L) lts_add \<Rightarrow> ('V,'W,'L) lts_add_succs" where
    "ltsga_add_succs a v e vs l = foldl (\<lambda>l v'. a v e v' l) l vs"

  lemma ltsga_add_succs_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes add_OK: "lts_add \<alpha> invar a"
    shows "lts_add_succs \<alpha> invar (ltsga_add_succs a)"
  proof 
    fix l v e vs
    assume invar: "invar l"

    note add_OK' = lts_add.lts_add_correct [OF add_OK]

    from invar 
    have "invar (ltsga_add_succs a v e vs l) \<and>
           (\<alpha> (ltsga_add_succs a v e vs l) =
            \<alpha> l \<union> {(v, e, v') |v'. v' \<in> set vs})"
    unfolding ltsga_add_succs_def
      by (induct vs arbitrary: l)
         (auto simp add: add_OK')
    thus "invar (ltsga_add_succs a v e vs l)"
         "\<alpha> (ltsga_add_succs a v e vs l) =
          \<alpha> l \<union> {(v, e, v') |v'. v' \<in> set vs}" 
    by simp_all
  qed

subsection\<open> connection to lists \<close>

  definition ltsga_from_list_aux :: 
    "'L \<Rightarrow> ('V,'W,'L) lts_add \<Rightarrow> ('V,'W,'L) lts_from_list"
    where 
    "ltsga_from_list_aux l a ll \<equiv> foldl (\<lambda>l vev. a (fst vev) (fst (snd vev)) (snd (snd vev)) l) l ll"

  definition ltsga_from_list :: 
    "('V,'W,'L) lts_empty \<Rightarrow> ('V,'W,'L) lts_add \<Rightarrow> ('V,'W,'L) lts_from_list"
    where 
    "ltsga_from_list e a ll \<equiv> ltsga_from_list_aux (e ()) a ll"
  
  lemma ltsga_from_list_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes "lts_empty \<alpha> invar e"
    assumes "lts_add \<alpha> invar a"
    shows "lts_from_list \<alpha> invar (ltsga_from_list e a)"
  proof -
    interpret 
      lts_empty \<alpha> invar e + 
      lts_add \<alpha> invar a
      by fact+

    {
      fix ll
      have "invar (ltsga_from_list e a ll) \<and>
            \<alpha> (ltsga_from_list e a ll) = set ll"
        unfolding ltsga_from_list_def[abs_def] ltsga_from_list_aux_def[abs_def]
        apply (induct ll rule: rev_induct)
          apply (simp add: lts_empty_correct)
          apply (simp add: lts_add_correct split: prod.split)
      done
    }
    thus ?thesis
      by unfold_locales simp_all
  qed

  lemma dltsga_from_list_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes "lts_empty \<alpha> invar e"
    assumes "dlts_add \<alpha> invar a"
    shows "dlts_from_list \<alpha> invar (ltsga_from_list e a)"
  proof 
    interpret 
      lts_empty \<alpha> invar e + 
      dlts_add \<alpha> invar a
      by fact+

    fix ll :: "('V \<times> 'W \<times> 'V) list"
    assume "\<forall>v w v' v''. (v, w, v') \<in> set ll \<and> (v, w, v'') \<in> set ll \<longrightarrow> v' = v''"
    hence "invar (ltsga_from_list e a ll) \<and> \<alpha> (ltsga_from_list e a ll) = set ll"
      unfolding ltsga_from_list_def[abs_def] ltsga_from_list_aux_def[abs_def]
      proof (induct ll rule: rev_induct)
        case Nil thus ?case by (simp add: lts_empty_correct)
      next
        case (snoc x xs)
        obtain v w v' where x_eq[simp]: "x = (v, w, v')" by (metis prod.exhaust)

        from snoc(2) have dist_xs: "\<forall>v w v' v''. (v, w, v') \<in> set xs \<and> (v, w, v'') \<in> set xs \<longrightarrow> v' = v''"
          apply (simp only: x_eq set_append Un_iff set_simps singleton_iff)
          apply metis
        done

        from snoc(2) have x_nin: "\<And>v''. v'' \<noteq> v' \<Longrightarrow> (v, w, v'') \<notin> set xs"
          apply (simp only: x_eq set_append Un_iff set_simps singleton_iff)
          apply (meson list.set_intros(1))
        done

        let ?l = "foldl (\<lambda>l vev. a (fst vev) (fst (snd vev)) (snd (snd vev)) l) (e()) xs"
        from snoc(1) [OF dist_xs] have ind_hyp: "invar ?l \<and> \<alpha> ?l = set xs" by simp

        from dlts_add_correct[where l="?l" and v=v and e=w and v'=v']
        show ?case
          apply (simp)
          apply (simp add: ind_hyp x_nin)
        done
      qed
      thus "invar (ltsga_from_list e a ll)" "\<alpha> (ltsga_from_list e a ll) = set ll" by simp_all
  qed

  fun ltsga_collect_list_to_list where
     "ltsga_collect_list_to_list [] = []"
   | "ltsga_collect_list_to_list ((v, [], v') # l) =
      ltsga_collect_list_to_list l"
   | "ltsga_collect_list_to_list ((v, w # ws, v') # l) =
      (v, w, v') # (ltsga_collect_list_to_list ((v, ws, v') # l))"

  lemma ltsga_collect_list_to_list_set :
    "set (ltsga_collect_list_to_list ll) = {(v, e, v'). \<exists>es. (v, es, v') \<in> set ll \<and> e \<in> set es} "
  proof (induct ll)
    case Nil thus ?case by auto
  next
    case (Cons vev' ll) note ind_hyp = this
    obtain v ws v' where vev'_eq[simp]: "vev' = (v, ws, v')" by (cases vev', blast)

    show ?case unfolding vev'_eq 
      by (induct ws, auto simp add: ind_hyp) 
  qed

  definition ltsga_from_collect_list_aux :: 
    "'L \<Rightarrow> ('V,'W,'L) lts_add \<Rightarrow> ('V,'W,'L) lts_from_collect_list"
    where 
    "ltsga_from_collect_list_aux l a ll \<equiv> ltsga_from_list_aux l a (ltsga_collect_list_to_list ll)"

  definition ltsga_from_collect_list :: 
    "('V,'W,'L) lts_empty \<Rightarrow> ('V,'W,'L) lts_add \<Rightarrow> ('V,'W,'L) lts_from_collect_list"
    where 
    "ltsga_from_collect_list e a ll \<equiv> ltsga_from_collect_list_aux (e ()) a ll"

  lemma ltsga_from_collect_list_alt_def :
    "ltsga_from_collect_list e a ll \<equiv> ltsga_from_list e a (ltsga_collect_list_to_list ll)"
    unfolding ltsga_from_collect_list_def ltsga_from_list_def ltsga_from_collect_list_aux_def .

  lemma ltsga_from_collect_list_aux_alt_def [code] :
   "ltsga_from_collect_list_aux l a [] = l"
   "ltsga_from_collect_list_aux l a ((v, [], v') # ll) = ltsga_from_collect_list_aux l a ll"
   "ltsga_from_collect_list_aux l a ((v, (w # ws), v') # ll) = 
    ltsga_from_collect_list_aux (a v w v' l) a ((v, ws, v') # ll)"
  unfolding ltsga_from_collect_list_aux_def ltsga_from_list_aux_def
  by simp_all
  
  lemma ltsga_from_collect_list_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes "lts_empty \<alpha> invar e"
    assumes "lts_add \<alpha> invar a"
    shows "lts_from_collect_list \<alpha> invar (ltsga_from_collect_list e a)"
  proof 
    fix ll
    note from_list_OK = ltsga_from_list_correct [OF assms]
    note step1 = lts_from_list.lts_from_list_correct [OF from_list_OK, of "ltsga_collect_list_to_list ll",
      folded ltsga_from_collect_list_alt_def]

    from step1 ltsga_collect_list_to_list_set[of ll] 
    show "invar (ltsga_from_collect_list e a ll)" 
         "\<alpha> (ltsga_from_collect_list e a ll) = 
          {(v, e, v'). \<exists>es. (v, es, v') \<in> set ll \<and> e \<in> set es}" 
    by simp_all
  qed

  lemma dltsga_from_collect_list_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes "lts_empty \<alpha> invar e"
    assumes "dlts_add \<alpha> invar a"
    shows "dlts_from_collect_list \<alpha> invar (ltsga_from_collect_list e a)"
  proof 
    fix ll :: "('V \<times> 'W list \<times> 'V) list"
    note from_list_OK = dltsga_from_list_correct [OF assms]
    note step1 = dlts_from_list.dlts_from_list_correct [OF from_list_OK, of "ltsga_collect_list_to_list ll",
      folded ltsga_from_collect_list_alt_def]

    assume "\<forall>v ws ws' w v' v''.
            (v, ws, v') \<in> set ll \<and> (v, ws', v'') \<in> set ll \<and> w \<in> set ws \<and> w \<in> set ws' \<longrightarrow>
            v' = v''"
    hence "\<forall>v w v' v''.
     (v, w, v') \<in> set (ltsga_collect_list_to_list ll) \<and>
     (v, w, v'') \<in> set (ltsga_collect_list_to_list ll) \<longrightarrow>
     v' = v''" by (simp add: ltsga_collect_list_to_list_set) metis

    with step1
    show "invar (ltsga_from_collect_list e a ll)"
         "\<alpha> (ltsga_from_collect_list e a ll) = 
          {(v, e, v'). \<exists>es. (v, es, v') \<in> set ll \<and> e \<in> set es}" 
      by (simp_all add: ltsga_collect_list_to_list_set)
  qed
      
  definition ltsga_to_list :: 
    "('V,'W,_,'L) lts_it \<Rightarrow> ('V,'W,'L) lts_to_list"
    where "ltsga_to_list it \<equiv> iterate_to_list \<circ> it"

  lemma ltsga_to_list_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes it_OK: "lts_iterator \<alpha> invar it"
    shows "lts_to_list \<alpha> invar (ltsga_to_list it)"  
  proof -
    note it_OK' = lts_iterator.lts_it_correct [OF it_OK]
    note to_list = iterate_to_list_correct [OF it_OK']
    
    from to_list show ?thesis
      unfolding lts_to_list_def ltsga_to_list_def o_def by simp
  qed

  fun ltsga_list_to_collect_list where
     "ltsga_list_to_collect_list [] = []"
   | "ltsga_list_to_collect_list ((v, e, v') # l) = 
      (let (yes, no) = partition (\<lambda>vev'. (fst vev' = v) \<and> (snd (snd vev') = v')) l in
       (v, e # (map (fst \<circ> snd) yes), v') # (ltsga_list_to_collect_list no))"

  lemma ltsga_list_to_collect_list_props :
    "distinct (ltsga_list_to_collect_list (l::('V \<times> 'W \<times> 'V) list)) \<and>
     set (ltsga_list_to_collect_list l) = {(v, es, v') . 
     (es \<noteq> [] \<and> es = (map (fst \<circ> snd) (filter (\<lambda>vev'. (fst vev' = v) \<and> (snd (snd vev') = v')) l)))}"
     (is "?P l")
  proof (rule length_induct[of _ l])
    fix l :: "('V \<times> 'W \<times> 'V) list"
    assume ind_hyp: "\<forall>l'. length l' < length l \<longrightarrow> ?P l'"
    show "?P l"
    proof (cases l)
      case Nil thus ?thesis by simp
    next
      case (Cons vev' l') note l_eq[simp] = this
      obtain v e v' where vev'_eq [simp]: "vev' = (v, e, v')" by (cases vev', blast)

      define yes where "yes \<equiv> [vev'\<leftarrow>l' . fst vev' = v \<and> snd (snd vev') = v']"
      define no where "no \<equiv> filter (Not \<circ> (\<lambda>vev'. fst vev' = v \<and> snd (snd vev') = v')) l'"

      have step: "ltsga_list_to_collect_list l = 
          (v, e # map (fst \<circ> snd) yes, v') # ltsga_list_to_collect_list no" 
        by (simp add: yes_def[symmetric] no_def[symmetric])

      have "length no \<le> length l'" unfolding no_def by (rule length_filter_le)
      hence pre_no: "length no < length l" by simp
      from pre_no ind_hyp have ind_hyp_no: "?P no" by simp


      have aux: "\<And>a b. v \<noteq> a \<or> v' \<noteq> b \<Longrightarrow> map (\<lambda>a. fst (snd a))
         [x\<leftarrow>l' .
         (fst x = v \<longrightarrow> snd (snd x) \<noteq> v') \<and>
         fst x = a \<and> snd (snd x) = b] =
       map (\<lambda>a. fst (snd a))
        [vev'\<leftarrow>l' . fst vev' = a \<and> snd (snd vev') = b]" 
        by (induct l', auto)

      show ?thesis 
        unfolding step
        apply (simp add: ind_hyp_no)
        apply (simp add: no_def yes_def set_eq_iff)
        apply (auto simp add: aux)
      done
    qed
  qed

  lemma ltsga_list_to_collect_list_props2 :
    "set l = {(v::'V, e::'W, v'::'V). \<exists>es. (v, es, v') \<in> set (ltsga_list_to_collect_list l) \<and> e \<in> set es}"
    "distinct (map (\<lambda>vesv'. (fst vesv', snd (snd vesv'))) (ltsga_list_to_collect_list l))"
    "(v, es, v') \<in> set (ltsga_list_to_collect_list l) \<longleftrightarrow> 
     (es \<noteq> [] \<and> es = (map (fst \<circ> snd) (filter (\<lambda>vev'. (fst vev' = v) \<and> (snd (snd vev') = v')) l)))"
    by (auto simp add: ltsga_list_to_collect_list_props image_iff filter_empty_conv Bex_def
                       distinct_map inj_on_def)

  definition ltsga_to_collect_list :: 
    "('V,'W,'L) lts_to_list \<Rightarrow> ('V,'W,'L) lts_to_collect_list"
    where "ltsga_to_collect_list to_list l \<equiv> ltsga_list_to_collect_list (to_list l)"

  lemma ltsga_to_collect_list_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes to_list_OK: "lts_to_list \<alpha> invar to_list"
    shows "lts_to_collect_list \<alpha> invar (ltsga_to_collect_list to_list)"  
  proof 
    fix l
    assume "invar l"
    note to_list_OK = lts_to_list.lts_to_list_correct [OF to_list_OK, OF `invar l`]
    note props = ltsga_list_to_collect_list_props [of "to_list l"]
    note props2 = ltsga_list_to_collect_list_props2 [of "to_list l"]

    from props2
    show "\<alpha> l =
        {(v, e, v').
         \<exists>es. (v, es, v') \<in> set (ltsga_to_collect_list to_list l) \<and>
              e \<in> set es}"
        "distinct (map (\<lambda>vesv'. (fst vesv', snd (snd vesv')))
           (ltsga_to_collect_list to_list l))"
      unfolding ltsga_to_collect_list_def
      by (simp_all add: to_list_OK)

    { fix v es v'
      assume "(v, es, v') \<in> set (ltsga_to_collect_list to_list l)" 
      with props show "es \<noteq> []"
        unfolding ltsga_to_collect_list_def
        by (auto simp add: to_list_OK)
    }
  qed

subsection\<open> reverse \<close>

  definition ltsga_reverse :: 
    "('V, 'W, 'L2) lts_empty \<Rightarrow> 
     ('V, 'W, 'L2) lts_add \<Rightarrow> 
     ('V,'W,_,'L1) lts_it \<Rightarrow> ('V,'W,'L1,'L2) lts_reverse"
    where "ltsga_reverse e a it l \<equiv> 
           it l (\<lambda>_. True) (\<lambda>(v, e, v') l'. a v' e v l') (e ())"

  lemma ltsga_reverse_correct :
    fixes \<alpha>1 :: "('V,'W,'L1) lts_\<alpha>"
    fixes \<alpha>2 :: "('V,'W,'L2) lts_\<alpha>"
    assumes "lts_empty \<alpha>2 invar2 e"
    assumes "lts_add \<alpha>2 invar2 a"
    assumes "lts_iterator \<alpha>1 invar1 it"
    shows "lts_reverse \<alpha>1 invar1 \<alpha>2 invar2 (ltsga_reverse e a it)"
  proof -
    interpret 
      lts_empty \<alpha>2 invar2 e + 
      lts_add \<alpha>2 invar2 a +
      lts_iterator \<alpha>1 invar1 it
      by fact+

    {
      fix l
      assume invar_l: "invar1 l"
      have "invar2 (ltsga_reverse e a it l) \<and>
            \<alpha>2 (ltsga_reverse e a it l) = {(v', e, v) |v e v'. (v, e, v') \<in> \<alpha>1 l}"
        unfolding ltsga_reverse_def
        apply (rule_tac set_iterator_no_cond_rule_P[OF lts_it_correct, where 
                 ?I="\<lambda>it \<sigma>. invar2 \<sigma> \<and> 
                             \<alpha>2 \<sigma> = {(v', e, v) |v e v'. (v, e, v') \<in> (\<alpha>1 l) - it}"])
        apply (auto simp add: lts_add_correct lts_empty_correct invar_l)
      done
    }
    thus ?thesis
      by unfold_locales simp_all
  qed

subsection\<open> Quantifiers \<close>

  definition "ltsga_succ_ball it l P v e \<equiv> iterate_ball (it l v e) P"
  definition "ltsga_succ_bex it l P v e \<equiv> iterate_bex (it l v e) P"
  definition "ltsga_pre_ball it l P v' e \<equiv> iterate_ball (it l v' e) P"
  definition "ltsga_pre_bex it l P v' e \<equiv> iterate_bex (it l v' e) P"

  lemma ltsga_succ_ball_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes it_OK: "lts_succ_it \<alpha> invar it"
    shows "lts_succ_ball \<alpha> invar (ltsga_succ_ball it)"  
  proof -
    note step1 = lts_succ_it.lts_succ_it_correct [OF it_OK]
    note step2 = iterate_ball_correct [OF step1]
    thus ?thesis
      unfolding lts_succ_ball_def ltsga_succ_ball_def by simp
  qed

  lemma ltsga_succ_bex_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes it_OK: "lts_succ_it \<alpha> invar it"
    shows "lts_succ_bex \<alpha> invar (ltsga_succ_bex it)"  
  proof -
    note step1 = lts_succ_it.lts_succ_it_correct [OF it_OK]
    note step2 = iterate_bex_correct [OF step1]
    thus ?thesis
      unfolding lts_succ_bex_def ltsga_succ_bex_def by simp
  qed

  lemma ltsga_pre_ball_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes it_OK: "lts_pre_it \<alpha> invar it"
    shows "lts_pre_ball \<alpha> invar (ltsga_pre_ball it)"  
  proof -
    note step1 = lts_pre_it.lts_pre_it_correct [OF it_OK]
    note step2 = iterate_ball_correct [OF step1]
    thus ?thesis
      unfolding lts_pre_ball_def ltsga_pre_ball_def by simp
  qed

  lemma ltsga_pre_bex_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes it_OK: "lts_pre_it \<alpha> invar it"
    shows "lts_pre_bex \<alpha> invar (ltsga_pre_bex it)"  
  proof -
    note step1 = lts_pre_it.lts_pre_it_correct [OF it_OK]
    note step2 = iterate_bex_correct [OF step1]
    thus ?thesis
      unfolding lts_pre_bex_def ltsga_pre_bex_def by simp
  qed

subsection\<open> iterators \<close>

  definition ltsga_iterator where
    "ltsga_iterator it = it (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True)"

  lemma ltsga_iterator_correct:
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes it_OK: "lts_filter_it \<alpha> invar it"
    shows "lts_iterator \<alpha> invar (ltsga_iterator it)"  
  proof (rule lts_iterator.intro)
    fix l
    assume "invar l"

    from lts_filter_it.lts_filter_it_correct [OF it_OK, OF `invar l`,
      of "\<lambda>_. True" "\<lambda>_. True" "\<lambda>_. True" "\<lambda>_. True", folded ltsga_iterator_def]
    show "set_iterator (ltsga_iterator it l) (\<alpha> l)" by simp
  qed


subsection\<open> image and filter \<close>

  definition ltsga_image_filter where
    "ltsga_image_filter e a it f P_v1 P_e P_v2 P l = 
      (it::('V,'W,'\<sigma>,'L) lts_filter_it) P_v1 P_e P_v2 P l (\<lambda>_. True) 
      (\<lambda>vev l. let (v, e, v') = f vev in a v e v' l) (e ())"

  definition ltsga_filter where
    "ltsga_filter e a it = ltsga_image_filter e a it id"

  lemma ltsga_image_filter_correct :
    fixes \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>"
    fixes \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>"
    assumes "lts_empty \<alpha>2 invar2 e"
    assumes "lts_add \<alpha>2 invar2 a"
    assumes "lts_filter_it \<alpha>1 invar1 it"
    shows "lts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (ltsga_image_filter e a it)"
  proof
    interpret 
      lts_empty \<alpha>2 invar2 e + 
      lts_add \<alpha>2 invar2 a +
      lts_filter_it \<alpha>1 invar1 it
      by fact+

    fix l P_v1 P_e P_v2 P and f :: "('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)"
    assume invar: "invar1 l"

    have it: "set_iterator (it P_v1 P_e P_v2 P l)
                {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}" 
      using lts_filter_it_correct [of l P_v1 P_e P_v2 P, OF invar] .

    let ?I = "\<lambda>S \<sigma>. invar2 \<sigma> \<and> \<alpha>2 \<sigma> = f ` S" 

    have "?I {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)} 
             (ltsga_image_filter e a it f P_v1 P_e P_v2 P l)"
      unfolding ltsga_image_filter_def
      apply (rule set_iterator_no_cond_rule_insert_P [OF it, where I = "?I"])
      apply (simp_all add: lts_empty_correct lts_add_correct Let_def split: prod.splits)
    done
    thus "invar2 (ltsga_image_filter e a it f P_v1 P_e P_v2 P l)"
         "\<alpha>2 (ltsga_image_filter e a it f P_v1 P_e P_v2 P l) =
          f ` {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}" 
      by simp_all
  qed

  lemma ltsga_filter_correct :
    fixes \<alpha> :: "('V1,'W1,'L1) lts_\<alpha>"
    assumes e_OK: "lts_empty \<alpha> invar e"
    assumes a_OK: "lts_add \<alpha> invar a"
    assumes it_OK: "lts_filter_it \<alpha> invar it"
    shows "lts_filter \<alpha> invar (ltsga_filter e a it)"
    using ltsga_image_filter_correct [OF e_OK a_OK it_OK]
    unfolding lts_filter_def lts_image_filter_def ltsga_filter_def
    by simp

  lemma dltsga_image_filter_correct :
    fixes \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>"
    fixes \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>"
    assumes "lts_empty \<alpha>2 invar2 e"
    assumes "dlts_add \<alpha>2 invar2 a"
    assumes "lts_filter_it \<alpha>1 invar1 it"
    shows "dlts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (ltsga_image_filter e a it)"
  proof
    interpret 
      lts_empty \<alpha>2 invar2 e + 
      dlts_add \<alpha>2 invar2 a +
      lts_filter_it \<alpha>1 invar1 it
      by fact+

    fix l P_v1 P_e P_v2 P and f :: "('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)"
    assume invar: "invar1 l"
       and weak_det: "LTS_is_deterministic (f ` {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)})"

    define D where "D \<equiv> {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

    have it: "set_iterator (it P_v1 P_e P_v2 P l) D" 
      using lts_filter_it_correct [of l P_v1 P_e P_v2 P, OF invar] unfolding D_def .

    let ?I = "\<lambda>S \<sigma>. invar2 \<sigma> \<and> \<alpha>2 \<sigma> = f ` S" 

    have "?I D (ltsga_image_filter e a it f P_v1 P_e P_v2 P l)"
      unfolding ltsga_image_filter_def
      apply (rule set_iterator_no_cond_rule_insert_P [OF it, where I = "?I"])
      apply (simp_all add: lts_empty_correct Let_def split: prod.splits)
      apply clarify
      apply (rename_tac S \<sigma> v1 w v2 v1' w' v2')
      proof -
        fix S \<sigma> v1 w v2 v1' w' v2'
        assume "S \<subseteq> D" and in_D: "(v1, w, v2) \<in> D" and "(v1, w, v2) \<notin> S" and
               invar: "invar2 \<sigma>" and \<alpha>2_\<sigma>: "\<alpha>2 \<sigma> = f ` S" and
               f_eq: "f (v1, w, v2) = (v1', w', v2')"

        { fix v'' 
          assume "(v1', w', v'') \<in> \<alpha>2 \<sigma>" 
          with \<alpha>2_\<sigma> `S \<subseteq> D` have "(v1', w', v'') \<in> f ` D" by auto
          moreover
            from in_D f_eq have "(v1', w', v2') \<in> f ` D" by (simp add: image_iff Bex_def) metis
          ultimately have "v'' = v2'" 
            using weak_det[folded D_def]
            unfolding LTS_is_deterministic_def by metis
        } note dist = this

        from dlts_add_correct[OF invar, of v2' v1' w'] dist \<alpha>2_\<sigma>
        show "invar2 (a v1' w' v2' \<sigma>) \<and> \<alpha>2 (a v1' w' v2' \<sigma>) = insert (v1', w', v2') (f ` S)" 
          by metis
      qed
    
    thus "invar2 (ltsga_image_filter e a it f P_v1 P_e P_v2 P l)"
         "\<alpha>2 (ltsga_image_filter e a it f P_v1 P_e P_v2 P l) =
          f ` {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}" 
      by (simp_all add: D_def[symmetric])
  qed

  lemma dltsga_inj_image_filter_correct :
    fixes \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>"
    fixes \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>"
    assumes e_OK: "lts_empty \<alpha>2 invar2 e"
    assumes a_OK: "dlts_add \<alpha>2 invar2 a"
    assumes it_OK: "lts_filter_it \<alpha>1 invar1 it"
    assumes dlts: "dlts \<alpha>1 invar1"
    shows "lts_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (ltsga_image_filter e a it)"
  proof 
    interpret 
      dlts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 "ltsga_image_filter e a it"
      using dltsga_image_filter_correct [OF e_OK a_OK it_OK] .

    fix l P_v1 P_e P_v2 P and f :: "('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)"
    assume invar: "invar1 l"
       and f_inj_on: "LTS_image_filter_inj_on f {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

    define D where "D \<equiv> {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

    have D_subset: "D \<subseteq> \<alpha>1 l" unfolding D_def by (simp add: subset_iff)
    from dlts invar have weak_det: "LTS_is_deterministic (\<alpha>1 l)"
      unfolding dlts_def by simp   

    have weak_det': "LTS_is_deterministic (f ` D)"
    proof 
      fix v1 w1 v2 v3
      assume v2_in: "(v1, w1, v2) \<in> f ` D" 
      assume v3_in: "(v1, w1, v3) \<in> f ` D"

      from v2_in obtain v1' w1' v2' where 
         v2_in': "(v1', w1', v2') \<in> D" and f_v2: "f (v1', w1', v2') = (v1, w1, v2)" by auto
      from v3_in obtain v1'' w1'' v3'' where 
         v3_in': "(v1'', w1'', v3'') \<in> D" and f_v3: "f (v1'', w1'', v3'') = (v1, w1, v3)" by auto

      from f_inj_on f_v3 f_v2 v2_in' v3_in' have v1''_eq[simp]: "v1'' = v1'"  and w1''_eq[simp]: "w1'' = w1'"
        unfolding LTS_image_filter_inj_on_def[abs_def] D_def[symmetric]
        by (simp_all add: Bex_def Ball_def)

      with weak_det D_subset v2_in' v3_in' have v3''_eq[simp]: "v3'' = v2'"
        unfolding LTS_is_deterministic_def by (simp add: subset_iff) metis
 
      from f_v2 f_v3 show "v2 = v3" by simp
    qed

    from dlts_image_filter_correct [OF invar, of f P_v1 P_e P_v2 P, folded D_def, OF weak_det']
    show "invar2 (ltsga_image_filter e a it f P_v1 P_e P_v2 P l)"
         "\<alpha>2 (ltsga_image_filter e a it f P_v1 P_e P_v2 P l) =
          f ` {(v1, e, v2). (v1, e, v2) \<in> \<alpha>1 l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}" 
      by (simp_all add: D_def[symmetric])
  qed

  lemma dltsga_filter_correct :
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes e_OK: "lts_empty \<alpha> invar e"
    assumes a_OK: "dlts_add \<alpha> invar a"
    assumes it_OK: "lts_filter_it \<alpha> invar it"
    assumes dlts: "dlts \<alpha> invar"
    shows "lts_filter \<alpha> invar (ltsga_filter e a it)"
    using dltsga_inj_image_filter_correct [OF e_OK a_OK it_OK dlts]
    unfolding lts_filter_def lts_inj_image_filter_def ltsga_filter_def
    by (simp add: LTS_image_filter_inj_on_id)

  definition ltsga_image where
    "ltsga_image imf f = imf f (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True)"

  lemma ltsga_image_correct :
    "lts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 imf \<Longrightarrow>
     lts_image \<alpha>1 invar1 \<alpha>2 invar2 (ltsga_image imf)"
  unfolding lts_image_filter_def lts_image_def ltsga_image_def by simp

  lemma dltsga_image_correct :
    "dlts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 imf \<Longrightarrow>
     dlts_image \<alpha>1 invar1 \<alpha>2 invar2 (ltsga_image imf)"
  unfolding dlts_image_filter_def dlts_image_def ltsga_image_def by simp    


subsection \<open> All successors of a set \<close>

  text \<open> Iterators visit each element exactly once.
          For getting all the successors of a set of nodes, it is therefore benefitial
          to collect the successors in a set and then later iterate over this set. \<close>

  definition ltsga_set_succs where
    "ltsga_set_succs 
       (v_ops :: ('V, 'V_set, _) set_ops_scheme)
       (succ_it :: ('V,'W,'V_set,'L) lts_succ_it)
       (v_it :: ('V_set2 \<Rightarrow> ('V,'V_set) set_iterator)) 
       (d :: 'L) 
       V e = 
     (v_it V (\<lambda>_. True) (\<lambda>v. succ_it d v e (\<lambda>_. True) (set_op_ins v_ops)) (set_op_empty v_ops ()))"

(* Unused in Cava, hence not ported
  lemma ltsga_set_succs_correct :
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
      and v_ops :: "('V, 'V_set, _) set_ops_scheme"
      and v2_ops :: "('V, 'V_set2, _) set_ops_scheme"
      and succ_it :: "('V,'W,'V_set,'L) lts_succ_it"
      and v_it :: "'V_set2 \<Rightarrow> ('V,'V_set) set_iterator"
      and e V
    assumes succ_it_OK: "lts_succ_it \<alpha> invar succ_it"
        and set_OK: "StdSet v_ops"
        and set_OK2: "StdSet v_ops2"
        and it_OK: "poly_set_iteratei 
          (set_op_\<alpha> v_ops2) (set_op_invar v_ops2) v_it"
        and invar_d: "invar d"
        and invar_V: "set_op_invar v_ops2 V"
    defines "res \<equiv> ltsga_set_succs v_ops succ_it v_it d V e"
    shows "set_op_invar v_ops res"
          "set_op_\<alpha> v_ops res = {v' |v v'. (v, e, v') \<in> \<alpha> d \<and> v \<in> set_op_\<alpha> v_ops2 V}"
   proof -
     interpret v: StdSet v_ops by fact
     interpret v2: StdSet v_ops2 by fact

     def inner \<equiv> "\<lambda>v s. succ_it d v e (\<lambda>_. True) (\<lambda>x s. v.ins x s) s"

     from lts_succ_it.lts_succ_it_correct[OF succ_it_OK, OF invar_d, of _ e]
     have succ_it_OK': "\<And>v. set_iterator (succ_it d v e) {v' |v'. (v, e, v') \<in> \<alpha> d}"
       by simp

     { fix v s
       assume invar_s: "v.invar s"
 
       let ?I = "\<lambda>S \<sigma>. v.invar \<sigma> \<and> v.\<alpha> \<sigma> = v.\<alpha> s \<union> S"
       
       have "?I {v' . (v, e, v') \<in> \<alpha> d} (inner v s)"
         apply (unfold inner_def)
         apply (rule set_iterator_no_cond_rule_insert_P [OF succ_it_OK', where I = ?I])
         apply (simp_all add: invar_s v.correct)
       done
     } note inner_OK = this
     
     thm it_OK

     let ?I2 = "\<lambda>S \<sigma>. v.invar \<sigma> \<and> v.\<alpha> \<sigma> = {v' |v v'. (v, e, v') \<in> \<alpha> d \<and> v \<in> S}"
     have "?I2 (v2.\<alpha> V) (v_it V (\<lambda>_. True) (\<lambda>v s. inner v s) (v.empty ()))"

       thm it_OK
       thm set_iterate.iterate_rule_insert_P

       apply (rule set_iteratei.iteratei_rule_insert_P [OF it_OK, OF invar_V, where I = ?I2])
       apply (simp_all add: v.correct inner_OK)
       apply auto
     done

     thus "v.invar res"
          "v.\<alpha> res = {v' |v v'. (v, e, v') \<in> \<alpha> d \<and> v \<in> v2.\<alpha> V}"
       unfolding inner_def res_def ltsga_set_succs_def
       by simp_all
  qed
*)

end
