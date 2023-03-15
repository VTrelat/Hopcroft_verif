header "Implementing Labelled Transition Systems by Maps"
theory DLTSByMap
imports LTSSpec LTSGA
begin

locale dltsbm_defs = 
  m1!: StdMap m1_ops +
  m2!: StdMap m2_ops 
  for m1_ops::"('V,'m2,'m1,_) map_ops_scheme"
  and m2_ops::"('W,'V,'m2,_) map_ops_scheme"
begin
  definition dltsbm_\<alpha> :: "('V,'W,'m1) lts_\<alpha>" where
    "dltsbm_\<alpha> m1 \<equiv> {(v,w,v'). 
      \<exists>m2. m1.\<alpha> m1 v = Some m2  \<and> m2.\<alpha> m2 w = Some v'}"

  definition "dltsbm_invar m1 \<equiv>
    m1.invar m1 \<and> (\<forall>m2 \<in> ran (m1.\<alpha> m1). m2.invar m2)"

  lemma dltsbm_invar_alt_def : 
    "dltsbm_invar m1 = 
     (m1.invar m1 \<and>
      (\<forall>v m2. m1.\<alpha> m1 v = Some m2 \<longrightarrow> (
         m2.invar m2)))"
  unfolding dltsbm_invar_def 
  by (auto simp add: ran_def)

  lemma dltsbm_invar_alt_def2 : 
    "dltsbm_invar m1 = 
     (m1.invar m1 \<and>
      (\<forall>v m2. m1.lookup v m1 = Some m2 \<longrightarrow> (
         m2.invar m2)))"
  unfolding dltsbm_invar_alt_def 
  by (auto simp add: m1.correct m2.correct)

  lemma dlts_correct : "dlts dltsbm_\<alpha> dltsbm_invar"
    unfolding dlts_def dltsbm_\<alpha>_def dltsbm_invar_alt_def
    by auto

  definition dltsbm_empty :: "('V,'W,'m1) lts_empty" where 
    "dltsbm_empty \<equiv> m1.empty"

  lemma dltsbm_empty_correct: 
    "lts_empty dltsbm_\<alpha> dltsbm_invar dltsbm_empty"    
    unfolding lts_empty_def dltsbm_empty_def dltsbm_\<alpha>_def dltsbm_invar_def
    by (simp add: m1.correct)

  definition dltsbm_succ :: "('V,'W,'m1) lts_succ" where 
    "dltsbm_succ l v e \<equiv> 
     case m1.lookup v l of 
        None \<Rightarrow> None |
        Some m2 \<Rightarrow> m2.lookup e m2"

  lemma dltsbm_succ_correct :
     "dlts_succ dltsbm_\<alpha> dltsbm_invar dltsbm_succ"
   unfolding dlts_succ_def dltsbm_invar_alt_def dltsbm_\<alpha>_def dltsbm_succ_def
   by (simp add: m1.correct m2.correct split: option.split)

  definition dltsbm_memb :: "('V,'W,'m1) lts_memb" where 
    "dltsbm_memb l v e v' \<equiv> 
     case m1.lookup v l of 
        None \<Rightarrow> False |
        Some m2 \<Rightarrow> m2.lookup e m2 = Some v'"

  lemma dltsbm_memb_correct :
     "lts_memb dltsbm_\<alpha> dltsbm_invar dltsbm_memb"
   unfolding lts_memb_def dltsbm_invar_alt_def dltsbm_\<alpha>_def dltsbm_memb_def
   by (simp add: m1.correct m2.correct split: option.split)

  definition dltsbm_add :: "('V,'W,'m1) lts_add" where 
    "dltsbm_add v w v' l \<equiv>  
     case m1.lookup v l of 
        None \<Rightarrow> (m1.update v (m2.sng w v') l) |
        Some m2 \<Rightarrow> m1.update v (m2.update w v' m2) l"

  lemma dltsbm_add_correct:
    "dlts_add dltsbm_\<alpha> dltsbm_invar dltsbm_add"
  proof
    fix l v w v'
    assume invar: "dltsbm_invar l"

    from invar
    show "dltsbm_invar (dltsbm_add v w v' l)"
      unfolding dltsbm_invar_alt_def dltsbm_add_def
      by (simp add: m1.correct m2.correct split: option.split split_if_asm)

    assume "\<And>v''. v'' \<noteq> v' \<Longrightarrow> (v, w, v'') \<notin> dltsbm_\<alpha> l" 
    with invar show "dltsbm_\<alpha> (dltsbm_add v w v' l) = insert (v, w, v') (dltsbm_\<alpha> l)"
      unfolding dltsbm_invar_alt_def dltsbm_\<alpha>_def dltsbm_add_def
      apply (simp add: m1.correct m2.correct set_eq_iff
               split: option.split split_if_asm)
      apply auto 
      apply metis
    done
  qed

  definition dltsbm_add_succs :: "('V,'W,'m1) lts_add_succs" where 
    "dltsbm_add_succs v w vs l \<equiv> (case vs of [] \<Rightarrow> l | (v'#vs') \<Rightarrow> dltsbm_add v w v' l)"

  lemma dltsbm_add_succs_correct:
    "dlts_add_succs dltsbm_\<alpha> dltsbm_invar dltsbm_add_succs"
  proof
    fix l :: "'m1" and v :: 'V and w :: 'W and vs :: "'V list"
    assume invar: "dltsbm_invar l"

    note add_OK = dlts_add.dlts_add_correct [OF dltsbm_add_correct, OF invar]
    assume len_vs: "length vs < 2"
    assume l_OK: "\<And>v'. v' \<notin> set vs \<Longrightarrow> (v, w, v') \<notin> dltsbm_\<alpha> l"
 
    have "dltsbm_invar (dltsbm_add_succs v w vs l) \<and>
          dltsbm_\<alpha> (dltsbm_add_succs v w vs l) = dltsbm_\<alpha> l \<union> {(v, w, v') |v'. v' \<in> set vs}"  
    proof (cases vs)
      case Nil thus ?thesis by (simp add: dltsbm_add_succs_def invar)
    next
      case (Cons v' vs')
      with len_vs have vs_eq[simp]:"vs = [v']" by auto
      with l_OK add_OK show ?thesis
        by (simp add: dltsbm_add_succs_def)
    qed
    thus "dltsbm_invar (dltsbm_add_succs v w vs l)"
         "dltsbm_\<alpha> (dltsbm_add_succs v w vs l) = dltsbm_\<alpha> l \<union> {(v, w, v') |v'. v' \<in> set vs}"  
      by simp_all
  qed

  definition dltsbm_delete :: "('V,'W,'m1) lts_delete" where 
    "dltsbm_delete v w v' m1 \<equiv>  
     case m1.lookup v m1 of 
        None \<Rightarrow> m1 |
        Some m2 \<Rightarrow> (case m2.lookup w m2 of
          None \<Rightarrow> m1 |
          Some v'' \<Rightarrow> if (v' = v'') then m1.update v (m2.delete w m2) m1 else m1)"

  lemma dltsbm_delete_correct:
    "lts_delete dltsbm_\<alpha> dltsbm_invar dltsbm_delete"
  proof
    fix l v w v'
    assume invar: "dltsbm_invar l"

    from invar
    show "dltsbm_invar (dltsbm_delete v w v' l)"
      unfolding dltsbm_invar_alt_def dltsbm_delete_def
      by (simp add: m1.correct m2.correct split: option.split split_if_asm)

    from invar 
    show "dltsbm_\<alpha> (dltsbm_delete v w v' l) = (dltsbm_\<alpha> l) - {(v, w, v')}"
      unfolding dltsbm_invar_alt_def dltsbm_\<alpha>_def dltsbm_delete_def
      apply (simp add: m1.correct m2.correct set_eq_iff restrict_map_def
               split: option.split split_if_asm)
      apply auto
    done
  qed

  definition dltsbm_succ_it where
    "dltsbm_succ_it m1 v e =
     (case m1.lookup v m1 of
         None \<Rightarrow> set_iterator_emp
       | Some m2 \<Rightarrow>
           (case m2.lookup e m2 of
               None \<Rightarrow> set_iterator_emp
             | Some v' \<Rightarrow> set_iterator_sng v'))"

  lemma dltsbm_succ_it_correct :
    shows "lts_succ_it dltsbm_\<alpha> dltsbm_invar dltsbm_succ_it"
  unfolding lts_succ_it_def
  proof (intro allI impI)
    fix l v e
    assume invar_l: "dltsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding dltsbm_invar_def by simp

    show "set_iterator (dltsbm_succ_it l v e)
             {v' . (v, e, v') \<in> dltsbm_\<alpha> l}"
    proof (cases "m1.lookup v l")
      case None note m1_v_eq = this
      with invar_m1 have "{v' |v'. (v, e, v') \<in> dltsbm_\<alpha> l} = {}"
        unfolding dltsbm_\<alpha>_def
         by (simp add: m1.correct)         
      thus ?thesis
        unfolding dltsbm_succ_it_def
        by (simp add: m1_v_eq set_iterator_emp_correct)
    next
      case (Some m2) note m1_v_eq = this
      with invar_l have invar_m2: "m2.invar m2" 
        unfolding dltsbm_invar_alt_def 
        by (simp add: m1.correct)

      show ?thesis
      proof (cases "m2.lookup e m2")
        case None note m2_e_eq = this
        with invar_m1 invar_m2 m1_v_eq have "{v' |v'. (v, e, v') \<in> dltsbm_\<alpha> l} = {}"
          unfolding dltsbm_\<alpha>_def
           by (simp add: m1.correct m2.correct)         
        thus ?thesis
          unfolding dltsbm_succ_it_def
          by (simp add: m1_v_eq m2_e_eq set_iterator_emp_correct)
      next
        case (Some v') note m2_e_eq = this
        with invar_m1 invar_m2 m1_v_eq have "{v' |v'. (v, e, v') \<in> dltsbm_\<alpha> l} = {v'}"
          unfolding dltsbm_\<alpha>_def
           by (simp add: m1.correct m2.correct)         
        thus ?thesis
          unfolding dltsbm_succ_it_def
          by (simp add: m1_v_eq m2_e_eq set_iterator_sng_correct)
      qed
    qed
  qed

  definition dltsbm_succ_label_it where
    "dltsbm_succ_label_it it2 m1 v =
     (case m1.lookup v m1 of
         None \<Rightarrow> set_iterator_emp
       | Some m2 \<Rightarrow> it2 m2)"

  lemma dltsbm_succ_label_it_alt_def :
    "dltsbm_succ_label_it = (\<lambda>it2 m1 v. 
      (case m1.lookup v m1 of
          None \<Rightarrow> \<lambda>c f \<sigma>0. \<sigma>0
        | Some m2 \<Rightarrow> it2 m2))"
    unfolding dltsbm_succ_label_it_def[abs_def] 
              curry_def set_iterator_emp_def[abs_def] fst_conv snd_conv
    by simp

  lemma dltsbm_succ_label_it_correct :
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    shows "lts_succ_label_it dltsbm_\<alpha> dltsbm_invar (dltsbm_succ_label_it it2)"
  unfolding lts_succ_label_it_def
  proof (intro allI impI)
    fix l v
    assume invar_l: "dltsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding dltsbm_invar_def by simp

    show "set_iterator (dltsbm_succ_label_it it2 l v) 
             {(e, v') . (v, e, v') \<in> dltsbm_\<alpha> l}"
    proof (cases "m1.lookup v l")
      case None note m1_v_eq = this
      with invar_m1 have "{(e, v') |e v'. (v, e, v') \<in> dltsbm_\<alpha> l} = {}"
        unfolding dltsbm_\<alpha>_def
         by (simp add: m1.correct)         
      thus ?thesis
        unfolding dltsbm_succ_label_it_def
        by (simp add: m1_v_eq set_iterator_emp_correct)
    next
      case (Some m2) note m1_v_eq = this
      with invar_l have invar_m2: "m2.invar m2" 
        unfolding dltsbm_invar_alt_def 
        by (simp add: m1.correct)

      have it2_OK': "map_iterator (it2 m2) (m2.\<alpha> m2)"
        using map_iteratei.iteratei_rule[OF it2_OK, OF invar_m2] by simp

      from m1_v_eq invar_m1 have "{(e, v') |e v'. (v, e, v') \<in> dltsbm_\<alpha> l} = map_to_set (m2.\<alpha> m2)"
        unfolding dltsbm_\<alpha>_def
        by (simp add: m1.correct map_to_set_def)         

      with it2_OK' show ?thesis 
        unfolding dltsbm_succ_label_it_def
        by (simp add: m1_v_eq set_iterator_emp_correct)
    qed
  qed

  definition dltsbm_filter_it where
    "dltsbm_filter_it it1 it2 P_v1 P_e P_v2 P m1 =
        set_iterator_filter (\<lambda>vev'. P_v2 (snd (snd vev')) \<and> P_e (fst (snd vev')) \<and> P vev')
        (map_iterator_product 
           (map_iterator_key_filter P_v1 (it1 m1)) 
           it2)"

  lemma dltsbm_filter_it_alt_def :
     "dltsbm_filter_it = (\<lambda>it1 it2 P_v1 P_e P_v2 P m1 c f.
        it1 m1 c
         (\<lambda>(v1, m2) \<sigma>. if P_v1 v1
                then it2 m2 c
                      (\<lambda>(e, v2) \<sigma>. if P_v2 v2 \<and>
                                P_e e \<and> P (v1, (e, v2))
                             then f (v1, (e, v2)) \<sigma> else \<sigma>)
                      \<sigma>
                else \<sigma>))"
     unfolding dltsbm_filter_it_def[abs_def] map_iterator_product_alt_def split_def pair_collapse
               fst_conv snd_conv set_iterator_filter_alt_def map_iterator_key_filter_alt_def
               
     by simp

  lemma dltsbm_filter_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    shows "lts_filter_it dltsbm_\<alpha> dltsbm_invar (dltsbm_filter_it it1 it2)"
  unfolding lts_filter_it_def
  proof (intro allI impI)
    fix l P_v1 P_e P_v2 P
    assume invar_l: "dltsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding dltsbm_invar_def by simp

    let ?S_2'' = "\<lambda>m2. {(e, v'). m2.\<alpha> m2 e = Some v'}"

    { fix v m2
      assume l_v_eq:"(m1.\<alpha> l |` {v. P_v1 v}) v = Some m2"

      from invar_l l_v_eq have invar_m2: "m2.invar m2"
        unfolding dltsbm_invar_alt_def 
        by (auto simp add: m1.correct restrict_map_eq)

      note it2_OK' = map_iteratei.iteratei_rule [OF it2_OK, OF invar_m2]
      hence "set_iterator (it2 m2) (?S_2'' m2)" unfolding map_to_set_def by simp
    } note it2_OK'' = this

    note it1_OK' = map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1]
    note it1_OK'' = map_iterator_key_filter_correct [OF it1_OK', of P_v1]

    let ?it1'' = "map_iterator_product 
      (map_iterator_key_filter P_v1 (it1 l)) it2"
    let ?S_1'' = "{(k, e). \<exists>v. m1.\<alpha> l k = Some v \<and> P_v1 k \<and>
           (case e of (e, v') \<Rightarrow> m2.\<alpha> v e = Some v')}"

    have S_1''_eq: "?S_1'' = {(v, e, v'). (v, e, v') \<in> dltsbm_\<alpha> l \<and> P_v1 v}"
      unfolding dltsbm_\<alpha>_def by auto

    from map_iterator_product_correct [OF it1_OK'', of it2 ?S_2''] it2_OK''
    have it1_OK'': "set_iterator ?it1'' 
       {(v, e, v'). (v, e, v') \<in> dltsbm_\<alpha> l \<and> P_v1 v}"
      by (simp add: restrict_map_eq S_1''_eq)

    from set_iterator_filter_correct [OF it1_OK'', of "\<lambda>vev'. P_v2 (snd (snd vev')) \<and> P_e (fst (snd vev')) \<and> P vev'"]
    show "set_iterator (dltsbm_filter_it it1 it2 P_v1 P_e P_v2 P l)
           {(v1, e, v2). (v1, e, v2) \<in> dltsbm_\<alpha> l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"
      unfolding dltsbm_filter_it_def[symmetric] 
      apply simp
      apply (rule subst [where P = "set_iterator (dltsbm_filter_it it1 it2 P_v1 P_e P_v2 P l)"])
      apply auto
    done
  qed

  definition dltsbm_it where
    "dltsbm_it it1 it2 = ltsga_iterator (dltsbm_filter_it it1 it2)"

  lemma dltsbm_it_alt_def :
     "dltsbm_it = (\<lambda>it1 it2 m1 c f. it1 m1 c (\<lambda>(v1, m2). it2 m2 c (\<lambda>(e, v2). f (v1, e, v2))))"
     unfolding dltsbm_it_def[abs_def] ltsga_iterator_def dltsbm_filter_it_alt_def 
     by simp

  lemma dltsbm_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    shows "lts_iterator dltsbm_\<alpha> dltsbm_invar (dltsbm_it it1 it2)"
  unfolding dltsbm_it_def
  apply (rule ltsga_iterator_correct)
    apply (rule dltsbm_filter_it_correct)
    apply fact+
  done

  definition dltsbm_pre_it where
   "dltsbm_pre_it it1 (l::'m1) (v'::'V) (e::'W) =
    map_iterator_dom_filter (\<lambda>vm2. 
      case m2.lookup e (snd vm2) of
         None \<Rightarrow> False
       | Some v'' \<Rightarrow> (v' = v'')) (it1 l)"

  lemma dltsbm_pre_it_alt_def :
    "dltsbm_pre_it = 
     (\<lambda>it1 l v' e c f.
        it1 l c
         (\<lambda>kv \<sigma>.
             if option_case False (op = v')
                 (map_op_lookup m2_ops e (snd kv))
             then f (fst kv) \<sigma> else \<sigma>))"
    unfolding dltsbm_pre_it_def[abs_def] map_iterator_dom_filter_alt_def curry_def
              fst_conv snd_conv by simp

  lemma dltsbm_pre_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    shows "lts_pre_it dltsbm_\<alpha> dltsbm_invar (dltsbm_pre_it it1)"
  unfolding lts_pre_it_def
  proof (intro allI impI)
    fix l v' e
    assume invar_l: "dltsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding dltsbm_invar_def by simp

    from map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1] have
      step1: "set_iterator (it1 l) (map_to_set (map_op_\<alpha> m1_ops l))" .
    
    from map_iterator_dom_filter_correct [OF step1, 
      of "\<lambda>vm2. case m2.lookup e (snd vm2) of None \<Rightarrow> False | Some v'' \<Rightarrow> v'=v''"]
    have step2: "set_iterator (dltsbm_pre_it it1 l v' e)
          {k. \<exists>v. m1.\<alpha> l k = Some v \<and>
             (case m2.lookup e v of None \<Rightarrow> False
              | Some v'' \<Rightarrow> v'= v'')}"
      by (simp add: dltsbm_pre_it_def[symmetric])
     
   from invar_l 
   have step3: "{k. \<exists>v. m1.\<alpha> l k = Some v \<and> (case m2.lookup e v of None \<Rightarrow> False
                                  | Some v'' \<Rightarrow> v' = v'')} = 
                {v |v. (v, e, v') \<in> dltsbm_\<alpha> l}"
     unfolding dltsbm_\<alpha>_def dltsbm_invar_alt_def
     by (auto simp add: map_to_set_def m1.correct m2.correct split: option.splits)
        (metis m2.lookup_correct map_upd_eqD1)

   from step2 step3
   show "set_iterator (dltsbm_pre_it it1 l v' e) {v . (v, e, v') \<in> dltsbm_\<alpha> l}" 
     unfolding dltsbm_pre_it_def by simp
  qed

  definition dltsbm_pre_label_it where
    "dltsbm_pre_label_it it1 it2 m1 v' =
        map_iterator_product (it1 m1) 
           (\<lambda>m2. map_iterator_dom_filter (op= v' \<circ> snd)
              (it2 m2))"

  lemma dltsbm_pre_label_it_alt_def :
     "dltsbm_pre_label_it = 
      (\<lambda>it1 it2 m1 v' c f.
        it1 m1 c
         (\<lambda>a. it2 (snd a) c
               (\<lambda>kv \<sigma>.
                   if v' = snd kv then f (fst a, fst kv) \<sigma>
                   else \<sigma>)))"
     unfolding dltsbm_pre_label_it_def[abs_def] map_iterator_product_alt_def  
               curry_def map_iterator_dom_filter_alt_def
               fst_conv snd_conv by simp

  lemma dltsbm_pre_label_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    shows "lts_pre_label_it dltsbm_\<alpha> dltsbm_invar (dltsbm_pre_label_it it1 it2)"
  unfolding lts_pre_label_it_def
  proof (intro allI impI)
    fix l v'
    assume invar_l: "dltsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding dltsbm_invar_def by simp

    let ?it_b = "\<lambda>m2. map_iterator_dom_filter (op= v' \<circ> snd) (it2 m2)"
    let ?S_b = "\<lambda>m2. {e . m2.\<alpha> m2 e = Some v'}"

    { fix v m2
      assume l_v_eq: "m1.\<alpha> l v = Some m2"

      from invar_l l_v_eq have invar_m2: "m2.invar m2"
        unfolding dltsbm_invar_alt_def 
        by (simp add: m1.correct)

      note it2_OK' = map_iteratei.iteratei_rule [OF it2_OK, OF invar_m2]
      from map_iterator_dom_filter_correct [OF it2_OK', of "op= v' \<circ> snd"]
      have "set_iterator (?it_b m2) (?S_b m2)" 
        by simp
    } note it_b_aux = this

    from invar_l
    have S_b_aux: "{(k, e). \<exists>v. m1.\<alpha> l k = Some v \<and> e \<in> ?S_b v} = 
                   {(v, e) |v e. (v, e, v') \<in> dltsbm_\<alpha> l}" 
      unfolding dltsbm_invar_alt_def dltsbm_\<alpha>_def
      by (auto simp add: m1.correct m2.correct)

    note it1_OK' = map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1]
    from map_iterator_product_correct [OF it1_OK', of ?it_b ?S_b] S_b_aux it_b_aux
    show "set_iterator (dltsbm_pre_label_it it1 it2 l v')
             {(v, e) . (v, e, v') \<in> dltsbm_\<alpha> l} "
      by (simp add: dltsbm_pre_label_it_def[symmetric])
  qed
end

end
