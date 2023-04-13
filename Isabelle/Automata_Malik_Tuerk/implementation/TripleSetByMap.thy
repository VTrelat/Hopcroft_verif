section "Implementing a set of triples by maps"
theory TripleSetByMap
imports TripleSetSpec
begin


locale tsbm_defs = 
  m1: StdMap m1_ops +
  m2: StdMap m2_ops +
  s3: StdSet s3_ops 
  for m1_ops::"('a,'m2,'m1,_) map_ops_scheme"
  and m2_ops::"('b,'s3,'m2,_) map_ops_scheme"
  and s3_ops::"('c,'s3,_) set_ops_scheme"
begin
  definition tsbm_\<alpha> :: "('a,'b,'c,'m1) triple_set_\<alpha>" where
    "tsbm_\<alpha> m1 \<equiv> {(v,w,v'). 
      \<exists>m2 s3. m1.\<alpha> m1 v = Some m2 
            \<and> m2.\<alpha> m2 w = Some s3
            \<and> v' \<in> s3.\<alpha> s3}"

  definition "tsbm_invar m1 \<equiv>
    m1.invar m1 \<and>
    (\<forall>m2 \<in> ran (m1.\<alpha> m1). m2.invar m2 \<and>
       (\<forall>s3\<in>ran (m2.\<alpha> m2). s3.invar s3))"

  lemma tsbm_invar_alt_def : 
    "tsbm_invar m1 = 
     (m1.invar m1 \<and>
      (\<forall>v m2. m1.\<alpha> m1 v = Some m2 \<longrightarrow> (
         m2.invar m2 \<and> 
         (\<forall>w s3. m2.\<alpha> m2 w = Some s3 \<longrightarrow>
             s3.invar s3))))"
  unfolding tsbm_invar_def 
  by (auto simp add: ran_def)

  lemma tsbm_invar_alt_def2 : 
    "tsbm_invar m1 = 
     (m1.invar m1 \<and>
      (\<forall>v m2. m1.lookup v m1 = Some m2 \<longrightarrow> (
         m2.invar m2 \<and> 
         (\<forall>w s3. m2.lookup w m2 = Some s3 \<longrightarrow>
             s3.invar s3))))"
  unfolding tsbm_invar_alt_def 
  by (auto simp add: m1.correct m2.correct)

  definition tsbm_empty :: "('a,'b,'c,'m1) triple_set_empty" where 
    "tsbm_empty \<equiv> m1.empty"

  lemma tsbm_empty_correct: 
    "triple_set_empty tsbm_\<alpha> tsbm_invar tsbm_empty"    
    unfolding triple_set_empty_def tsbm_empty_def tsbm_\<alpha>_def tsbm_invar_def
    by (simp add: m1.correct)

  definition tsbm_add :: "('a,'b,'c,'m1) triple_set_add" where 
    "tsbm_add v w v' l \<equiv>  
     case m1.lookup v l of 
        None \<Rightarrow> (m1.update v (m2.sng w (s3.sng v')) l) |
        Some m2 \<Rightarrow> (case m2.lookup w m2 of
          None \<Rightarrow>    m1.update v (m2.update w (s3.sng v')    m2) l |
          Some s3 \<Rightarrow> m1.update v (m2.update w (s3.ins v' s3) m2) l)"

  lemma tsbm_add_correct:
    "triple_set_add tsbm_\<alpha> tsbm_invar tsbm_add"
  proof
    fix l v w v'
    assume invar: "tsbm_invar l"

    from invar
    show "tsbm_invar (tsbm_add v w v' l)"
      unfolding tsbm_invar_alt_def tsbm_add_def
      by (simp add: m1.correct m2.correct s3.correct 
               split: option.split if_split)

    from invar 
    show "tsbm_\<alpha> (tsbm_add v w v' l) = insert (v, w, v') (tsbm_\<alpha> l)"
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def tsbm_add_def
      by (simp add: m1.correct m2.correct s3.correct set_eq_iff
               split: option.split if_split)
  qed

  definition tsbm_memb :: "('a,'b,'c,'m1) triple_set_memb" where 
    "tsbm_memb t a b c \<equiv>  
     case m1.lookup a t of 
        None \<Rightarrow> False |
        Some m2 \<Rightarrow> (case m2.lookup b m2 of
          None \<Rightarrow>    False |
          Some s3 \<Rightarrow> s3.memb c s3)"

  lemma tsbm_memb_correct:
    "triple_set_memb tsbm_\<alpha> tsbm_invar tsbm_memb"
  proof
    fix t a b c
    assume invar: "tsbm_invar t"
    thus "tsbm_memb t a b c = ((a, b, c) \<in> tsbm_\<alpha> t)"
      unfolding tsbm_memb_def tsbm_\<alpha>_def
      by (simp split: option.split add: s3.correct tsbm_invar_alt_def m1.correct m2.correct)
  qed

  definition tsbm_add_Cs :: "('a,'b,'s3,'m1) triple_set_add_Cs" where 
    "tsbm_add_Cs a b cs l \<equiv>  
     case m1.lookup a l of 
        None \<Rightarrow> (m1.update a (m2.sng b cs) l) |
        Some m2 \<Rightarrow> (case m2.lookup b m2 of
          None \<Rightarrow>    m1.update a (m2.update b cs m2) l |
          Some s3 \<Rightarrow> m1.update a (m2.update b (s3.union s3 cs) m2) l)"

  lemma tsbm_add_Cs_correct:
    "triple_set_add_Cs s3.\<alpha> s3.invar tsbm_\<alpha> tsbm_invar tsbm_add_Cs"
  proof
    fix cs t a b
    assume invar_t: "tsbm_invar t"
    assume invar_cs: "s3.invar cs"

    from invar_t invar_cs
    show "tsbm_invar (tsbm_add_Cs a b cs t)"
      unfolding tsbm_invar_alt_def2 tsbm_add_Cs_def
      by (simp add: m1.correct m2.correct s3.correct split: option.split if_split)

    from invar_t invar_cs 
    show "tsbm_\<alpha> (tsbm_add_Cs a b cs t) = {(a, b, c) |c. c \<in> s3.\<alpha> cs} \<union> (tsbm_\<alpha> t)"
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def tsbm_add_Cs_def
      by (auto simp add: m1.correct m2.correct s3.correct set_eq_iff 
               split: option.split if_split)
  qed


  definition tsbm_set_Cs :: "('a,'b,'s3,'m1) triple_set_add_Cs" where 
    "tsbm_set_Cs a b cs l \<equiv>  
     case m1.lookup a l of 
        None \<Rightarrow> (m1.update a (m2.sng b cs) l) |
        Some m2 \<Rightarrow> m1.update a (m2.update b cs m2) l"

  lemma tsbm_set_Cs_correct:
    "triple_set_set_Cs s3.\<alpha> s3.invar tsbm_\<alpha> tsbm_invar tsbm_set_Cs"
  proof
    fix cs t a b
    assume invar_t: "tsbm_invar t"
    assume invar_cs: "s3.invar cs"
    assume dj: "\<And>c. (a, b, c) \<notin> tsbm_\<alpha> t"

    from invar_t invar_cs
    show "tsbm_invar (tsbm_set_Cs a b cs t)"
      unfolding tsbm_invar_alt_def2 tsbm_set_Cs_def
      by (simp add: m1.correct m2.correct s3.correct split: option.split if_split)

    from invar_t invar_cs dj
    show "tsbm_\<alpha> (tsbm_set_Cs a b cs t) = {(a, b, c) |c. c \<in> s3.\<alpha> cs} \<union> (tsbm_\<alpha> t)"
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def tsbm_set_Cs_def
      by (auto simp add: m1.correct m2.correct s3.correct set_eq_iff 
               split: option.split if_split)
  qed

  definition tsbm_add_Cl :: "('a,'b,'c,'m1) triple_set_add_Cl" where 
    "tsbm_add_Cl a b cs l \<equiv>  
     case m1.lookup a l of 
        None \<Rightarrow> (m1.update a (m2.sng b (s3.from_list cs)) l) |
        Some m2 \<Rightarrow> (case m2.lookup b m2 of
          None \<Rightarrow>    m1.update a (m2.update b (s3.from_list cs) m2) l |
          Some s3 \<Rightarrow> m1.update a (m2.update b (foldl (\<lambda>s3 v'. s3.ins v' s3) s3 cs) m2) l)"

  lemma tsbm_add_Cl_correct:
    "triple_set_add_Cl tsbm_\<alpha> tsbm_invar tsbm_add_Cl"
  proof
    fix l v w vs
    assume invar: "tsbm_invar l"
    define inner_add where "inner_add \<equiv> \<lambda>s3. foldl (\<lambda>s3 v'. s3.ins v' s3) s3 vs" 
    have inner_add_fold : "\<And>s3. foldl (\<lambda>s3 v'. s3.ins v' s3) s3 vs = inner_add s3"
      unfolding inner_add_def by simp

    have inner_add_thm: "\<And>s3. s3.invar s3 \<Longrightarrow> 
      s3.invar (inner_add s3) \<and> s3.\<alpha> (inner_add s3) = s3.\<alpha> s3 \<union> set vs"
      unfolding inner_add_def
      apply (induct vs)
      apply (simp_all add: s3.correct)
    done

    from invar
    show "tsbm_invar (tsbm_add_Cl v w vs l)"
      unfolding tsbm_invar_alt_def2 tsbm_add_Cl_def
      by (simp add: m1.correct m2.correct s3.correct inner_add_fold inner_add_thm
               split: option.split if_split)

    from invar 
    show "tsbm_\<alpha> (tsbm_add_Cl v w vs l) = {(v, w, v') |v'. v' \<in> set vs} \<union> (tsbm_\<alpha> l)"
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def tsbm_add_Cl_def
      by (auto simp add: m1.correct m2.correct s3.correct set_eq_iff inner_add_fold inner_add_thm
               split: option.split if_split)
  qed


  definition tsbm_add_Al :: "('a,'b,'c,'m1) triple_set_add_Al" where 
    "tsbm_add_Al as b c t \<equiv> foldl (\<lambda>t a. tsbm_add a b c t) t as"

  lemma tsbm_add_Al_correct:
    "triple_set_add_Al tsbm_\<alpha> tsbm_invar tsbm_add_Al"
  proof 
    fix t as b c 
    assume invar_t: "tsbm_invar t"

    hence "tsbm_invar (tsbm_add_Al as b c t) \<and>
           tsbm_\<alpha> (tsbm_add_Al as b c t) = {(a, b, c) |a. a \<in> set as} \<union> tsbm_\<alpha> t"
    proof (induct as arbitrary: t)
      case Nil thus ?case unfolding tsbm_add_Al_def by simp
    next
      case (Cons a as)
      note ind_hyp = Cons(1)
      note invar_t = Cons(2)

      from triple_set_add.triple_set_add_correct[OF tsbm_add_correct,
         OF invar_t, of a b c]
         ind_hyp [of "tsbm_add a b c t"]
      show ?case unfolding tsbm_add_Al_def by auto
    qed

    thus "tsbm_invar (tsbm_add_Al as b c t)"
         "tsbm_\<alpha> (tsbm_add_Al as b c t) = {(a, b, c) |a. a \<in> set as} \<union> tsbm_\<alpha> t"
      by simp_all
  qed

  definition tsbm_add_Bl :: "('a,'b,'c,'m1) triple_set_add_Bl" where 
    "tsbm_add_Bl a bs c t \<equiv> foldl (\<lambda>t b. tsbm_add a b c t) t bs"

  lemma tsbm_add_Bl_correct:
    "triple_set_add_Bl tsbm_\<alpha> tsbm_invar tsbm_add_Bl"
  proof 
    fix t a bs c 
    assume invar_t: "tsbm_invar t"

    hence "tsbm_invar (tsbm_add_Bl a bs c t) \<and>
           tsbm_\<alpha> (tsbm_add_Bl a bs c t) = {(a, b, c) |b. b \<in> set bs} \<union> tsbm_\<alpha> t"
    proof (induct bs arbitrary: t)
      case Nil thus ?case unfolding tsbm_add_Bl_def by simp
    next
      case (Cons b bs)
      note ind_hyp = Cons(1)
      note invar_t = Cons(2)

      from triple_set_add.triple_set_add_correct[OF tsbm_add_correct,
         OF invar_t, of a b c]
         ind_hyp [of "tsbm_add a b c t"]
      show ?case unfolding tsbm_add_Bl_def by auto
    qed

    thus "tsbm_invar (tsbm_add_Bl a bs c t)"
         "tsbm_\<alpha> (tsbm_add_Bl a bs c t) = {(a, b, c) |b. b \<in> set bs} \<union> tsbm_\<alpha> t"
      by simp_all
  qed

  definition tsbm_delete :: "('a,'b,'c,'m1) triple_set_delete" where 
    "tsbm_delete a b c m1 \<equiv>  
     case m1.lookup a m1 of 
        None \<Rightarrow> m1 |
        Some m2 \<Rightarrow> (case m2.lookup b m2 of
          None \<Rightarrow>    m1 |
          Some s3 \<Rightarrow> m1.update a (m2.update b (s3.delete c s3) m2) m1)"

  lemma tsbm_delete_correct:
    "triple_set_delete tsbm_\<alpha> tsbm_invar tsbm_delete"
  proof
    fix l v w v'
    assume invar: "tsbm_invar l"

    from invar
    show "tsbm_invar (tsbm_delete v w v' l)"
      unfolding tsbm_invar_alt_def tsbm_delete_def
      by (simp add: m1.correct m2.correct s3.correct 
               split: option.split if_split)

    from invar 
    show "tsbm_\<alpha> (tsbm_delete v w v' l) = (tsbm_\<alpha> l) - {(v, w, v')}"
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def tsbm_delete_def
      by (simp add: m1.correct m2.correct s3.correct set_eq_iff
               split: option.split if_split) auto
  qed

  definition tsbm_filter_it where
    "tsbm_filter_it it1 it2 it3 P_a P_b P_c P m1 =
        set_iterator_filter (\<lambda>vev'. P_c (snd (snd vev')) \<and> P vev')
        (map_iterator_product 
           (map_iterator_key_filter P_a (it1 m1)) 
           (\<lambda>m2. map_iterator_product 
               (map_iterator_key_filter P_b (it2 m2)) it3))"

  lemma tsbm_filter_it_alt_def[code] :
     "tsbm_filter_it = (\<lambda>it1 it2 it3 P_a P_b P_c P m1 c f.
        it1 m1 c
         (\<lambda>(a, m2) \<sigma>. if P_a a
                then it2 m2 c
                      (\<lambda>(b, s3) \<sigma>. if P_b b
                              then it3 s3 c (\<lambda>c \<sigma>. if P_c c \<and> P (a, b, c) then 
                                f (a, b, c) \<sigma> else \<sigma>) \<sigma> else \<sigma>)
                      \<sigma>
                else \<sigma>))"
     unfolding tsbm_filter_it_def[abs_def] set_iterator_filter_alt_def
               map_iterator_product_alt_def map_iterator_key_filter_alt_def
               fst_conv snd_conv split_def
     by simp 

  lemma tsbm_filter_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    assumes it3_OK: "set_iteratei s3.\<alpha> s3.invar it3"
    shows "triple_set_filter_it tsbm_\<alpha> tsbm_invar (tsbm_filter_it it1 it2 it3)"
  unfolding triple_set_filter_it_def 
  proof (intro allI impI)
    fix t and P_a :: "'a \<Rightarrow> bool" and P_b :: "'b \<Rightarrow> bool" and P_c :: "'c \<Rightarrow> bool" and 
        P :: "('a \<times> 'b \<times> 'c) \<Rightarrow> bool"
    assume invar_t: "tsbm_invar t"
    from invar_t have invar_m1: "m1.invar t"
      unfolding tsbm_invar_def by simp

    let ?it2'' = "\<lambda>m2. map_iterator_product 
      (map_iterator_key_filter P_b (it2 m2)) it3"
    let ?S_2'' = "\<lambda>m2. {(e, v'). \<exists>s3. m2.\<alpha> m2 e = Some s3 \<and> P_b e \<and> v' \<in> s3.\<alpha> s3}"

    { fix a m2
      assume t_a_eq:"(m1.\<alpha> t |` {a. P_a a}) a = Some m2"

      from invar_t t_a_eq have invar_m2: "m2.invar m2"
        unfolding tsbm_invar_alt_def 
        by (auto simp add: m1.correct restrict_map_eq)

      { fix b s3
        assume m2_b_eq: "(m2.\<alpha> m2 |` {e. P_b b}) b = Some s3"
        from invar_t t_a_eq invar_m2 m2_b_eq have invar_s3: "s3.invar s3"
          unfolding tsbm_invar_alt_def restrict_map_def
          by (simp add: m1.correct m2.correct split: if_splits)

        note it3_OK' = set_iteratei.iteratei_rule [OF it3_OK, OF invar_s3]
      } note it3_OK'' = this

      note it2_OK' = map_iteratei.iteratei_rule [OF it2_OK, OF invar_m2]
      note it2_OK'' = map_iterator_key_filter_correct [OF it2_OK', of P_b]

      from map_iterator_product_correct [OF it2_OK'', of it3 s3.\<alpha>] it3_OK''
      have "set_iterator (?it2'' m2) (?S_2'' m2)" 
        by (simp add: restrict_map_eq)
           (metis (no_types) UNIV_I)
    } note it2_OK'' = this

    have aux: "{(k, e). \<exists>v. m1.\<alpha> t k = Some v \<and> (case e of (k, e) \<Rightarrow>
              \<exists>va. m2.\<alpha> v k = Some va \<and> e \<in> s3.\<alpha> va)} = tsbm_\<alpha> t"
      unfolding tsbm_\<alpha>_def by auto

    note it1_OK' = map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1]
    note it1_OK'' = map_iterator_key_filter_correct [OF it1_OK', of P_a]

    let ?it1'' = "map_iterator_product 
      (map_iterator_key_filter P_a (it1 t)) ?it2''"
    let ?S_1'' = "{(k, e). \<exists>v. m1.\<alpha> t k = Some v \<and> P_a k \<and>
           (case e of (e, v') \<Rightarrow> \<exists>s3. m2.\<alpha> v e = Some s3 \<and> P_b e \<and> v' \<in> s3.\<alpha> s3)}"

    have S_1''_eq: "?S_1'' = {(v, e, v'). (v, e, v') \<in> tsbm_\<alpha> t \<and> P_a v \<and> P_b e}"
      unfolding tsbm_\<alpha>_def by auto

   from map_iterator_product_correct [OF it1_OK'', of ?it2'' ?S_2''] it2_OK''
    have it1_OK'': "set_iterator ?it1'' 
       {(v, e, v'). (v, e, v') \<in> tsbm_\<alpha> t \<and> P_a v \<and> P_b e}"
      by (simp add: restrict_map_eq S_1''_eq)

    from set_iterator_filter_correct [OF it1_OK'', of "(\<lambda>vev'. P_c (snd (snd vev')) \<and> P vev')"]
    show "set_iterator (tsbm_filter_it it1 it2 it3 P_a P_b P_c P t)
           {(v1, e, v2). (v1, e, v2) \<in> tsbm_\<alpha> t \<and> P_a v1 \<and> P_b e \<and> P_c v2 \<and> P (v1, e, v2)}"
      unfolding tsbm_filter_it_def[symmetric] 
      apply simp
      apply (rule subst [where P = "set_iterator (tsbm_filter_it it1 it2 it3 P_a P_b P_c P t)"])
      apply auto
    done
  qed

  definition tsbm_it where
    "tsbm_it it1 it2 it3 = tsbm_filter_it it1 it2 it3 (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True)"

  lemma tsbm_it_alt_def [code] :
    "tsbm_it it1 it2 it3 = (\<lambda>m1 c f.
        it1 m1 c (\<lambda>(a, m2). it2 m2 c (\<lambda>(b, s3). it3 s3 c (\<lambda>c. f (a, b, c)))))"
    unfolding tsbm_it_def tsbm_filter_it_alt_def by simp

  lemma tsbm_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    assumes it3_OK: "set_iteratei s3.\<alpha> s3.invar it3"
    shows "triple_set_iterator tsbm_\<alpha> tsbm_invar (tsbm_it it1 it2 it3)"  
  unfolding triple_set_iterator_def tsbm_it_def
    apply (intro allI impI)
    apply (insert triple_set_filter_it.triple_set_filter_it_correct [OF
     tsbm_filter_it_correct[OF it1_OK it2_OK it3_OK], of _ "\<lambda>_. True" "\<lambda>_. True" "\<lambda>_. True" "\<lambda>_. True"])
    apply simp
  done

  definition tsbm_A_it where
   "tsbm_A_it it1 (t::'m1) (b::'b) (c::'c) =
    map_iterator_dom_filter (\<lambda>am2. 
      case m2.lookup b (snd am2) of
         None \<Rightarrow> False
       | Some s3 \<Rightarrow> s3.memb c s3) (it1 t)"

  lemma tsbm_A_it_alt_def[code] :
    "tsbm_A_it = (\<lambda>it1 t b c c' f.
        it1 t c'
         (\<lambda>(a,m2) \<sigma>. if case_option False (set_op_memb s3_ops c)
                     (map_op_lookup m2_ops b m2)
                 then f a \<sigma> else \<sigma>))"
    unfolding tsbm_A_it_def[abs_def] map_iterator_dom_filter_alt_def 
              curry_def split_def
              fst_conv snd_conv by simp

  lemma tsbm_A_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    shows "triple_set_A_it tsbm_\<alpha> tsbm_invar (tsbm_A_it it1)"
  unfolding triple_set_A_it_def
  proof (intro allI impI)
    fix t b c
    assume invar_t: "tsbm_invar t"
    from invar_t have invar_m1: "m1.invar t"
      unfolding tsbm_invar_def by simp

    from map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1] have
      step1: "map_iterator (it1 t) (map_op_\<alpha> m1_ops t)" .
    
    from map_iterator_dom_filter_correct [OF step1, 
      of "\<lambda>am2. case m2.lookup b (snd am2) of None \<Rightarrow> False | Some s3 \<Rightarrow> s3.memb c s3"]
    have step2: "set_iterator (tsbm_A_it it1 t b c)
          {k. \<exists>v. m1.\<alpha> t k = Some v \<and>
             (case m2.lookup b v of None \<Rightarrow> False
              | Some s3 \<Rightarrow> s3.memb c s3)}"
      by (simp add: tsbm_A_it_def[symmetric])
     
   from invar_t
   have step3: "{k. \<exists>v. m1.\<alpha> t k = Some v \<and> (case m2.lookup b v of None \<Rightarrow> False
                                  | Some s3 \<Rightarrow> s3.memb c s3)} = 
                {a . (a, b, c) \<in> tsbm_\<alpha> t}"
     unfolding tsbm_\<alpha>_def tsbm_invar_alt_def
     by (auto simp add: map_to_set_def m1.correct m2.correct s3.correct split: option.splits)
        (metis m2.lookup_correct map_upd_eqD1 s3.memb_correct)

   from step2 step3
   show "set_iterator (tsbm_A_it it1 t b c) {a . (a, b, c) \<in> tsbm_\<alpha> t}" 
     unfolding tsbm_A_it_def by simp
  qed

  definition tsbm_B_it where
   "tsbm_B_it it (t::'m1) (a::'a) (c::'c) =
     (case m1.lookup a t of
         None \<Rightarrow> set_iterator_emp
       | Some m2 \<Rightarrow>
           (map_iterator_dom_filter (\<lambda>bs3. s3.memb c (snd bs3)) (it m2)))"
          
  lemma tsbm_B_it_alt_def[code] :
    "tsbm_B_it = (\<lambda>it t a c.
        case map_op_lookup m1_ops a t of None \<Rightarrow> (\<lambda>c f \<sigma>0. \<sigma>0)
        | Some m2 \<Rightarrow> \<lambda>ca f. it m2 ca (\<lambda>(x, y) \<sigma>. if set_op_memb s3_ops c y then f x \<sigma> else \<sigma>))"
    unfolding tsbm_B_it_def[abs_def] map_iterator_dom_filter_alt_def 
              curry_def split_def
              fst_conv snd_conv set_iterator_emp_def[abs_def] by simp

  lemma tsbm_B_it_correct :
    assumes it_OK: "map_iteratei m2.\<alpha> m2.invar it"
    shows "triple_set_B_it tsbm_\<alpha> tsbm_invar (tsbm_B_it it)"
  unfolding triple_set_B_it_def
  proof (intro allI impI)
    fix t a c
    assume invar_t: "tsbm_invar t"
    from invar_t have invar_m1: "m1.invar t"
      unfolding tsbm_invar_def by simp

    show "set_iterator (tsbm_B_it it t a c)
             {b . (a, b, c) \<in> tsbm_\<alpha> t}"
    proof (cases "m1.lookup a t")
      case None note m1_a_eq = this
      with invar_m1 have "{b . (a, b, c) \<in> tsbm_\<alpha> t} = {}"
        unfolding tsbm_\<alpha>_def
         by (simp add: m1.correct)         
      thus ?thesis
        unfolding tsbm_B_it_def
        by (simp add: m1_a_eq set_iterator_emp_correct)
    next
      case (Some m2) note m1_a_eq = this
      with invar_t have invar_m2: "m2.invar m2"  and 
                        invar_s3: "\<And>w s3. m2.\<alpha> m2 w = Some s3 \<Longrightarrow> s3.invar s3"
        unfolding tsbm_invar_alt_def 
        by (simp_all add: m1.correct)

      from invar_s3 have c_in_simp:
        "\<And>k s3. m2.\<alpha> m2 k = Some s3 \<and> s3.memb c s3 \<longleftrightarrow>
                m2.\<alpha> m2 k = Some s3 \<and> c \<in> s3.\<alpha> s3" 
        by (auto simp add: s3.correct)

      from map_iteratei.iteratei_rule[OF it_OK, OF invar_m2]
      have it_m2: "map_iterator (it m2) (m2.\<alpha> m2)" .

      from map_iterator_dom_filter_correct [OF it_m2, of "(\<lambda>bs3. s3.memb c (snd bs3))"]
           m1_a_eq invar_m1 
      show ?thesis
        by (simp add: tsbm_B_it_def tsbm_\<alpha>_def m1.correct c_in_simp)
    qed
  qed

  definition tsbm_C_it where
    "tsbm_C_it it m1 a b =
     (case m1.lookup a m1 of
         None \<Rightarrow> set_iterator_emp
       | Some m2 \<Rightarrow>
           (case m2.lookup b m2 of
               None \<Rightarrow> set_iterator_emp
             | Some s3 \<Rightarrow> it s3))"

  lemmas tsbm_C_it_alt_def[code] =   
    tsbm_C_it_def[abs_def, unfolded set_iterator_emp_def[abs_def]]

  lemma tsbm_C_it_correct :
    assumes it_OK: "set_iteratei s3.\<alpha> s3.invar it"
    shows "triple_set_C_it tsbm_\<alpha> tsbm_invar (tsbm_C_it it)"
  unfolding triple_set_C_it_def
  proof (intro allI impI)
    fix t a b
    assume invar_t: "tsbm_invar t"
    from invar_t have invar_m1: "m1.invar t"
      unfolding tsbm_invar_def by simp

    show "set_iterator (tsbm_C_it it t a b)
             {c . (a, b, c) \<in> tsbm_\<alpha> t}"
    proof (cases "m1.lookup a t")
      case None note m1_v_eq = this
      with invar_m1 have "{c . (a, b, c) \<in> tsbm_\<alpha> t} = {}"
        unfolding tsbm_\<alpha>_def
         by (simp add: m1.correct)         
      thus ?thesis
        unfolding tsbm_C_it_def
        by (simp add: m1_v_eq set_iterator_emp_correct)
    next
      case (Some m2) note m1_a_eq = this
      with invar_t have invar_m2: "m2.invar m2" 
        unfolding tsbm_invar_alt_def 
        by (simp add: m1.correct)

      show ?thesis
      proof (cases "m2.lookup b m2")
        case None note m2_b_eq = this
        with invar_m1 invar_m2 m1_a_eq have "{c . (a, b, c) \<in> tsbm_\<alpha> t} = {}"
          unfolding tsbm_\<alpha>_def
           by (simp add: m1.correct m2.correct)         
        thus ?thesis
          unfolding tsbm_C_it_def
          by (simp add: m1_a_eq m2_b_eq set_iterator_emp_correct)
      next
        case (Some s3) note m2_b_eq = this

        with invar_t invar_m2 m1_a_eq have invar_s3: "s3.invar s3" 
          unfolding tsbm_invar_alt_def 
          by (simp add: m1.correct m2.correct)

        from set_iteratei.iteratei_rule[OF it_OK, OF invar_s3]
        have it_s3: "set_iterator (it s3) (s3.\<alpha> s3)" by simp

        have succ_eq: "{c . (a, b, c) \<in> tsbm_\<alpha> t} = s3.\<alpha> s3"
          using m1_a_eq m2_b_eq invar_m1 invar_m2
          unfolding tsbm_\<alpha>_def by (simp add: m1.correct m2.correct)

        show ?thesis
          using succ_eq it_s3
          unfolding tsbm_C_it_def
          by (simp add: m1_a_eq m2_b_eq)
      qed
    qed
  qed

  definition tsbm_BC_it where
    "tsbm_BC_it it2 it3 m1 a =
     (case m1.lookup a m1 of
         None \<Rightarrow> set_iterator_emp
       | Some m2 \<Rightarrow>
           map_iterator_product (it2 m2) it3)"

  lemma tsbm_BC_it_alt_def[code] :
    "tsbm_BC_it = (\<lambda>it2 it3 m1 a. 
      (case m1.lookup a m1 of
          None \<Rightarrow> \<lambda>c f \<sigma>0. \<sigma>0
        | Some m2 \<Rightarrow> \<lambda>c f. it2 m2 c (\<lambda>(b, s3). it3 s3 c (\<lambda>c'. f (b, c')))))"
    unfolding tsbm_BC_it_def[abs_def] map_iterator_product_alt_def split_def
              curry_def set_iterator_emp_def[abs_def] fst_conv snd_conv
    by simp

  lemma tsbm_BC_it_correct :
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    assumes it3_OK: "set_iteratei s3.\<alpha> s3.invar it3"
    shows "triple_set_BC_it tsbm_\<alpha> tsbm_invar (tsbm_BC_it it2 it3)"
  unfolding triple_set_BC_it_def
  proof (intro allI impI)
    fix t a
    assume invar_t: "tsbm_invar t"
    from invar_t have invar_m1: "m1.invar t"
      unfolding tsbm_invar_def by simp

    show "set_iterator (tsbm_BC_it it2 it3 t a) 
             {(b, c) . (a, b, c) \<in> tsbm_\<alpha> t}"
    proof (cases "m1.lookup a t")
      case None note m1_a_eq = this
      with invar_m1 have "{(b, c) . (a, b, c) \<in> tsbm_\<alpha> t} = {}"
        unfolding tsbm_\<alpha>_def
         by (simp add: m1.correct)         
      thus ?thesis
        unfolding tsbm_BC_it_def
        by (simp add: m1_a_eq set_iterator_emp_correct)
    next
      case (Some m2) note m1_a_eq = this
      with invar_t have invar_m2: "m2.invar m2" 
        unfolding tsbm_invar_alt_def 
        by (simp add: m1.correct)

      from map_iteratei.iteratei_rule[OF it2_OK, OF invar_m2] 
      have it2_OK': "map_iterator (it2 m2) (m2.\<alpha> m2)" .

      have it3_OK': "\<And>k s3. m2.\<alpha> m2 k = Some s3 \<Longrightarrow> 
           set_iterator (it3 s3) (s3.\<alpha> s3)"
      proof -
        fix k s3
        assume m2_k_eq: "m2.\<alpha> m2 k = Some s3"

        from invar_t invar_m1 invar_m2 m1_a_eq m2_k_eq 
        have invar_s3: "s3.invar s3"
          unfolding tsbm_invar_alt_def
          by (simp add: m1.correct m2.correct)

        with set_iteratei.iteratei_rule[OF it3_OK]
        show "set_iterator (it3 s3) (s3.\<alpha> s3)"
          by simp
      qed

      from map_iterator_product_correct [OF it2_OK', 
         of it3 "s3.\<alpha>"] it3_OK' m1_a_eq invar_m1
      show ?thesis
         by (simp add: tsbm_BC_it_def tsbm_\<alpha>_def m1.correct)
    qed
  qed

  definition tsbm_AB_it where
    "tsbm_AB_it it1 it2 m1 c =
        map_iterator_product (it1 m1) 
           (\<lambda>m2. map_iterator_dom_filter (s3.memb c \<circ> snd)
              (it2 m2))"

  lemma tsbm_AB_it_alt_def[code] :
     "tsbm_AB_it = (\<lambda>it1 it2 m1 c ca f.
        it1 m1 ca
         (\<lambda>(a, m2). it2 m2 ca
               (\<lambda>(b, s3) \<sigma>. if set_op_memb s3_ops c s3 then f (a, b) \<sigma>
                       else \<sigma>)))"
     unfolding tsbm_AB_it_def[abs_def] map_iterator_product_alt_def  
               curry_def map_iterator_dom_filter_alt_def o_def
               split_def fst_conv snd_conv by simp

  lemma tsbm_AB_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it2_OK: "map_iteratei m2.\<alpha> m2.invar it2"
    shows "triple_set_AB_it tsbm_\<alpha> tsbm_invar (tsbm_AB_it it1 it2)"
  unfolding triple_set_AB_it_def
  proof (intro allI impI)
    fix l v'
    assume invar_l: "tsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding tsbm_invar_def by simp

    let ?it_b = "\<lambda>m2. map_iterator_dom_filter (s3.memb v' \<circ> snd) (it2 m2)"
    let ?S_b = "\<lambda>m2. {e . \<exists>s3. m2.\<alpha> m2 e = Some s3 \<and> s3.memb v' s3}"

    { fix v m2
      assume l_v_eq: "m1.\<alpha> l v = Some m2"

      from invar_l l_v_eq have invar_m2: "m2.invar m2"
        unfolding tsbm_invar_alt_def 
        by (simp add: m1.correct)

      note it2_OK' = map_iteratei.iteratei_rule [OF it2_OK, OF invar_m2]
      from map_iterator_dom_filter_correct [OF it2_OK', of "s3.memb v' \<circ> snd"]
      have "set_iterator (?it_b m2) (?S_b m2)" 
        by simp
    } note it_b_aux = this

    from invar_l
    have S_b_aux: "{(k, e). \<exists>v. m1.\<alpha> l k = Some v \<and> e \<in> ?S_b v} = 
                   {(v, e) |v e. (v, e, v') \<in> tsbm_\<alpha> l}" 
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def
      by (auto simp add: m1.correct m2.correct s3.correct)

    note it1_OK' = map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1]
    from map_iterator_product_correct [OF it1_OK', of ?it_b ?S_b] S_b_aux it_b_aux
    show "set_iterator (tsbm_AB_it it1 it2 l v')
             {(v, e) . (v, e, v') \<in> tsbm_\<alpha> l} "
      by (simp add: tsbm_AB_it_def[symmetric])
  qed


  definition tsbm_AC_it where
    "tsbm_AC_it it1 it3 m1 b =
        map_iterator_product (it1 m1) 
           (\<lambda>m2. case m2.lookup b m2 of None \<Rightarrow> set_iterator_emp
                 | Some s3 \<Rightarrow> it3 s3)"

  lemma tsbm_AC_it_alt_def[code] :
     "tsbm_AC_it = (\<lambda>it1 it3 m1 b c f.
        it1 m1 c
         (\<lambda>(a, m2). case_option (\<lambda>c f \<sigma>0. \<sigma>0) it3 (map_op_lookup m2_ops b m2) c
               (\<lambda>b. f (a, b))))"
     unfolding tsbm_AC_it_def[abs_def] map_iterator_product_alt_def 
               curry_def map_iterator_dom_filter_alt_def set_iterator_emp_def[abs_def]
               fst_conv snd_conv split_def by simp

  lemma tsbm_AC_it_correct :
    assumes it1_OK: "map_iteratei m1.\<alpha> m1.invar it1"
    assumes it3_OK: "set_iteratei s3.\<alpha> s3.invar it3"
    shows "triple_set_AC_it tsbm_\<alpha> tsbm_invar (tsbm_AC_it it1 it3)"
  unfolding triple_set_AC_it_def
  proof (intro allI impI)
    fix l b
    assume invar_l: "tsbm_invar l"
    from invar_l have invar_m1: "m1.invar l"
      unfolding tsbm_invar_def by simp

    let ?it_c = " (\<lambda>m2. case m2.lookup b m2 of None \<Rightarrow> set_iterator_emp
                 | Some s3 \<Rightarrow> it3 s3)"
    let ?S_c = "\<lambda>m2. {c . \<exists>s3. m2.\<alpha> m2 b = Some s3 \<and> s3.memb c s3}"

    have it_c_aux: "\<And>a m2. m1.\<alpha> l a = Some m2 \<Longrightarrow>
       set_iterator (?it_c m2) (?S_c m2)"
    proof -
      fix m2 a
      assume "m1.\<alpha> l a = Some m2"
      with invar_l have invar_m2: "m2.invar m2"  and 
                        invar_s3: "\<And>w s3. m2.\<alpha> m2 w = Some s3 \<Longrightarrow> s3.invar s3"
        unfolding tsbm_invar_alt_def 
        by (simp_all add: m1.correct)

      show "set_iterator (?it_c m2) (?S_c m2)"
      proof (cases "m2.lookup b m2")
        case None note m2_b_eq = this
        with invar_m2 show ?thesis by (simp add: m2.correct set_iterator_emp_correct)
      next
        case (Some s3) note m2_b_eq = this
        with invar_s3 invar_m2 have s3_invar': "s3.invar s3" by (simp add: m2.correct)

        from set_iteratei.iteratei_rule[OF it3_OK, OF s3_invar'] m2_b_eq s3_invar'
        show ?thesis by (simp add: invar_m2 m2.correct s3.correct)
      qed
    qed

    from invar_l
    have S_c_aux: "{(a, c). \<exists>m2. m1.\<alpha> l a = Some m2 \<and> c \<in> ?S_c m2} = 
                   {(a, c) . (a, b, c) \<in> tsbm_\<alpha> l}" 
      unfolding tsbm_invar_alt_def tsbm_\<alpha>_def
      by (auto simp add: m1.correct m2.correct s3.correct)

    note it1_OK' = map_iteratei.iteratei_rule [OF it1_OK, OF invar_m1]
    from map_iterator_product_correct [OF it1_OK', of ?it_c ?S_c] S_c_aux it_c_aux
    show "set_iterator (tsbm_AC_it it1 it3 l b)
             {(a, c) . (a, b, c) \<in> tsbm_\<alpha> l} "
      by (simp add: tsbm_AC_it_def[symmetric])
  qed

end

consts test :: bool

find_theorems "test"

end
