section "Interface for Labelled Transition Systems"
theory LTSSpec
imports 
  Main 
  "../LTS"
  "../../Collections/Refine_Dflt"
  "../..//Collections/ICF/CollectionsV1"
begin
  type_synonym ('V,'W,'L) lts_\<alpha> = "'L \<Rightarrow> ('V * 'W * 'V) set"
  locale lts =
    fixes \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes invar :: "'L \<Rightarrow> bool"

  locale finite_lts = lts +
    assumes finite[simp, intro!]: "invar l \<Longrightarrow> finite (\<alpha> l)"

  locale dlts = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    assumes dlts_det: "invar l \<Longrightarrow> LTS_is_deterministic (\<alpha> l)"

  type_synonym ('V,'W,'L) lts_succ = "'L \<Rightarrow> 'V \<Rightarrow>'W \<Rightarrow> 'V option"
  locale lts_succ = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes succ :: "('V,'W,'L)lts_succ"
    assumes lts_succ_correct:
      "invar l \<Longrightarrow> (succ l v w = None) \<Longrightarrow> \<forall>v'. (v, w, v') \<notin> (\<alpha> l)"
      "invar l \<Longrightarrow> (succ l v w = Some v') \<Longrightarrow> (v, w, v') \<in> (\<alpha> l)"
  begin
    lemma lts_succ_det_correct:
      "invar l \<Longrightarrow> LTS_is_deterministic (\<alpha> l) \<Longrightarrow>
          (succ l v w = Some v') \<longleftrightarrow> (v, w, v') \<in> (\<alpha> l)"
      "invar l \<Longrightarrow> LTS_is_deterministic (\<alpha> l) \<Longrightarrow>
          (succ l v w = None) \<longleftrightarrow> (\<forall>v'. (v, w, v') \<notin> (\<alpha> l))"
       using lts_succ_correct[of l v w]
       unfolding LTS_is_deterministic_def
    by (metis not_Some_eq)+
  end

  locale dlts_succ = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes succ :: "('V,'W,'L)lts_succ"
    assumes dlts_succ_correct:
      "invar l \<Longrightarrow> (succ l v w = Some v') \<longleftrightarrow> (v, w, v') \<in> (\<alpha> l)"

  lemma dlts_succ_sublocale: "dlts_succ \<alpha> invar succ \<Longrightarrow> lts_succ \<alpha> invar succ"
  unfolding lts_succ_def dlts_succ_def
  by auto (metis option.simps(2))

  lemma lts_succ_sublocale: "dlts \<alpha> invar \<Longrightarrow> lts_succ \<alpha> invar succ \<Longrightarrow> dlts_succ \<alpha> invar succ"
  proof -
    assume dlts_OK: "dlts \<alpha> invar"
    assume lts_succ: "lts_succ \<alpha> invar succ"

    show "dlts_succ \<alpha> invar succ"
    proof
      fix l v w v'
      assume invar_l: "invar l"
      from dlts.dlts_det [OF dlts_OK, OF invar_l] 
      have det_l: "LTS_is_deterministic (\<alpha> l)" .

      from lts_succ.lts_succ_det_correct[OF lts_succ, OF invar_l det_l]
      show "(succ l v w = Some v') = ((v, w, v') \<in> \<alpha> l)" by simp
    qed
  qed

  type_synonym ('V,'W,'L) lts_memb = "'L \<Rightarrow> 'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> bool"
  locale lts_memb = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes memb :: "('V,'W,'L) lts_memb"
    assumes lts_memb_correct:
      "invar l \<Longrightarrow> (memb l v w v') \<longleftrightarrow> (v, w, v') \<in> (\<alpha> l)"

  locale lts_copy = lts \<alpha>1 invar1 + lts \<alpha>2 invar2
  for \<alpha>1 :: "'L1 \<Rightarrow> ('A * 'B * 'A) set" and invar1
  and \<alpha>2 :: "'L2 \<Rightarrow> ('A * 'B * 'A) set" and invar2
  +
  fixes copy :: "'L1 \<Rightarrow> 'L2"
  assumes copy_correct: 
    "invar1 t1 \<Longrightarrow> \<alpha>2 (copy t1) = \<alpha>1 t1"
    "invar1 t1 \<Longrightarrow> invar2 (copy t1)"

  type_synonym ('V,'W,'L) lts_empty  = "unit \<Rightarrow> 'L"
  locale lts_empty = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes empty :: "unit \<Rightarrow> 'L"
    assumes lts_empty_correct:
      "\<alpha> (empty ()) = {}"
      "invar (empty ())"

  type_synonym ('V,'W,'L) lts_add = "'V \<Rightarrow>'W \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
  locale lts_add = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes add :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes lts_add_correct:
      "invar l \<Longrightarrow> invar (add v e v' l)"
      "invar l \<Longrightarrow> \<alpha> (add v e v' l) = insert (v, e, v') (\<alpha> l)"

  locale dlts_add = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes add :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes dlts_add_correct:
      "invar l \<Longrightarrow> \<lbrakk>\<And>v''. v'' \<noteq> v' \<Longrightarrow> (v, e, v'') \<notin> \<alpha> l\<rbrakk> \<Longrightarrow> invar (add v e v' l)"
      "invar l \<Longrightarrow> \<lbrakk>\<And>v''. v'' \<noteq> v' \<Longrightarrow> (v, e, v'') \<notin> \<alpha> l\<rbrakk> \<Longrightarrow>
       \<alpha> (add v e v' l) = insert (v, e, v') (\<alpha> l)"

  definition lts_dlts_add where
    "lts_dlts_add \<alpha> invar add \<longleftrightarrow>
     lts_add \<alpha> invar (add False) \<and> dlts_add \<alpha> invar (add True)"

  lemma lts_add_sublocale: "lts_add \<alpha> invar add \<Longrightarrow> dlts_add \<alpha> invar add"
  unfolding lts_add_def dlts_add_def
  by simp

  type_synonym ('V,'W,'L) lts_add_succs = "'V \<Rightarrow>'W \<Rightarrow> 'V list \<Rightarrow> 'L \<Rightarrow> 'L"
  locale lts_add_succs = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes add_succs :: "'V \<Rightarrow> 'W \<Rightarrow> 'V list \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes lts_add_succs_correct:
      "invar l \<Longrightarrow> invar (add_succs v e vs l)"
      "invar l \<Longrightarrow> \<alpha> (add_succs v e vs l) = (\<alpha> l) \<union> {(v, e, v') | v'. v' \<in> set vs}"

  locale dlts_add_succs = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes add_succs :: "'V \<Rightarrow> 'W \<Rightarrow> 'V list \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes dlts_add_succs_correct:
      "invar l \<Longrightarrow> length vs < 2 \<Longrightarrow> \<lbrakk>\<And>v'. v' \<notin> set vs \<Longrightarrow> (v, e, v') \<notin> \<alpha> l\<rbrakk> \<Longrightarrow> invar (add_succs v e vs l)"
      "invar l \<Longrightarrow> length vs < 2 \<Longrightarrow> \<lbrakk>\<And>v'. v' \<notin> set vs \<Longrightarrow> (v, e, v') \<notin> \<alpha> l\<rbrakk> \<Longrightarrow>
       \<alpha> (add_succs v e vs l) = (\<alpha> l) \<union> {(v, e, v') | v'. v' \<in> set vs}"

  lemma lts_add_succs_sublocale: "lts_add_succs \<alpha> invar add_succs \<Longrightarrow> dlts_add_succs \<alpha> invar add_succs"
  unfolding lts_add_succs_def dlts_add_succs_def
  by simp

  type_synonym ('V, 'W, 'L1, 'L2, 'L3) lts_union = "'L1 \<Rightarrow> 'L2 \<Rightarrow> 'L3"

  locale lts_union = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 + lts \<alpha>3 invar3
    for \<alpha>1 :: "('V, 'W, 'L1) lts_\<alpha>" and invar1
    and \<alpha>2 :: "('V, 'W, 'L2) lts_\<alpha>" and invar2
    and \<alpha>3 :: "('V, 'W, 'L3) lts_\<alpha>" and invar3
    +
    fixes union :: "('V, 'W, 'L1, 'L2, 'L3) lts_union"
    assumes lts_union_correct:
      "invar1 l1 \<Longrightarrow> invar2 l2 \<Longrightarrow> invar3 (union l1 l2)"
      "invar1 l1 \<Longrightarrow> invar2 l2 \<Longrightarrow> \<alpha>3 (union l1 l2) = \<alpha>1 l1 \<union> \<alpha>2 l2"

  locale dlts_union = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 + lts \<alpha>3 invar3
    for \<alpha>1 :: "('V, 'W, 'L1) lts_\<alpha>" and invar1
    and \<alpha>2 :: "('V, 'W, 'L2) lts_\<alpha>" and invar2
    and \<alpha>3 :: "('V, 'W, 'L3) lts_\<alpha>" and invar3
    +
    fixes union :: "('V, 'W, 'L1, 'L2, 'L3) lts_union"
    assumes dlts_union_correct:
      "invar1 l1 \<Longrightarrow> invar2 l2 \<Longrightarrow> LTS_is_deterministic (\<alpha>1 l1) \<Longrightarrow>
        (\<And> p a q1 q2. (p, a, q1) \<in> \<alpha>1 l1 \<Longrightarrow> (p, a, q2) \<in> \<alpha>2 l2 \<Longrightarrow> q1 = q2) \<Longrightarrow>
        invar3 (union l1 l2)"
      "invar1 l1 \<Longrightarrow> invar2 l2 \<Longrightarrow> LTS_is_deterministic (\<alpha>1 l1) \<Longrightarrow>
        (\<And> p a q1 q2. (p, a, q1) \<in> \<alpha>1 l1 \<Longrightarrow> (p, a, q2) \<in> \<alpha>2 l2 \<Longrightarrow> q1 = q2) \<Longrightarrow>
        \<alpha>3 (union l1 l2) = \<alpha>1 l1 \<union> \<alpha>2 l2"

  lemma lts_union_sublocale:
    assumes "lts_union \<alpha> invar \<alpha> invar \<alpha> invar union'"
    shows "dlts_union \<alpha> invar \<alpha> invar \<alpha> invar union'"
    using assms
    unfolding lts_union_def dlts_union_def
    by simp

  locale lts_add_label_set = lts \<alpha> invar + set \<alpha>_s invar_s 
    for \<alpha> :: "('V,'W,'L) lts_\<alpha>" and invar
    and \<alpha>_s :: "'Wset \<Rightarrow> 'W set" and invar_s +
    fixes add_label_set :: "'V \<Rightarrow> 'Wset \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes lts_add_label_set_correct:
      "invar l \<Longrightarrow> invar_s es \<Longrightarrow> invar (add_label_set v es v' l)"
      "invar l \<Longrightarrow> invar_s es \<Longrightarrow>  \<alpha> (add_label_set v es v' l) = (\<alpha> l) \<union> {(v, e, v') | e. e \<in> \<alpha>_s es}"

  locale dlts_add_label_set = lts \<alpha> invar + set \<alpha>_s invar_s 
    for \<alpha> :: "('V,'W,'L) lts_\<alpha>" and invar
    and \<alpha>_s :: "'Wset \<Rightarrow> 'W set" and invar_s +
    fixes add_label_set :: "'V \<Rightarrow> 'Wset \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes dlts_add_label_set_correct:
      "invar l \<Longrightarrow> invar_s es \<Longrightarrow> \<lbrakk>\<And>e v''. e \<in> \<alpha>_s es \<Longrightarrow> v'' \<noteq> v' \<Longrightarrow> (v, e, v'') \<notin> \<alpha> l\<rbrakk> \<Longrightarrow> 
       invar (add_label_set v es v' l)"
      "invar l \<Longrightarrow> invar_s es \<Longrightarrow> \<lbrakk>\<And>e v''. e \<in> \<alpha>_s es \<Longrightarrow> v'' \<noteq> v' \<Longrightarrow> (v, e, v'') \<notin> \<alpha> l\<rbrakk> \<Longrightarrow> 
       \<alpha> (add_label_set v es v' l) = (\<alpha> l) \<union> {(v, e, v') | e. e \<in> \<alpha>_s es}"

  lemma lts_add_label_set_sublocale: "lts_add_label_set \<alpha> invar \<alpha>_s invar_s add_label_set \<Longrightarrow> 
      dlts_add_label_set \<alpha> invar \<alpha>_s invar_s add_label_set"
  unfolding lts_add_label_set_def dlts_add_label_set_def
  by simp

  type_synonym ('V,'W,'L) lts_delete = "'V \<Rightarrow>'W \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
  locale lts_delete = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes delete :: "'V \<Rightarrow> 'W \<Rightarrow> 'V \<Rightarrow> 'L \<Rightarrow> 'L"
    assumes lts_delete_correct:
      "invar l \<Longrightarrow> invar (delete v e v' l)"
      "invar l \<Longrightarrow> \<alpha> (delete v e v' l) = (\<alpha> l) - {(v, e, v')}"

  type_synonym ('V,'W,'\<sigma>,'L) lts_it = "'L \<Rightarrow> (('V\<times>'W\<times>'V),'\<sigma>) set_iterator"
  locale lts_iterator = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes it :: "('V,'W,'\<sigma>,'L) lts_it"
    assumes lts_it_correct:
      "invar l \<Longrightarrow> set_iterator (it l) (\<alpha> l)"

  type_synonym ('V,'W,'\<sigma>,'L) lts_filter_it = "('V \<Rightarrow> bool) \<Rightarrow> ('W \<Rightarrow> bool) \<Rightarrow> ('V \<Rightarrow> bool) \<Rightarrow>
        (('V \<times> 'W \<times> 'V) \<Rightarrow> bool) \<Rightarrow> 'L \<Rightarrow> (('V\<times>'W\<times>'V),'\<sigma>) set_iterator"
  locale lts_filter_it = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes filter_it :: "('V,'W,'\<sigma>,'L) lts_filter_it"
    assumes lts_filter_it_correct :
      "invar l \<Longrightarrow> set_iterator (filter_it P_v1 P_e P_v2 P l) 
         {(v1, e, v2) . (v1, e, v2) \<in> (\<alpha> l) \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

  type_synonym ('V,'W,'L) lts_filter = "('V \<Rightarrow> bool) \<Rightarrow> ('W \<Rightarrow> bool) \<Rightarrow> ('V \<Rightarrow> bool) \<Rightarrow>
        (('V \<times> 'W \<times> 'V) \<Rightarrow> bool) \<Rightarrow> 'L \<Rightarrow> 'L"
  locale lts_filter = lts  +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>" 
    fixes filter :: "('V,'W,'L) lts_filter"
    assumes lts_filter_correct :
      "invar l \<Longrightarrow> invar (filter P_v1 P_e P_v2 P l)"
      "invar l \<Longrightarrow> \<alpha>(filter P_v1 P_e P_v2 P l) =
             {(v1, e, v2). (v1, e, v2) \<in> (\<alpha> l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

  type_synonym ('V1,'W1,'L1,'V2,'W2,'L2) lts_image_filter = "
        (('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)) \<Rightarrow>
        ('V1 \<Rightarrow> bool) \<Rightarrow> ('W1 \<Rightarrow> bool) \<Rightarrow> ('V1 \<Rightarrow> bool) \<Rightarrow>
        (('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> bool) \<Rightarrow> 'L1 \<Rightarrow> 'L2"
  locale lts_image_filter = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes image_filter :: "('V1,'W1,'L1,'V2,'W2,'L2) lts_image_filter"
    assumes lts_image_filter_correct :
      "invar1 l \<Longrightarrow> invar2 (image_filter f P_v1 P_e P_v2 P l)"
      "invar1 l \<Longrightarrow> \<alpha>2(image_filter f P_v1 P_e P_v2 P l) =
         f ` {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

  locale dlts_image_filter = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes image_filter 
    assumes dlts_image_filter_correct :
      "invar1 l \<Longrightarrow> LTS_is_deterministic (f ` {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}) \<Longrightarrow> invar2 (image_filter f P_v1 P_e P_v2 P l)"
      "invar1 l \<Longrightarrow> LTS_is_deterministic (f ` {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}) \<Longrightarrow> \<alpha>2(image_filter f P_v1 P_e P_v2 P l) =
         f ` {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

  lemma dlts_image_filter_sublocale :
    "lts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 image_filter \<Longrightarrow>
     dlts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 image_filter"
  unfolding lts_image_filter_def dlts_image_filter_def by simp

  locale lts_image_fixed = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes image_f :: "'L1 \<Rightarrow> 'L2" and f :: "('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)"
    assumes lts_image_fixed_correct :
      "invar1 l \<Longrightarrow> invar2 (image_f l)"
      "invar1 l \<Longrightarrow> \<alpha>2(image_f l) = f ` (\<alpha>1 l)"

  type_synonym ('V1,'W1,'L1,'V2,'W2,'L2) lts_image = "
        (('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)) \<Rightarrow> 'L1 \<Rightarrow> 'L2"
  locale lts_image = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes image :: "('V1,'W1,'L1,'V2,'W2,'L2) lts_image"
    assumes lts_image_correct :
      "invar1 l \<Longrightarrow> invar2 (image f l)"
      "invar1 l \<Longrightarrow> \<alpha>2(image f l) = f ` (\<alpha>1 l)"

  lemma lts_image_alt_def :
    "lts_image \<alpha>1 invar1 \<alpha>2 invar2 im \<longleftrightarrow>
     (\<forall>f. lts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 (im f) f)"
    unfolding lts_image_def lts_image_fixed_def by auto

  locale dlts_image_fixed = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes image_f :: "'L1 \<Rightarrow> 'L2" and f :: "('V1 \<times> 'W1 \<times> 'V1) \<Rightarrow> ('V2 \<times> 'W2 \<times> 'V2)"
    assumes dlts_image_fixed_correct :
      "invar1 l \<Longrightarrow> LTS_is_deterministic (f ` (\<alpha>1 l)) \<Longrightarrow> invar2 (image_f l)"
      "invar1 l \<Longrightarrow> LTS_is_deterministic (f ` (\<alpha>1 l)) \<Longrightarrow> \<alpha>2(image_f l) = f ` (\<alpha>1 l)"

  locale dlts_image = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes image :: "('V1,'W1,'L1,'V2,'W2,'L2) lts_image" 
    assumes dlts_image_correct :
      "invar1 l \<Longrightarrow> LTS_is_deterministic (f ` (\<alpha>1 l)) \<Longrightarrow> invar2 (image f l)"
      "invar1 l \<Longrightarrow> LTS_is_deterministic (f ` (\<alpha>1 l)) \<Longrightarrow> \<alpha>2(image f l) = f ` (\<alpha>1 l)"

  lemma dlts_image_alt_def :
    "dlts_image \<alpha>1 invar1 \<alpha>2 invar2 im \<longleftrightarrow>
     (\<forall>f. dlts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 (im f) f)"
    unfolding dlts_image_def dlts_image_fixed_def by auto

  lemma dlts_image_sublocale :
    "lts_image \<alpha>1 invar1 \<alpha>2 invar2 im \<Longrightarrow>
     dlts_image \<alpha>1 invar1 \<alpha>2 invar2 im"
  unfolding lts_image_def dlts_image_def by simp

  lemma dlts_image_fixed_sublocale :
    "lts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 im f \<Longrightarrow>
     dlts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 im f"
  unfolding lts_image_fixed_def dlts_image_fixed_def by simp

  definition lts_rename_states_fixed where
    "lts_rename_states_fixed \<alpha>1 invar1 \<alpha>2 invar2 im f =
     lts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 im 
        (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq))))"

  definition dlts_rename_states_fixed where
    "dlts_rename_states_fixed \<alpha>1 invar1 \<alpha>2 invar2 im f =
     dlts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 im 
        (\<lambda>qaq. (f (fst qaq), fst (snd qaq), f (snd (snd qaq))))"

  definition lts_rename_labels_fixed where
    "lts_rename_labels_fixed \<alpha>1 invar1 \<alpha>2 invar2 im f =
     lts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 im 
        (\<lambda>qaq. (fst qaq, f (fst (snd qaq)), snd (snd qaq)))"

  definition dlts_rename_labels_fixed where
    "dlts_rename_labels_fixed \<alpha>1 invar1 \<alpha>2 invar2 im f =
     dlts_image_fixed \<alpha>1 invar1 \<alpha>2 invar2 im 
        (\<lambda>qaq. (fst qaq, f (fst (snd qaq)), snd (snd qaq)))"

  locale lts_inj_image_filter = lts \<alpha>1 invar1 + lts \<alpha>2 invar2 
    for \<alpha>1 :: "('V1,'W1,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V2,'W2,'L2) lts_\<alpha>" and invar2 +
    fixes inj_image_filter 
    assumes lts_inj_image_filter_correct :
      "invar1 l \<Longrightarrow> LTS_image_filter_inj_on f {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)} \<Longrightarrow> invar2 (inj_image_filter f P_v1 P_e P_v2 P l)"
      "invar1 l \<Longrightarrow> LTS_image_filter_inj_on f {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)} \<Longrightarrow> \<alpha>2(inj_image_filter f P_v1 P_e P_v2 P l) =
         f ` {(v1, e, v2). (v1, e, v2) \<in> (\<alpha>1 l) \<and> P_v1 v1 \<and> 
               P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

  lemma lts_inj_image_filter_sublocale :
    "lts_image_filter \<alpha>1 invar1 \<alpha>2 invar2 image_filter \<Longrightarrow>
     lts_inj_image_filter \<alpha>1 invar1 \<alpha>2 invar2 image_filter"
  unfolding lts_image_filter_def lts_inj_image_filter_def by simp

  type_synonym ('V,'W,'\<sigma>,'L) lts_succ_label_it = 
    "'L \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,'\<sigma>) set_iterator"
  locale lts_succ_label_it = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes succ_label_it :: "('V,'W,'\<sigma>,'L) lts_succ_label_it"
    assumes lts_succ_label_it_correct:
      "invar l \<Longrightarrow> set_iterator (succ_label_it l v) {(e, v') . (v, e, v') \<in> (\<alpha> l)}"

  type_synonym ('V,'W,'\<sigma>,'L) lts_succ_label_abs_it = 
    "'L \<Rightarrow> 'V \<Rightarrow> ('W\<times>'V,'\<sigma>) set_iterator"
  locale lts_succ_label_abs_it = lts \<alpha> invar + set \<alpha>_s invar_s 
    for \<alpha> :: "('V,'W,'L) lts_\<alpha>" and invar
    and \<alpha>_s :: "'Vset \<Rightarrow> 'V set" and invar_s +
    fixes succ_label_abs_it 
    assumes lts_succ_label_abs_it_correct:
      "invar l \<Longrightarrow> map_iterator_abs \<alpha>_s invar_s (succ_label_abs_it l v) 
           (\<lambda>e. let vs = {v' . (v, e, v') \<in> \<alpha> l} in (if vs = {} then None else Some vs))"

  type_synonym ('V,'W,'\<sigma>,'L) lts_pre_label_it =  "'L \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,'\<sigma>) set_iterator"
  locale lts_pre_label_it = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes pre_label_it :: "'L \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,'\<sigma>) set_iterator"
    assumes lts_pre_label_it_correct:
      "invar l \<Longrightarrow> set_iterator (pre_label_it l v') {(v, e) . (v, e, v') \<in> (\<alpha> l)}"

  type_synonym ('V,'W,'\<sigma>,'L) lts_succ_it = 
    "'L \<Rightarrow> 'V \<Rightarrow> 'W \<Rightarrow> ('V,'\<sigma>) set_iterator"
  locale lts_succ_it = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes succ_it :: "('V,'W,'\<sigma>,'L) lts_succ_it"
    assumes lts_succ_it_correct:
      "invar l \<Longrightarrow> set_iterator (succ_it l v e) {v' . (v, e, v') \<in> (\<alpha> l)}"

  type_synonym ('V,'W,'\<sigma>,'L) lts_pre_it =  "'L \<Rightarrow> 'V \<Rightarrow> 'W \<Rightarrow> ('V,'\<sigma>) set_iterator"
  locale lts_pre_it = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes pre_it :: "('V,'W,'\<sigma>,'L) lts_pre_it"
    assumes lts_pre_it_correct:
      "invar l \<Longrightarrow> set_iterator (pre_it l v' e) {v . (v, e, v') \<in> (\<alpha> l)}"

  type_synonym ('V,'W,'L) lts_succ_bquant = "'L \<Rightarrow> ('V \<Rightarrow> bool) \<Rightarrow> 'V \<Rightarrow> 'W \<Rightarrow> bool"
  locale lts_succ_ball = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes succ_ball :: "('V,'W,'L) lts_succ_bquant"
    assumes lts_succ_ball_correct:
      "invar l \<Longrightarrow> succ_ball l P v e \<longleftrightarrow> (\<forall>v'. (v, e, v') \<in> (\<alpha> l) \<longrightarrow> P v')"

  locale lts_succ_bex = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes succ_bex :: "('V,'W,'L) lts_succ_bquant"
    assumes lts_succ_bex_correct:
      "invar l \<Longrightarrow> succ_bex l P v e \<longleftrightarrow> (\<exists>v'. (v, e, v') \<in> (\<alpha> l) \<and> P v')"

  type_synonym ('V,'W,'L) lts_pre_bquant = "'L \<Rightarrow> ('V \<Rightarrow> bool) \<Rightarrow> 'V \<Rightarrow> 'W \<Rightarrow> bool"
  locale lts_pre_ball = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes pre_ball :: "('V,'W,'L) lts_pre_bquant"
    assumes lts_pre_ball_correct:
      "invar l \<Longrightarrow> pre_ball l P v' e \<longleftrightarrow> (\<forall>v. (v, e, v') \<in> (\<alpha> l) \<longrightarrow> P v)"

  locale lts_pre_bex = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes pre_bex :: "('V,'W,'L) lts_pre_bquant"
    assumes lts_pre_bex_correct:
      "invar l \<Longrightarrow> pre_bex l P v' e \<longleftrightarrow> (\<exists>v. (v, e, v') \<in> (\<alpha> l) \<and> P v)"

  type_synonym ('V,'W,'L) lts_from_list = "('V \<times> 'W \<times> 'V) list \<Rightarrow> 'L"
  locale lts_from_list = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes from_list :: "('V,'W,'L) lts_from_list"
    assumes lts_from_list_correct:
      "invar (from_list ll)"
      "\<alpha> (from_list ll) = set ll"

  locale dlts_from_list = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes from_list :: "('V,'W,'L) lts_from_list"
    assumes dlts_from_list_correct:
      "(\<forall>v w v' v''. (v, w, v') \<in> set ll \<and> (v, w, v'') \<in> set ll \<longrightarrow> v' = v'') \<Longrightarrow> invar (from_list ll)"
      "(\<forall>v w v' v''. (v, w, v') \<in> set ll \<and> (v, w, v'') \<in> set ll \<longrightarrow> v' = v'') \<Longrightarrow> 
         \<alpha> (from_list ll) = set ll"

  lemma lts_from_list_sublocale: "lts_from_list \<alpha> invar from_list \<Longrightarrow> 
                                  dlts_from_list \<alpha> invar from_list"
  unfolding lts_from_list_def dlts_from_list_def
  by simp
  
  type_synonym ('V,'W,'L) lts_to_list = "'L \<Rightarrow> ('V \<times> 'W \<times> 'V) list"
  locale lts_to_list = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes to_list :: "('V,'W,'L) lts_to_list"
    assumes lts_to_list_correct:
      "invar l \<Longrightarrow> set (to_list l) = \<alpha> l"
      "invar l \<Longrightarrow> distinct (to_list l)"

  type_synonym ('V,'W,'L) lts_to_collect_list = "'L \<Rightarrow> ('V \<times> 'W list \<times> 'V) list"
  locale lts_to_collect_list = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes to_collect_list :: "('V,'W,'L) lts_to_collect_list"
    assumes lts_to_collect_list_correct:
      "invar l \<Longrightarrow> \<alpha> l = {(v, e, v'). \<exists>es. (v, es, v') \<in> set (to_collect_list l) \<and> e \<in> set es}"
      "invar l \<Longrightarrow> distinct (map (\<lambda>vesv'. (fst vesv', snd (snd vesv'))) (to_collect_list l))"
      "invar l \<Longrightarrow> (v, es, v') \<in> set (to_collect_list l) \<Longrightarrow> es \<noteq> []"


  type_synonym ('V,'W,'L) lts_from_collect_list = "('V \<times> 'W list \<times> 'V) list \<Rightarrow> 'L"
  locale lts_from_collect_list = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes from_collect_list :: "('V,'W,'L) lts_from_collect_list"
    assumes lts_from_collect_list_correct:
      "invar (from_collect_list ll)"
      "\<alpha> (from_collect_list ll) = {(v, e, v'). \<exists>es. (v, es, v') \<in> set ll \<and> e \<in> set es}"

  locale dlts_from_collect_list = lts +
    constrains \<alpha> :: "('V,'W,'L) lts_\<alpha>"
    fixes from_collect_list :: "('V,'W,'L) lts_from_collect_list"
    assumes dlts_from_collect_list_correct:
      "(\<forall>v ws ws' w v' v''. (v, ws, v') \<in> set ll \<and> (v, ws', v'') \<in> set ll \<and>
                               (w \<in> set ws) \<and> (w \<in> set ws') \<longrightarrow> (v' = v'')) \<Longrightarrow>
       invar (from_collect_list ll)"
      "(\<forall>v ws ws' w v' v''. (v, ws, v') \<in> set ll \<and> (v, ws', v'') \<in> set ll \<and>
                               (w \<in> set ws) \<and> (w \<in> set ws') \<longrightarrow> (v' = v'')) \<Longrightarrow>
       \<alpha> (from_collect_list ll) = {(v, e, v'). \<exists>es. (v, es, v') \<in> set ll \<and> e \<in> set es}"

  lemma lts_from_collect_list_sublocale: "lts_from_collect_list \<alpha> invar from_collect_list \<Longrightarrow> 
                                  dlts_from_collect_list \<alpha> invar from_collect_list"
  unfolding lts_from_collect_list_def dlts_from_collect_list_def
  by simp

  type_synonym ('V,'W,'L1,'L2) lts_reverse = "'L1 \<Rightarrow> 'L2"
  locale lts_reverse = lts \<alpha>1 invar1 + lts \<alpha>2 invar2  
    for \<alpha>1 :: "('V,'W,'L1) lts_\<alpha>" and invar1 and
        \<alpha>2 :: "('V,'W,'L2) lts_\<alpha>" and invar2 +
    fixes reverse :: "('V,'W,'L1,'L2) lts_reverse"
    assumes lts_reverse_correct:
      "invar1 l \<Longrightarrow> invar2 (reverse l)"
      "invar1 l \<Longrightarrow> \<alpha>2 (reverse l) = {(v', e, v) | v e v'. (v, e, v') \<in> \<alpha>1 l}"

  type_synonym ('V,'W,'L,'\<sigma>_s) lts_get_succ_set = 
    "'L \<Rightarrow> 'V list \<Rightarrow> 'W \<Rightarrow> '\<sigma>_s"
  locale lts_get_succ_set = lts \<alpha> invar + set \<alpha>_s invar_s 
    for \<alpha> :: "('V,'W,'L) lts_\<alpha>" and invar and
        \<alpha>_s :: "'\<sigma>_s \<Rightarrow> 'V set" and invar_s +
    fixes get_succ_set :: "('V,'W,'L,'\<sigma>_s) lts_get_succ_set"
    assumes lts_get_succ_set_correct:
      "invar l \<Longrightarrow> invar_s (get_succ_set l vs e)"
      "invar l \<Longrightarrow> \<alpha>_s (get_succ_set l vs e) = {v' . \<exists>v. v \<in> set vs \<and> (v, e, v') \<in> (\<alpha> l)}"

  definition lts_iterator_union :: "('V, 'W, 'L, 'L) lts_it \<Rightarrow>
    ('V ,'W, 'L) lts_add \<Rightarrow> ('V, 'W, 'L, 'L, 'L) lts_union"
  where "lts_iterator_union iterator add l1 l2 =
    iterator l1 (\<lambda> _. True) (\<lambda> (p, a, q). add p a q) l2"

  lemma lts_iterator_union_correct:
    assumes a: "lts_iterator \<alpha> invar iterator"
    assumes b: "lts_add \<alpha> invar add"
    shows "lts_union \<alpha> invar \<alpha> invar \<alpha> invar (lts_iterator_union iterator add)"
  proof -
    interpret lts_iterator \<alpha> invar iterator using a by assumption
    interpret lts_add \<alpha> invar add using b by assumption
    show ?thesis
      apply (unfold_locales)
      unfolding lts_iterator_union_def
      apply (rule_tac I = "\<lambda> _ \<sigma>. invar \<sigma>" in set_iterator_rule_P[OF lts_it_correct])
      apply (auto simp: lts_add_correct) [5]
      apply (rule_tac I = "\<lambda> it \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = it \<union> \<alpha> l2"
        in set_iterator_rule_insert_P[OF lts_it_correct])
      apply (auto simp: lts_add_correct) [5]
    done
  qed

  lemma dlts_iterator_union_correct:
    assumes a: "lts_iterator \<alpha> invar iterator"
    assumes b: "dlts_add \<alpha> invar add"
    shows "dlts_union \<alpha> invar \<alpha> invar \<alpha> invar (lts_iterator_union iterator add)"
  proof -
    interpret lts_iterator \<alpha> invar iterator using a by assumption
    interpret dlts_add \<alpha> invar add using b by assumption
    show ?thesis
    proof (unfold_locales)
      fix l1 l2
      assume a: "invar l1" "invar l2"
      assume b: "LTS_is_deterministic (\<alpha> l1)"
      assume c: "\<And> p a q1 q2. (p, a, q1) \<in> \<alpha> l1 \<Longrightarrow> (p, a, q2) \<in> \<alpha> l2 \<Longrightarrow> q1 = q2"

      {
        fix S \<sigma> p a q
        assume a: "(p, a, q) \<in> \<alpha> l1 - S" "invar \<sigma>" "\<alpha> \<sigma> = S \<union> \<alpha> l2" "S \<subseteq> \<alpha> l1"
        have "\<And> q'. (p, a, q') \<in> \<alpha> \<sigma> \<Longrightarrow> q' = q"
          using a b c
          unfolding LTS_is_deterministic_def 
          by blast
        hence
          "invar (add p a q \<sigma>)"
          "\<alpha> (add p a q \<sigma>) = insert (p, a, q) S \<union> \<alpha> l2"
          using dlts_add_correct a
          by blast+
      }
      note d = this

      let ?I = "\<lambda> S \<sigma>. invar \<sigma> \<and> \<alpha> \<sigma> = S \<union> \<alpha> l2"
      show "invar (lts_iterator_union iterator add l1 l2)"
        unfolding lts_iterator_union_def
        apply (rule set_iterator_rule_insert_P[OF lts_it_correct, where I = ?I])
        using a d
        apply auto
      done
      show "\<alpha> (lts_iterator_union iterator add l1 l2) = \<alpha> l1 \<union> \<alpha> l2"
        unfolding lts_iterator_union_def
        apply (rule set_iterator_rule_insert_P[OF lts_it_correct, where I = ?I])
        using a d
        apply auto
      done
    qed
  qed

  section \<open> Record Based Interface \<close>
  record ('V,'W,'L) lts_ops =
    lts_op_\<alpha> :: "('V,'W,'L) lts_\<alpha>"
    lts_op_invar :: "'L \<Rightarrow> bool"
    lts_op_empty :: "('V,'W,'L) lts_empty"
    lts_op_memb :: "('V,'W,'L) lts_memb"
    lts_op_iterator :: "('V, 'W, 'L, 'L) lts_it"
    lts_op_add :: "('V,'W,'L) lts_add"
    lts_op_add_succs :: "('V,'W,'L) lts_add_succs"
    lts_op_delete :: "('V,'W,'L) lts_delete"
    lts_op_succ_ball :: "('V,'W,'L) lts_succ_bquant"
    lts_op_succ_bex :: "('V,'W,'L) lts_succ_bquant"
    lts_op_pre_ball :: "('V,'W,'L) lts_pre_bquant"
    lts_op_pre_bex :: "('V,'W,'L) lts_pre_bquant"
    lts_op_to_list :: "('V,'W,'L) lts_to_list"
    lts_op_to_collect_list :: "('V,'W,'L) lts_to_collect_list"
    lts_op_from_list :: "('V,'W,'L) lts_from_list"
    lts_op_from_collect_list :: "('V,'W,'L) lts_from_collect_list"
    lts_op_image_filter :: "('V,'W,'L,'V,'W,'L) lts_image_filter"
    lts_op_filter :: "('V,'W,'L) lts_filter"
    lts_op_image :: "('V,'W,'L,'V,'W,'L) lts_image"
    lts_op_succ :: "('V,'W,'L) lts_succ"
   

  locale StdCommonLTSDefs =
    fixes ops :: "('V,'W,'L,'m) lts_ops_scheme"
  begin
    abbreviation \<alpha> where "\<alpha> \<equiv> lts_op_\<alpha> ops"
    abbreviation invar where "invar \<equiv> lts_op_invar ops"
    abbreviation empty where "empty \<equiv> lts_op_empty ops"
    abbreviation memb where "memb \<equiv> lts_op_memb ops"
    abbreviation iterator where "iterator \<equiv> lts_op_iterator ops"
    abbreviation add where "add \<equiv> lts_op_add ops"
    abbreviation add_succs where "add_succs \<equiv> lts_op_add_succs ops"
    abbreviation delete where "delete \<equiv> lts_op_delete ops"
    abbreviation from_list where "from_list \<equiv> lts_op_from_list ops"
    abbreviation from_collect_list where "from_collect_list \<equiv> lts_op_from_collect_list ops"
    abbreviation to_list where "to_list \<equiv> lts_op_to_list ops"
    abbreviation to_collect_list where "to_collect_list \<equiv> lts_op_to_collect_list ops"
    abbreviation succ_ball where "succ_ball \<equiv> lts_op_succ_ball ops"
    abbreviation succ_bex where "succ_bex \<equiv> lts_op_succ_bex ops"
    abbreviation pre_ball where "pre_ball \<equiv> lts_op_pre_ball ops"
    abbreviation pre_bex where "pre_bex \<equiv> lts_op_pre_bex ops"
    abbreviation image_filter where "image_filter \<equiv> lts_op_image_filter ops"
    abbreviation filter where "filter \<equiv> lts_op_filter ops"
    abbreviation image where "image \<equiv> lts_op_image ops"
    abbreviation succ where "succ \<equiv> lts_op_succ ops"
    abbreviation union where "union \<equiv> lts_iterator_union iterator add"
  end

  locale StdCommonLTS = StdCommonLTSDefs +
    finite_lts \<alpha> invar +
    lts_empty \<alpha> invar empty +
    lts_memb \<alpha> invar memb +
    lts_iterator \<alpha> invar iterator +
    lts_to_list \<alpha> invar to_list +
    lts_to_collect_list \<alpha> invar to_collect_list +
    lts_succ_ball \<alpha> invar succ_ball +
    lts_pre_ball \<alpha> invar pre_ball +
    lts_succ_bex \<alpha> invar succ_bex +
    lts_pre_bex \<alpha> invar pre_bex +
    dlts_add \<alpha> invar add +
    dlts_add_succs \<alpha> invar add_succs +
    lts_delete \<alpha> invar delete +
    dlts_from_list \<alpha> invar from_list +
    dlts_from_collect_list \<alpha> invar from_collect_list +
    lts_filter \<alpha> invar filter +
    dlts_image_filter \<alpha> invar \<alpha> invar image_filter +
    dlts_image \<alpha> invar \<alpha> invar image +
    lts_inj_image_filter \<alpha> invar  \<alpha> invar image_filter +
    lts_succ \<alpha> invar succ 
  begin
    lemmas dlts_union_axioms = dlts_iterator_union_correct[OF lts_iterator_axioms dlts_add_axioms]
    lemmas correct_common = lts_empty_correct lts_memb_correct lts_it_correct
       lts_to_list_correct dlts_from_collect_list_correct 
       lts_succ_ball_correct lts_pre_ball_correct lts_succ_correct
       lts_succ_bex_correct lts_pre_bex_correct 
       dlts_add_correct dlts_add_succs_correct lts_delete_correct dlts_from_list_correct
       dlts_image_filter_correct lts_inj_image_filter_correct lts_filter_correct dlts_image_correct
       dlts_union.dlts_union_correct[OF dlts_union_axioms]
  end

  locale StdLTS = StdCommonLTSDefs +
    finite_lts \<alpha> invar +
    lts_empty \<alpha> invar empty +
    lts_memb \<alpha> invar memb +
    lts_iterator \<alpha> invar iterator +
    lts_to_list \<alpha> invar to_list +
    lts_to_collect_list \<alpha> invar to_collect_list +
    lts_succ_ball \<alpha> invar succ_ball +
    lts_pre_ball \<alpha> invar pre_ball +
    lts_succ_bex \<alpha> invar succ_bex +
    lts_pre_bex \<alpha> invar pre_bex +
    lts_add \<alpha> invar add +
    lts_add_succs \<alpha> invar add_succs +
    lts_delete \<alpha> invar delete +
    lts_from_list \<alpha> invar from_list +
    lts_from_collect_list \<alpha> invar from_collect_list +
    lts_filter \<alpha> invar filter +
    lts_image_filter \<alpha> invar \<alpha> invar image_filter +
    lts_image \<alpha> invar \<alpha> invar image +
    lts_succ \<alpha> invar succ 
  begin
    lemmas lts_union_axioms = lts_iterator_union_correct[OF lts_iterator_axioms lts_add_axioms]
    lemmas correct = lts_empty_correct lts_memb_correct lts_it_correct
       lts_to_list_correct lts_succ_ball_correct lts_pre_ball_correct
       lts_succ_bex_correct lts_pre_bex_correct lts_succ_correct
       lts_add_correct lts_add_succs_correct lts_delete_correct lts_from_list_correct
       lts_from_collect_list_correct
       lts_image_filter_correct lts_filter_correct lts_image_correct
       lts_union.lts_union_correct[OF lts_union_axioms]
  end

  lemma StdLTS_sublocale : "StdLTS ops \<Longrightarrow> StdCommonLTS ops"
    unfolding StdLTS_def StdCommonLTS_def
    by (simp add: lts_add_sublocale lts_add_succs_sublocale 
                  lts_from_list_sublocale lts_from_collect_list_sublocale
                  lts_inj_image_filter_sublocale dlts_image_filter_sublocale
                  dlts_image_sublocale)

  sublocale StdLTS < StdCommonLTS using StdLTS_sublocale [OF StdLTS_axioms] .

  locale StdDLTS = StdCommonLTSDefs +
    finite_lts \<alpha> invar +
    lts_empty \<alpha> invar empty +
    lts_memb \<alpha> invar memb +
    lts_iterator \<alpha> invar iterator +
    lts_to_list \<alpha> invar to_list +
    lts_to_collect_list \<alpha> invar to_collect_list +
    lts_succ_ball \<alpha> invar succ_ball +
    lts_pre_ball \<alpha> invar pre_ball +
    lts_succ_bex \<alpha> invar succ_bex +
    lts_pre_bex \<alpha> invar pre_bex +
    dlts_add \<alpha> invar add +
    dlts_add_succs \<alpha> invar add_succs +
    lts_delete \<alpha> invar delete +
    dlts_from_list \<alpha> invar from_list +
    dlts_from_collect_list \<alpha> invar from_collect_list +
    lts_filter \<alpha> invar filter +
    dlts_image_filter \<alpha> invar \<alpha> invar image_filter +
    dlts_image \<alpha> invar \<alpha> invar image +
    lts_inj_image_filter \<alpha> invar  \<alpha> invar image_filter +
    dlts_succ \<alpha> invar succ 
  begin
    lemmas dlts_union_axioms = dlts_iterator_union_correct[OF lts_iterator_axioms dlts_add_axioms]
    lemmas correct = lts_empty_correct lts_memb_correct lts_it_correct
       lts_to_list_correct dlts_from_collect_list_correct 
       lts_succ_ball_correct lts_pre_ball_correct dlts_succ_correct
       lts_succ_bex_correct lts_pre_bex_correct 
       dlts_add_correct dlts_add_succs_correct lts_delete_correct dlts_from_list_correct
       dlts_image_filter_correct lts_inj_image_filter_correct lts_filter_correct dlts_image_correct
       dlts_union.dlts_union_correct[OF dlts_union_axioms]
  end

  lemma StdDLTS_sublocale : "StdDLTS ops \<Longrightarrow> StdCommonLTS ops"
    unfolding StdDLTS_def StdCommonLTS_def
    by (simp add: dlts_succ_sublocale)

  lemma StdLTS_sublocale2 : "StdLTS ops \<Longrightarrow> StdDLTS (ops \<lparr> lts_op_invar := 
       \<lambda>l. LTS_is_deterministic (lts_op_\<alpha> ops l) \<and> lts_op_invar ops l \<rparr>)"
    unfolding StdDLTS_def
    apply simp_all
    proof (intro conjI)
      assume "StdLTS ops"
      interpret lts: StdLTS ops by fact
      let ?invar' = "\<lambda>l. LTS_is_deterministic (lts_op_\<alpha> ops l) \<and> lts_op_invar ops l"


      show "finite_lts lts.\<alpha> ?invar'"
           "lts_memb lts.\<alpha> ?invar' lts.memb"
           "lts_iterator lts.\<alpha> ?invar' lts.iterator"
           "lts_to_list lts.\<alpha> ?invar' lts.to_list"
           "lts_succ_ball lts.\<alpha> ?invar' lts.succ_ball"
           "lts_succ_bex lts.\<alpha> ?invar' lts.succ_bex"
           "lts_pre_ball lts.\<alpha> ?invar' lts.pre_ball"
           "lts_pre_bex lts.\<alpha> ?invar' lts.pre_bex"
           "dlts_image_filter lts.\<alpha> ?invar' lts.\<alpha> ?invar' lts.image_filter"
        unfolding finite_lts_def lts_empty_def lts_memb_def lts_iterator_def
                  lts_to_list_def lts_succ_ball_def lts_succ_bex_def
                  lts_pre_ball_def lts_pre_bex_def lts_delete_def
                  dlts_image_filter_def
        by (simp_all add: lts.correct)

      show "lts_empty lts.\<alpha> ?invar' lts.empty"
        unfolding lts_empty_def LTS_is_deterministic_def 
      by (simp add: lts.correct)

      show "lts_to_collect_list lts.\<alpha> ?invar' lts.to_collect_list"
        unfolding lts_to_collect_list_def 
        using lts.lts_to_collect_list_correct
      by blast

      show "dlts_add lts.\<alpha> ?invar' lts.add"
        unfolding dlts_add_def
        using lts.lts_add_correct
      by (auto simp add: LTS_is_deterministic_def) metis+

      show "dlts_add_succs lts.\<alpha> ?invar' lts.add_succs"
        unfolding dlts_add_succs_def
        using lts.lts_add_succs_correct
        apply (simp add: LTS_is_deterministic_def length_Suc_conv) 
        apply (subgoal_tac "\<And>xs::'a list. length xs < 2 \<longleftrightarrow> xs = [] \<or> (\<exists>x. xs = [x])")
        apply auto[]
        apply fastforce
        apply (case_tac xs)
        apply simp_all
      done

      show "lts_delete lts.\<alpha> ?invar' lts.delete"
        unfolding lts_delete_def
        using lts.lts_delete_correct
        by (auto simp add: LTS_is_deterministic_def)

      show "dlts_from_list lts.\<alpha> ?invar' lts.from_list"
        unfolding dlts_from_list_def
        using lts.lts_from_list_correct
      by (simp add: LTS_is_deterministic_def) 

      show "dlts_from_collect_list lts.\<alpha> ?invar' lts.from_collect_list"
        unfolding dlts_from_collect_list_def
        using lts.lts_from_collect_list_correct
      by (simp add: LTS_is_deterministic_def) blast

      show "lts_filter lts.\<alpha> ?invar' lts.filter"
        unfolding lts_filter_def
        using lts.lts_filter_correct
      by (simp add: LTS_is_deterministic_def) blast

      show "lts_inj_image_filter lts.\<alpha> ?invar' lts.\<alpha> ?invar' lts.image_filter"
      proof 
        fix f :: "'a \<times> 'b \<times> 'a \<Rightarrow> 'a \<times> 'b \<times> 'a"
        fix l P_v1 P_e P_v2 P
        assume invar_l: "LTS_is_deterministic (lts.\<alpha> l) \<and> lts.invar l"
        assume inj_on: "LTS_image_filter_inj_on f {(v1, e, v2).
          (v1, e, v2) \<in> lts.\<alpha> l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)}"

        have \<alpha>_eq: "lts.\<alpha> (lts.image_filter f P_v1 P_e P_v2 P l) =
           f ` {(v1, e, v2). (v1, e, v2) \<in> lts.\<alpha> l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)} "
          and invar_filter: "lts.invar (lts.image_filter f P_v1 P_e P_v2 P l)"
          using lts.lts_image_filter_correct [of l f P_v1 P_e P_v2 P] invar_l by simp_all

        show "lts.\<alpha> (lts.image_filter f P_v1 P_e P_v2 P l) =
           f ` {(v1, e, v2). (v1, e, v2) \<in> lts.\<alpha> l \<and> P_v1 v1 \<and> P_e e \<and> P_v2 v2 \<and> P (v1, e, v2)} "
          using \<alpha>_eq .

        from inj_on invar_l 
        show "LTS_is_deterministic (lts.\<alpha> (lts.image_filter f P_v1 P_e P_v2 P l)) \<and>
              lts.invar (lts.image_filter f P_v1 P_e P_v2 P l)"
          unfolding \<alpha>_eq  
          apply (simp add: invar_filter)
          apply (rule_tac lts_image_filter_inj_on_implies_deterministic)
          apply (simp_all add: LTS_is_deterministic_def)
          apply blast
        done
      qed

      show "dlts_image lts.\<alpha> ?invar' lts.\<alpha> ?invar' lts.image"
        unfolding dlts_image_def
        using lts.lts_image_correct
      by (simp add: LTS_is_deterministic_def) 

      show "dlts_succ lts.\<alpha> ?invar' lts.succ"
        unfolding dlts_succ_def
        using lts.lts_succ_det_correct
      by simp
    qed 
    
end
