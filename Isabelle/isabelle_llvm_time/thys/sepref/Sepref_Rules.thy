section \<open>Refinement Rule Management\<close>
theory Sepref_Rules
  imports Sepref_Basic Sepref_Constraints 
begin
  text \<open>This theory contains tools for managing the refinement rules used by Sepref\<close>

  text \<open>The theories are based on uncurried functions, i.e.,
    every function has type @{typ "'a\<Rightarrow>'b"}, where @{typ 'a} is the 
    tuple of parameters, or unit if there are none.
    \<close>

    
  definition "non_dep R \<equiv> \<forall>b. R b = R undefined"
  lemma non_dep_simp: "non_dep R \<Longrightarrow> NO_MATCH undefined x \<Longrightarrow> R x = R undefined"
    by (auto simp: non_dep_def)
    
  lemma non_dep_K[simp, intro!]: "non_dep (\<lambda>_. c)"  
    by (auto simp: non_dep_def)
    
  definition "non_dep2 R \<equiv> \<forall>a b. R a b = R undefined undefined"
  lemma non_dep2_simp: 
    "non_dep2 R \<Longrightarrow> NO_MATCH undefined x \<Longrightarrow> R x y = R undefined undefined"
    "non_dep2 R \<Longrightarrow> NO_MATCH undefined y \<Longrightarrow> R x y = R undefined undefined"
    by (auto simp: non_dep2_def)
    
  lemma non_dep2_K[simp, intro!]: "non_dep2 (\<lambda>_ _. c)"  
    by (auto simp: non_dep2_def)
    
    
    

  subsection \<open>Assertion Interface Binding\<close>
  text \<open>Binding of interface types to refinement assertions\<close>
  definition intf_of_assn :: "('a \<Rightarrow> _ \<Rightarrow> assn) \<Rightarrow> 'b itself \<Rightarrow> bool" where
    [simp]: "intf_of_assn a b = True"

  lemma intf_of_assnI: "intf_of_assn R TYPE('a)" by simp
  
  named_theorems_rev intf_of_assn \<open>Links between refinement assertions and interface types\<close>  

  lemma intf_of_assn_fallback: "intf_of_assn (R :: 'a \<Rightarrow> _ \<Rightarrow> assn) TYPE('a)" by simp

  subsection \<open>Function Refinement with Precondition\<close>
  definition fref :: "('c \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> ('c \<Rightarrow> ('b \<times> 'd) set)
           \<Rightarrow> (('a \<Rightarrow> 'b) \<times> ('c \<Rightarrow> 'd)) set"
    ("[_]\<^sub>f\<^sub>d _ \<rightarrow> _" [0,60,60] 60)         
  where "[P]\<^sub>f\<^sub>d R \<rightarrow> S \<equiv> {(f,g). \<forall>x y. P y \<and> (x,y)\<in>R \<longrightarrow> (f x, g y)\<in>S y}"
  
  abbreviation freft ("_ \<rightarrow>\<^sub>f\<^sub>d _" [60,60] 60) where "R \<rightarrow>\<^sub>f\<^sub>d S \<equiv> ([\<lambda>_. True]\<^sub>f\<^sub>d R \<rightarrow> S)"
  abbreviation freftnd ("_ \<rightarrow>\<^sub>f _" [60,60] 60) where "R \<rightarrow>\<^sub>f S \<equiv> ([\<lambda>_. True]\<^sub>f\<^sub>d R \<rightarrow> (\<lambda>_. S))"
  abbreviation frefnd ("[_]\<^sub>f _ \<rightarrow> _" [0,60,60] 60) where "[P]\<^sub>f R \<rightarrow> S \<equiv> [P]\<^sub>f\<^sub>d R \<rightarrow> (\<lambda>_. S)"

  
  
  lemma rel2p_fref[rel2p]: "rel2p (fref P R S) 
    = (\<lambda>f g. (\<forall>x y. P y \<longrightarrow> rel2p R x y \<longrightarrow> rel2p (S y) (f x) (g y)))"  
    by (auto simp: fref_def rel2p_def[abs_def])

  lemma fref_cons:  
    assumes "(f,g) \<in> [P]\<^sub>f\<^sub>d R \<rightarrow> S"
    assumes "\<And>c a. (c,a)\<in>R' \<Longrightarrow> Q a \<Longrightarrow> P a"
    assumes "R' \<subseteq> R"
    assumes "\<And>c a. \<lbrakk>(c,a)\<in>R'; Q a\<rbrakk> \<Longrightarrow> S a \<subseteq> S' a"
    shows "(f,g) \<in> [Q]\<^sub>f\<^sub>d R' \<rightarrow> S'"
    using assms
    unfolding fref_def
    by fastforce

  lemmas fref_cons' = fref_cons[OF _ _ order_refl order_refl]  

  lemma frefI[intro?]: 
    assumes "\<And>x y. \<lbrakk>P y; (x,y)\<in>R\<rbrakk> \<Longrightarrow> (f x, g y)\<in>S y"
    shows "(f,g)\<in>fref P R S"
    using assms
    unfolding fref_def
    by auto

  lemma fref_ncI: "(f,g)\<in>R\<rightarrow>S \<Longrightarrow> (f,g)\<in>R\<rightarrow>\<^sub>fS"  
    apply (rule frefI)
    apply parametricity
    done

  lemma frefD: 
    assumes "(f,g)\<in>fref P R S"
    shows "\<lbrakk>P y; (x,y)\<in>R\<rbrakk> \<Longrightarrow> (f x, g y)\<in>S y"
    using assms
    unfolding fref_def
    by auto

  lemma fref_ncD: "(f,g)\<in>R\<rightarrow>\<^sub>fS \<Longrightarrow> (f,g)\<in>R\<rightarrow>S"  
    apply (rule fun_relI)
    apply (drule frefD)
    apply simp
    apply assumption+
    done


      
  definition "rr_comp S R1 R2 x \<equiv> if non_dep R1 then R1 undefined O R2 x else (\<Union>{R1 y | y. (y,x)\<in>S}) O R2 x"  
    
  lemma rr_comp_K[simp]: "rr_comp S (\<lambda>_. R1) R2 = (\<lambda>x. R1 O R2 x)"
    by (auto simp: rr_comp_def fun_eq_iff)

  lemma rr_comp_nondep: "rr_comp T (\<lambda>_. A) R = (\<lambda>x. A O (R x))"
    unfolding rr_comp_def
    by (auto simp: fun_eq_iff)
    
      
  lemma fref_compI: 
    "fref P R1 R2 O fref Q S1 S2 \<subseteq>
      fref (\<lambda>x. Q x \<and> (\<forall>y. (y,x)\<in>S1 \<longrightarrow> P y)) (R1 O S1) (rr_comp S1 R2 S2)"
    unfolding fref_def rr_comp_def 
    apply (cases "non_dep R2"; simp)
    subgoal by (fastforce simp: non_dep_simp[of R2])
    subgoal by fastforce
    done
    
  lemma fref_compI':
    "\<lbrakk> (f,g)\<in>fref P R1 R2; (g,h)\<in>fref Q S1 S2 \<rbrakk> 
      \<Longrightarrow> (f,h) \<in> fref (\<lambda>x. Q x \<and> (\<forall>y. (y,x)\<in>S1 \<longrightarrow> P y)) (R1 O S1) (rr_comp S1 R2 S2)"
    using fref_compI[of P R1 R2 Q S1 S2]   
    by auto

  lemma fref_unit_conv:
    "(\<lambda>_. c, \<lambda>_. a) \<in> fref P unit_rel S \<longleftrightarrow> (P () \<longrightarrow> (c,a)\<in>S ())"   
    by (auto simp: fref_def)

  lemma fref_uncurry_conv:
    "(uncurry c, uncurry a) \<in> fref P (R1\<times>\<^sub>rR2) S 
    \<longleftrightarrow> (\<forall>x1 y1 x2 y2. P (y1,y2) \<longrightarrow> (x1,y1)\<in>R1 \<longrightarrow> (x2,y2)\<in>R2 \<longrightarrow> (c x1 x2, a y1 y2) \<in> S (y1,y2))"
    by (auto simp: fref_def)

  lemma fref_mono: "\<lbrakk> \<And>x. P' x \<Longrightarrow> P x; R' \<subseteq> R; \<And>x y. P' x \<Longrightarrow> S x \<subseteq> S' x \<rbrakk> 
    \<Longrightarrow> fref P R S \<subseteq> fref P' R' S'"  
    unfolding fref_def
    by auto blast

  lemma fref_composeI:
    assumes FR1: "(f,g)\<in>fref P R1 R2"
    assumes FR2: "(g,h)\<in>fref Q S1 S2"
    assumes C1: "\<And>x. P' x \<Longrightarrow> Q x"
    assumes C2: "\<And>x y. \<lbrakk>P' x; (y,x)\<in>S1\<rbrakk> \<Longrightarrow> P y"
    assumes R1: "R' \<subseteq> R1 O S1"
    assumes R2: "\<And>x. \<lbrakk> P' x \<rbrakk> \<Longrightarrow> rr_comp S1 R2 S2 x \<subseteq> S' x"
    assumes FH: "f'=f" "h'=h"
    shows "(f',h') \<in> fref P' R' S'"
    unfolding FH
    apply (rule set_mp[OF fref_mono fref_compI'[OF FR1 FR2]])
    using C1 C2 apply blast
    using R1 apply blast
    using R2 apply blast
    done

  lemma fref_triv: "A\<subseteq>Id \<Longrightarrow> (f,f)\<in>[P]\<^sub>f A \<rightarrow> Id"
    by (auto simp: fref_def)


  subsection \<open>Heap-Function Refinement\<close>
  text \<open>
    The following relates a heap-function with a pure function.
    It contains a precondition, a refinement assertion for the arguments
    before and after execution, and a refinement relation for the result.
    \<close>
  (* TODO: We only use this with keep/destroy information, so we could model
    the parameter relations as such (('a\<Rightarrow>'ai \<Rightarrow> assn) \<times> bool) *)
  definition hfref 
    :: "
      ('a \<Rightarrow> bool) 
   \<Rightarrow> (('a \<Rightarrow> 'ai \<Rightarrow> assn) \<times> ('a \<Rightarrow> 'ai \<Rightarrow> assn)) 
   \<Rightarrow> ('a \<Rightarrow> 'ai \<Rightarrow> 'b \<Rightarrow> 'bi \<Rightarrow> assn) 
   \<Rightarrow> (('ai \<Rightarrow> 'bi llM) \<times> ('a\<Rightarrow>('b,_) nrest)) set"
   ("[_]\<^sub>a\<^sub>d _ \<rightarrow> _" [0,60,60] 60)
   where
    "[P]\<^sub>a\<^sub>d RS \<rightarrow> T \<equiv> { (f,g) . \<forall>c a.  P a \<longrightarrow> hn_refine (fst RS a c) (f c) (snd RS a c) (T a c) (g a)}"

  abbreviation hfrefnd ("[_]\<^sub>a _ \<rightarrow> _" [0,60,60] 60) where "[P]\<^sub>a RS \<rightarrow> T \<equiv> ([P]\<^sub>a\<^sub>d RS \<rightarrow> (\<lambda>_ _. T))"
  abbreviation hfreft ("_ \<rightarrow>\<^sub>a\<^sub>d _" [60,60] 60) where "RS \<rightarrow>\<^sub>a\<^sub>d T \<equiv> ([\<lambda>_. True]\<^sub>a\<^sub>d RS \<rightarrow> T)"
  abbreviation hfreftnd ("_ \<rightarrow>\<^sub>a _" [60,60] 60) where "RS \<rightarrow>\<^sub>a T \<equiv> [\<lambda>_. True]\<^sub>a RS \<rightarrow> T"

  lemma hfrefI[intro?]: 
    assumes "\<And>c a. P a \<Longrightarrow> hn_refine (fst RS a c) (f c) (snd RS a c) (T a c) (g a)"
    shows "(f,g)\<in>hfref P RS T"
    using assms unfolding hfref_def by blast

  lemma hfrefD: 
    assumes "(f,g)\<in>hfref P RS T"
    shows "\<And>c a. P a \<Longrightarrow> hn_refine (fst RS a c) (f c) (snd RS a c) (T a c) (g a)"
    using assms unfolding hfref_def by blast

  lemma hfref_to_ASSERT_conv: 
    "NO_MATCH (\<lambda>_. True) P \<Longrightarrow> (a,b)\<in>[P]\<^sub>a\<^sub>d R \<rightarrow> S \<longleftrightarrow> (a,\<lambda>x. do {ASSERT (P x); b x}) \<in> R \<rightarrow>\<^sub>a\<^sub>d S"  
    unfolding hfref_def
    apply (clarsimp; safe; clarsimp?)
    apply (rule hn_refine_nofailI)
    apply (simp add: refine_pw_simps)
    subgoal for xc xa
      apply (drule spec[of _ xc])
      apply (drule spec[of _ xa])
      by simp
    done

  text \<open>
    A pair of argument refinement assertions can be created by the 
    input assertion and the information whether the parameter is kept or destroyed
    by the function.
    \<close>  
  primrec hf_pres 
    :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn)\<times>('a \<Rightarrow> 'b \<Rightarrow> assn)"
    where 
      "hf_pres R True = (R,R)" | "hf_pres R False = (R,invalid_assn R)"

  abbreviation hfkeep 
    :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn)\<times>('a \<Rightarrow> 'b \<Rightarrow> assn)" 
    ("(_\<^sup>k)" [1000] 999)
    where "R\<^sup>k \<equiv> hf_pres R True"
  abbreviation hfdrop 
    :: "('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn)\<times>('a \<Rightarrow> 'b \<Rightarrow> assn)" 
    ("(_\<^sup>d)" [1000] 999)
    where "R\<^sup>d \<equiv> hf_pres R False"

  abbreviation "hn_kede R kd \<equiv> hn_ctxt (snd (hf_pres R kd))"
  abbreviation "hn_keep R \<equiv> hn_kede R True"
  abbreviation "hn_dest R \<equiv> hn_kede R False"

  lemma keep_drop_sels[simp]:  
    "fst (R\<^sup>k) = R"
    "snd (R\<^sup>k) = R"
    "fst (R\<^sup>d) = R"
    "snd (R\<^sup>d) = invalid_assn R"
    by auto

  lemma hf_pres_fst[simp]: "fst (hf_pres R k) = R" by (cases k) auto

  text \<open>
    The following operator combines multiple argument assertion-pairs to
    argument assertion-pairs for the product. It is required to state
    argument assertion-pairs for uncurried functions.
    \<close>  
  definition hfprod :: "
    (('a \<Rightarrow> 'b \<Rightarrow> assn)\<times>('a \<Rightarrow> 'b \<Rightarrow> assn)) 
    \<Rightarrow> (('c \<Rightarrow> 'd \<Rightarrow> assn)\<times>('c \<Rightarrow> 'd \<Rightarrow> assn))
    \<Rightarrow> ((('a\<times>'c) \<Rightarrow> ('b \<times> 'd) \<Rightarrow> assn) \<times> (('a\<times>'c) \<Rightarrow> ('b \<times> 'd) \<Rightarrow> assn))"
    (infixl "*\<^sub>a" 65)
    where "RR *\<^sub>a SS \<equiv> (prod_assn (fst RR) (fst SS), prod_assn (snd RR) (snd SS))"

  lemma hfprod_fst_snd[simp]:
    "fst (A *\<^sub>a B) = prod_assn (fst A) (fst B)" 
    "snd (A *\<^sub>a B) = prod_assn (snd A) (snd B)" 
    unfolding hfprod_def by auto



  subsubsection \<open>Conversion from fref to hfref\<close>  
  (* TODO: Variant of import-param! Automate this! *)
(*  lemma fref_to_pure_hfref':
    assumes "(f,g) \<in> [P]\<^sub>f R\<rightarrow>\<langle>S\<rangle>nrest_rel"
    assumes "\<And>x. x\<in>Domain R \<inter> R\<inverse>``Collect P \<Longrightarrow> f x = RETURN (f' x)"
    shows "(return o f', g) \<in> [P]\<^sub>a (pure R)\<^sup>k\<rightarrow>pure S"
  proof -
  
    {
      fix c a
      assume A: "P a" "nofailT (g a)" "(c, a) \<in> R"
      hence "\<exists>x. (f' c, x) \<in> S \<and> RETURN x \<le> g a" 
        using assms
        apply (auto simp: fref_def pw_acost_le_iff pw_acost_nrest_rel_iff refine_pw_simps)
        (* TODO: refactor! thank you SH *)
      proof -
        assume a1: "(c, a) \<in> R"
        assume a2: "\<And>x. x \<in> Domain R \<and> x \<in> R\<inverse> `` Collect P \<Longrightarrow> f x = RETURNT (f' x)"
        assume a3: "\<forall>x y. P y \<and> (x, y) \<in> R \<longrightarrow> nofailT (g y) \<longrightarrow> nofailT (f x) \<and> (\<forall>xa. (\<exists>b. Ex (inresT (project_acost b (f x)) xa)) \<longrightarrow> (\<exists>x'. (xa, x') \<in> S)) \<and> (\<forall>xa c t. (nofailT (f x) \<longrightarrow> (\<forall>xa. Ex (inresT (project_acost c (f x)) xa) \<longrightarrow> (\<exists>x'. (xa, x') \<in> S)) \<longrightarrow> (\<exists>ca. (ca, xa) \<in> S \<and> inresT (project_acost c (f x)) ca t)) \<longrightarrow> inresT (project_acost c (g y)) xa t)"
        assume a4: "P a"
        assume a5: "nofailT (g a)"
        { fix ccs :: "'d \<Rightarrow> char list"
          have "\<forall>cs n. (inresT (project_acost cs (f c)) (f' c) n \<or> a \<notin> Collect P) \<or> \<not> n \<le> 0"
            using a2 a1 by (metis (no_types) Domain.DomainI ImageI converse_iff inresT_RETURNT project_acost_RETURNT)
          then have "\<exists>d. (f' c, d) \<in> S \<and> inresT (project_acost (ccs d) (g a)) d 0"
            using a5 a4 a3 a1 by (metis (no_types) mem_Collect_eq zero_le) }
        then show "\<exists>d. (f' c, d) \<in> S \<and> (\<forall>cs. inresT (project_acost cs (g a)) d 0)"
          by (metis (no_types))
      qed  


      hence "ENTAILS F ((\<up>((c, a) \<in> R) \<and>* (\<lambda>s. \<exists>x. (\<up>((f' c, x) \<in> S) \<and>* \<up>(RETURN x \<le> g a)) s)) \<and>* F)" 
        for F :: assn 
        using A by vcg
    } note AUX=this 
    
    show ?thesis
      apply (rule hfrefI) apply (rule hn_refineI)
      unfolding pure_def 
      apply vcg
      apply (rule AUX)
      .
  qed      
*)

  subsubsection \<open>Conversion from hfref to hnr\<close>  
  text \<open>This section contains the lemmas. The ML code is further down. \<close>
  lemma hf2hnr:
    assumes "(f,g) \<in> [P]\<^sub>a\<^sub>d R \<rightarrow> S"
    shows "\<forall>x xi. P x \<longrightarrow> hn_refine (hn_ctxt (fst R) x xi ** \<box>) (f$xi) (hn_ctxt (snd R) x xi ** \<box>) (S x xi) (g$x)"
    using assms
    unfolding hfref_def 
    by (auto simp: hn_ctxt_def)

  (* Products that stem from currying are tagged by a special refinement relation *)  
  definition [simp]: "to_hnr_prod \<equiv> prod_assn"

  lemma to_hnr_prod_fst_snd:
    "fst (A *\<^sub>a B) = to_hnr_prod (fst A) (fst B)" 
    "snd (A *\<^sub>a B) = to_hnr_prod (snd A) (snd B)" 
    unfolding hfprod_def by auto

  (* Warning: This lemma is carefully set up to be applicable as an unfold rule,
    for more than one level of uncurrying*)
  lemma hnr_uncurry_unfold: "
    (\<forall>x xi. P x \<longrightarrow> 
      hn_refine 
        (hn_ctxt (to_hnr_prod A B) x xi ** \<Gamma>) 
        (fi xi) 
        (hn_ctxt (to_hnr_prod A' B') x xi ** \<Gamma>') 
        (R x xi) 
        (f x))
\<longleftrightarrow> (\<forall>b bi a ai. P (a,b) \<longrightarrow>
      hn_refine 
        (hn_ctxt A a ai ** hn_ctxt B b bi ** \<Gamma>) 
        (fi (ai,bi)) 
        (hn_ctxt A' a ai ** hn_ctxt B' b bi ** \<Gamma>')
        (R (a,b) (ai,bi))
        (f (a,b))
    )"
    by (auto simp: hn_ctxt_def prod_assn_def sep_conj_ac)
    
  (*  
  lemma hnr_intro_dummy:
    "\<forall>x xi. P x \<longrightarrow> hn_refine (\<Gamma> x xi) (c xi) (\<Gamma>' x xi) (R x) (a x) \<Longrightarrow> \<forall>x xi. P x \<longrightarrow> hn_refine (\<Gamma> x xi ** \<box>) (c xi) (\<Gamma>' x xi ** \<box>) (R x) (a x)" 
    by simp
  *)

  lemma hn_ctxt_ctxt_fix_conv: "hn_ctxt (hn_ctxt R) = hn_ctxt R"
    by (simp add: hn_ctxt_def[abs_def])

  lemma uncurry_APP: "uncurry f$(a,b) = f$a$b" by auto

  (* TODO: Replace by more general rule. *)  
  lemma norm_RETURN_o: 
    "\<And>f. (RETURN o f)$x = (RETURN$(f$x))"
    "\<And>f. (RETURN oo f)$x$y = (RETURN$(f$x$y))"
    "\<And>f. (RETURN ooo f)$x$y$z = (RETURN$(f$x$y$z))"
    "\<And>f. (\<lambda>x. RETURN ooo f x)$x$y$z$a = (RETURN$(f$x$y$z$a))"
    "\<And>f. (\<lambda>x y. RETURN ooo f x y)$x$y$z$a$b = (RETURN$(f$x$y$z$a$b))"
    by auto

  lemma norm_return_o: 
    "\<And>f. (return o f)$x = (return$(f$x))"
    "\<And>f. (return oo f)$x$y = (return$(f$x$y))"
    "\<And>f. (return ooo f)$x$y$z = (return$(f$x$y$z))"
    "\<And>f. (\<lambda>x. return ooo f x)$x$y$z$a = (return$(f$x$y$z$a))"
    "\<And>f. (\<lambda>x y. return ooo f x y)$x$y$z$a$b = (return$(f$x$y$z$a$b))"
    by auto

  
  lemma hn_val_unit_conv_emp[simp]: "hn_val unit_rel x y = \<box>"
    by (auto simp: hn_ctxt_def pure_def sep_algebra_simps)

  subsubsection \<open>Conversion from hnr to hfref\<close>  
  text \<open>This section contains the lemmas. The ML code is further down. \<close>

  abbreviation "id_assn \<equiv> pure Id"
  abbreviation "unit_assn \<equiv> id_assn :: unit \<Rightarrow> _"

  lemma pure_unit_rel_eq_empty: "unit_assn x y = \<box>"  
    by (auto simp: pure_def sep_algebra_simps)

  lemma uc_hfprod_sel:
    "fst (A *\<^sub>a B) a c = (case (a,c) of ((a1,a2),(c1,c2)) \<Rightarrow> fst A a1 c1 ** fst B a2 c2)" 
    "snd (A *\<^sub>a B) a c = (case (a,c) of ((a1,a2),(c1,c2)) \<Rightarrow> snd A a1 c1 ** snd B a2 c2)" 
    by auto

  subsubsection \<open>Conversion from relation to fref\<close>  
  text \<open>This section contains the lemmas. The ML code is further down. \<close>

  definition "CURRY R \<equiv> { (f,g). (uncurry f, uncurry g) \<in> R }"

  lemma fref_param1: "R\<rightarrow>S = R\<rightarrow>\<^sub>fS"  
    by (auto simp: fref_def fun_relD)

  lemma fref_nest: "[P1]\<^sub>f R1 \<rightarrow> ([P2]\<^sub>f R2 \<rightarrow> S) 
    \<equiv> CURRY ([(\<lambda>(a,b). P1 a \<and> P2 b)]\<^sub>f (R1\<times>\<^sub>rR2) \<rightarrow> S)"
    apply (rule eq_reflection)
    by (auto simp: fref_def CURRY_def)

  lemma in_CURRY_conv: "(f,g) \<in> CURRY R \<longleftrightarrow> (uncurry f, uncurry g) \<in> R"  
    unfolding CURRY_def by auto

  lemma uncurry0_APP[simp]: "uncurry0 c $ x = c" by auto

  lemma fref_param0I: "(c,a)\<in>R \<Longrightarrow> (uncurry0 c, uncurry0 a) \<in> unit_rel \<rightarrow>\<^sub>f R"
    by (auto simp: fref_def)

  subsubsection \<open>Composition\<close>
  definition hr_comp :: "('b \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> ('b \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn"
    \<comment> \<open>Compose refinement assertion with refinement relation\<close>
    where "hr_comp R1 R2 a c \<equiv> EXS b. R1 b c ** \<up>((b,a)\<in>R2)"

  definition hrp_comp 
    :: "('d \<Rightarrow> 'b \<Rightarrow> assn) \<times> ('d \<Rightarrow> 'c \<Rightarrow> assn)
        \<Rightarrow> ('d \<times> 'a) set \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> assn) \<times> ('a \<Rightarrow> 'c \<Rightarrow> assn)"
    \<comment> \<open>Compose argument assertion-pair with refinement relation\<close>    
    where "hrp_comp RR' S \<equiv> (hr_comp (fst RR') S, hr_comp (snd RR') S) "

  lemma hr_compI: "(b,a)\<in>R2 \<Longrightarrow> R1 b c \<turnstile> hr_comp R1 R2 a c"  
    unfolding hr_comp_def
    by (auto simp: sep_algebra_simps entails_def pred_lift_extract_simps)

  lemma hr_comp_Id1[simp]: "hr_comp (pure Id) R = pure R"  
    unfolding hr_comp_def[abs_def] pure_def
    apply (intro ext)
    by (auto simp: pred_lift_extract_simps)

  lemma hr_comp_Id2[simp]: "hr_comp R Id = R"  
    unfolding hr_comp_def[abs_def]
    apply (intro ext)
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)
    
  lemma hr_comp_emp[simp]: "hr_comp (\<lambda>a c. \<box>) R a c = \<up>(\<exists>b. (b,a)\<in>R)"
    unfolding hr_comp_def[abs_def]
    apply (intro ext)
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)

  lemma hr_comp_prod_conv[simp]:
    "hr_comp (prod_assn Ra Rb) (Ra' \<times>\<^sub>r Rb') 
    = prod_assn (hr_comp Ra Ra') (hr_comp Rb Rb')"  
    unfolding hr_comp_def[abs_def] prod_assn_def[abs_def]
    apply (intro ext)
    apply (auto 0 3 simp: sep_algebra_simps pred_lift_extract_simps)
    done

  lemma hr_comp_pure: "hr_comp (pure R) S = pure (R O S)"  
    apply (intro ext)
    unfolding hr_comp_def[abs_def] pure_def
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)

  lemma hr_comp_is_pure[safe_constraint_rules]: "is_pure A \<Longrightarrow> is_pure (hr_comp A B)"
    by (auto simp: hr_comp_pure is_pure_conv)

  lemma hr_comp_the_pure: "is_pure A \<Longrightarrow> the_pure (hr_comp A B) = the_pure A O B"
    unfolding is_pure_conv
    by (clarsimp simp: hr_comp_pure)

  lemma rdomp_hrcomp_conv[simp]: "rdomp (hr_comp A R) x \<longleftrightarrow> (\<exists>y. rdomp A y \<and> (y,x)\<in>R)"
    by (auto simp: rdomp_def hr_comp_def sep_algebra_simps pred_lift_extract_simps)
(*
  lemma hn_rel_compI: 
    "\<lbrakk>nofailT a; (b,a)\<in>\<langle>R2\<rangle>nrest_rel\<rbrakk> \<Longrightarrow> hn_rel R1 b c \<turnstile> hn_rel (hr_comp R1 R2) a c"
    unfolding hr_comp_def hn_rel_def nres_rel_def entails_def
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
    apply (drule (1) order_trans)
    apply (auto simp add: ret_le_down_conv)
    done
*)
  (*  
  lemma hr_comp_precise[constraint_rules]:
    assumes [safe_constraint_rules]: "precise R"
    assumes SV: "single_valued S"
    shows "precise (hr_comp R S)"
    apply (rule preciseI)
    unfolding hr_comp_def
    apply clarsimp
    by (metis SV assms(1) preciseD single_valuedD)
  *)

  lemma hr_comp_assoc: "hr_comp (hr_comp R S) T = hr_comp R (S O T)"
    apply (intro ext)
    unfolding hr_comp_def
    by (auto simp: sep_algebra_simps pred_lift_extract_simps)

    
  lemma hrp_comp_Id1[simp]:
  fixes pp
  shows "hrp_comp (hf_pres (pure Id) pp) R = hf_pres (pure R) pp"
    unfolding hrp_comp_def apply (cases pp) apply auto
    by (auto simp: hr_comp_def[abs_def] invalid_assn_def[abs_def] fun_eq_iff sep_algebra_simps pred_lift_extract_simps)
  
  lemma hrp_comp_Id2[simp]: "hrp_comp A Id = A"
    unfolding hrp_comp_def by auto


lemma pwD2:
  assumes "S\<le>S'" "inresT S x t"
  shows "inresT S' x t"
  using assms using Time_Refinement.ff by metis

  lemma hnr_comp_aux:
    assumes "RETURNT x \<le> m" "nofailT m'" "(m,m')\<in>\<langle>R\<rangle>nrest_rel"
    obtains x' where "(x,x')\<in>R" "RETURN x' \<le> m'"
    using assms(3)[THEN nrest_relD]
(*
    apply (meson assms(1) assms(2) assms(3) inresT_def nrest_relD pwD2 inresT_abs_fun)
    *) oops



lemma SomeSup_D: "Some y \<le> Sup {M' a |a. (r, a) \<in> RR} \<Longrightarrow> (\<exists>a. (r, a) \<in> RR)"
  unfolding Sup_option_def by (auto split: if_splits)

lemma aux:
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "\<And>r. r\<in>dom M \<Longrightarrow> (\<exists>a. (r,a)\<in>RR) \<Longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  shows "\<forall>r\<in>dom M. \<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms
  (* with single_valued RR *)
  apply (auto simp: conc_fun_RES)
  unfolding le_fun_def 
  subgoal premises p for r y using p(2)[rule_format, of r] p(1)[of r, OF _ SomeSup_D] p(3)
    by force
  done

lemma aux':
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "\<And>r. r\<in>dom M \<Longrightarrow> (\<exists>a. (r,a)\<in>RR) \<Longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms aux[of M RR M']
  by fastforce


lemma single_valued_SupinSup:
  fixes M' :: "_ \<Rightarrow> (_::complete_lattice) option"
  shows "single_valued RR \<Longrightarrow> (\<exists>a. (r,a)\<in>RR) \<Longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"
proof -
  assume SV: "single_valued RR" and "(\<exists>a. (r,a)\<in>RR)"
  then obtain a where "(r,a)\<in>RR" by auto
  then have "{M' a| a. (r,a)\<in>RR} = {M' a}"
    apply auto using SV[THEN single_valuedD] by auto
  then show ?thesis by auto
qed
  

lemma conc_fun_inRR: "SPECT x2 \<le> \<Down> RR (SPECT M) \<Longrightarrow> r \<in> dom x2 \<Longrightarrow> (\<exists>a. (r,a)\<in>RR)"
  unfolding conc_fun_def apply auto unfolding le_fun_def 
  subgoal premises p for y apply(rule SomeSup_D)
    using p(1)[rule_format, of r] p(2) by simp
  done

paragraph \<open>attains_sup\<close>
  
definition "attains_sup m m' RR \<equiv> 
  \<forall>r M' M. m=SPECT M \<longrightarrow> m'=SPECT M' \<longrightarrow> r\<in>dom M \<longrightarrow> (\<exists>a. (r,a)\<in>RR) \<longrightarrow> Sup {M' a| a. (r,a)\<in>RR} \<in> {M' a| a. (r,a)\<in>RR}"  

(* Proving attains_sup *)  

(* Single Valued *)
lemma attains_sup_sv: "single_valued RR \<Longrightarrow> attains_sup m m' RR"  
  unfolding attains_sup_def
  using single_valued_SupinSup by fastforce  
  

(* Time does not depend on Result (one-time) *)
 
definition "one_time m \<equiv> \<forall>M. m=SPECT M \<longrightarrow> (\<forall>x y s t. M x = Some s \<and> M y = Some t \<longrightarrow> s=t)"

lemma one_time_attains_sup:
  assumes one_time: "one_time m'"
  shows "attains_sup m m' RR"
  unfolding attains_sup_def 
  apply clarify
proof -
  fix r M' M y aa
  assume [simp]: "m' = SPECT M'" and "(r, aa) \<in> RR"
  show "\<exists>aa. Sup {M' a |a. (r, a) \<in> RR} = M' aa \<and> (r, aa) \<in> RR" (is "\<exists>_. Sup ?MM = _ \<and> _")
  proof (cases "\<exists>a c. (r,a)\<in>RR \<and> M' a = Some c")
    case True
    then obtain a c where 1: "(r,a)\<in>RR" "M' a = Some c" by blast
    with one_time have "Some c \<in> ?MM" "?MM \<subseteq> {None,Some c}"
      unfolding one_time_def
      by (auto) metis
    thus ?thesis using 1
      by (smt Sup_insert Sup_le_iff Sup_subset_mono cSup_eq_maximum ccpo_Sup_singleton empty_Sup insert_commute) 
  next
    case False   
    hence "?MM = {None}" using \<open>(r,aa)\<in>RR\<close> by force
    thus ?thesis using False \<open>(r,aa)\<in>RR\<close> by auto
  qed      
qed  

named_theorems OT_intros


lemma OT_return[OT_intros]: "one_time (RETURNT x)"
  unfolding one_time_def by auto
  
lemma OT_consume[OT_intros]: "one_time m \<Longrightarrow> one_time (consume m c)"  
  unfolding one_time_def consume_def
  by (auto split: nrest.splits; blast)
  
lemma OT_assert[OT_intros]: "one_time (ASSERT \<Phi>)"  
  unfolding one_time_def 
  by (cases \<Phi>) auto
  
lemma OT_fail: "one_time FAILT"
  unfolding one_time_def by auto

lemma OT_spec[OT_intros]: "one_time (SPEC P (\<lambda>_. c))"
  unfolding one_time_def SPEC_def by auto
  
    
lemma attains_sup_mop_return:
  "attains_sup m (do {ASSERT \<Phi>; consume (RETURNT x) (c::ecost)}) R"
  apply (rule one_time_attains_sup)
  apply (cases \<Phi>; simp add: OT_consume OT_return OT_fail)
  done

lemma attains_sup_mop_spec:
  "attains_sup m (do {ASSERT \<Phi>; SPEC P (\<lambda>_. c::ecost)}) R"
  apply (rule one_time_attains_sup)
  apply (cases \<Phi>; simp add: OT_consume OT_return OT_fail OT_spec)
  done


  
  
  
experiment
begin

lemma aux_abs_help:
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "\<Up> RR (SPECT M) \<le>  (SPECT M')"
  shows "\<forall>r\<in>dom M. (\<exists>r'. (r,r')\<in>RR) \<and> (\<forall>r'. (r,r')\<in>RR \<longrightarrow> M r \<le> M' r')"
  using assms
  (* with single_valued RR *)
  apply (auto simp: abs_fun_RES split: if_splits simp: le_fun_def) 
  subgoal premises prems for r y r'
    using prems(2)[rule_format, of r'] prems(3,4)  
    by (metis (mono_tags, lifting) Sup_le_iff mem_Collect_eq)  
  done

lemma aux_abs:
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "\<Up> RR (SPECT M) \<le>  (SPECT M')"
  shows "\<forall>r\<in>dom M. \<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using aux_abs_help[OF assms] by blast

lemma aux_abs':
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "\<Up> RR (SPECT M) \<le> (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms aux_abs[of RR M M']
  by fastforce




lemma aux:
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "single_valued RR"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  shows "\<forall>r\<in>dom M. \<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms
  (* with single_valued RR *)
  apply (auto simp: conc_fun_RES)
  by (smt Sup_Some cSup_eq_maximum dual_order.refl le_fun_def le_some_optE mem_Collect_eq sv_the)
  
lemma aux':
  fixes M :: "_ \<rightharpoonup> ecost"
  assumes "single_valued RR"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
  using assms aux[of RR M M']
  by fastforce
  
  lemma hn_refine_result':
  assumes R: "hn_refine P c Q R m"
  assumes LE: "\<Up>RR m\<le>m'" 
  shows "hn_refine P c Q (hr_comp R RR) m'"
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated], simp)
  apply (elim exE conjE)
  apply (drule (1) aux_abs')
  apply (elim exE conjE)
  
  apply (intro exI conjI)
  apply (rule order_trans, assumption+)  

  apply (erule wp_post_cons)
  unfolding hr_comp_def
  apply (rule ENTAILSD)
  apply fri
  done


lemma hn_refine_result:
  assumes R: "hn_refine P c Q R m"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes SV: "single_valued RR"
  shows "hn_refine P c Q (hr_comp R RR) m'"
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated], simp)
  apply (elim exE conjE)
  apply (drule (1) aux'[OF SV])
  apply (elim exE conjE)
  
  apply (intro exI conjI)
  apply (rule order_trans, assumption+)  

  apply (erule wp_post_cons)
  unfolding hr_comp_def
  apply (rule ENTAILSD)
  apply fri
  done

end
   
  
  
lemma hn_refine_result:
  assumes R: "hn_refine P c Q R m"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes WB: "attains_sup m m' RR"
  shows "hn_refine P c Q (hr_comp R RR) m'"
  supply WB' = WB[unfolded attains_sup_def, rule_format]
  unfolding hn_refine_def
  apply clarify
  using LE apply (cases m; simp)
  apply (frule (1) R[unfolded hn_refine_def, rule_format, rotated], simp)
  apply (elim exE conjE)
  subgoal premises p for F s cr M x2 ra Ca
    using aux'[OF WB'[OF p(4,1)], simplified, OF _ p(3,5), simplified] p(5,6)
    apply -
    apply (elim exE conjE)

    apply (intro exI conjI)
     apply (rule order_trans, assumption+)  

    apply (erule wp_post_cons)
    unfolding hr_comp_def
    apply (rule ENTAILSD)
    apply fri
    done
  done


lemma hn_refine_result_SV:
  assumes R: "hn_refine P c Q R m"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes SV: "single_valued RR"
  shows "hn_refine P c Q (hr_comp R RR) m'"
  apply(rule hn_refine_result)
    apply fact
   apply fact
  apply(rule attains_sup_sv)
   apply (rule SV)
  done


    
lemma hn_refine_cons_res_complete:
  assumes R: "hn_refine P' c Q R m"
  assumes I: "P\<turnstile>P'"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes SV: "single_valued RR"
  shows "hn_refine P c Q' (hr_comp R RR) m'"
  apply (rule hn_refine_result)
  apply (rule hn_refine_cons)
  by (fact|rule attains_sup_sv|simp)+

lemma hn_refine_cons_res_complete_loose:
  assumes R: "hn_refine P' c Q R m"
  assumes I: "P\<turnstile>P'"
  assumes I': "Q\<turnstile>Q'"
  assumes R': "\<And>x y. R x y \<turnstile> R' x y"
  assumes LE: "m\<le>\<Down>RR m'"
  assumes AS: "attains_sup m m' RR"
  shows "hn_refine P c Q' (hr_comp R RR) m'"
  apply (rule hn_refine_result)
  apply (rule hn_refine_cons)
  by (fact|simp)+

    
    
  definition "hrr_comp R R1 R2 x y a c \<equiv> 
    if non_dep2 R1 then
      hr_comp (R1 undefined undefined) (R2 x) a c
    else
      EXS b. \<up>((b,x)\<in>R) ** hr_comp (R1 b y) (R2 x) a c"


lemma pw_ref_iff:
  shows "S \<le> \<Down>R S' 
  \<longleftrightarrow> (nofailT S' 
    \<longrightarrow> nofailT S \<and> (\<forall>x t. inresT S x t \<longrightarrow> (\<exists>s'. (x, s') \<in> R \<and> inresT S' s' t)))"
  by (simp add: pw_le_iff refine_pw_simps)

lemma pw_acost_ref_iff:
  shows "S \<le> \<Down>R S' 
  \<longleftrightarrow> (nofailT S' 
    \<longrightarrow> nofailT S \<and> (\<forall>x t b. inresT (project_acost b S) x t \<longrightarrow> (\<exists>s'. (x, s') \<in> R \<and> inresT (project_acost b S') s' t)))"
  apply (simp add: pw_acost_le_iff refine_pw_simps)
  by blast

  
  lemma aux_attains_sup:
  fixes M :: "_ \<rightharpoonup> ecost" 
  assumes "attains_sup (SPECT M) (SPECT M') RR"
  assumes "SPECT M \<le> \<Down> RR (SPECT M')"
  assumes "Some cr \<le> M r"
  shows "\<exists>r'. (r,r')\<in>RR \<and> M r \<le> M' r'"
    using   assms(1)[unfolded attains_sup_def, rule_format, of M M'] assms(2) assms(3)
  using  aux[of M RR M']
  by fastforce



  lemma hnr_comp:
    assumes R: "\<And>b1 c1. P b1 \<Longrightarrow> hn_refine (R1 b1 c1 ** \<Gamma>) (c c1) (R1p b1 c1 ** \<Gamma>') (R b1 c1) (b b1)"
    assumes S: "\<And>a1 b1. \<lbrakk>Q a1; (b1,a1)\<in>R1'\<rbrakk> \<Longrightarrow> (b b1,a a1)\<in>\<langle>R' a1\<rangle>nrest_rel"
    assumes PQ: "\<And>a1 b1. \<lbrakk>Q a1; (b1,a1)\<in>R1'\<rbrakk> \<Longrightarrow> P b1"
    assumes Q: "Q a1"
    assumes SC: "\<And>b1. attains_sup (b b1) (a a1) (R' a1)" (* TODO maybe more be more precise here*)
    shows "hn_refine 
      (hr_comp R1 R1' a1 c1 ** \<Gamma>) 
      (c c1)
      (hr_comp R1p R1' a1 c1 ** \<Gamma>') 
      (hrr_comp R1' R R' a1 c1) 
      (a a1)"
  proof -

    note f[vcg_rules] = R[THEN hn_refineD, of _ _ c1]
    
    have tbx[simp]: "nofailT (b x)" if  "nofailT (a a1)" "(x, a1) \<in> R1'" for x
      using that Q S nrest_rel_def pw_acost_ref_iff by fastforce

    have exM: "\<exists>Mb. b x = SPECT Mb" if  "a a1 = SPECT Ma" "(x, a1) \<in> R1'" for x Ma
      unfolding nofailT_def  using nofail'' tbx that(1) that(2) by fastforce  

    show ?thesis      
      unfolding hn_refine_def

      unfolding hr_comp_def   hrr_comp_def
      apply (cases "non_dep2 R"; simp)
      subgoal premises prems
        apply (auto simp: sep_algebra_simps)
        unfolding STATE_def apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
        subgoal premises p2 for F s cr M b1
          using exM[OF p2(1) p2(2)]   apply auto
          subgoal premises p3 for Mb
            using f[simplified sep_conj_assoc, OF  PQ[OF Q], OF p2(2) p3(1) p2(3) ]
            apply safe
            subgoal premises p4 for rb C
              supply pf = S[OF Q p2(2), THEN nrest_relD, unfolded p2(1) p3(1), simplified]
              using aux_attains_sup[OF SC[of b1 ,unfolded p2(1) p3(1)] pf p4(1)] 
              apply auto
              subgoal premises p5 for ra
              apply(rule exI[where x=ra])
                apply(rule exI[where x=C])
                apply safe 
                subgoal using p5(2) p4(1) by simp
                subgoal apply(rule wp_monoI[OF p4(2)])
                  apply(rule exI[where x=b1])
                  using p2(2) apply simp
                  apply(rule exI[where x=rb])
                  using p5(1)  by (simp add:  non_dep2_simp[OF prems])
                done
              done
            done
          done
        done
      subgoal premises prems
        apply (auto simp: sep_algebra_simps)
        unfolding STATE_def apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
        subgoal premises p2 for F s cr M b1
          using exM[OF p2(1) p2(2)]   apply auto
          subgoal premises p3 for Mb
            using f[simplified sep_conj_assoc, OF  PQ[OF Q], OF p2(2) p3(1) p2(3) ]
            apply safe
            subgoal premises p4 for rb C
              supply pf = S[OF Q p2(2), THEN nrest_relD, unfolded p2(1) p3(1), simplified]
              using aux_attains_sup[OF SC[of b1 ,unfolded p2(1) p3(1)] pf p4(1)] 
              apply auto
              subgoal premises p5 for ra
              apply(rule exI[where x=ra])
                apply(rule exI[where x=C])
                apply safe 
                subgoal using p5(2) p4(1) by simp
                subgoal apply(rule wp_monoI[OF p4(2)])
                  apply(rule exI[where x=b1])
                  using p2(2) apply simp
                  apply(rule exI[where x=b1])
                  using p2(2) apply simp
                  apply(rule exI[where x=rb])
                  using p5(1)  by simp
                done
              done
            done
          done
        done        
      done
  qed
  

  lemma hnr_comp1_aux:
    assumes R: "\<And>b1 c1. P b1 \<Longrightarrow> hn_refine (hn_ctxt R1 b1 c1) (c c1) (hn_ctxt R1p b1 c1) (R b1 c1) (b$b1)"
    assumes S: "\<And>a1 b1. \<lbrakk>Q a1; (b1,a1)\<in>R1'\<rbrakk> \<Longrightarrow> (b$b1,a$a1)\<in>\<langle>R' a1\<rangle>nrest_rel"
    assumes PQ: "\<And>a1 b1. \<lbrakk>Q a1; (b1,a1)\<in>R1'\<rbrakk> \<Longrightarrow> P b1"
    assumes Q: "Q a1"
    assumes SC: "\<And>b1. attains_sup (b b1) (a a1) (R' a1)"
    shows "hn_refine 
      (hr_comp R1 R1' a1 c1) 
      (c c1)
      (hr_comp R1p R1' a1 c1) 
      (hrr_comp R1' R R' a1 c1) 
      (a a1)"
    using assms hnr_comp[where \<Gamma>=\<box> and \<Gamma>'=\<box> and a=a and b=b and c=c and P=P and Q=Q]  
    unfolding hn_ctxt_def
    by auto

  lemma hfcomp:
    assumes A: "(f,g) \<in> [P]\<^sub>a\<^sub>d RR' \<rightarrow> S"
    assumes B: "(g,h) \<in> [Q]\<^sub>f\<^sub>d T \<rightarrow> (\<lambda>x. \<langle>U x\<rangle>nrest_rel)"
    assumes SC: "\<And>b1 a1. attains_sup (g b1) (h a1) (U a1)"
    shows "(f,h) \<in> [\<lambda>a. Q a \<and> (\<forall>a'. (a',a)\<in>T \<longrightarrow> P a')]\<^sub>a\<^sub>d 
      hrp_comp RR' T \<rightarrow> hrr_comp T S U"
    using assms  
    unfolding fref_def hfref_def hrp_comp_def
    apply clarsimp
    apply (rule hnr_comp1_aux[of 
        P "fst RR'" f "snd RR'" S g "\<lambda>a. Q a \<and> (\<forall>a'. (a',a)\<in>T \<longrightarrow> P a')" T h U])
    apply (auto simp: hn_ctxt_def)
    done

  lemma hrr_comp_nondep: "hrr_comp T (\<lambda>_ _. A) R = (\<lambda>x _. hr_comp A (R x))"
    unfolding hrr_comp_def
    by (auto simp: fun_eq_iff)
    
  (* TODO: Concept of lifting dependent relation over other relation! Allows us to handle hrr_comp R R1 (\<lambda>_. Id) *)
  lemma hrr_comp_Id_R_Id: "hrr_comp Id R1 (\<lambda>_. Id) = R1"
    by (auto simp: hrr_comp_def fun_eq_iff pred_lift_extract_simps non_dep2_simp[of R1])
  
  lemma hrr_comp_id_conv[simp]: "hrr_comp Id R1 R2 = (\<lambda>x y. hr_comp (R1 x y) (R2 x))"
    unfolding hrr_comp_def
    by (auto simp: fun_eq_iff pred_lift_extract_simps non_dep2_simp[of R1])
  
    
  lemma hfref_weaken_pre_nofail: 
    assumes "(f,g) \<in> [P]\<^sub>a\<^sub>d R \<rightarrow> S"  
    shows "(f,g) \<in> [\<lambda>x. nofailT (g x) \<longrightarrow> P x]\<^sub>a\<^sub>d R \<rightarrow> S"
    using assms
    unfolding hfref_def hn_refine_def
    by auto

  lemma hfref_cons:
    assumes "(f,g) \<in> [P]\<^sub>a\<^sub>d R \<rightarrow> S"
    assumes "\<And>x. P' x \<Longrightarrow> P x"
    assumes "\<And>x y. fst R' x y \<turnstile> fst R x y"
    assumes "\<And>x y. snd R x y \<turnstile> snd R' x y"
    assumes "\<And>x y a c. P' a \<Longrightarrow> S a c x y \<turnstile> S' a c x y"
    shows "(f,g) \<in> [P']\<^sub>a\<^sub>d R' \<rightarrow> S'"
    unfolding hfref_def
    apply clarsimp
    apply (rule hn_refine_cons[rotated])
    apply (rule assms(3)) 

    apply (rule entails_trans[OF assms(4) entails_refl])
    apply (erule assms(5))
    apply (frule assms(2))
    using assms(1)
    unfolding hfref_def
    apply auto
    done
    
  (*lemma xfer_hrr_comp:
    assumes "\<And>x y a c. \<lbrakk> (x,y)\<in>T \<rbrakk> \<Longrightarrow> R x a c \<turnstile> R' y a c"  
    shows "hrr_comp T R S x a c \<turnstile> (hr_comp (R' x) S) a c"
    using assms unfolding hrr_comp_def
    apply (cases "non_dep R"; simp)
    subgoal sorry
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps entails_def hr_comp_def non_dep_simp[of R])
  *)  

  subsubsection \<open>Composition Automation\<close>  
  text \<open>This section contains the lemmas. The ML code is further down. \<close>

  lemma prod_hrp_comp: 
    "hrp_comp (A *\<^sub>a B) (C \<times>\<^sub>r D) = hrp_comp A C *\<^sub>a hrp_comp B D"
    unfolding hrp_comp_def hfprod_def by simp
  
  lemma hrp_comp_keep: "hrp_comp (A\<^sup>k) B = (hr_comp A B)\<^sup>k"
    by (auto simp: hrp_comp_def)

  lemma hr_comp_invalid: "hr_comp (invalid_assn R1) R2 = invalid_assn (hr_comp R1 R2)"
    apply (intro ext)
    unfolding invalid_assn_def hr_comp_def
    apply (auto simp: sep_algebra_simps pred_lift_extract_simps)
    apply (auto simp: pure_part_def) (* TODO: too low-level! *)
    done

  lemma hrp_comp_dest: "hrp_comp (A\<^sup>d) B = (hr_comp A B)\<^sup>d"
    by (auto simp: hrp_comp_def hr_comp_invalid)



  definition "hrp_imp RR RR' \<equiv> 
    \<forall>a b. (fst RR' a b \<turnstile> fst RR a b) \<and> (snd RR a b \<turnstile> snd RR' a b)"

  lemma hfref_imp: "hrp_imp RR RR' \<Longrightarrow> [P]\<^sub>a RR \<rightarrow> S \<subseteq> [P]\<^sub>a RR' \<rightarrow> S"  
    apply clarsimp
    apply (erule hfref_cons)
    apply (simp_all add: hrp_imp_def)
    done
    
  lemma hrp_imp_refl: "hrp_imp RR RR"
    unfolding hrp_imp_def by auto

  lemma hrp_imp_reflI: "RR = RR' \<Longrightarrow> hrp_imp RR RR'"
    unfolding hrp_imp_def by auto


  lemma hrp_comp_cong: "hrp_imp A A' \<Longrightarrow> B=B' \<Longrightarrow> hrp_imp (hrp_comp A B) (hrp_comp A' B')"
    by (auto simp: hrp_imp_def hrp_comp_def hr_comp_def entails_def sep_algebra_simps pred_lift_extract_simps)
    
  lemma hrp_prod_cong: "hrp_imp A A' \<Longrightarrow> hrp_imp B B' \<Longrightarrow> hrp_imp (A*\<^sub>aB) (A'*\<^sub>aB')"
    by (auto simp: hrp_imp_def prod_assn_def sep_algebra_simps pred_lift_extract_simps
      intro: conj_entails_mono
    )

  lemma hrp_imp_trans: "hrp_imp A B \<Longrightarrow> hrp_imp B C \<Longrightarrow> hrp_imp A C"  
    unfolding hrp_imp_def
    by (fastforce intro: entails_trans)

  lemma fcomp_norm_dflt_init: "x\<in>[P]\<^sub>a R \<rightarrow> T \<Longrightarrow> hrp_imp R S \<Longrightarrow> x\<in>[P]\<^sub>a S \<rightarrow> T"
    apply (erule set_rev_mp)
    by (rule hfref_imp)

  definition "comp_PRE R P Q S \<equiv> \<lambda>x. S x \<longrightarrow> (P x \<and> (\<forall>y. (y,x)\<in>R \<longrightarrow> Q x y))"

  lemma comp_PRE_cong[cong]: 
    assumes "R\<equiv>R'"
    assumes "\<And>x. P x \<equiv> P' x"
    assumes "\<And>x. S x \<equiv> S' x"
    assumes "\<And>x y. \<lbrakk>P x; (y,x)\<in>R; y\<in>Domain R; S' x \<rbrakk> \<Longrightarrow> Q x y \<equiv> Q' x y"
    shows "comp_PRE R P Q S \<equiv> comp_PRE R' P' Q' S'"
    using assms
    by (fastforce simp: comp_PRE_def intro!: eq_reflection ext)

  lemma fref_compI_PRE:
    "\<lbrakk> (f,g)\<in>fref P R1 R2; (g,h)\<in>fref Q S1 S2 \<rbrakk> 
      \<Longrightarrow> (f,h) \<in> fref (comp_PRE S1 Q (\<lambda>_. P) (\<lambda>_. True)) (R1 O S1) (rr_comp S1 R2 S2)"
    using fref_compI[of P R1 R2 Q S1 S2]   
    unfolding comp_PRE_def
    by auto

  lemma PRE_D1: "(Q x \<and> P x) \<longrightarrow> comp_PRE S1 Q (\<lambda>x _. P x) S x"
    by (auto simp: comp_PRE_def)

  lemma PRE_D2: "(Q x \<and> (\<forall>y. (y,x)\<in>S1 \<longrightarrow> S x \<longrightarrow> P x y)) \<longrightarrow> comp_PRE S1 Q P S x"
    by (auto simp: comp_PRE_def)

  lemma fref_weaken_pre: 
    assumes "\<And>x. P x \<longrightarrow> P' x"  
    assumes "(f,h) \<in> fref P' R S"
    shows "(f,h) \<in> fref P R S"
    apply (rule set_rev_mp[OF assms(2) fref_mono])
    using assms(1) by auto
    
  lemma fref_PRE_D1:
    assumes "(f,h) \<in> fref (comp_PRE S1 Q (\<lambda>x _. P x) X) R S"  
    shows "(f,h) \<in> fref (\<lambda>x. Q x \<and> P x) R S"
    by (rule fref_weaken_pre[OF PRE_D1 assms])

  lemma fref_PRE_D2:
    assumes "(f,h) \<in> fref (comp_PRE S1 Q P X) R S"  
    shows "(f,h) \<in> fref (\<lambda>x. Q x \<and> (\<forall>y. (y,x)\<in>S1 \<longrightarrow> X x \<longrightarrow> P x y)) R S"
    by (rule fref_weaken_pre[OF PRE_D2 assms])

  lemmas fref_PRE_D = fref_PRE_D1 fref_PRE_D2

  lemma hfref_weaken_pre: 
    assumes "\<And>x. P x \<longrightarrow> P' x"  
    assumes "(f,h) \<in> hfref P' R S"
    shows "(f,h) \<in> hfref P R S"
    using assms
    by (auto simp: hfref_def)

  lemma hfref_weaken_pre': 
    assumes "\<And>x. \<lbrakk>P x; rdomp (fst R) x\<rbrakk> \<Longrightarrow> P' x"  
    assumes "(f,h) \<in> hfref P' R S"
    shows "(f,h) \<in> hfref P R S"
    apply (rule hfrefI)
    apply (rule hn_refine_preI)
    using assms
    by (auto simp: hfref_def rdomp_def)

  lemma hfref_weaken_pre_nofail': 
    assumes "(f,g) \<in> [P]\<^sub>a\<^sub>d R \<rightarrow> S"  
    assumes "\<And>x. \<lbrakk>nofailT (g x); Q x\<rbrakk> \<Longrightarrow> P x"
    shows "(f,g) \<in> [Q]\<^sub>a\<^sub>d R \<rightarrow> S"
    apply (rule hfref_weaken_pre[OF _ assms(1)[THEN hfref_weaken_pre_nofail]])
    using assms(2) 
    by blast

  lemma hfref_with_rdomI:
    assumes "(c,a)\<in>[\<lambda>x. P x \<and> rdomp (fst A) x]\<^sub>a\<^sub>d A \<rightarrow> R"
    shows "(c,a)\<in>[P]\<^sub>a\<^sub>d A \<rightarrow> R"
    by (metis (no_types, lifting) assms hfref_weaken_pre')
    
  lemma hfref_compI_PRE_aux:
    assumes A: "(f,g) \<in> [P]\<^sub>a\<^sub>d RR' \<rightarrow> S"
    assumes B: "(g,h) \<in> [Q]\<^sub>f\<^sub>d T \<rightarrow> (\<lambda>x. \<langle>U x\<rangle>nrest_rel)"
    assumes SC: "\<And>a1 b1. attains_sup (g b1) (h a1) (U a1)"
    shows "(f,h) \<in> [comp_PRE T Q (\<lambda>_. P) (\<lambda>_. True)]\<^sub>a\<^sub>d 
      hrp_comp RR' T \<rightarrow> hrr_comp T S U"
    apply (rule hfref_weaken_pre[OF _ hfcomp[OF A B]])
    using SC
    by (auto simp: comp_PRE_def)

  definition "SC_attains_sup f = f"

  lemma hfref_compI_PRE:
    assumes A: "(f,g) \<in> [P]\<^sub>a\<^sub>d RR' \<rightarrow> S"
    assumes B: "(g,h) \<in> [Q]\<^sub>f\<^sub>d T \<rightarrow> (\<lambda>x. \<langle>U x\<rangle>nrest_rel)"
    assumes SC: "SC_attains_sup (\<forall>a1 b1. attains_sup (g b1) (h a1) (U a1))"
    shows "(f,h) \<in> [comp_PRE T Q (\<lambda>x y. P y) (\<lambda>x. nofailT (h x))]\<^sub>a\<^sub>d 
      hrp_comp RR' T \<rightarrow> hrr_comp T S U"
    using hfref_compI_PRE_aux[OF A B, THEN hfref_weaken_pre_nofail]  
    apply (rule hfref_weaken_pre[rotated])
    using SC[unfolded SC_attains_sup_def]
    apply (auto simp: comp_PRE_def)
    done

  lemma hfref_PRE_D1:
    assumes "(f,h) \<in> hfref (comp_PRE S1 Q (\<lambda>x _. P x) X) R S"  
    shows "(f,h) \<in> hfref (\<lambda>x. Q x \<and> P x) R S"
    by (rule hfref_weaken_pre[OF PRE_D1 assms])

  lemma hfref_PRE_D2:
    assumes "(f,h) \<in> hfref (comp_PRE S1 Q P X) R S"  
    shows "(f,h) \<in> hfref (\<lambda>x. Q x \<and> (\<forall>y. (y,x)\<in>S1 \<longrightarrow> X x \<longrightarrow> P x y)) R S"
    by (rule hfref_weaken_pre[OF PRE_D2 assms])

  lemma hfref_PRE_D3:
    assumes "(f,h) \<in> hfref (comp_PRE S1 Q P X) R S"  
    shows "(f,h) \<in> hfref (comp_PRE S1 Q P X) R S"
    using assms .

  lemmas hfref_PRE_D = hfref_PRE_D1 hfref_PRE_D3

  subsection \<open>Automation\<close>  
  text \<open>Purity configuration for constraint solver\<close>
  lemmas [safe_constraint_rules] = pure_pure

  lemma invalid_pure[safe_constraint_rules]: "is_pure (invalid_assn A)"
    unfolding invalid_assn_def is_pure_def by auto
  
  text \<open>Configuration for hfref to hnr conversion\<close>
  named_theorems to_hnr_post \<open>to_hnr converter: Postprocessing unfold rules\<close>

  lemma uncurry0_add_app_tag: "uncurry0 (RETURN c) = uncurry0 (RETURN$c)" by simp

  thm sep_conj_empty[of "P::ll_assn" for P]
  
  lemmas [to_hnr_post] = norm_RETURN_o norm_return_o
    uncurry0_add_app_tag uncurry0_apply uncurry0_APP hn_val_unit_conv_emp
    sep_conj_empty[of "P::ll_assn" for P] sep_conj_empty'[of "P::ll_assn" for P]

  named_theorems to_hfref_post \<open>to_hfref converter: Postprocessing unfold rules\<close> 
  lemma prod_casesK[to_hfref_post]: "case_prod (\<lambda>_ _. k) = (\<lambda>_. k)" by auto
  lemma uncurry0_hfref_post[to_hfref_post]: "hfref (uncurry0 True) R S = hfref (\<lambda>_. True) R S" 
    apply (fo_rule arg_cong fun_cong)+ by auto


  (* Currently not used, we keep it in here anyway. *)  
  text \<open>Configuration for relation normalization after composition\<close>
  named_theorems fcomp_norm_unfold \<open>fcomp-normalizer: Unfold theorems\<close>
  named_theorems fcomp_norm_simps \<open>fcomp-normalizer: Simplification theorems\<close>
  named_theorems fcomp_norm_init "fcomp-normalizer: Initialization rules"  
  named_theorems fcomp_norm_trans "fcomp-normalizer: Transitivity rules"  
  named_theorems fcomp_norm_cong "fcomp-normalizer: Congruence rules"  
  named_theorems fcomp_norm_norm "fcomp-normalizer: Normalization rules"  
  named_theorems fcomp_norm_refl "fcomp-normalizer: Reflexivity rules"  

  text \<open>Default Setup\<close>
  lemmas [fcomp_norm_unfold] = prod_rel_comp nrest_rel_comp Id_O_R R_O_Id
  lemmas [fcomp_norm_unfold] = hr_comp_Id1 hr_comp_Id2 hrp_comp_Id1 hrp_comp_Id2
  find_theorems rr_comp
  lemmas [fcomp_norm_unfold] = hrr_comp_nondep rr_comp_nondep
  lemmas [fcomp_norm_unfold] = hr_comp_prod_conv
  lemmas [fcomp_norm_unfold] = prod_hrp_comp hrp_comp_keep hrp_comp_dest hr_comp_pure
  (*lemmas [fcomp_norm_unfold] = prod_casesK uncurry0_hfref_post*)

  lemma [fcomp_norm_simps]: "CONSTRAINT is_pure P \<Longrightarrow> pure (the_pure P) = P" by simp
  lemmas [fcomp_norm_simps] = True_implies_equals 
  
  lemmas [fcomp_norm_init] = fcomp_norm_dflt_init
  lemmas [fcomp_norm_trans] = hrp_imp_trans
  lemmas [fcomp_norm_cong] = hrp_comp_cong hrp_prod_cong
  (*lemmas [fcomp_norm_norm] = hrp_comp_dest*)
  lemmas [fcomp_norm_refl] = refl hrp_imp_refl

  lemma ensure_fref_nresI: "(f,g)\<in>[P]\<^sub>f\<^sub>d R\<rightarrow>S \<Longrightarrow> (RETURN o f, RETURN o g)\<in>[P]\<^sub>f\<^sub>d R\<rightarrow>(\<lambda>x. \<langle>S x\<rangle>nrest_rel)" 
    apply (auto intro!: nrest_relI simp: fref_def)
    unfolding RETURNT_def conc_fun_def le_fun_def
    apply (auto intro!: le_funI)
    apply(rule Sup_upper) by auto

  lemma ensure_fref_nres_unfold:
    "\<And>f. RETURN o (uncurry0 f) = uncurry0 (RETURN f)" 
    "\<And>f. RETURN o (uncurry f) = uncurry (RETURN oo f)"
    "\<And>f. (RETURN ooo uncurry) f = uncurry (RETURN ooo f)"
    by auto

  text \<open>Composed precondition normalizer\<close>  
  named_theorems fcomp_prenorm_simps \<open>fcomp precondition-normalizer: Simplification theorems\<close>

  text \<open>Support for preconditions of the form @{text "_\<in>Domain R"}, 
    where @{text R} is the relation of the next more abstract level.\<close>
  declare DomainI[fcomp_prenorm_simps]

  lemma auto_weaken_pre_init_hf: 
    assumes "\<And>x. PROTECT P x \<longrightarrow> P' x"  
    assumes "(f,h) \<in> hfref P' R S"
    shows "(f,h) \<in> hfref P R S"
    using assms
    by (auto simp: hfref_def)

  lemma auto_weaken_pre_init_f: 
    assumes "\<And>x. PROTECT P x \<longrightarrow> P' x"  
    assumes "(f,h) \<in> fref P' R S"
    shows "(f,h) \<in> fref P R S"
    using assms
    by (auto simp: fref_def)

  lemmas auto_weaken_pre_init = auto_weaken_pre_init_hf auto_weaken_pre_init_f  

  lemma auto_weaken_pre_uncurry_step:
    assumes "PROTECT f a \<equiv> f'"
    shows "PROTECT (\<lambda>(x,y). f x y) (a,b) \<equiv> f' b" 
    using assms
    by (auto simp: curry_def dest!: meta_eq_to_obj_eq intro!: eq_reflection)

  lemma auto_weaken_pre_uncurry_finish:  
    "PROTECT f x \<equiv> f x" by (auto)

  lemma auto_weaken_pre_uncurry_start:
    assumes "P \<equiv> P'"
    assumes "P'\<longrightarrow>Q"
    shows "P\<longrightarrow>Q"
    using assms by (auto)

  lemma auto_weaken_pre_comp_PRE_I:
    assumes "S x \<Longrightarrow> P x"
    assumes "\<And>y. \<lbrakk>(y,x)\<in>R; P x; S x\<rbrakk> \<Longrightarrow> Q x y"
    shows "comp_PRE R P Q S x"
    using assms by (auto simp: comp_PRE_def)

  lemma auto_weaken_pre_to_imp_nf:
    "(A\<longrightarrow>B\<longrightarrow>C) = (A\<and>B \<longrightarrow> C)"
    "((A\<and>B)\<and>C) = (A\<and>B\<and>C)"
    by auto

  lemma auto_weaken_pre_add_dummy_imp:
    "P \<Longrightarrow> True \<longrightarrow> P" by simp


  text \<open>Synthesis for hfref statements\<close>  
  definition hfsynth_ID_R :: "('a \<Rightarrow> _ \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" where
    [simp]: "hfsynth_ID_R _ _ \<equiv> True"

  lemma hfsynth_ID_R_D:
    fixes I :: "'a itself"
    assumes "hfsynth_ID_R R a"
    assumes "intf_of_assn R I"
    shows "a ::\<^sub>i I"
    by simp

  lemma hfsynth_hnr_from_hfI:
    assumes "\<forall>x xi. P x \<and> hfsynth_ID_R (fst R) x \<longrightarrow> hn_refine (hn_ctxt (fst R) x xi ** \<box>) (f$xi) (hn_ctxt (snd R) x xi ** \<box>) (S x xi) (g$x)"
    shows "(f,g) \<in> [P]\<^sub>a\<^sub>d R \<rightarrow> S"
    using assms
    unfolding hfref_def 
    by (auto simp: hn_ctxt_def)


  lemma hfsynth_ID_R_uncurry_unfold: 
    "hfsynth_ID_R (to_hnr_prod R S) (a,b) \<equiv> hfsynth_ID_R R a \<and> hfsynth_ID_R S b" 
    "hfsynth_ID_R (fst (hf_pres R k)) \<equiv> hfsynth_ID_R R"
    by (auto intro!: eq_reflection)



(* TODO: Move *)
lemma SC_attains_supI: "C \<Longrightarrow> SC_attains_sup C" 
  unfolding SC_attains_sup_def by simp

method solve_attains_sup = (intro allI SC_attains_supI, 
                (   (rule attains_sup_sv, tagged_solver; fail)
                  | (rule one_time_attains_sup, intro OT_intros; fail)
                    ))

thm OT_intros

lemma "SC_attains_sup (attains_sup A B Id)"
  apply solve_attains_sup done

lemma "single_valued C \<Longrightarrow> SC_attains_sup (attains_sup A B C)"
  apply solve_attains_sup done

lemma "SC_attains_sup (attains_sup A (RETURNT x) R)"
  apply solve_attains_sup done


  ML \<open>

    signature SEPREF_RULES = sig
      (* Analysis of relations, both fref and fun_rel *)
      (* "R1\<rightarrow>...\<rightarrow>Rn\<rightarrow>_" / "[_]\<^sub>f ((R1\<times>\<^sub>rR2)...\<times>\<^sub>rRn)"  \<mapsto>  "[R1,...,Rn]" *)
      val binder_rels: term -> term list 
      (* "_\<rightarrow>...\<rightarrow>_\<rightarrow>S" / "[_]\<^sub>f _ \<rightarrow> S"  \<mapsto>  "S" *)
      val body_rel: term -> term 
      (* Map \<rightarrow>/fref to (precond,args,res). NONE if no/trivial precond. *)
      val analyze_rel: term -> term option * term list * term 
      (* Make trivial ("\<lambda>_. True") precond *)
      val mk_triv_precond: term list -> term 
      (* Make "[P]\<^sub>f\<^sub>d ((R1\<times>\<^sub>rR2)...\<times>\<^sub>rRn) \<rightarrow> S". Insert trivial precond if NONE. *)
      val mk_rel: term option * term list * term -> term 
      (* Map relation to (args,res) *)
      val strip_rel: term -> term list * term 

      (* Make hfprod (op *\<^sub>a) *)
      val mk_hfprod : term * term -> term
      val mk_hfprods : term list -> term

      (* Determine interface type of refinement assertion, using default fallback
        if necessary. Use named_thms intf_of_assn for configuration. *)
      val intf_of_assn : Proof.context -> term -> typ

      (*
        Convert a parametricity theorem in higher-order form to
        uncurried fref-form. For functions without arguments, 
        a unit-argument is added.

        TODO/FIXME: Currently this only works for higher-order theorems,
          i.e., theorems of the form (f,g)\<in>R1\<rightarrow>\<dots>\<rightarrow>Rn. 
          
          First-order theorems are silently treated as refinement theorems
          for functions with zero arguments, i.e., a unit-argument is added.
      *)
      val to_fref : Proof.context -> thm -> thm

      (* Convert a parametricity or fref theorem to first order form *)
      val to_foparam : Proof.context -> thm -> thm

      (* Convert schematic hfref goal to hnr-goal *)
      val prepare_hfref_synth_tac : Proof.context -> tactic'

      (* Convert theorem in hfref-form to hnr-form *)
      val to_hnr : Proof.context -> thm -> thm

      (* Convert theorem in hnr-form to hfref-form *)
      val to_hfref: Proof.context -> thm -> thm

      (* Convert theorem to given form, if not yet in this form *)
      val ensure_fref : Proof.context -> thm -> thm
      val ensure_fref_nres : Proof.context -> thm -> thm
      val ensure_hfref : Proof.context -> thm -> thm
      val ensure_hnr : Proof.context -> thm -> thm


      type hnr_analysis = {
        thm: thm,                     (* Original theorem, may be normalized *)
        precond: term,                (* Precondition, abstracted over abs-arguments *)
        prems : term list,            (* Premises not depending on arguments *)
        ahead: term * bool,           (* Abstract function, has leading RETURN *)
        chead: term * bool,           (* Concrete function, has leading return *)
        argrels: (term * bool) list,  (* Argument relations, preserved (keep-flag) *)
        result_rel: term              (* Result relation *)
      }
  
      val analyze_hnr: Proof.context -> thm -> hnr_analysis
      val pretty_hnr_analysis: Proof.context -> hnr_analysis -> Pretty.T
      val mk_hfref_thm: Proof.context -> hnr_analysis -> thm
  
  

      (* Simplify precondition of fref/hfref-theorem *)
      val simplify_precond: Proof.context -> thm -> thm

      (* Normalize hfref-theorem after composition *)
      val norm_fcomp_rule: Proof.context -> thm -> thm

      (* Replace "pure ?A" by "?A'" and is_pure constraint, then normalize *)
      val add_pure_constraints_rule: Proof.context -> thm -> thm

      (* Compose fref/hfref and fref theorem, to produce hfref theorem.
        The input theorems may also be in ho-param or hnr form, and
        are converted accordingly.
      *)
      val gen_compose : Proof.context -> thm -> thm -> thm

      (* FCOMP-attribute *)
      val fcomp_attrib: attribute context_parser

      (* Check FCOMP-result for artifacts that should be removed by normalization *)      
      val check_fcomp_result: Proof.context -> thm -> unit
      
    end

    structure Sepref_Rules: SEPREF_RULES = struct

      local open Refine_Util Relators in
        fun binder_rels @{mpat "?F \<rightarrow> ?G"} = F::binder_rels G
          | binder_rels @{mpat "fref _ ?F _"} = strip_prodrel_left F
          | binder_rels _ = []
    
        local 
          fun br_aux @{mpat "_ \<rightarrow> ?G"} = br_aux G
            | br_aux R = R
        in    
          fun body_rel @{mpat "fref _ _ ?G"} = G
            | body_rel R = br_aux R
        end
    
        fun strip_rel R = (binder_rels R, body_rel R)   
    
        fun analyze_rel @{mpat "fref (\<lambda>_. True) ?R ?S"} = (NONE,strip_prodrel_left R,S)
          | analyze_rel @{mpat "fref ?P ?R ?S"} = (SOME P,strip_prodrel_left R,S)
          | analyze_rel R = let
              val (args,res) = strip_rel R
              val argTuc = 
                   map (fastype_of #> HOLogic.dest_setT #> HOLogic.dest_prodT #> snd) args 
                |> list_prodT_left
              val res = Term.absdummy argTuc res
            in
              (NONE,args,res)
            end
    
        fun mk_triv_precond Rs = absdummy (map rel_absT Rs |> list_prodT_left) @{term True}
    
        fun mk_rel (P,Rs,S) = let 
          val R = list_prodrel_left Rs 
    
          val P = case P of 
              SOME P => P 
            | NONE => mk_triv_precond Rs
    
        in 
          @{mk_term "fref ?P ?R ?S"} 
        end
      end


      fun mk_hfprod (a, b) = @{mk_term "?a*\<^sub>a?b"}
  
      local 
        fun mk_hfprods_rev [] = @{mk_term "unit_assn\<^sup>k"}
          | mk_hfprods_rev [Rk] = Rk
          | mk_hfprods_rev (Rkn::Rks) = mk_hfprod (mk_hfprods_rev Rks, Rkn)
      in
        val mk_hfprods = mk_hfprods_rev o rev
      end


      fun intf_of_assn ctxt t = let
        val orig_ctxt = ctxt
        val (t,ctxt) = yield_singleton (Variable.import_terms false) t ctxt

        val v = TVar (("T",0),Proof_Context.default_sort ctxt ("T",0)) |> Logic.mk_type
        val goal = @{mk_term "Trueprop (intf_of_assn ?t ?v)"}

        val i_of_assn_rls = 
          Named_Theorems_Rev.get ctxt @{named_theorems_rev intf_of_assn}
          @ @{thms intf_of_assn_fallback}

        fun tac ctxt = REPEAT_ALL_NEW (resolve_tac ctxt i_of_assn_rls)

        val thm = Goal.prove ctxt [] [] goal (fn {context,...} => ALLGOALS (tac context))
        val intf = case Thm.concl_of thm of
            @{mpat "Trueprop (intf_of_assn _ (?v AS\<^sub>p TYPE (_)))"} => v 
          | _ => raise THM("Intf_of_assn: Proved a different theorem?",~1,[thm])

        val intf = singleton (Variable.export_terms ctxt orig_ctxt) intf
          |> Logic.dest_type

      in
        intf
      end

      datatype rthm_type = 
        RT_HOPARAM    (* (_,_) \<in> _ \<rightarrow> \<dots> \<rightarrow> _ *)
      | RT_FREF       (* (_,_) \<in> [_]\<^sub>f _ \<rightarrow> _ *)
      | RT_HNR        (* hn_refine _ _ _ _ _ *)
      | RT_HFREF      (* (_,_) \<in> [_]\<^sub>a _ \<rightarrow> _ *)
      | RT_OTHER

      fun rthm_type thm =
        case Thm.concl_of thm |> HOLogic.dest_Trueprop of
          @{mpat "(_,_) \<in> fref _ _ _"} => RT_FREF
        | @{mpat "(_,_) \<in> hfref _ _ _"} => RT_HFREF
        | @{mpat "hn_refine _ _ _ _ _"} => RT_HNR
        | @{mpat "(_,_) \<in> _"} => RT_HOPARAM (* TODO: Distinction between ho-param and fo-param *)
        | _ => RT_OTHER


      fun to_fref ctxt thm = let
        open Conv
      in  
        case Thm.concl_of thm |> HOLogic.dest_Trueprop of
          @{mpat "(_,_)\<in>_\<rightarrow>_"} =>
            Local_Defs.unfold0 ctxt @{thms fref_param1} thm
            |> fconv_rule (repeat_conv (Refine_Util.ftop_conv (K (rewr_conv @{thm fref_nest})) ctxt))
            |> Local_Defs.unfold0 ctxt @{thms in_CURRY_conv}
        | @{mpat "(_,_)\<in>_"} => thm RS @{thm fref_param0I}   
        | _ => raise THM ("to_fref: Expected theorem of form (_,_)\<in>_",~1,[thm])
      end

      fun to_foparam ctxt thm = let
        val unf_thms = @{thms 
          split_tupled_all prod_rel_simp uncurry_apply cnv_conj_to_meta Product_Type.split}
      in
        case Thm.concl_of thm of
          @{mpat "Trueprop ((_,_) \<in> fref _ _ _)"} =>
            (@{thm frefD} OF [thm])
            |> Thm.forall_intr_vars
            |> Local_Defs.unfold0 ctxt unf_thms
            |> Variable.gen_all ctxt
        | @{mpat "Trueprop ((_,_) \<in> _)"} =>
            Parametricity.fo_rule thm
        | _ => raise THM("Expected parametricity or fref theorem",~1,[thm])
      end

      fun to_hnr ctxt thm =
        (thm RS @{thm hf2hnr})
        |> Local_Defs.unfold0 ctxt @{thms to_hnr_prod_fst_snd keep_drop_sels} (* Resolve fst and snd over *\<^sub>a and R\<^sup>k, R\<^sup>d *)
        |> Local_Defs.unfold0 ctxt @{thms hnr_uncurry_unfold} (* Resolve products for uncurried parameters *)
        |> Local_Defs.unfold0 ctxt @{thms uncurry_apply uncurry_APP sep_conj_empty' split} (* Remove the uncurry modifiers, the emp-dummy, and unfold product cases *)
        |> Local_Defs.unfold0 ctxt @{thms hn_ctxt_ctxt_fix_conv} (* Remove duplicate hn_ctxt tagging *)
        |> Local_Defs.unfold0 ctxt @{thms all_to_meta imp_to_meta HOL.True_implies_equals HOL.implies_True_equals Pure.triv_forall_equality cnv_conj_to_meta} (* Convert to meta-level, remove vacuous condition *)
        |> Local_Defs.unfold0 ctxt (Named_Theorems.get ctxt @{named_theorems to_hnr_post}) (* Post-Processing *)
        |> Goal.norm_result ctxt
        |> Conv.fconv_rule Thm.eta_conversion

      (* Convert schematic hfref-goal to hn_refine goal *)  
      fun prepare_hfref_synth_tac ctxt = let
        val i_of_assn_rls = 
          Named_Theorems_Rev.get ctxt @{named_theorems_rev intf_of_assn}
          @ @{thms intf_of_assn_fallback}

        val to_hnr_post_rls = 
          Named_Theorems.get ctxt @{named_theorems to_hnr_post}

        val i_of_assn_tac = (
          REPEAT' (
            DETERM o dresolve_tac ctxt @{thms hfsynth_ID_R_D}
            THEN' DETERM o SOLVED' (REPEAT_ALL_NEW (resolve_tac ctxt i_of_assn_rls))
          )
        )
      in
        (* Note: To re-use the to_hnr infrastructure, we first work with
          $-tags on the abstract function, which are finally removed.
        *)
        resolve_tac ctxt @{thms hfsynth_hnr_from_hfI} THEN_ELSE' (
          SELECT_GOAL (
            unfold_tac ctxt @{thms to_hnr_prod_fst_snd keep_drop_sels hf_pres_fst} (* Distribute fst,snd over product and hf_pres *)
            THEN unfold_tac ctxt @{thms hnr_uncurry_unfold hfsynth_ID_R_uncurry_unfold} (* Curry parameters *)
            THEN unfold_tac ctxt @{thms uncurry_apply uncurry_APP sep_conj_empty' split} (* Curry parameters (II) and remove emp assertion *)
            (*THEN unfold_tac ctxt @{thms hn_ctxt_ctxt_fix_conv} (* Remove duplicate hn_ctxt (Should not be necessary) *)*)
            THEN unfold_tac ctxt @{thms all_to_meta imp_to_meta HOL.True_implies_equals HOL.implies_True_equals Pure.triv_forall_equality cnv_conj_to_meta} (* Convert precondition to meta-level *)
            THEN ALLGOALS i_of_assn_tac (* Generate _::\<^sub>i_ premises*)
            THEN unfold_tac ctxt to_hnr_post_rls (* Postprocessing *)
            THEN unfold_tac ctxt @{thms APP_def} (* Get rid of $ - tags *)
          )
        ,
          K all_tac
        )
      end


      (************************************)  
      (* Analyze hnr *)
      structure Termtab2 = Table(
        type key = term * term 
        val ord = prod_ord Term_Ord.fast_term_ord Term_Ord.fast_term_ord);
  
      type hnr_analysis = {
        thm: thm,                     
        precond: term,                
        prems : term list,
        ahead: term * bool,           
        chead: term * bool,           
        argrels: (term * bool) list,  
        result_rel: term              
      }
  
    
      fun analyze_hnr (ctxt:Proof.context) thm = let
    
        (* Debug information: Stores string*term pairs, which are pretty-printed on error *)
        val dbg = Unsynchronized.ref []
        fun add_dbg msg ts = (
          dbg := (msg,ts) :: !dbg;
          ()
        )
        fun pretty_dbg (msg,ts) = Pretty.block [
          Pretty.str msg,
          Pretty.str ":",
          Pretty.brk 1,
          Pretty.list "[" "]" (map (Syntax.pretty_term ctxt) ts)
        ]
        fun pretty_dbgs l = map pretty_dbg l |> Pretty.fbreaks |> Pretty.block
    
        fun trace_dbg msg = Pretty.block [Pretty.str msg, Pretty.fbrk, pretty_dbgs (rev (!dbg))] |> Pretty.string_of |> tracing
    
        fun fail msg = (trace_dbg msg; raise THM(msg,~1,[thm])) 
        fun assert cond msg = cond orelse fail msg;
    
    
        (* Heads may have a leading return/RETURN.
          The following code strips off the leading return, unless it has the form
          "return x" for an argument x
        *)
        fun check_strip_leading args t f = (* Handle the case RETURN x, where x is an argument *)
          if Termtab.defined args f then (t,false) else (f,true)
    
        fun strip_leading_RETURN args (t as @{mpat "RETURN$(?f)"}) = check_strip_leading args t f
          | strip_leading_RETURN args (t as @{mpat "RETURN ?f"}) = check_strip_leading args t f
          | strip_leading_RETURN _ t = (t,false)
    
        fun strip_leading_return args (t as @{mpat "return$(?f)"}) = check_strip_leading args t f
            | strip_leading_return args (t as @{mpat "return ?f"}) = check_strip_leading args t f
            | strip_leading_return _ t = (t,false)
    
    
        (* The following code strips the arguments of the concrete or abstract
          function. It knows how to handle APP-tags ($), and stops at PR_CONST-tags.
    
          Moreover, it only strips actual arguments that occur in the 
          precondition-section of the hn_refine-statement. This ensures
          that non-arguments, like maxsize, are treated correctly.
        *)    
        fun strip_fun _ (t as @{mpat "PR_CONST _"}) = (t,[])
          | strip_fun s (t as @{mpat "?f$?x"}) = check_arg s t f x
          | strip_fun s (t as @{mpat "?f ?x"}) = check_arg s t f x
          | strip_fun _ f = (f,[])
        and check_arg s t f x = 
            if Termtab.defined s x then
              strip_fun s f |> apsnd (curry op :: x)
            else (t,[])  
    
        (* Arguments in the pre/postcondition are wrapped into hn_ctxt tags. 
          This function strips them off. *)    
        fun dest_hn_ctxt @{mpat "hn_ctxt ?R ?a ?c"} = ((a,c),R)
          | dest_hn_ctxt _ = fail "Invalid hn_ctxt parameter in pre or postcondition"
    
    
        fun dest_hn_refine @{mpat "(hn_refine ?G ?c ?G' ?R ?a)"} = (G,c,G',R,a) 
          | dest_hn_refine _ = fail "Conclusion is not a hn_refine statement"
    
        (*
          Strip separation conjunctions. Special case for "emp", which is ignored. 
        *)  
        fun is_emp @{mpat \<box>} = true | is_emp _ = false
  
        val strip_star' = Sepref_Basic.strip_star #> filter (not o is_emp)
  
        (* Compare Termtab2s for equality of keys *)  
        fun pairs_eq pairs1 pairs2 = 
                  Termtab2.forall (Termtab2.defined pairs1 o fst) pairs2
          andalso Termtab2.forall (Termtab2.defined pairs2 o fst) pairs1
    
    
        fun atomize_prem @{mpat "Trueprop ?p"} = p
          | atomize_prem _ = fail "Non-atomic premises"
    
        (* Make HOL conjunction list *)  
        fun mk_conjs [] = @{const True}
          | mk_conjs [p] = p
          | mk_conjs (p::ps) = HOLogic.mk_binop @{const_name "HOL.conj"} (p,mk_conjs ps)
    
    
        (***********************)      
        (* Start actual analysis *)
    
        val _ = add_dbg "thm" [Thm.prop_of thm]
        val prems = Thm.prems_of thm
        val concl = Thm.concl_of thm |> HOLogic.dest_Trueprop
        val (G,c,G',R,a) = dest_hn_refine concl
    
        val pre_pairs = G 
          |> strip_star'
          |> tap (add_dbg "precondition")
          |> map dest_hn_ctxt
          |> Termtab2.make
    
        val post_pairs = G' 
          |> strip_star'
          |> tap (add_dbg "postcondition")
          |> map dest_hn_ctxt
          |> Termtab2.make
    
        val _ = assert (pairs_eq pre_pairs post_pairs) 
          "Parameters in precondition do not match postcondition"
    
        val aa_set = pre_pairs |> Termtab2.keys |> map fst |> Termtab.make_set
        val ca_set = pre_pairs |> Termtab2.keys |> map snd |> Termtab.make_set
    
        val (a,leading_RETURN) = strip_leading_RETURN aa_set a
        val (c,leading_return) = strip_leading_return ca_set c
    
        val _ = add_dbg "stripped abstract term" [a]
        val _ = add_dbg "stripped concrete term" [c]
    
        val (ahead,aargs) = strip_fun aa_set a;
        val (chead,cargs) = strip_fun ca_set c;
    
        val _ = add_dbg "abstract head" [ahead]
        val _ = add_dbg "abstract args" aargs
        val _ = add_dbg "concrete head" [chead]
        val _ = add_dbg "concrete args" cargs
    
    
        val _ = assert (length cargs = length aargs) "Different number of abstract and concrete arguments";
    
        val _ = assert (not (has_duplicates op aconv aargs)) "Duplicate abstract arguments"
        val _ = assert (not (has_duplicates op aconv cargs)) "Duplicate concrete arguments"
    
        val argpairs = aargs ~~ cargs
        val ap_set = Termtab2.make_set argpairs
        val _ = assert (pairs_eq pre_pairs ap_set) "Arguments from pre/postcondition do not match operation's arguments"
    
        val pre_rels = map (the o (Termtab2.lookup pre_pairs)) argpairs
        val post_rels = map (the o (Termtab2.lookup post_pairs)) argpairs
    
        val _ = add_dbg "pre-rels" pre_rels
        val _ = add_dbg "post-rels" post_rels

        fun adjust_hf_pres @{mpat "snd (?R\<^sup>k)"} = R
          | adjust_hf_pres t = t
          
        val post_rels = map adjust_hf_pres post_rels
    
        fun is_invalid R @{mpat "invalid_assn ?R'"} = R aconv R'
          | is_invalid _ @{mpat "snd (_\<^sup>d)"} = true
          | is_invalid _ _ = false
    
        fun is_keep (R,R') =
          if R aconv R' then true
          else if is_invalid R R' then false
          else fail "Mismatch between pre and post relation for argument"
    
        val keep = map is_keep (pre_rels ~~ post_rels)
    
        val argrels = pre_rels ~~ keep

        val aa_set = Termtab.make_set aargs
        val ca_set = Termtab.make_set cargs

        fun is_precond t =
          (exists_subterm (Termtab.defined ca_set) t andalso fail "Premise contains concrete argument")
          orelse exists_subterm (Termtab.defined aa_set) t

        val (preconds, prems) = split is_precond prems  
    
        val precond = 
          map atomize_prem preconds 
          |> mk_conjs
          |> fold lambda aargs
    
        val _ = add_dbg "precond" [precond]
        val _ = add_dbg "prems" prems
    
      in
        {
          thm = thm,
          precond = precond,
          prems = prems,
          ahead = (ahead,leading_RETURN),
          chead = (chead,leading_return),
          argrels = argrels,
          result_rel = R
        }
      end  
    
      fun pretty_hnr_analysis 
        ctxt 
        ({thm,precond,ahead,chead,argrels,result_rel,...}) 
        : Pretty.T =
      let  
        val _ = thm (* Suppress unused warning for thm *)

        fun pretty_argrel (R,k) = Pretty.block [
          Syntax.pretty_term ctxt R,
          if k then Pretty.str "\<^sup>k" else Pretty.str "\<^sup>d"
        ]
    
        val pretty_chead = case chead of 
          (t,false) => Syntax.pretty_term ctxt t 
        | (t,true) => Pretty.block [Pretty.str "return ", Syntax.pretty_term ctxt t]

        val pretty_ahead = case ahead of 
          (t,false) => Syntax.pretty_term ctxt t 
        | (t,true) => Pretty.block [Pretty.str "RETURN ", Syntax.pretty_term ctxt t]

      in
        Pretty.fbreaks [
          (*Display.pretty_thm ctxt thm,*)
          Pretty.block [ 
            Pretty.enclose "[" "]" [pretty_chead, pretty_ahead],
            Pretty.enclose "[" "]" [Syntax.pretty_term ctxt precond],
            Pretty.brk 1,
            Pretty.block (Pretty.separate " \<rightarrow>" (map pretty_argrel argrels @ [Syntax.pretty_term ctxt result_rel]))
          ]
        ] |> Pretty.block
    
      end
    
    
      fun mk_hfref_thm 
        ctxt 
        ({thm,precond,prems,ahead,chead,argrels,result_rel}) = 
      let
    
        fun mk_keep (R,true) = @{mk_term "?R\<^sup>k"}
          | mk_keep (R,false) = @{mk_term "?R\<^sup>d"}
    
        (* TODO: Move, this is of general use! *)  
        fun mk_uncurry f = @{mk_term "uncurry ?f"}  
      
        (* Uncurry function for the given number of arguments. 
          For zero arguments, add a unit-parameter.
        *)
        fun rpt_uncurry n t =
          if n=0 then @{mk_term "uncurry0 ?t"}
          else if n=1 then t 
          else funpow (n-1) mk_uncurry t
      
        (* Rewrite uncurried lambda's to \<lambda>(_,_). _ form. Use top-down rewriting
          to correctly handle nesting to the left. 
    
          TODO: Combine with abstraction and  uncurry-procedure,
            and mark the deviation about uncurry as redundant 
            intermediate step to be eliminated.
        *)  
        fun rew_uncurry_lambda t = let
          val rr = map (Logic.dest_equals o Thm.prop_of) @{thms uncurry_def uncurry0_def}
          val thy = Proof_Context.theory_of ctxt
        in 
          Pattern.rewrite_term_top thy rr [] t 
        end  
    
        (* Shortcuts for simplification tactics *)
        fun gsimp_only ctxt sec = let
          val ss = put_simpset HOL_basic_ss ctxt |> sec
        in asm_full_simp_tac ss end
    
        fun simp_only ctxt thms = gsimp_only ctxt (fn ctxt => ctxt addsimps thms)
    
    
        (********************************)
        (* Build theorem statement *)
        (* \<lbrakk>prems\<rbrakk> \<Longrightarrow> (chead,ahead) \<in> [precond] rels \<rightarrow> R *)
    
        (* Uncurry precondition *)
        val num_args = length argrels
        val precond = precond
          |> rpt_uncurry num_args
          |> rew_uncurry_lambda (* Convert to nicer \<lambda>((...,_),_) - form*)

        (* Re-attach leading RETURN/return *)
        fun mk_RETURN (t,r) = if r then 
            let
              val T = funpow num_args range_type (fastype_of (fst ahead))
              val tRETURN = Const (@{const_name RETURNT}, T --> Type(@{type_name nrest},[T]))
            in
              Refine_Util.mk_compN num_args tRETURN t
            end  
          else t
    
        fun mk_return (t,r) = if r then @{mk_term "return ?t :: _ llM"}
            (*let
              val T = funpow num_args range_type (fastype_of (fst chead))
              val tRETURN = Const (@{const_name return}, T --> Type(@{type_name llvm_memory},[T]))
            in
              Refine_Util.mk_compN num_args tRETURN t
            end  *)
          else t
          
        (* Hrmpf!: Gone for good from 2015\<rightarrow>2016. Inserting ctxt-based substitute here. *)  
        fun certify_inst ctxt (instT, inst) =
         (TVars.map (K (Thm.ctyp_of ctxt)) instT,
          Vars.map (K (Thm.cterm_of ctxt)) inst);

        (*  
        fun mk_RETURN (t,r) = if r then @{mk_term "RETURN o ?t"} else t
        fun mk_return (t,r) = if r then @{mk_term "return o ?t"} else t
        *)
    
        (* Uncurry abstract and concrete function, append leading return *)
        val ahead = ahead |> mk_RETURN |> rpt_uncurry num_args  
        val chead = chead |> mk_return |> rpt_uncurry num_args 
    
        (* Add keep-flags and summarize argument relations to product *)
        val argrel = map mk_keep argrels |> rev (* TODO: Why this rev? *) |> mk_hfprods
    
        (* Produce final result statement *)
        
        val _ = @{print} chead
        val _ = @{print} (fastype_of chead)
        
        val result = @{mk_term "Trueprop ((?chead,?ahead) \<in> [?precond]\<^sub>a ?argrel \<rightarrow> ?result_rel)"}
        val result = Logic.list_implies (prems,result)
    
        (********************************)
        (* Prove theorem *)
    
        (* Create context and import result statement and original theorem *)
        val orig_ctxt = ctxt
        (*val thy = Proof_Context.theory_of ctxt*)
        val (insts, ctxt) = Variable.import_inst true [result] ctxt
        val insts' = certify_inst ctxt insts
        val result = Term_Subst.instantiate insts result
        val thm = Thm.instantiate insts' thm
    
        (* Unfold APP tags. This is required as some APP-tags have also been unfolded by analysis *)
        val thm = Local_Defs.unfold0 ctxt @{thms APP_def} thm
    
        (* Tactic to prove the theorem. 
          A first step uses hfrefI to get a hnr-goal.
          This is then normalized in several consecutive steps, which 
            get rid of uncurrying. Finally, the original theorem is used for resolution,
            where the pre- and postcondition, and result relation are connected with 
            a consequence rule, to handle unfolded hn_ctxt-tags, re-ordered relations,
            and introduced unit-parameters (TODO: 
              Mark artificially introduced unit-parameter specially, it may get confused 
              with intentional unit-parameter, e.g., functional empty_set ()!)
    
          *)
        fun tac ctxt = 
                resolve_tac ctxt @{thms hfrefI}
          THEN' gsimp_only ctxt (fn c => c 
            addsimps @{thms uncurry_def hn_ctxt_def uncurry0_def
                            keep_drop_sels uc_hfprod_sel o_apply
                            APP_def}
            |> Splitter.add_split @{thm prod.split}
          ) 
    
          THEN' TRY o (
            REPEAT_ALL_NEW (match_tac ctxt @{thms allI impI})
            THEN' simp_only ctxt @{thms Product_Type.split prod.inject})
    
          THEN' TRY o REPEAT_ALL_NEW (ematch_tac ctxt @{thms conjE})
          THEN' TRY o hyp_subst_tac ctxt
          THEN' simp_only ctxt @{thms triv_forall_equality}
          THEN' (
            resolve_tac ctxt @{thms hn_refine_cons} 
            THEN' (resolve_tac ctxt [thm] THEN_ALL_NEW assume_tac ctxt))
          THEN_ALL_NEW simp_only ctxt 
            @{thms hn_ctxt_def entails_refl pure_unit_rel_eq_empty
              mult_ac mult_1 mult_1_right keep_drop_sels}  
    
        (* Prove theorem *)  
        val result = Thm.cterm_of ctxt result |> @{print}
        val rthm = Goal.prove_internal ctxt [] result (fn _ => ALLGOALS (tac ctxt))
    
        (* Export statement to original context *)
        val rthm = singleton (Variable.export ctxt orig_ctxt) rthm
    
        (* Post-processing *)
        val rthm = Local_Defs.unfold0 ctxt (Named_Theorems.get ctxt @{named_theorems to_hfref_post}) rthm

      in
        rthm
      end
  
      fun to_hfref ctxt = analyze_hnr ctxt #> mk_hfref_thm ctxt




      (***********************************)
      (* Composition *)

    
      fun check_fcomp_result ctxt thm = let
        val (_,R,S) = case Thm.concl_of thm of
          @{mpat "Trueprop (_\<in>hfref ?P ?R ?S)"} => (P,R,S)
        | _ => raise THM("FCOMP chk_result: Expected hfref-theorem",~1,[thm])  
    
        fun err t = let
          val ts = Syntax.pretty_term ctxt t |> Pretty.string_of
        in
          raise THM ("FCOMP chk_result: Invalid pattern left in assertions: " ^ ts,~1,[thm])
        end  
        fun check_invalid (t as @{mpat "hr_comp _ _"}) = err t 
          | check_invalid (t as @{mpat "hrp_comp _ _"}) = err t
          | check_invalid (t as @{mpat "hrr_comp _ _ _"}) = err t
          | check_invalid (t as @{mpat "pure (the_pure _)"}) = err t
          | check_invalid (t as @{mpat "_ O _"}) = err t
          | check_invalid _ = false
          
    
        val _ = exists_subterm check_invalid R 
        val _ = exists_subterm check_invalid S
      in
        ()
      end
      
      
      
      local
        fun norm_set_of ctxt = {
          trans_rules = Named_Theorems.get ctxt @{named_theorems fcomp_norm_trans},
          cong_rules = Named_Theorems.get ctxt @{named_theorems fcomp_norm_cong},
          norm_rules = Named_Theorems.get ctxt @{named_theorems fcomp_norm_norm},
          refl_rules = Named_Theorems.get ctxt @{named_theorems fcomp_norm_refl}
        }
    
        fun init_rules_of ctxt = Named_Theorems.get ctxt @{named_theorems fcomp_norm_init}
        fun unfold_rules_of ctxt = Named_Theorems.get ctxt @{named_theorems fcomp_norm_unfold}
        fun simp_rules_of ctxt = Named_Theorems.get ctxt @{named_theorems fcomp_norm_simps}

      in  
        fun norm_fcomp_rule ctxt = let
          open PO_Normalizer Refine_Util
          val norm1 = gen_norm_rule (init_rules_of ctxt) (norm_set_of ctxt) ctxt
          val norm2 = Local_Defs.unfold0 ctxt (unfold_rules_of ctxt)
          val norm3 = Conv.fconv_rule (
            Simplifier.asm_full_rewrite 
              (put_simpset HOL_basic_ss ctxt addsimps simp_rules_of ctxt))
    
          val norm = changed_rule (try_rule norm1 o try_rule norm2 o try_rule norm3)
        in
          repeat_rule norm
        end
      end  

      fun add_pure_constraints_rule ctxt thm = let
        val orig_ctxt = ctxt
    
        val t = Thm.prop_of thm
    
        fun 
          cnv (@{mpat (typs) "pure (mpaq_STRUCT (mpaq_Var ?x _) :: (?'v_c\<times>?'v_a) set)"}) = 
          let
            val T = a --> c --> @{typ assn}
            val t = Var (x,T)
            val t = @{mk_term "(the_pure ?t)"}
          in
            [(x,T,t)]
          end
        | cnv (t$u) = union op= (cnv t) (cnv u)
        | cnv (Abs (_,_,t)) = cnv t  
        | cnv _ = []
    
        val pvars = cnv t
    
        val _ = (pvars |> map #1 |> has_duplicates op=) 
          andalso raise TERM ("Duplicate indexname with different type",[t]) (* This should not happen *)
    
        val substs = map (fn (x,_,t) => (x,t)) pvars
    
        val t' = subst_Vars substs t  
    
        fun mk_asm (x,T,_) = let
          val t = Var (x,T)
          val t = @{mk_term "Trueprop (CONSTRAINT is_pure ?t)"}
        in
          t
        end
    
        val assms = map mk_asm pvars
    
        fun add_prems prems t = let
          val prems' = Logic.strip_imp_prems t
          val concl = Logic.strip_imp_concl t
        in
          Logic.list_implies (prems@prems', concl)
        end
    
        val t' = add_prems assms t'
    
        val (t',ctxt) = yield_singleton (Variable.import_terms true) t' ctxt
    
        val thm' = Goal.prove_internal ctxt [] (Thm.cterm_of ctxt t') (fn _ => 
          ALLGOALS (resolve_tac ctxt [thm] THEN_ALL_NEW assume_tac ctxt))
    
        val thm' = norm_fcomp_rule ctxt thm' 

        val thm' = singleton (Variable.export ctxt orig_ctxt) thm'
      in
        thm'
      end  


      val cfg_simp_precond = 
        Attrib.setup_config_bool @{binding fcomp_simp_precond} (K true)

      val cfg_check_result = 
        Attrib.setup_config_bool @{binding fcomp_check_result} (K true)
        
        
      local
        fun mk_simp_thm ctxt t = let
          val st = t
            |> HOLogic.mk_Trueprop
            |> Thm.cterm_of ctxt
            |> Goal.init
      
          val ctxt = Context_Position.set_visible false ctxt  
          val ctxt = ctxt addsimps (
              refine_pw_simps.get ctxt 
            @ Named_Theorems.get ctxt @{named_theorems fcomp_prenorm_simps}
            @ @{thms split_tupled_all cnv_conj_to_meta}  
            )
          
          val trace_incomplete_transfer_tac =
            COND (Thm.prems_of #> exists (strip_all_body #> Logic.strip_imp_concl #> Term.is_open))
              (print_tac ctxt "Failed transfer from intermediate level:") all_tac
    
          val tac = 
            ALLGOALS (resolve_tac ctxt @{thms auto_weaken_pre_comp_PRE_I} )
            THEN ALLGOALS (Simplifier.asm_full_simp_tac ctxt)
            THEN trace_incomplete_transfer_tac
            THEN ALLGOALS (TRY o filter_prems_tac ctxt (K false))
            THEN Local_Defs.unfold0_tac ctxt [Drule.triv_forall_equality]
      
          val st' = tac st |> Seq.take 1 |> Seq.list_of
          val thm = case st' of [st'] => Goal.conclude st' | _ => raise THM("Simp_Precond: Simp-Tactic failed",~1,[st])
    
          (* Check generated premises for leftover intermediate stuff *)
          val _ = exists (Logic.is_all) (Thm.prems_of thm) 
            andalso raise THM("Simp_Precond: Transfer from intermediate level failed",~1,[thm])
    
          val thm = 
             thm
          (*|> map (Simplifier.asm_full_simplify ctxt)*)
          |> Conv.fconv_rule (Object_Logic.atomize ctxt)
          |> Local_Defs.unfold0 ctxt @{thms auto_weaken_pre_to_imp_nf}
    
          val thm = case Thm.concl_of thm of
            @{mpat "Trueprop (_ \<longrightarrow> _)"} => thm
          | @{mpat "Trueprop _"} => thm RS @{thm auto_weaken_pre_add_dummy_imp}  
          | _ => raise THM("Simp_Precond: Generated odd theorem, expected form 'P\<longrightarrow>Q'",~1,[thm])
    
    
        in
          thm
        end
      in  
        fun simplify_precond ctxt thm = let
          val orig_ctxt = ctxt
          val thm = Refine_Util.OF_fst @{thms auto_weaken_pre_init} [asm_rl,thm]
          val thm = 
            Local_Defs.unfold0 ctxt @{thms split_tupled_all} thm
            OF @{thms auto_weaken_pre_uncurry_start}
      
          fun rec_uncurry thm =
            case try (fn () => thm OF @{thms auto_weaken_pre_uncurry_step}) () of
              NONE => thm OF @{thms auto_weaken_pre_uncurry_finish}
            | SOME thm => rec_uncurry thm  
      
          val thm = rec_uncurry thm  
            |> Conv.fconv_rule Thm.eta_conversion
      
          val t = case Thm.prems_of thm of
            t::_ => t | _ => raise THM("Simp-Precond: Expected at least one premise",~1,[thm])
      
          val (t,ctxt) = yield_singleton (Variable.import_terms false) t ctxt
          val ((_,t),ctxt) = Variable.focus NONE t ctxt
          val t = case t of
            @{mpat "Trueprop (_ \<longrightarrow> ?t)"} => t | _ => raise TERM("Simp_Precond: Expected implication",[t])
      
          val simpthm = mk_simp_thm ctxt t  
            |> singleton (Variable.export ctxt orig_ctxt)
            
          val thm = thm OF [simpthm]  
          val thm = Local_Defs.unfold0 ctxt @{thms prod_casesK} thm
        in
          thm
        end

        fun simplify_precond_if_cfg ctxt =
          if Config.get ctxt cfg_simp_precond then
            simplify_precond ctxt
          else I

      end  

      fun check_result_if_cfg ctxt thm = 
        if Config.get ctxt cfg_check_result then
          (check_fcomp_result ctxt thm; thm)
        else thm
      
      
      (* fref O fref *)
      fun compose_ff ctxt A B = 
          (@{thm fref_compI_PRE} OF [A,B])
        |> norm_fcomp_rule ctxt
        |> simplify_precond_if_cfg ctxt
        |> Conv.fconv_rule Thm.eta_conversion
        |> check_result_if_cfg ctxt

      val solve_attains_sup_tac =
        More_Eisbach_Basic.apply_method_noargs @{method solve_attains_sup}

      fun solve_attains_sup ctxt thm =
        More_Refine_Util.prove_prems true ctxt thm 
            ([SOME solve_attains_sup_tac])

      (* hfref O fref *)
      fun compose_hf ctxt A B =
          (@{thm hfref_compI_PRE} OF [A,B])
        |> solve_attains_sup ctxt
        |> norm_fcomp_rule ctxt
        |> simplify_precond_if_cfg ctxt
        |> Conv.fconv_rule Thm.eta_conversion
        |> add_pure_constraints_rule ctxt
        |> Conv.fconv_rule Thm.eta_conversion
        |> check_result_if_cfg ctxt

      fun ensure_fref ctxt thm = case rthm_type thm of
        RT_HOPARAM => to_fref ctxt thm
      | RT_FREF => thm
      | _ => raise THM("Expected parametricity or fref theorem",~1,[thm])

      fun ensure_fref_nres ctxt thm = let
        val thm = ensure_fref ctxt thm
      in
        case Thm.concl_of thm of
          @{mpat (typs) "Trueprop (_\<in>fref _ _ (_::_ \<Rightarrow> ((_,_)nrest\<times>_)set))"} => thm
        | @{mpat "Trueprop ((_,_)\<in>fref _ _ _)"} => 
            (thm RS @{thm ensure_fref_nresI}) |> Local_Defs.unfold0 ctxt @{thms ensure_fref_nres_unfold}
        | _ => raise THM("Expected fref-theorem",~1,[thm])
      end

      fun ensure_hfref ctxt thm = case rthm_type thm of
        RT_HNR => to_hfref ctxt thm
      | RT_HFREF => thm
      | _ => raise THM("Expected hnr or hfref theorem",~1,[thm])

      fun ensure_hnr ctxt thm = case rthm_type thm of
        RT_HNR => thm
      | RT_HFREF => to_hnr ctxt thm
      | _ => raise THM("Expected hnr or hfref theorem",~1,[thm])

      fun gen_compose ctxt A B = let
        val rtA = rthm_type A
      in
        if rtA = RT_HOPARAM orelse rtA = RT_FREF then
          compose_ff ctxt (ensure_fref ctxt A) (ensure_fref ctxt B)
        else  
          compose_hf ctxt (ensure_hfref ctxt A) ((ensure_fref_nres ctxt B))
        
      end

      val parse_fcomp_flags = Refine_Util.parse_paren_lists 
        (Refine_Util.parse_bool_config "prenorm" cfg_simp_precond
          || Refine_Util.parse_bool_config "check" cfg_check_result
        )

      val fcomp_attrib = parse_fcomp_flags |-- Attrib.thm >> (fn B => Thm.rule_attribute [] (fn context => fn A => 
      let
        val ctxt = Context.proof_of context
      in  
        gen_compose ctxt A B
      end))

    end
  \<close>

  attribute_setup to_fref = \<open>
    Scan.succeed (Thm.rule_attribute [] (Sepref_Rules.to_fref o Context.proof_of))
  \<close> "Convert parametricity theorem to uncurried fref-form" 

  attribute_setup to_foparam = \<open>
      Scan.succeed (Thm.rule_attribute [] (Sepref_Rules.to_foparam o Context.proof_of))
  \<close> \<open>Convert param or fref rule to first order rule\<close>
  (* Overloading existing param_fo - attribute from Parametricity.thy *)
  attribute_setup param_fo = \<open>
      Scan.succeed (Thm.rule_attribute [] (Sepref_Rules.to_foparam o Context.proof_of))
  \<close> \<open>Convert param or fref rule to first order rule\<close>

  attribute_setup to_hnr = \<open>
    Scan.succeed (Thm.rule_attribute [] (Sepref_Rules.to_hnr o Context.proof_of))
  \<close> "Convert hfref-rule to hnr-rule"
  
  attribute_setup to_hfref = \<open>Scan.succeed (
      Thm.rule_attribute [] (Context.proof_of #> Sepref_Rules.to_hfref)
    )\<close> \<open>Convert hnr to hfref theorem\<close>


  attribute_setup ensure_fref_nres = \<open>Scan.succeed (
      Thm.rule_attribute [] (Context.proof_of #> Sepref_Rules.ensure_fref_nres)
    )\<close>

  attribute_setup sepref_dbg_norm_fcomp_rule = \<open>Scan.succeed (
      Thm.rule_attribute [] (Context.proof_of #> Sepref_Rules.norm_fcomp_rule)
    )\<close>

  attribute_setup sepref_simplify_precond = \<open>Scan.succeed (
      Thm.rule_attribute [] (Context.proof_of #> Sepref_Rules.simplify_precond)
    )\<close> \<open>Simplify precondition of fref/hfref-theorem\<close>

  attribute_setup FCOMP = Sepref_Rules.fcomp_attrib "Composition of refinement rules"


notepad
begin
thm hn_refine_def[no_vars]
  fix c :: "nat \<Rightarrow> nat \<Rightarrow> nat llM"  and m m'
  assume A: "(uncurry c,uncurry m) \<in> id_assn\<^sup>k *\<^sub>a id_assn\<^sup>d \<rightarrow>\<^sub>a id_assn" 

  term id_assn
  assume B: "(uncurry m, uncurry m') \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nrest_rel" 

  text \<open>@{method solve_attains_sup}\<close>

  thm A[FCOMP B]
end

end
