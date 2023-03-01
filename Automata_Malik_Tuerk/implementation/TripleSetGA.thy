theory TripleSetGA
imports TripleSetSpec TripleSetByMap
begin

subsection{* finite *}

  lemma tsga_it_implies_finite :
    "triple_set_iterator \<alpha> invar it \<Longrightarrow>
     finite_triple_set \<alpha> invar"
    unfolding finite_triple_set_def triple_set_iterator_def
    by (metis set_iterator_finite)

subsection{* connection to lists *}

  definition tsga_from_list_aux :: 
    "'T \<Rightarrow> ('A,'B,'C,'T) triple_set_add \<Rightarrow> ('A,'B,'C,'T) triple_set_from_list"
    where 
    "tsga_from_list_aux l a ll \<equiv> 
       foldl (\<lambda>l vev. a (fst vev) (fst (snd vev)) (snd (snd vev)) l) l ll"

  definition tsga_from_list :: 
    "('A,'B,'C,'T) triple_set_empty \<Rightarrow> ('A,'B,'C,'T) triple_set_add \<Rightarrow> 
     ('A,'B,'C,'T) triple_set_from_list"
    where 
    "tsga_from_list e a ll \<equiv> tsga_from_list_aux (e ()) a ll"
  
  lemma tsga_from_list_alt_def :
    "tsga_from_list = (\<lambda>emp add. foldl (\<lambda>l (a,b,c). add a b c l)(emp ()))" 
    unfolding tsga_from_list_def[abs_def] tsga_from_list_aux_def split_def by simp

  lemma tsga_from_list_correct:
    fixes \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    assumes "triple_set_empty \<alpha> invar e"
    assumes "triple_set_add \<alpha> invar a"
    shows "triple_set_from_list \<alpha> invar (tsga_from_list e a)"
  proof -
    interpret 
      triple_set_empty \<alpha> invar e + 
      triple_set_add \<alpha> invar a
      by fact+

    {
      fix ll
      have "invar (tsga_from_list e a ll) \<and>
            \<alpha> (tsga_from_list e a ll) = set ll"
        unfolding tsga_from_list_def[abs_def] tsga_from_list_aux_def[abs_def]
        apply (induct ll rule: rev_induct)
          apply (simp add: triple_set_empty_correct)
          apply (simp add: triple_set_add_correct split: prod.split)
      done
    }
    thus ?thesis
      by unfold_locales simp_all
  qed
      
  definition tsga_to_list :: 
    "('A,'B,'C,_,'T) triple_set_it \<Rightarrow> ('A,'B,'C,'T) triple_set_to_list"
    where "tsga_to_list it \<equiv> iterate_to_list \<circ> it"

  lemma tsga_to_list_alt_def :
   "tsga_to_list = (\<lambda>it x. it x (\<lambda>_. True) op # [])"
  unfolding tsga_to_list_def[abs_def] iterate_to_list_def[abs_def] o_def by simp

  lemma tsga_to_list_correct:
    fixes \<alpha> :: "('A,'B,'C,'T) triple_set_\<alpha>"
    assumes it_OK: "triple_set_iterator \<alpha> invar it"
    shows "triple_set_to_list \<alpha> invar (tsga_to_list it)"  
  proof -
    note it_OK' = triple_set_iterator.triple_set_it_correct [OF it_OK]
    note to_list = iterate_to_list_correct [OF it_OK']
    
    from to_list show ?thesis
      unfolding triple_set_to_list_def tsga_to_list_def o_def by simp
  qed


subsection{* image and filter *}

  definition tsga_image_filter where
    "tsga_image_filter e a it f P_a P_b P_c P t =       
      (it::('A,'B,'C,'\<sigma>,'T) triple_set_filter_it) 
            P_a P_b P_c P t (\<lambda>_. True) 
      (\<lambda>vev l. let (v, e, v') = f vev in a v e v' l) (e ())"

  definition tsga_filter where
    "tsga_filter e a it = tsga_image_filter e a it id"

  lemma tsga_image_filter_correct :
    fixes \<alpha>1 :: "('A1,'B1,'C1,'T1) triple_set_\<alpha>"
    fixes \<alpha>2 :: "('A2,'B2,'C2,'T2) triple_set_\<alpha>"
    assumes "triple_set_empty \<alpha>2 invar2 e"
    assumes "triple_set_add \<alpha>2 invar2 a"
    assumes "triple_set_filter_it \<alpha>1 invar1 it"
    shows "triple_set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 (tsga_image_filter e a it)"
  proof
    interpret 
      triple_set_empty \<alpha>2 invar2 e + 
      triple_set_add \<alpha>2 invar2 a +
      triple_set_filter_it \<alpha>1 invar1 it
      by fact+

    fix t P_a P_b P_c P and f :: "('A1 \<times> 'B1 \<times> 'C1) \<Rightarrow> ('A2 \<times> 'B2 \<times> 'C2)"
    assume invar: "invar1 t"

    have it: "set_iterator (it P_a P_b P_c P t)
                    {(a, b, c).(a, b, c) \<in> \<alpha>1 t \<and> P_a a \<and> P_b b \<and> P_c c \<and> P (a, b, c)}" 
      using triple_set_filter_it_correct [of t P_a P_b P_c P, OF invar] .

    let ?I = "\<lambda>S \<sigma>. invar2 \<sigma> \<and> \<alpha>2 \<sigma> = f ` S" 

    have "?I {(a, b, c). (a, b, c) \<in> \<alpha>1 t \<and> P_a a \<and> P_b b \<and> P_c c \<and> P (a, b, c)} 
             (tsga_image_filter e a it f P_a P_b P_c P t)"
      unfolding tsga_image_filter_def
      apply (rule set_iterator_no_cond_rule_insert_P [OF it, where I = "?I"])
      apply (simp_all add: triple_set_empty_correct triple_set_add_correct Let_def split: prod.splits)
    done
    thus "invar2 (tsga_image_filter e a it f P_a P_b P_c P t)"
         "\<alpha>2 (tsga_image_filter e a it f P_a P_b P_c P t) =
          f ` {(a, b, c). (a, b, c) \<in> \<alpha>1 t \<and> P_a a \<and> P_b b \<and> P_c c \<and> P (a, b, c)}" 
      by simp_all
  qed

  lemma tsga_filter_correct :
    fixes \<alpha> :: "('A1,'B1,'C1,'T1) triple_set_\<alpha>"
    assumes e_OK: "triple_set_empty \<alpha> invar e"
    assumes a_OK: "triple_set_add \<alpha> invar a"
    assumes it_OK: "triple_set_filter_it \<alpha> invar it"
    shows "triple_set_filter \<alpha> invar (tsga_filter e a it)"
    using tsga_image_filter_correct [OF e_OK a_OK it_OK]
    unfolding triple_set_filter_def triple_set_image_filter_def tsga_filter_def
    by simp

  definition tsga_image where
    "tsga_image imf f = imf f (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True) (\<lambda>_. True)"

  lemma tsga_image_correct :
    "triple_set_image_filter \<alpha>1 invar1 \<alpha>2 invar2 imf \<Longrightarrow>
     triple_set_image \<alpha>1 invar1 \<alpha>2 invar2 (tsga_image imf)"
  unfolding triple_set_image_filter_def triple_set_image_def tsga_image_def by simp


subsection {* Building the record *}

context tsbm_defs
begin

  definition triple_set_ops where
    "triple_set_ops if_it1 if_it2 if_it3 if2_it1 if2_it2 if2_it3 = \<lparr>
    triple_set_op_\<alpha> = tsbm_\<alpha>,
    triple_set_op_invar = tsbm_invar,
    triple_set_op_empty = tsbm_empty,
    triple_set_op_memb = tsbm_memb,
    triple_set_op_add = tsbm_add,
    triple_set_op_add_Al = tsbm_add_Al,
    triple_set_op_add_Bl = tsbm_add_Bl,
    triple_set_op_add_Cl = tsbm_add_Cl,
    triple_set_op_delete = tsbm_delete,
    triple_set_op_to_list = tsga_to_list (tsbm_it if_it1 if_it2 if_it3),
    triple_set_op_from_list = tsga_from_list tsbm_empty tsbm_add,
    triple_set_op_image_filter = tsga_image_filter tsbm_empty tsbm_add (tsbm_filter_it if2_it1 if2_it2 if2_it3),
    triple_set_op_filter = tsga_filter tsbm_empty tsbm_add (tsbm_filter_it if2_it1 if2_it2 if2_it3),
    triple_set_op_image = tsga_image ((tsga_image_filter tsbm_empty tsbm_add (tsbm_filter_it if2_it1 if2_it2 if2_it3))) \<rparr>"

  lemma triple_set_ops_unfold :
    fixes if_it1 if_it2 if_it3 if2_it1 if2_it2 if2_it3 ts_ops
    defines "ts_ops \<equiv> triple_set_ops if_it1 if_it2 if_it3 if2_it1 if2_it2 if2_it3"
    shows 
      "triple_set_op_\<alpha> ts_ops = tsbm_\<alpha>"
      "triple_set_op_invar ts_ops = tsbm_invar"
      "triple_set_op_empty ts_ops = tsbm_empty"
      "triple_set_op_memb ts_ops = tsbm_memb"
      "triple_set_op_add ts_ops = tsbm_add"
      "triple_set_op_add_Al ts_ops = tsbm_add_Al"
      "triple_set_op_add_Bl ts_ops = tsbm_add_Bl"
      "triple_set_op_add_Cl ts_ops = tsbm_add_Cl"
      "triple_set_op_delete ts_ops = tsbm_delete"
      "triple_set_op_to_list ts_ops = tsga_to_list (tsbm_it if_it1 if_it2 if_it3)"
      "triple_set_op_from_list ts_ops = tsga_from_list tsbm_empty tsbm_add"
      "triple_set_op_image_filter ts_ops = tsga_image_filter tsbm_empty tsbm_add (tsbm_filter_it if2_it1 if2_it2 if2_it3)"
      "triple_set_op_filter ts_ops = tsga_filter tsbm_empty tsbm_add (tsbm_filter_it if2_it1 if2_it2 if2_it3)"
      "triple_set_op_image ts_ops = tsga_image ((tsga_image_filter tsbm_empty tsbm_add (tsbm_filter_it if2_it1 if2_it2 if2_it3)))"
     unfolding ts_ops_def triple_set_ops_def by simp_all

  lemma triple_set_ops_correct :
    assumes if_it1_OK: "map_iteratei m1.\<alpha> m1.invar if_it1"
    assumes if_it2_OK: "map_iteratei m2.\<alpha> m2.invar if_it2"
    assumes if_it3_OK: "set_iteratei s3.\<alpha> s3.invar if_it3"
    assumes if2_it1_OK: "map_iteratei m1.\<alpha> m1.invar if2_it1"
    assumes if2_it2_OK: "map_iteratei m2.\<alpha> m2.invar if2_it2"
    assumes if2_it3_OK: "set_iteratei s3.\<alpha> s3.invar if2_it3"
    shows "StdTripleSet (triple_set_ops if_it1 if_it2 if_it3 if2_it1 if2_it2 if2_it3)"
   unfolding StdTripleSet_def triple_set_ops_def
     apply (simp)
     apply (intro conjI assms 
                tsga_it_implies_finite[of _ _ "tsbm_it if_it1 if_it2 if_it3"]
                tsga_to_list_correct tsbm_empty_correct tsbm_memb_correct
                tsbm_add_correct tsbm_add_Al_correct tsbm_add_Bl_correct tsbm_add_Cl_correct
                tsbm_delete_correct tsga_image_correct tsga_from_list_correct tsga_filter_correct
                tsbm_filter_it_correct tsbm_it_correct tsga_image_filter_correct )
   done
end

end
