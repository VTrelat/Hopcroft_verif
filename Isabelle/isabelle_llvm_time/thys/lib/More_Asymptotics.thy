theory More_Asymptotics
  imports
   "Asymptotics_1D"
   "Asymptotics_2D"
   "HOL-Real_Asymp.Real_Asymp"
begin

(* by Manuel Eberl *)
lemma dlog[asym_bound]:  "(\<lambda>x. real (Discrete.log x)) \<in> \<Theta>(\<lambda>x. ln (real x))"
proof -
  have "(\<lambda>x. real (Discrete.log x))  \<in> \<Theta>(\<lambda>n. real (nat \<lfloor>log 2 (real n)\<rfloor>))"
    by (intro bigthetaI_cong eventually_mono[OF eventually_gt_at_top[of 0]])
       (auto simp: Discrete.log_altdef)
  also have "(\<lambda>n. real (nat \<lfloor>log 2 (real n)\<rfloor>)) \<in> \<Theta>(\<lambda>x. ln (real x))"
    by real_asymp
  finally show ?thesis .
qed

end