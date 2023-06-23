theory wp1_incorrectness imports pl1 regular_interpretation fixed_points HOL.Complete_Partial_Order
begin

section \<open>instantiate fixed point theory\<close>


interpretation power_set_Fix_Lim_Ord \<open>{} :: (string \<Rightarrow> int) set\<close>
proof
  have \<open>infinite (UNIV :: (string \<Rightarrow> int) set)\<close> 
    using finite_fun_UNIVD2 infinite_UNIV_char_0 by auto
  then show \<open>infinite (UNIV :: (string \<Rightarrow> int) set set)\<close>
    by (simp add: Finite_Set.finite_set)
qed

lemma xfmax: 
  \<open>x \<in> under ( |UNIV| ) (max2 ( |UNIV| ) x y)\<close>  
  using Field_card_of UNIV_I wo_rel.max2_def Refl_under_in card_of_well_order_on in_mono under_incr wo_rel.REFL wo_rel.TRANS wo_rel_def 
  by metis
lemma yfmax: 
  \<open>y \<in> under ( |UNIV| ) (max2 ( |UNIV| ) x y)\<close> 
  using Field_card_of UNIV_I wo_rel.max2_def Refl_under_in card_of_well_order_on in_mono under_incr wo_rel.REFL wo_rel.TRANS wo_rel_def wo_rel.max2_equals1 
  by metis

lemma fsucc: \<open>mono f \<Longrightarrow> iter f ({} :: (string \<Rightarrow> int) set) (Fix\<delta> f {}) = iter f {} (succ ( |UNIV| ) (Fix\<delta> f {}))\<close> 
  using Fix_in_Field_and_fixed by simp

lemma fmax: \<open>mono f \<Longrightarrow> iter f {} (Fix\<delta> f {}) = 
    iter f {} (max2 ( |UNIV| ) (Fix\<delta> f ({} :: (string \<Rightarrow> int) set)) n)\<close>
  using fsucc xfmax reach_fixpoint_above by (metis empty_subsetI)
lemma gmax: \<open>mono g \<Longrightarrow> iter g {} (Fix\<delta> g {}) = 
    iter g {} (max2 ( |UNIV| ) n (Fix\<delta> g ({} :: (string \<Rightarrow> int) set)))\<close>
  using fsucc yfmax reach_fixpoint_above by (metis empty_subsetI)


section \<open>weakest precondition\<close>

fun wpst where (*weakest postcondition for total incorrectness*)
  \<open>wpst p (Assert r) = p \<inter> {i. i \<^bold>\<Turnstile> r}\<close> |
  \<open>wpst p (Var x) = {i. \<exists> v. i(x := v) \<in> p}\<close> |
  \<open>wpst p (Assign x a) = (\<lambda> i. i(x := i\<lparr>a\<rparr>)) ` p\<close> |
  \<open>wpst p (Choice s1 s2) = wpst p s1 \<union> wpst p s2\<close> |
  \<open>wpst p (Seq s1 s2) = wpst (wpst p s1) s2\<close> |
  \<open>wpst p (If b s1 s2) = wpst (p \<inter> {i. i \<^bold>\<Turnstile> b}) s1 \<union> wpst (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2\<close> | 
  \<open>wpst p (While b I s) = (\<Union> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p) \<inter> {i. \<not>i \<^bold>\<Turnstile> b}\<close> | 
  \<open>wpst p (Ghost s) = wpst p s\<close>

lemma wpst_mono: \<open>mono (\<lambda> q. wpst q s)\<close>
proof (rule monoI, induct rule: wpst.induct)
  case (4 p s1 s2)
  then show ?case 
    by (simp add: le_supI1 le_supI2)
next
  case (6 p b s1 s2)
  then have \<open>(x \<inter> {i. i \<^bold>\<Turnstile> b}) \<subseteq> (y \<inter> {i. i \<^bold>\<Turnstile> b})\<close> \<open>(x \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) \<subseteq> (y \<inter> {i. \<not>i \<^bold>\<Turnstile> b})\<close> 
    by auto
  then have \<open>wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s1 \<subseteq> wpst (y \<inter> {i. i \<^bold>\<Turnstile> b}) s1\<close> \<open>wpst (x \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2 \<subseteq> wpst (y \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2\<close>
    using 6 by auto
  then show ?case 
    by auto
next
  case (7 p b I s)
  have \<open>((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) x \<subseteq> ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) y\<close> for n
  proof (induct n)
    case 0
    then show ?case 
      using 7 by simp
  next
    case (Suc n)
    let ?x = \<open>((\<lambda>x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) x\<close>
    let ?y = \<open>((\<lambda>x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) y\<close>
    from Suc have \<open>?x \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> ?y \<inter> {i. i \<^bold>\<Turnstile> b}\<close> 
      by auto
    then have \<open>wpst (?x \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> wpst (?y \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close>
      using 7 by auto
    then have \<open>?x \<union> wpst (?x \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> ?y \<union> wpst (?y \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close>
      using Suc by auto
    then show ?case 
      by auto
  qed
  then show ?case 
    by auto
qed auto


primrec erase_ghost where
  \<open>erase_ghost (Assert b) = Assert b\<close> |
  \<open>erase_ghost (Var x) = Var x\<close> |
  \<open>erase_ghost (Assign x a) = Assign x a\<close> |
  \<open>erase_ghost (Choice s1 s2) = Choice (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (Seq s1 s2) = Seq (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (If b s1 s2) = If b (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (While b I s) = While b I (erase_ghost s)\<close> |
  \<open>erase_ghost (Ghost s) = Assign (''x'') (V ''x'')\<close> (*needed to change definition of skip because of assert_check*)


primrec gc_check where 
  \<open>gc_check g (Assert b) = True\<close> |
  \<open>gc_check g (Var x) = g x\<close> |
  \<open>gc_check g (Assign x a) = g x\<close> |
  \<open>gc_check g (Choice s1 s2) = (gc_check g s1 \<and> gc_check g s2)\<close> |
  \<open>gc_check g (Seq s1 s2) = (gc_check g s1 \<and> gc_check g s2)\<close> |
  \<open>gc_check g (If b s1 s2) = (gc_check g s1 \<and> gc_check g s2)\<close> | 
  \<open>gc_check g (While b I s) = (gc_check g s)\<close> |
  \<open>gc_check g (Ghost s) = gc_check g s\<close>

lemma gc_check_lemma: \<open>gc_check g s \<Longrightarrow> regular_s g q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> wpst p s \<subseteq> q\<close> 
proof (induct s arbitrary: p q)
  case (Var x)
  {
    fix i v
    assume \<open>i(x := v) \<in> p\<close>
    then have \<open>i (x := v) \<in> q\<close>
      using Var by auto
    then have \<open>i \<in> q\<close> 
      using Var(1,2) by (simp add: regular_alt)
  }
  then show ?case 
    by auto
next
  case (Assign x a)
  {
    fix i
    assume \<open>i \<in> p\<close>
    then have \<open>i \<in> q\<close>
      using Assign by auto
    then have \<open>i(x := i\<lparr>a\<rparr>) \<in> q\<close> 
      using Assign(1,2) by (simp add: regular_alt)
  }
  then show ?case 
    by auto
next
  case (Seq s1 s2)
  then have \<open>wpst p s1 \<subseteq> q\<close>
    by simp
  then have \<open>wpst (wpst p s1) s2 \<subseteq> wpst q s2\<close> 
    using wpst_mono monoD by blast
  moreover have \<open>... \<subseteq> q\<close>
    using Seq by simp
  ultimately show ?case 
    by simp
next
  case (If b s1 s2)
  then have \<open>wpst p s1 \<subseteq> q\<close> \<open>wpst p s2 \<subseteq> q\<close>
    by simp_all
  moreover have \<open>wpst (p \<inter> {i. i \<^bold>\<Turnstile> b}) s1 \<subseteq> wpst p s1\<close> \<open>wpst (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2 \<subseteq> wpst p s2\<close>
    using wpst_mono monoD by blast+
  ultimately show ?case
    by auto
next
  case (While b I s)
  have \<open>((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p \<subseteq> q\<close> for n
  proof (induct n)
    case 0
    then show ?case 
      using While by simp
  next
    case (Suc n)
    let ?pn = \<open>((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p\<close>
    from Suc have \<open>?pn \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> q\<close> 
      by auto
    then have \<open>wpst (?pn \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> q\<close>
      using While by simp
    then show ?case
      using Suc by simp
  qed
  then show ?case
    by auto
qed auto

primrec rc_check where
  \<open>rc_check g (Assert b) = regular_p g b\<close> |
  \<open>rc_check g (Var x) = True\<close> |
  \<open>rc_check g (Assign x a) = (\<not>g x \<and> regular_a g a)\<close> |
  \<open>rc_check g (Choice s1 s2) = (rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (Seq s1 s2) = (rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (If b s1 s2) = (regular_p g b \<and> rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (While b I s) = (regular_p g b \<and> rc_check g s)\<close> |
  \<open>rc_check g (Ghost s) = gc_check g s\<close> 

lemma rc_regular: \<open>rc_check g s \<Longrightarrow> regular_s g p \<Longrightarrow> regular_s g (wpst p (erase_ghost s))\<close>
proof (induct s arbitrary: p)
  case (Assert q)
  then show ?case 
    by (metis Int_iff rc_check.simps(1) regular_p_then_regular_s wpst.simps(1) erase_ghost.simps(1))
next
  case (Var x)
  {
    fix i j :: \<open>char list \<Rightarrow> int\<close>
    assume \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> 
    assume \<open>\<exists> v. i(x := v) \<in> p\<close>
    then obtain v where \<open>i(x := v) \<in> p\<close>
      by auto
    moreover have \<open>i(x := v) \<^bold>\<down> g = j(x := v) \<^bold>\<down> g\<close>
      using \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> by (simp add: regular_alt)
    ultimately have \<open>j(x := v) \<in> p\<close> 
      using Var.prems(2) by blast
    then have \<open>\<exists> v. j(x := v) \<in> p\<close> 
      by auto
  }
  then show ?case 
    by auto
next
  case (Assign x a)
  {
    fix i j :: \<open>char list \<Rightarrow> int\<close>
    assume \<open>i \<in> (\<lambda> i. i(x := i\<lparr>a\<rparr>)) ` p\<close>
    then obtain i' where \<open>i' \<in> p\<close> \<open>i'(x := i'\<lparr>a\<rparr>) = i\<close>
      by auto
    moreover assume \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> 
    ultimately have *: \<open>i' \<^bold>\<down> g = j(x := i' x) \<^bold>\<down> g\<close> 
      by (smt (verit) fun_upd_apply regular_alt)
    then have \<open>j(x := i' x) \<in> p\<close>
      using \<open>i' \<in> p\<close> Assign by auto
    with * have \<open>j(x := (j(x := i' x)) \<lparr>a\<rparr>) \<in> (\<lambda> i. i(x := i\<lparr>a\<rparr>)) ` p\<close> 
      using Assign by (metis (mono_tags, lifting) fun_upd_upd image_iff)
    moreover have \<open>j(x := (j(x := i' x)) \<lparr>a\<rparr>) = j\<close>
      using \<open>i'(x := i'\<lparr>a\<rparr>) = i\<close> \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> Assign 
      by (metis (mono_tags, lifting) "*" fun_upd_idem fun_upd_same rc_check.simps(3) regular_agree_aexp regular_alt)
    ultimately have \<open>j \<in> (\<lambda> i. i(x := i\<lparr>a\<rparr>)) ` p\<close> 
      by simp
  }
  then show ?case 
    by auto
next
  case (Seq s1 s2)
  then have \<open>regular_s g (wpst p (erase_ghost s1))\<close> 
    by simp
  then have \<open>regular_s g (wpst (wpst p (erase_ghost s1)) (erase_ghost s2))\<close>
    using Seq by (meson rc_check.simps(5))
  then show ?case 
    by simp
next
  case (Choice s1 s2)
  then have \<open>regular_s g (wpst p (erase_ghost s1))\<close> \<open>regular_s g (wpst p (erase_ghost s2))\<close>
    by auto
  then show ?case 
    by (metis Un_iff erase_ghost.simps(4) wpst.simps(4))
next
  case (If b s1 s2)
  then have \<open>regular_s g (p \<inter> {i. i \<^bold>\<Turnstile> b})\<close> \<open>regular_s g (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b})\<close>
    by (metis Int_Collect rc_check.simps(6) regular_agree_pexp)+
  with If have \<open>regular_s g (wpst (p \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s1))\<close> \<open>regular_s g (wpst (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) (erase_ghost s2))\<close>
    by (smt (verit, best) rc_check.simps(6))+
  moreover have \<open>regular_s g x \<Longrightarrow> regular_s g y \<Longrightarrow> regular_s g (x \<union> y)\<close> for x y :: \<open>(string \<Rightarrow> int) set\<close> 
    by blast
  ultimately show ?case 
    using erase_ghost.simps(6) wpst.simps(6) by presburger
next
  case (While b I s)
  define \<Phi> where \<open>\<Phi> \<equiv> \<lambda> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)) ^^ n) p\<close> 
  have *: \<open>regular_s g (\<Phi> n)\<close> for n 
  proof (induct n)
    case 0
    then show ?case 
      unfolding \<Phi>_def using While by simp
  next
    case (Suc n)
    then have \<open>regular_s g (\<Phi> n \<inter> {i. i \<^bold>\<Turnstile> b})\<close>
      using While by (metis Int_Collect rc_check.simps(7) regular_agree_pexp)
    then have \<open>regular_s g (wpst (\<Phi> n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s))\<close>
      using While rc_check.simps(7) by blast
    then have \<open>regular_s g (\<Phi> n \<union> wpst (\<Phi> n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s))\<close>
      using Suc by auto
    then show ?case 
      unfolding \<Phi>_def by simp
  qed
  {
    fix i j :: \<open>char list \<Rightarrow> int\<close>
    assume \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> 
    assume \<open>i \<in> (\<Union> n. \<Phi> n) \<inter> {i. \<not>i \<^bold>\<Turnstile> b}\<close>
    then obtain n where \<open>i \<in> \<Phi> n\<close> 
      by auto
    then have \<open>j \<in> \<Phi> n\<close>
      using * \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> by simp
    from \<open>i \<in> (\<Union> n. \<Phi> n) \<inter> {i. \<not>i \<^bold>\<Turnstile> b}\<close> have \<open>\<not>i \<^bold>\<Turnstile> b\<close> 
      by simp
    then have \<open>\<not>j \<^bold>\<Turnstile> b\<close>
      using \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> While(2) by (simp add: regular_agree_pexp)
    with \<open>j \<in> \<Phi> n\<close> have \<open>j \<in> (\<Union> n. \<Phi> n) \<inter> {i. \<not>i \<^bold>\<Turnstile> b}\<close> 
      by auto
  }
  then have \<open>regular_s g ((\<Union> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)) ^^ n) p) \<inter> {i. \<not>i \<^bold>\<Turnstile> b})\<close> 
    unfolding \<Phi>_def by blast
  then show ?case 
    using erase_ghost.simps(7) wpst.simps(7) by presburger 
next
  case (Ghost s)
  moreover have \<open>(wpst p (erase_ghost (\<^bold>g s))) = p\<close> 
    by simp
  ultimately show ?case 
    by simp
qed


lemma rc_check_lemma: \<open>rc_check g s \<Longrightarrow> regular_s g q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> wpst p s \<subseteq> wpst q (erase_ghost s)\<close> 
proof (induct s arbitrary: p q)
  case (Seq s1 s2)
  then have \<open>wpst p s1 \<subseteq> wpst q (erase_ghost s1)\<close> 
    by simp
  moreover have \<open>regular_s g (wpst q (erase_ghost s1))\<close> 
    by (meson Seq.prems(1) Seq.prems(2) rc_check.simps(5) rc_regular)
  ultimately show ?case 
    using Seq by simp
next
  case (Choice s1 s2)
  then have \<open>wpst p s1 \<subseteq> wpst q (erase_ghost s1)\<close> \<open>wpst p s2 \<subseteq> wpst q (erase_ghost s2)\<close>
    by simp_all
  then show ?case 
    by auto 
next
  case (If b s1 s2)
  then have \<open>regular_s g (q \<inter> {i. i \<^bold>\<Turnstile> b})\<close> \<open>regular_s g (q \<inter> {i. \<not>i \<^bold>\<Turnstile> b})\<close>
    by (metis Int_Collect rc_check.simps(6) regular_agree_pexp)+
  moreover have \<open>p \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> q \<inter> {i. i \<^bold>\<Turnstile> b}\<close> \<open>p \<inter> {i. \<not>i \<^bold>\<Turnstile> b} \<subseteq> q \<inter> {i. \<not>i \<^bold>\<Turnstile> b}\<close> 
    using If by auto
  moreover have \<open>rc_check g s1\<close> \<open>rc_check g s2\<close>
    using If by simp_all
  ultimately have \<open>wpst (p \<inter> {i. i \<^bold>\<Turnstile> b}) s1 \<subseteq> wpst (q \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s1)\<close> \<open>wpst (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2 \<subseteq> wpst (q \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) (erase_ghost s2)\<close> 
    using If(1,2) by meson+
  then show ?case 
    by auto
next
  case (While b I s)
  let ?\<Phi>p = \<open>\<lambda> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p\<close>
  let ?\<Phi>q = \<open>\<lambda> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)) ^^ n) q\<close>
  have \<open>?\<Phi>p n \<subseteq> ?\<Phi>q n\<close> \<open>regular_s g (?\<Phi>q n)\<close> for n 
  proof (induct n)
    case (Suc n)
    from Suc(2) have *: \<open>regular_s g (?\<Phi>q n \<inter> {i. i \<^bold>\<Turnstile> b})\<close>
      using While(2) regular_agree_pexp by fastforce
    then have \<open>regular_s g (wpst (?\<Phi>q n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s))\<close> 
      using While(2) rc_check.simps(7) rc_regular by (smt (verit, best))
    then have \<open>regular_s g (?\<Phi>q n \<union> wpst (?\<Phi>q n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s))\<close>
      using Suc by auto
    then have reg: \<open>regular_s g ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)) (?\<Phi>q  n))\<close> 
      by simp
    {
      case 1
      from Suc have **: \<open>?\<Phi>p n \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> ?\<Phi>q n \<inter> {i. i \<^bold>\<Turnstile> b}\<close>
        by auto
      have ***: \<open>rc_check g s\<close>
        using While(2) by simp
      have \<open>wpst (?\<Phi>p n \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> wpst (?\<Phi>q n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)\<close> 
        using While(1)[OF *** * **] by simp
      then have \<open>?\<Phi>p n \<union> wpst (?\<Phi>p n \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> ?\<Phi>q n \<union> wpst (?\<Phi>q n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)\<close> 
        using Suc by auto
      then show ?case 
        by simp
    next
      case 2
      then show ?case 
        using reg by simp
    }
  qed (simp_all add: While)
  then show ?case 
    by auto
next
  case (Ghost s)
  then show ?case 
    using gc_check_lemma by simp
qed auto

corollary
  assumes \<open>rc_check g s\<close> \<open>regular_s g p\<close> \<open>regular_s g q\<close>
    and \<open>q \<subseteq> wpst p s\<close>
  shows \<open>q \<subseteq> wpst p (erase_ghost s)\<close> 
  using assms rc_check_lemma by fastforce


fun assert_check where 
  \<open>assert_check p (Assert r) = (p \<supseteq> {i. i \<^bold>\<Turnstile> r})\<close> |
  \<open>assert_check p (Var x) = True\<close> |
  \<open>assert_check p (Assign x a) = True\<close> |
  \<open>assert_check p (Choice s1 s2) = (assert_check p s1 \<and> assert_check p s2)\<close> |
  \<open>assert_check p (Seq s1 s2) = (assert_check p s1 \<and> assert_check (wpst p s1) s2)\<close> |
  \<open>assert_check p (If b s1 s2) = (assert_check (p \<inter> {i. i \<^bold>\<Turnstile> b}) s1 \<and> assert_check (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2)\<close> | 
  \<open>assert_check p (While b I s) = assert_check ((\<Union> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p) \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close> | 
  \<open>assert_check p (Ghost s) = assert_check p s\<close>


lemma assert_check_lemma: \<open>rc_check g s \<Longrightarrow> regular_s g q \<Longrightarrow> p \<subseteq> q \<Longrightarrow> assert_check p s \<longrightarrow> assert_check q (erase_ghost s)\<close>
proof (induct s arbitrary: p q)
  case (Seq s1 s2)
  then have \<open>wpst p s1 \<subseteq> wpst q (erase_ghost s1)\<close> 
    by (metis rc_check.simps(5) rc_check_lemma)
  moreover have \<open>regular_s g (wpst q (erase_ghost s1))\<close>
    using Seq by (meson rc_check.simps(5) rc_regular)
  ultimately have \<open>assert_check (wpst p s1) s2 \<longrightarrow> assert_check (wpst q (erase_ghost s1)) (erase_ghost s2)\<close>
    using Seq by simp
  then show ?case 
    using Seq by auto
next
  case (If b s1 s2)
  then have \<open>rc_check g s1\<close>
    by simp
  moreover have \<open>regular_s g (q \<inter> {i. i \<^bold>\<Turnstile> b})\<close> 
    using If regular_agree_pexp by fastforce
  moreover have \<open>p \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> q \<inter> {i. i \<^bold>\<Turnstile> b}\<close>
    using If by auto
  ultimately have *: \<open>assert_check (p \<inter> {i. i \<^bold>\<Turnstile> b}) s1 \<longrightarrow> assert_check (q \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s1)\<close>
    using If(1) by blast
  from If have \<open>rc_check g s2\<close>
    by simp
  moreover have \<open>regular_s g (q \<inter> {i. \<not>i \<^bold>\<Turnstile> b})\<close> 
    using If regular_agree_pexp by fastforce
  moreover have \<open>p \<inter> {i. \<not>i \<^bold>\<Turnstile> b} \<subseteq> q \<inter> {i. \<not>i \<^bold>\<Turnstile> b}\<close>
    using If by auto
  ultimately have \<open>assert_check (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2 \<longrightarrow> assert_check (q \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) (erase_ghost s2)\<close>
    using If(2) by blast
  with * show ?case 
    by simp
next
  case (While b I s)
  define \<Phi>r where \<open>\<Phi>r \<equiv> \<lambda> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p\<close>
  define \<Phi>g where \<open>\<Phi>g \<equiv> \<lambda> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)) ^^ n) q\<close>
  have \<open>\<Phi>r n \<subseteq> \<Phi>g n\<close> \<open>regular_s g (\<Phi>g n)\<close> for n
  proof (induct n)
    case (Suc n)
    from Suc(2) have *: \<open>regular_s g (\<Phi>g n \<inter> {i. i \<^bold>\<Turnstile> b})\<close>
      using While(2) regular_agree_pexp by fastforce
    then have \<open>regular_s g (wpst (\<Phi>g n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s))\<close> 
      using While(2) rc_check.simps(7) rc_regular by (smt (verit, best))
    then have \<open>regular_s g (\<Phi>g n \<union> wpst (\<Phi>g n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s))\<close>
      using Suc by auto
    then have reg: \<open>regular_s g ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)) (\<Phi>g  n))\<close> 
      by simp
    {
      case 1
      from Suc have \<open>\<Phi>r n \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> \<Phi>g n \<inter> {i. i \<^bold>\<Turnstile> b}\<close> 
        by auto
      with * have \<open>wpst (\<Phi>r n \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> wpst (\<Phi>g n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)\<close>
        using While(2) rc_check_lemma rc_check.simps(7) by metis
      then have \<open>\<Phi>r n \<union> wpst (\<Phi>r n \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> \<Phi>g n \<union> wpst (\<Phi>g n \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)\<close>
        using Suc(1) by auto
      then show ?case 
        unfolding \<Phi>r_def \<Phi>g_def by simp
    next
      case 2
      then show ?case 
        using reg unfolding \<Phi>g_def by simp
    }
  qed (auto simp add: While \<Phi>r_def \<Phi>g_def)
  then have *:\<open>(\<Union> n. \<Phi>r n) \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> (\<Union> n. \<Phi>g n) \<inter> {i. i \<^bold>\<Turnstile> b}\<close>
    by auto

  have \<open>rc_check g s\<close> 
    using While by simp
  {
    fix i j :: \<open>char list \<Rightarrow> int\<close>
    assume \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> 
    assume \<open>i \<in> (\<Union> n. \<Phi>g n) \<inter> {i. i \<^bold>\<Turnstile> b}\<close>
    then obtain n where \<open>i \<in> \<Phi>g n\<close> 
      by auto
    then have \<open>j \<in> \<Phi>g n\<close>
      using \<open>regular_s g (\<Phi>g n)\<close> \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> by simp
    from \<open>i \<in> (\<Union> n. \<Phi>g n) \<inter> {i. i \<^bold>\<Turnstile> b}\<close> have \<open>i \<^bold>\<Turnstile> b\<close> 
      by simp
    then have \<open>j \<^bold>\<Turnstile> b\<close>
      using \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> While(2) by (simp add: regular_agree_pexp)
    with \<open>j \<in> \<Phi>g n\<close> have \<open>j \<in> (\<Union> n. \<Phi>g n) \<inter> {i. i \<^bold>\<Turnstile> b}\<close> 
      by auto
  }
  then have **: \<open>regular_s g ((\<Union> n. \<Phi>g n) \<inter> {i. i \<^bold>\<Turnstile> b})\<close> 
    by blast
  have \<open>assert_check ((\<Union> n. \<Phi>r n) \<inter> {i. i \<^bold>\<Turnstile> b}) s \<longrightarrow> assert_check ((\<Union> n. \<Phi>g n) \<inter> {i. i \<^bold>\<Turnstile> b}) (erase_ghost s)\<close>
    using While(1)[OF \<open>rc_check g s\<close> ** *] .
  then show ?case 
    unfolding \<Phi>r_def \<Phi>g_def by simp
qed auto



section \<open>Correspondence to "Incorrectness Logic" by PETER W. O’HEARN\<close>
(*definition of incorrectness triple using my predicate transformer*)
definition \<open>psq p s q \<equiv> wpst p s \<supseteq> q\<close>

lemma empty_under_approximates: \<open>psq p s {}\<close>
  unfolding psq_def by simp

lemma consequence: \<open>p' \<supseteq> p \<Longrightarrow> psq p s q \<Longrightarrow> q \<supseteq> q' \<Longrightarrow> psq p' s q'\<close>
  using wpst_mono monoD unfolding psq_def by blast

lemma disjunction: \<open>psq p1 s q1 \<Longrightarrow> psq p2 s q2 \<Longrightarrow> psq (p1 \<union> p2) s (q1 \<union> q2)\<close>
  using wpst_mono monoD unfolding psq_def by blast

lemma unit: \<open>psq p (Assert \<^bold>\<top>) p\<close>
  unfolding psq_def by simp

lemma sequencing: \<open>psq p s1 q \<Longrightarrow> psq q s2 r \<Longrightarrow> psq p (s1\<^bold>;s2) r\<close>
proof (unfold psq_def wpst.simps)
  assume \<open>q \<subseteq> wpst p s1\<close>
  then have \<open>wpst q s2 \<subseteq> wpst (wpst p s1) s2\<close>
    using wpst_mono monoD by blast
  moreover assume \<open>r \<subseteq> wpst q s2\<close>
  ultimately show \<open>r \<subseteq> wpst (wpst p s1) s2\<close> 
    by simp
qed

lemma choice: \<open>psq p s1 q \<or> psq p s2 q \<Longrightarrow> psq p (s1 \<^bold>[\<^bold>] s2) q\<close>
  unfolding psq_def by auto

lemma assignment: \<open>psq p (x \<^bold>\<leftarrow> a) {i(x := i\<lparr>a\<rparr>) | i. i \<in> p}\<close>
  unfolding psq_def by auto

lemma nondet_assignment: \<open>psq p (Var x) {i. \<exists> v. i(x := v) \<in> p}\<close>
  unfolding psq_def by simp

lemma assert: \<open>psq p (\<^bold>\<turnstile> r) (p \<inter> {i. i \<^bold>\<Turnstile> r})\<close> 
  unfolding psq_def by simp

(*O\<acute>Hearn gives rules for kleene iteration, but not while. The following are my analogous rules*)

lemma while_zero: \<open>psq p (While b I s) (p \<inter> {i. \<not> i \<^bold>\<Turnstile> b})\<close>
proof-
  have \<open>p \<subseteq> ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ 0) p\<close> 
    by simp
  then have \<open>p \<subseteq> (\<Union> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p)\<close> 
    by fast
  then show ?thesis
    unfolding psq_def by auto
qed

lemma while_non_zero: \<open>psq p (If b s (\<^bold>\<turnstile> \<^bold>\<top>)\<^bold>; While b I s) q \<Longrightarrow> psq p (While b I s) q\<close> 
proof (unfold psq_def)
  let ?p = \<open>wpst (p \<inter> {i. i \<^bold>\<Turnstile> b}) s \<union> (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b})\<close>
  have \<open>wpst p (If b s (\<^bold>\<turnstile> \<^bold>\<top>)) = ?p\<close>
    by auto
  have \<open>((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) ?p \<subseteq> ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ (n + 1)) p\<close> for n 
  proof (induct n)
    case (Suc n)
    let ?r = \<open>((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) ?p\<close>
    let ?q = \<open>((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ (n + 1)) p\<close>
    from Suc have \<open>?r \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> ?q \<inter> {i. i \<^bold>\<Turnstile> b}\<close>
      by auto
    then have \<open>wpst (?r \<inter> {i. i \<^bold>\<Turnstile> b}) s \<subseteq> wpst (?q \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close>
      using wpst_mono monoD by blast
    then show ?case 
      using Suc by auto
  qed auto
  then have \<open>(\<Union> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) ?p) \<subseteq> (\<Union> n. ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) p)\<close> 
    by blast
  moreover assume \<open>q \<subseteq> wpst p (If b s (\<^bold>\<turnstile> \<^bold>\<top>)\<^bold>; While b I s)\<close>
  ultimately show \<open>q \<subseteq> wpst p (While b I s)\<close> 
    by auto
qed

lemma backwards_variant: \<open>(\<forall> n :: nat. psq (p n \<inter> {i. i \<^bold>\<Turnstile> b}) s (p (n + 1))) \<Longrightarrow> psq (p 0) (While b I s) ((\<Union> n. p n) \<inter> {i. \<not> i \<^bold>\<Turnstile> b})\<close> 
proof (unfold psq_def)
  assume a: \<open>\<forall>n. p (n + 1) \<subseteq> wpst (p n \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close>
  have \<open>p n \<subseteq> ((\<lambda> x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) (p 0)\<close> for n 
  proof (induct n)
    case (Suc n)
    let ?\<Phi> = \<open>((\<lambda>x. x \<union> wpst (x \<inter> {i. i \<^bold>\<Turnstile> b}) s) ^^ n) (p 0)\<close>
    have *: \<open>p n \<inter> {i. i \<^bold>\<Turnstile> b} \<subseteq> ?\<Phi> \<inter> {i. i \<^bold>\<Turnstile> b}\<close>
      using Suc by auto
    have \<open>p (n + 1) \<subseteq> wpst (p n \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close>
      using a by simp
    moreover have \<open>... \<subseteq> wpst (?\<Phi> \<inter> {i. i \<^bold>\<Turnstile> b}) s\<close>
      using * wpst_mono monoD by blast
    ultimately show ?case
      by auto
  qed auto
  then show \<open>(\<Union> n. p n) \<inter> {i. \<not> i \<^bold>\<Turnstile> b} \<subseteq> wpst (p 0) (While b I s)\<close> 
    by auto
qed

(*O\<acute>Hearn doesn't give a rule for if, but the following can be derived from his encoding*)

lemma \<open>psq (p \<inter> {i. i \<^bold>\<Turnstile> b}) s1 q \<Longrightarrow> psq (p \<inter> {i. i \<^bold>\<Turnstile> b}) (If b s1 s2) q\<close> 
  unfolding psq_def by auto

lemma \<open>psq (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) s2 q \<Longrightarrow> psq (p \<inter> {i. \<not>i \<^bold>\<Turnstile> b}) (If b s1 s2) q\<close>
  unfolding psq_def by auto


end