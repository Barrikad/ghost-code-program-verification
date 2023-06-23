theory regular_interpretation imports pexp
begin


abbreviation \<open>regular_p g p \<equiv> \<forall> v \<in> pexp_fv p. \<not>g v\<close>
abbreviation \<open>regular_a g a \<equiv> \<forall> v \<in> aexp_fv a. \<not>g v\<close>
abbreviation \<open>ghost_b g b \<equiv> \<forall> v \<in> pexp_fv b. g v\<close>
abbreviation \<open>ghost_a g a \<equiv> \<forall> v \<in> aexp_fv a. g v\<close>

lemma regular_asubst: \<open>regular_a g a \<Longrightarrow> regular_a g a' \<Longrightarrow> regular_a g (asubst x a' a)\<close>
  using no_new_fv_asubst by blast
lemma regular_psubst: \<open>regular_p g p \<Longrightarrow> regular_a g a \<Longrightarrow> regular_p g (psubst x a p)\<close> 
  using no_new_fv_psubst by blast

definition regular_interpretation (infix \<open>\<^bold>\<down>\<close> 105) where \<open>i \<^bold>\<down> g \<equiv> { (x,i x) | x. \<not>g x }\<close>

abbreviation ghost_interpretation (infix \<open>\<^bold>\<up>\<close> 105) where \<open>i \<^bold>\<up> g \<equiv> i \<^bold>\<down> (Not \<circ> g)\<close>

lemma regular_agree_aexp: \<open>i \<^bold>\<down> g = j \<^bold>\<down> g \<Longrightarrow> regular_a g a \<Longrightarrow> asem i a = asem j a\<close>
  unfolding regular_interpretation_def by (induct a) auto

lemma regular_agree_pexp: \<open>i \<^bold>\<down> g = j \<^bold>\<down> g \<Longrightarrow> regular_p g p \<Longrightarrow> psem i p = psem j p\<close>
proof (induct p arbitrary: i j g)
  case (Neg b)
  then show ?case 
    by (metis pexp_fv.simps(1) psem.simps(1))
next
  case (Con b1 b2)
  then show ?case
    by (metis UnCI pexp_fv.simps(2) psem.simps(2))
next
  case (Uni x p)
  let ?g = \<open>g(x := False)\<close>
  from Uni have \<open>\<forall> v. (i(x := v)) \<^bold>\<down> ?g = (j(x := v)) \<^bold>\<down> ?g\<close>
    unfolding regular_interpretation_def by fastforce
  moreover have \<open>regular_p ?g p\<close> 
    using Uni by simp
  ultimately have \<open>\<forall> v. psem (i(x := v)) p = psem (j(x := v)) p\<close>
    using Uni by metis
  then show ?case 
    by simp
next
  case (A a p b)
  then show ?case 
    using regular_agree_aexp by simp
qed

lemma agree_pexp_alt: \<open>\<forall> x \<in> pexp_fv p. i x = j x \<Longrightarrow> i \<^bold>\<Turnstile> p = j \<^bold>\<Turnstile> p\<close>
proof-
  assume \<open>\<forall> x \<in> pexp_fv p. i x = j x\<close>
  then have \<open>i \<^bold>\<down> (\<lambda> x. x \<notin> pexp_fv p) = j \<^bold>\<down> (\<lambda> x. x \<notin> pexp_fv p)\<close>
    unfolding regular_interpretation_def by auto
  moreover have \<open>regular_p (\<lambda> x. x \<notin> pexp_fv p) p\<close> 
    by simp
  ultimately show ?thesis 
    using regular_agree_pexp by simp
qed

lemma subsume_regular_imply:
  \<open>regular_p g q \<Longrightarrow> {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> p} \<subseteq> {i \<^bold>\<down> g|i. i \<^bold>\<Turnstile> q} \<Longrightarrow> i \<^bold>\<Turnstile> p \<Longrightarrow> i \<^bold>\<Turnstile> q\<close>
proof-
  assume \<open>{i \<^bold>\<down> g |i. psem i p} \<subseteq> {i \<^bold>\<down> g|i. psem i q}\<close> \<open>psem i p\<close>
  then obtain i' where \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> psem i' q\<close> 
    by auto
  moreover assume \<open>regular_p g q\<close>
  ultimately show \<open>psem i q\<close> 
    using regular_agree_pexp by blast
qed



section \<open>exi form\<close>

definition \<open>exi_form p vs \<equiv> foldr (\<lambda> v r. \<^bold>\<exists> v. r) vs p\<close>

lemma exi_form_binds_vs: \<open>pexp_fv (exi_form p vs) \<inter> (set vs) = {}\<close>
proof (induct vs)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  then show ?case 
    unfolding exi_form_def by auto
qed

lemma exi_form_only_binds: \<open>pexp_fv (exi_form p vs) \<subseteq> pexp_fv p\<close>
  unfolding exi_form_def by (induct vs) auto

lemma exi_form_regular: \<open>set vs = {v \<in> pexp_fv p. g v} \<Longrightarrow> regular_p g (exi_form p vs)\<close>
proof-
  assume \<open>set vs = {v \<in> pexp_fv p. g v}\<close>
  moreover have \<open>finite {v \<in> pexp_fv p. g v}\<close>
    by (simp add: pexp_fv_finite)
  ultimately have \<open>pexp_fv (exi_form p vs) \<inter> {v \<in> pexp_fv p. g v} = {}\<close>
    using exi_form_binds_vs by auto
  then show ?thesis 
    using exi_form_only_binds by auto
qed

lemma exi_form_unwrap:\<open>psem i (exi_form p vs) = (\<exists> i'. (\<forall> w. w \<notin> set vs \<longrightarrow> i w = i' w) \<and> psem i' p)\<close>
proof (induct vs arbitrary: i)
  case Nil
  then show ?case 
    unfolding exi_form_def by auto
next
  case (Cons v vs)
  let ?wrapped = \<open>psem i (exi_form p (v # vs))\<close>
  let ?unwrapped = \<open>(\<exists>i'. (\<forall>w. w \<notin> set (v # vs) \<longrightarrow> i w = i' w) \<and> psem i' p)\<close>
  show ?case 
  proof
    assume ?wrapped
    then have \<open>\<exists> n. psem (i(v := n)) (exi_form p vs)\<close> 
      unfolding exi_form_def by simp
    then show ?unwrapped 
      using Cons by (metis fun_upd_other list.set_intros(1) list.set_intros(2))
  next
    assume ?unwrapped
    then obtain i' where \<open>(\<forall>w. w \<notin> set (v # vs) \<longrightarrow> i w = i' w) \<and> psem i' p \<close> 
      by auto
    then have \<open>(\<forall>w. w \<notin> set vs \<longrightarrow> (i(v := i' v)) w = i' w) \<and> psem i' p\<close>
      by simp
    then have \<open>psem (i(v := i' v)) (exi_form p vs)\<close>
      using Cons by auto
    then have \<open>psem i (\<^bold>\<exists> v. exi_form p vs)\<close> 
      by auto
    then show ?wrapped 
      unfolding exi_form_def by simp
  qed
qed

lemma psem_exi_form_I: \<open>psem i p \<Longrightarrow> psem i (exi_form p vs)\<close> 
  using exi_form_unwrap by auto

lemma regular_alt: \<open>(i \<^bold>\<down> g = i' \<^bold>\<down> g) = (\<forall> w. \<not>g w \<longrightarrow> i w = i' w)\<close>
  unfolding regular_interpretation_def by auto

lemma psem_exi_form_E:
  \<open>set vs = {v \<in> pexp_fv p. g v} \<Longrightarrow> psem i (exi_form p vs) \<Longrightarrow> \<exists> i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> psem i' p\<close> 
proof-
  assume \<open>psem i (exi_form p vs)\<close>
  then obtain i' where \<open>(\<forall> w. w \<notin> set vs \<longrightarrow> i w = i' w) \<and> psem i' p\<close> 
    using exi_form_unwrap by auto
  moreover assume \<open>set vs = {v \<in> pexp_fv p. g v}\<close>
  moreover have \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close>
    using calculation regular_alt by blast
  ultimately show ?thesis 
    by auto
qed

theorem subsumed_iff_exi_implies:
  assumes \<open>set vs = {v \<in> pexp_fv p. g v}\<close> \<open>set ws = {v \<in> pexp_fv q. g v}\<close>
  shows \<open>
    {i \<^bold>\<down> g |i. psem i p} \<subseteq> {i \<^bold>\<down> g |i. psem i q} \<longleftrightarrow> 
    (\<forall> i. psem i (exi_form p vs) \<longrightarrow> psem i (exi_form q ws))\<close> 
      (is \<open>?subsume \<longleftrightarrow> ?exid\<close>)
proof
  assume 1:?subsume
  show ?exid 
  proof (rule, rule)
    fix i
    assume 2:\<open>psem i (exi_form p vs)\<close>
    then obtain i' where i'_def: \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close> \<open>psem i' q\<close>
      using assms(1) psem_exi_form_E 1 by blast
    then have \<open>psem i' (exi_form q ws)\<close>
      using psem_exi_form_I by simp
    moreover have \<open>regular_p g (exi_form q ws)\<close> 
      using assms(2) exi_form_regular by blast
    ultimately show \<open>psem i (exi_form q ws)\<close> 
      using i'_def(1) by (metis regular_agree_pexp)
  qed
next
  assume 1:?exid
  show ?subsume 
  proof (safe)
    fix x i
    assume \<open>psem i p\<close>
    then have \<open>psem i (exi_form q ws)\<close>
      using 1 assms psem_exi_form_I by auto
    then show \<open>\<exists> i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> psem i' q\<close>
      using assms(2) psem_exi_form_E by auto
  qed
qed



section \<open>uni form\<close>

definition \<open>uni_form p vs \<equiv> foldr (\<lambda> v r. \<^bold>\<forall> v. r) vs p\<close>

lemma uni_form_binds_vs: \<open>pexp_fv (uni_form p vs) \<inter> (set vs) = {}\<close>
proof (induct vs)
  case Nil
  then show ?case by simp
next
  case (Cons v vs)
  then show ?case 
    unfolding uni_form_def by auto
qed

lemma uni_form_only_binds: \<open>pexp_fv (uni_form p vs) \<subseteq> pexp_fv p\<close>
  unfolding uni_form_def by (induct vs) auto

lemma uni_form_regular: \<open>set vs = {v \<in> pexp_fv p. g v} \<Longrightarrow> regular_p g (uni_form p vs)\<close>
proof-
  assume \<open>set vs = {v \<in> pexp_fv p. g v}\<close>
  moreover have \<open>finite {v \<in> pexp_fv p. g v}\<close>
    by (simp add: pexp_fv_finite)
  ultimately have \<open>pexp_fv (uni_form p vs) \<inter> {v \<in> pexp_fv p. g v} = {}\<close>
    using uni_form_binds_vs by auto
  then show ?thesis 
    using uni_form_only_binds by auto
qed

lemma uni_form_unwrap:\<open>psem i (uni_form p vs) = (\<forall> i'. (\<forall> w. w \<notin> set vs \<longrightarrow> i w = i' w) \<longrightarrow> psem i' p)\<close>
proof (induct vs arbitrary: i)
  case Nil
  then show ?case 
    unfolding uni_form_def by auto
next
  case (Cons v vs)
  let ?wrapped = \<open>psem i (uni_form p (v # vs))\<close>
  let ?unwrapped = \<open>\<forall> i'. (\<forall> w. w \<notin> set (v # vs) \<longrightarrow> i w = i' w) \<longrightarrow> psem i' p\<close>
  show ?case 
  proof
    assume ?wrapped
    then have \<open>\<forall> n. psem (i(v := n)) (uni_form p vs)\<close> 
      unfolding uni_form_def by simp
    then show ?unwrapped 
      using Cons by (metis fun_upd_other fun_upd_same set_ConsD)
  next
    assume ?unwrapped
    then have \<open>\<forall> i'. (\<forall>w. w \<notin> set vs \<longrightarrow> (i(v := i' v)) w = i' w) \<longrightarrow> psem i' p\<close>
      by simp
    then have \<open>\<forall> i'. psem (i(v := i' v)) (uni_form p vs)\<close>
      using Cons by auto
    then have \<open>psem i (\<^bold>\<forall> v. uni_form p vs)\<close> 
      by auto
    then show ?wrapped 
      unfolding uni_form_def by simp
  qed
qed

lemma psem_uni_form_E: \<open>i \<^bold>\<Turnstile> uni_form p vs \<Longrightarrow> i \<^bold>\<Turnstile> p\<close> 
  using uni_form_unwrap by auto

lemma psem_uni_form_I:
  \<open>set vs = {v \<in> pexp_fv p. g v} \<Longrightarrow> \<forall> i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<longrightarrow> i' \<^bold>\<Turnstile> p \<Longrightarrow> i \<^bold>\<Turnstile> uni_form p vs\<close>  
proof-
  assume \<open>\<forall> i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<longrightarrow> i' \<^bold>\<Turnstile> p\<close>
  moreover assume \<open>set vs = {v \<in> pexp_fv p. g v}\<close>
  ultimately have \<open>\<forall> i'. (\<forall> w. w \<notin> set vs \<longrightarrow> i w = i' w) \<longrightarrow> i' \<^bold>\<Turnstile> p\<close>  
    using regular_alt by (metis (mono_tags, lifting) mem_Collect_eq)
  then show ?thesis
    using uni_form_unwrap by auto
qed

lemma uni_form_split: \<open>i \<^bold>\<Turnstile> uni_form (p \<^bold>\<and> q) vs \<^bold>\<longrightarrow> uni_form p vs \<^bold>\<and> uni_form q vs\<close> 
proof (induct vs)
  case Nil
  then show ?case 
    using uni_form_unwrap by auto
next
  case (Cons a vs)
  then show ?case 
    by (simp add: uni_form_unwrap)
qed

lemma fewer_vs: \<open>set ws \<subseteq> set vs \<Longrightarrow> i \<^bold>\<Turnstile> uni_form p vs \<^bold>\<longrightarrow> uni_form p ws\<close>
  by (metis (no_types, lifting) impsem subset_code(1) uni_form_unwrap)

lemma move_uni_form:
  \<open>set vs \<inter> pexp_fv p = {} \<Longrightarrow> i \<^bold>\<Turnstile> uni_form (p \<^bold>\<longrightarrow> q) vs \<Longrightarrow> i \<^bold>\<Turnstile> p \<^bold>\<longrightarrow> uni_form q vs\<close>
proof (induct vs arbitrary: i)
  case Nil
  then show ?case 
    using uni_form_unwrap by auto
next
  case (Cons v vs)
  then have \<open>\<forall> n. i(v := n) \<^bold>\<Turnstile> uni_form (p \<^bold>\<longrightarrow> q) vs\<close> 
    unfolding uni_form_def by simp
  then have \<open>i \<^bold>\<Turnstile> p \<^bold>\<longrightarrow> (\<^bold>\<forall> v. uni_form q vs)\<close>
    using Cons agreeing_i_pexp by auto
  then show ?case 
    unfolding uni_form_def by simp
qed

abbreviation \<open>g_fv g p \<equiv> SOME vs. set vs = {v \<in> pexp_fv p. g v}\<close>
abbreviation \<open>g_uni_form g p \<equiv> uni_form p (g_fv g p)\<close>
abbreviation \<open>g_exi_form g p \<equiv> exi_form p (g_fv g p)\<close>

lemma vs_exists: \<open>set (g_fv g p) = {v \<in> pexp_fv p. g v}\<close> 
proof-
  have \<open>\<exists> vs. set vs = {v \<in> pexp_fv p. g v}\<close>
    using pexp_fv_finite finite_list by (metis Collect_mem_eq finite_Collect_conjI)
  then show ?thesis 
    by (metis (mono_tags, lifting) someI2)
qed

lemma another_vs: \<open>set vs = {v \<in> pexp_fv p. g v} \<Longrightarrow> i \<^bold>\<Turnstile> uni_form p vs = i \<^bold>\<Turnstile> g_uni_form g p\<close> 
  by (metis (mono_tags, lifting) someI2 uni_form_unwrap)

lemma uni_exi_translate: \<open>i \<^bold>\<Turnstile> uni_form p vs = i \<^bold>\<Turnstile> \<^bold>\<not>exi_form (\<^bold>\<not>p) vs\<close>
  using exi_form_unwrap uni_form_unwrap by auto

lemma subsumed_iff_uni_implies:
  \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>p} \<longleftrightarrow> (\<forall> i. i \<^bold>\<Turnstile> g_uni_form g p \<^bold>\<longrightarrow> q)\<close> 
proof-
  let ?vs = \<open>g_fv g (\<^bold>\<not>p)\<close>
  let ?ws = \<open>g_fv g (\<^bold>\<not>q)\<close>
  have \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>p} \<longleftrightarrow> (\<forall> i. i \<^bold>\<Turnstile> exi_form (\<^bold>\<not>q) ?ws \<longrightarrow> i \<^bold>\<Turnstile> exi_form (\<^bold>\<not>p) ?vs)\<close> 
    using vs_exists subsumed_iff_exi_implies by presburger
  moreover have \<open>... = (\<forall> i. i \<^bold>\<Turnstile> \<^bold>\<not>exi_form (\<^bold>\<not>p) ?vs \<longrightarrow> i \<^bold>\<Turnstile> \<^bold>\<not>exi_form (\<^bold>\<not>q) ?ws)\<close>
    by auto
  moreover have \<open>... = (\<forall> i. i \<^bold>\<Turnstile> uni_form p ?vs \<longrightarrow> i \<^bold>\<Turnstile> uni_form q ?ws)\<close>
    by (simp add: uni_exi_translate)
  ultimately have \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>p} \<longleftrightarrow> (\<forall> i. i \<^bold>\<Turnstile> uni_form p ?vs \<^bold>\<longrightarrow> uni_form q ?ws)\<close>
   using another_vs by auto
  moreover have \<open>... \<longleftrightarrow> (\<forall> i. i \<^bold>\<Turnstile> uni_form p ?vs \<^bold>\<longrightarrow> q)\<close> 
  proof-
    have \<open>set ?ws \<inter> pexp_fv (uni_form p ?vs) = {}\<close> 
    proof (rule ccontr)
      assume \<open>set ?ws \<inter> pexp_fv (uni_form p ?vs) \<noteq> {}\<close>
      then obtain v where \<open>v \<in> pexp_fv (uni_form p ?vs) \<and> g v\<close> 
        using vs_exists by auto
      moreover have \<open>?vs = g_fv g p\<close>
        by auto
      ultimately show False 
        using vs_exists by (metis (full_types) uni_form_regular)
    qed
    then show ?thesis
      by (metis (no_types, lifting) impsem move_uni_form uni_form_unwrap)
  qed
  ultimately show ?thesis
    using another_vs by auto
qed

definition \<open>uni_all p \<equiv> g_uni_form (\<lambda> v. True) p\<close>

lemma uni_all_simp[simp]: \<open>i \<^bold>\<Turnstile> uni_all p = (\<forall> i. i \<^bold>\<Turnstile> p)\<close>
  unfolding uni_all_def
proof (rule, rule)
  fix i'
  obtain vs where vs_def: \<open>set vs = pexp_fv p\<close> 
    using pexp_fv_finite finite_list by blast
  moreover assume \<open>i \<^bold>\<Turnstile> g_uni_form (\<lambda> v. True) p\<close>
  ultimately have *:\<open>i \<^bold>\<Turnstile> uni_form p vs\<close>
    using another_vs by fastforce
  have \<open>pexp_fv (uni_form p vs) = {}\<close>
    using vs_def uni_form_binds_vs uni_form_only_binds by fastforce
  then  have \<open>regular_p (\<lambda> v. True) (uni_form p vs)\<close> 
    by simp
  moreover have \<open>i \<^bold>\<down> (\<lambda> v. True) = i' \<^bold>\<down> (\<lambda> v. True)\<close>
    unfolding regular_interpretation_def by simp
  ultimately have \<open>i' \<^bold>\<Turnstile> uni_form p vs\<close>
    using * regular_agree_pexp by blast
  then show \<open>i' \<^bold>\<Turnstile> p\<close>
    using psem_uni_form_E by blast
next
  assume \<open>\<forall> i. i \<^bold>\<Turnstile> p\<close>
  then show \<open>i \<^bold>\<Turnstile> g_uni_form (\<lambda> v. True) p\<close> 
    by (simp add: uni_form_unwrap)
qed


section \<open>regular sets\<close>

abbreviation \<open>regular_s g s \<equiv> \<forall> i \<in> s. (\<forall> j. i \<^bold>\<down> g = j \<^bold>\<down> g \<longrightarrow> j \<in> s)\<close>

lemma \<open>regular_s g s = ({j. \<exists> i \<in> s. i \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> s)\<close> by auto

lemma regular_p_then_regular_s: \<open>regular_p g p \<Longrightarrow> regular_s g {i. i \<^bold>\<Turnstile> p}\<close> 
  by (metis mem_Collect_eq regular_agree_pexp)

end