theory wp0_soundness imports wp0
begin

section \<open>soundness and completeness of wp wrt. hoare triples\<close>
abbreviation \<open>
  hoare p s q \<equiv> 
  \<forall> i. psem i p \<longrightarrow> Error \<notin> comsem i s \<and> (\<forall> i'. Terminated i' \<in> comsem i s \<longrightarrow> psem i' q)\<close>

lemma comsem_Seq_rule: \<open>
  \<forall> r \<in> comsem i (Seq s1 s2). \<exists> r' \<in> comsem i s1. 
    (r = r' \<and> (r = Error \<or> r = Magic)) \<or> (\<exists> i'. r' = Terminated i' \<and> r \<in> comsem i' s2)\<close>
proof
  fix r
  assume \<open>r \<in> comsem i (Seq s1 s2)\<close>
  then obtain r' where r'_def: \<open>r' \<in> comsem i s1\<close> \<open>r \<in> comres_bind (\<lambda> i. comsem i s2) r'\<close>
    by auto
  then show \<open>\<exists> r' \<in> comsem i s1. (r = r' \<and> (r = Error \<or> r = Magic)) \<or> (\<exists> i'. r' = Terminated i' \<and> r \<in> comsem i' s2)\<close> 
    by (cases r',auto)
qed

lemma hoare_Seq: \<open>hoare p s1 q \<Longrightarrow> hoare q s2 r \<Longrightarrow> hoare p (Seq s1 s2) r\<close> 
  using comsem_Seq_rule by blast

lemma hoare_wp_refl: \<open>hoare (wp q s) s q\<close> 
proof (induct s arbitrary: q)
  case (Assign x1a x2a)
  then show ?case 
    by (metis psubst_iff_psem comres.distinct(1) comres.inject comsem.simps(4) singletonD wp.simps(4))
next
  case (Seq s1 s2)
  then have \<open>hoare (wp (wp q s2) s1) s1 (wp q s2)\<close>
    by blast
  moreover have \<open>hoare (wp q s2) s2 q\<close>
    using Seq by blast
  ultimately have \<open>hoare (wp (wp q s2) s1) (Seq s1 s2) q\<close>
    using hoare_Seq by blast
  then show ?case 
    by simp
next
  case (Choice s1 s2)
  then show ?case 
    by (metis UnE psem.simps(2) comsem.simps(6) wp.simps(5))
qed auto

lemma wp_sound: \<open>verified p s q \<Longrightarrow> hoare p s q\<close>
  using hoare_wp_refl impsem by blast

lemma if_i_valid_then_in_wp:
  \<open>Error \<notin> comsem i s \<and> (\<forall> i'. Terminated i' \<in> comsem i s \<longrightarrow> psem i' q) \<Longrightarrow> psem i (wp q s)\<close>
proof (induct s arbitrary: q i)
  case (Assert x)
  then show ?case 
    by (metis (full_types) psem.simps(2) comsem.simps(1) insertI1 wp.simps(1))
next
  case (Assign x a)
  then have \<open>psem (i(x := asem i a)) q\<close>
    by fastforce
  then show ?case
    by (simp add: psubst_iff_psem)
next
  case (Seq s1 s2)
  then have 1: \<open>\<forall> r \<in> comsem i (Seq s1 s2). r \<noteq> Error \<and> (\<forall>i'. Terminated i' = r \<longrightarrow> psem i' q)\<close>
    by auto
  {
    fix i'
    assume \<open>Terminated i' \<in> comsem i s1\<close>
    then have \<open>\<forall> r \<in> comsem i' s2. r \<in> comsem i (Seq s1 s2)\<close>
      by force
    then have \<open>Error \<notin> comsem i' s2 \<and> (\<forall>i''. Terminated i'' \<in> comsem i' s2 \<longrightarrow> psem i'' q)\<close>
      using 1 comsem_Seq_rule by metis
    then have \<open>psem i' (wp q s2)\<close>
      using Seq(2) by simp
  }
  then show ?case 
    by (metis Seq.hyps(1) Seq.prems UN_I comres_bind.simps(2) comsem.simps(7) singletonI wp.simps(6))
qed auto

lemma wp_is_weakest: \<open>hoare p s q \<Longrightarrow> psem i (p \<^bold>\<longrightarrow> (wp q s))\<close>
  using if_i_valid_then_in_wp by simp

(*soundness and completeness:*)
theorem wp_iff_hoare: \<open>verified p s q = hoare p s q\<close>
  using wp_is_weakest wp_sound by blast

(*
section \<open>wp vs. wp_2\<close>

lemma wp_iff_wp2A: \<open>i \<^bold>\<Turnstile> wp (formalize q) s \<longleftrightarrow> i \<^bold>\<Turnstile> formalize (wp_2.wp q s)\<close> 
proof (induct s arbitrary: q i)
  case (Assume b)
  have \<open>i \<^bold>\<Turnstile> wp (formalize q) (\<^bold>\<stileturn> b) = (\<not>i \<^bold>\<Turnstile> b \<or> (\<forall> p \<in> set q. i \<^bold>\<Turnstile> form_wrap p))\<close> by simp
  moreover have \<open>i \<^bold>\<Turnstile> formalize (wp_2.wp q (\<^bold>\<stileturn> b)) = (\<forall> p \<in> set q. \<not>i \<^bold>\<Turnstile> b \<or> i \<^bold>\<Turnstile> form_wrap p)\<close> by simp
  ultimately show ?case 
    by blast
next
  case (Var x)
  have \<open>i \<^bold>\<Turnstile> wp (formalize q) (Var x) = (\<forall> v. i(x := v) \<^bold>\<Turnstile> formalize q)\<close> by simp
  moreover have \<open>i \<^bold>\<Turnstile> formalize (wp_2.wp q (Var x)) = (\<forall> p \<in> set q. \<forall> v. i(x := v) \<^bold>\<Turnstile> form_wrap p)\<close> by simp
  ultimately show ?case
    by fastforce
next
  case (Assign x a)
  have \<open>i \<^bold>\<Turnstile> wp (formalize q) (x \<^bold>\<leftarrow> a) = (i \<^bold>\<Turnstile> psubst x a (formalize q))\<close> by simp
  moreover have \<open>... = (\<forall> p \<in> set q. i \<^bold>\<Turnstile> psubst x a (form_wrap p))\<close>
    by (induct q) auto
  moreover have \<open>... = (\<forall> p \<in> set q. i \<^bold>\<Turnstile> form_wrap (psubst_list x a p))\<close>
    using subst_form_wrap by simp
  moreover have \<open>... = i \<^bold>\<Turnstile> formalize (wp_2.wp q (x \<^bold>\<leftarrow> a))\<close> 
    by simp
  ultimately show ?case 
    by presburger
next
  case (Seq s1 s2)
  then have \<open>i \<^bold>\<Turnstile> wp (formalize q) s2 = i \<^bold>\<Turnstile> formalize (wp_2.wp q s2)\<close> for i
    by fast
  then have \<open>i \<^bold>\<Turnstile> wp (wp (formalize q) s2) s1 = i \<^bold>\<Turnstile> wp (formalize (wp_2.wp q s2)) s1\<close> for i 
    using post_condition_imp by blast
  moreover have \<open>i \<^bold>\<Turnstile> wp (formalize (wp_2.wp q s2)) s1 = i \<^bold>\<Turnstile> formalize (wp_2.wp (wp_2.wp q s2) s1)\<close> for i
    using Seq by fast
  ultimately show ?case 
    by (metis weakest_precondition.wp.simps(6) wp_2.wp.simps(6))
next
  case (Choice s1 s2)
  have \<open>i \<^bold>\<Turnstile> formalize (ps @ qs) = (i \<^bold>\<Turnstile> formalize ps \<and> i \<^bold>\<Turnstile> formalize qs)\<close> for ps qs
    by (induct ps) auto
  then show ?case 
    using Choice  psem.simps(1) psem.simps(2) weakest_precondition.wp.simps(5) wp_2.wp.simps(5) by presburger
qed auto

lemma wp_iff_wp2B: \<open>i \<^bold>\<Turnstile> wp q s \<longleftrightarrow> i \<^bold>\<Turnstile> formalize (wp_2.wp [[F (\<^bold>\<not>q)]] s)\<close> 
proof-
  have \<open>i \<^bold>\<Turnstile> wp ((\<^bold>\<not>\<^bold>\<not>q \<^bold>\<or> \<^bold>\<bottom>) \<^bold>\<and> \<^bold>\<top>) s \<longleftrightarrow> i \<^bold>\<Turnstile> formalize (wp_2.wp [[F (\<^bold>\<not>q)]] s)\<close>
    using wp_iff_wp2A by force
  moreover have \<open>i \<^bold>\<Turnstile> ((\<^bold>\<not>\<^bold>\<not>q \<^bold>\<or> \<^bold>\<bottom>) \<^bold>\<and> \<^bold>\<top>) = i \<^bold>\<Turnstile> q\<close> for i
    by auto
  ultimately show ?thesis 
    using post_condition_imp by blast
qed *)


end