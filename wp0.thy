theory wp0 imports regular_interpretation pl0
begin

section \<open>weakest precondition\<close>

fun wp where
  \<open>wp q (Assert r) = r \<^bold>\<and> q\<close> |
  \<open>wp q (Assume r) = r \<^bold>\<longrightarrow> q\<close> |
  \<open>wp q (Var x) = Uni x q\<close> |
  \<open>wp q (Assign x a) = psubst x a q\<close> |
  \<open>wp q (Choice s1 s2) = wp q s1 \<^bold>\<and> wp q s2\<close> |
  \<open>wp q (Seq s1 s2) = wp (wp q s2) s1\<close> |
  \<open>wp q (Ghost s) = wp q s\<close>

abbreviation \<open>verified p s q \<equiv> \<forall> i. psem i (p \<^bold>\<longrightarrow> wp q s)\<close>

section \<open>example verifications\<close>

lemma \<open>
  verified 
    (V x \<^bold>> N 0) 
    (Assign x (V x \<^bold>+ N 1)) 
    (V x \<^bold>> N 1)\<close>
  by fastforce

lemma \<open>
  verified
    (\<^bold>\<top>)
    (Choice (Assign x (N 1)) (Assign x (N 2)))
    (N 0 \<^bold>< V x \<^bold>\<and> V x \<^bold>< N 3)\<close> 
  by fastforce

lemma \<open>
  verified
    (N 0 \<^bold>< V x)
    (Seq (Assign x (V x \<^bold>+ N 1)) (Assign x (V x \<^bold>+ N 1)))
    (N 2 \<^bold>< V x)\<close>
  by fastforce

lemma \<open>
  verified
    \<^bold>\<top>
    (Seq (Seq 
      (Ghost (Assign y (V x \<^bold>* V x))) 
      (Ghost (Assume (V y \<^bold>< N 0)))) 
      (Assert \<^bold>\<bottom>))
    \<^bold>\<top>\<close>
  by fastforce

term \<open>Seq (Ghost (Assume (V x \<^bold>> N 0))) (Assert (V x \<^bold>> N 0))\<close>

section \<open>ghost code\<close>

primrec erase_ghost where
  \<open>erase_ghost (Assert b) = Assert b\<close> |
  \<open>erase_ghost (Assume b) = Assume b\<close> |
  \<open>erase_ghost (Var x) = Var x\<close> |
  \<open>erase_ghost (Assign x a) = Assign x a\<close> |
  \<open>erase_ghost (Choice s1 s2) = Choice (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (Seq s1 s2) = Seq (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (Ghost s) = Assert \<^bold>\<top>\<close>

definition \<open>well_formed p s q \<equiv> 
  (\<forall> i. psem i p \<longrightarrow> psem i (wp q s)) \<longrightarrow> (\<forall> i. psem i p \<longrightarrow> psem i (wp q (erase_ghost s)))\<close>

(*the following lemma shows that if one can deduce well-formedness then one can show the validity of any formula*)
proposition validity_by_well_formedness: 
  \<open>well_formed \<^bold>\<top> (Seq (Ghost (Assume \<^bold>\<bottom>)) (Assert p)) \<^bold>\<top> \<Longrightarrow> \<forall> i. psem i p\<close>
  unfolding well_formed_def by simp

(*checks that regular code only uses regular variables*)
primrec rc_pure where
  \<open>rc_pure g (Assert b) = regular_p g b\<close> |
  \<open>rc_pure g (Assume b) = regular_p g b\<close> |
  \<open>rc_pure g (Var x) = (\<not>g x)\<close> |
  \<open>rc_pure g (Assign x a) = ((\<not>g x) \<and> regular_a g a)\<close> |
  \<open>rc_pure g (Choice s1 s2) = (rc_pure g s1 \<and> rc_pure g s2)\<close> |
  \<open>rc_pure g (Seq s1 s2) = (rc_pure g s1 \<and> rc_pure g s2)\<close> |
  \<open>rc_pure g (Ghost s) = True\<close> 

(*first type checkers for ghost-code annotations*)
(*ghost assumptions are here completely disallowed*)
primrec gc_check where 
  \<open>gc_check g (Assert b) = True\<close> |
  \<open>gc_check g (Assume b) = False\<close> |
  \<open>gc_check g (Var x) = True\<close> |
  \<open>gc_check g (Assign x a) = g x\<close> |
  \<open>gc_check g (Choice s1 s2) = (gc_check g s1 \<or> gc_check g s2)\<close> |
  \<open>gc_check g (Seq s1 s2) = (gc_check g s1 \<and> gc_check g s2)\<close> |
  \<open>gc_check g (Ghost s) = gc_check g s\<close>

primrec rc_check where
  \<open>rc_check g (Assert b) = regular_p g b\<close> |
  \<open>rc_check g (Assume b) = regular_p g b\<close> |
  \<open>rc_check g (Var x) = (\<not>g x)\<close> |
  \<open>rc_check g (Assign x a) = ((\<not>g x) \<and> regular_a g a)\<close> |
  \<open>rc_check g (Choice s1 s2) = (rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (Seq s1 s2) = (rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (Ghost s) = gc_check g s\<close> 

lemma rc_pure_implies_regular_wp: \<open>rc_pure g s \<Longrightarrow> regular_p g q \<Longrightarrow> regular_p g (wp q (erase_ghost s))\<close>
proof (induct s arbitrary: q)
  case (Assume x)
  then show ?case 
    using Imp_def by auto
next
  case (Assign x1a x2a)
  then show ?case 
    by (metis erase_ghost.simps(4) rc_pure.simps(4) regular_psubst wp.simps(4))
next
  case (Seq s1 s2)
  then have \<open>regular_p g (wp q (erase_ghost s2))\<close>
    using rc_pure.simps(6) by metis
  then have \<open>regular_p g (wp (wp q (erase_ghost s2)) (erase_ghost s1))\<close>
    using Seq rc_pure.simps(6) by metis
  then show ?case 
    by simp
next
  case (Choice s1 s2)
  then show ?case 
    by (metis Un_iff pexp_fv.simps(2) erase_ghost.simps(5) rc_pure.simps(5) wp.simps(5))
next
  case (Ghost s)
  then show ?case 
    by (simp add: Eql_def Tru_def)
qed auto

lemma post_condition_imp:
  \<open>\<forall> i. psem i p \<longrightarrow> psem i q \<Longrightarrow> \<forall> i. psem i (wp p s) \<longrightarrow> psem i (wp q s)\<close>  
proof (induct s arbitrary: p q)
  case (Assign x1a x2a)
  then show ?case 
    using psubst_iff_psem by auto
next
  case (Seq s1 s2)
  then show ?case 
    using wp.simps(6) by (smt (verit, best))
qed auto

lemma regular_erase: \<open>rc_check g s \<Longrightarrow> regular_p g q \<Longrightarrow> regular_p g (wp q (erase_ghost s))\<close> 
proof (induct s arbitrary: q)
  case (Assume x)
  then show ?case 
    using Imp_def by auto
next
  case (Assign x1a x2a)
  then show ?case 
    by (metis erase_ghost.simps(4) rc_check.simps(4) regular_psubst wp.simps(4))
next
  case (Seq s1 s2)
  then show ?case 
    by (metis erase_ghost.simps(6) rc_check.simps(6) wp.simps(6))
next
  case (Choice s1 s2)
  then have \<open>regular_p g (wp q (erase_ghost s1))\<close> \<open>regular_p g (wp q (erase_ghost s1))\<close> 
    using rc_check.simps(5) by blast+
  then have \<open>regular_p g (wp q (erase_ghost s1) \<^bold>\<and> wp q (erase_ghost s2))\<close> 
    by (metis Choice.hyps(2) Choice.prems(1) Choice.prems(2) UnE pexp_fv.simps(2) rc_check.simps(5))
  then show ?case
    by simp
next
  case (Ghost s)
  then show ?case
    by (simp add: Eql_def Tru_def wfE_min')
qed auto

lemma ghost_code_regular_post_condition: 
  \<open>gc_check g s \<Longrightarrow> regular_p g q \<Longrightarrow> psem i (wp q s) \<Longrightarrow> psem i q\<close> 
proof (induct s arbitrary: q i)
  case (Var x)
  then have \<open>\<forall> v. i(x := v) \<^bold>\<Turnstile> q\<close> 
    by simp
  then show ?case 
    by (metis fun_upd_triv)
next
  case (Assign x1a x2a)
  then show ?case 
    using agreeing_i_pexp psubst_iff_psem by auto
next
  case (Seq s1 s2)
  then show ?case
    by (smt (verit, best) gc_check.simps(6) post_condition_imp wp.simps(6))
qed auto

lemma rc_check_lemma: 
  \<open>rc_check g s \<Longrightarrow> regular_p g q \<Longrightarrow> \<forall> i. psem i (wp q s) \<longrightarrow> psem i (wp q (erase_ghost s))\<close>
proof (induct s arbitrary: q)
  case (Seq s1 s2)
  then have \<open>\<forall> i. psem i (wp q s2) \<longrightarrow> psem i (wp q (erase_ghost s2))\<close> 
    by simp
  then have \<open>\<forall> i. psem i (wp (wp q s2) s1) \<longrightarrow> psem i(wp (wp q (erase_ghost s2)) s1)\<close>
    using post_condition_imp by simp
  moreover have \<open>\<forall> i. psem i (wp (wp q (erase_ghost s2)) s1) \<longrightarrow> psem i (wp (wp q (erase_ghost s2)) (erase_ghost s1))\<close> 
    using Seq regular_erase by force
  ultimately show ?case 
    by simp
next
  case (Ghost s)
  then show ?case 
    using ghost_code_regular_post_condition by simp
qed auto

theorem rc_check_implies_well_formed:
  \<open>rc_check g s \<Longrightarrow> regular_p g p \<Longrightarrow> regular_p g q \<Longrightarrow> well_formed p s q\<close>
  using rc_check_lemma unfolding well_formed_def by simp


section \<open>non-interference and strengthening\<close>

fun gwp where
  \<open>gwp q (Assert r) = q\<close> | (*wp excluding ghost assertions*)
  \<open>gwp q (Assume r) = r \<^bold>\<longrightarrow> q\<close> |
  \<open>gwp q (Var x) = \<^bold>\<forall> x. q\<close> |
  \<open>gwp q (Assign x a) = psubst x a q\<close> |
  \<open>gwp q (Choice s1 s2) = gwp q s1 \<^bold>\<and> gwp q s2\<close> |
  \<open>gwp q (Seq s1 s2) = gwp (gwp q s2) s1\<close> |
  \<open>gwp q (Ghost s) = gwp q s\<close>

lemma wp_implies_gwp: \<open>i \<^bold>\<Turnstile> wp q s \<Longrightarrow> i \<^bold>\<Turnstile> gwp q s\<close>
proof (induct s arbitrary: q i)
  case (Seq s1 s2)
  then show ?case 
    by (smt (verit) gwp.simps(6) post_condition_imp wp.simps(6))
qed auto

lemma post_conditions_imp_gwp: \<open>\<forall> i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> q \<Longrightarrow> \<forall> i. i \<^bold>\<Turnstile> gwp p s \<longrightarrow> i \<^bold>\<Turnstile> gwp q s\<close>
proof (induct s arbitrary: p q)
  case (Assign x1a x2a)
  then show ?case 
    using psubst_iff_psem by auto
next
  case (Seq s1 s2)
  then show ?case 
    by (smt (verit) gwp.simps(6))
qed auto

lemma gwp_fv: \<open>pexp_fv p \<subseteq> pexp_fv q \<Longrightarrow> pexp_fv (gwp p s) \<subseteq> pexp_fv (wp q s)\<close>
proof (induct s arbitrary: p q)
  case (Assign x1a x2a)
  then show ?case 
    using subset_psubst_fv by simp
next
  case (Choice s1 s2)
  then show ?case 
    by (metis Un_mono pexp_fv.simps(2) gwp.simps(5) wp.simps(5))
qed auto

fun rwp where
  \<open>rwp q (Assert r) = r \<^bold>\<and> q\<close> |
  \<open>rwp q (Assume r) = r \<^bold>\<longrightarrow> q\<close> |
  \<open>rwp q (Var x) = \<^bold>\<forall> x. q\<close> |
  \<open>rwp q (Assign x a) = psubst x a q\<close> |
  \<open>rwp q (Choice s1 s2) = rwp q s1 \<^bold>\<and> rwp q s2\<close> |
  \<open>rwp q (Seq s1 s2) = rwp (rwp q s2) s1\<close> |
  \<open>rwp q (Ghost s) = gwp q s\<close>


lemma wp_implies_rwp: \<open>i \<^bold>\<Turnstile> wp q s \<Longrightarrow> i \<^bold>\<Turnstile> rwp q s\<close>
proof (induct s arbitrary: q i)
  case (Seq s1 s2)
  then show ?case 
    by (smt (verit) rwp.simps(6) post_condition_imp wp.simps(6))
next
  case (Ghost s)
  then show ?case 
    using wp_implies_gwp by auto
qed auto

lemma post_conditions_imp_rwp: \<open>\<forall> i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> q \<Longrightarrow> \<forall> i. i \<^bold>\<Turnstile> rwp p s \<longrightarrow> i \<^bold>\<Turnstile> rwp q s\<close>
proof (induct s arbitrary: p q)
  case (Assign x1a x2a)
  then show ?case 
    using psubst_iff_psem by auto
next
  case (Seq s1 s2)
  then show ?case 
    by (smt (verit) rwp.simps(6))
next
  case (Ghost s)
  then show ?case
    using post_conditions_imp_gwp by simp
qed auto

lemma rwp_implies_erased_wp: \<open>i \<^bold>\<Turnstile> rwp q (erase_ghost s) \<Longrightarrow> i \<^bold>\<Turnstile> wp q (erase_ghost s)\<close>
proof (induct s arbitrary: q i)
  case (Seq s1 s2)
  then show ?case
    by (smt (verit, ccfv_threshold) erase_ghost.simps(6) post_condition_imp rwp.simps(6) wp.simps(6))
qed auto


lemma rwp_fv: \<open>pexp_fv p \<subseteq> pexp_fv q \<Longrightarrow> pexp_fv (rwp p s) \<subseteq> pexp_fv (wp q s)\<close>
proof (induct s arbitrary: p q)
  case (Assign x1a x2a)
  then show ?case 
    using subset_psubst_fv by simp
next
  case (Choice s1 s2)
  then show ?case 
    by (metis Un_mono pexp_fv.simps(2) rwp.simps(5) wp.simps(5))
next
  case (Ghost s)
  then show ?case 
    using gwp_fv by simp
qed auto

primrec gc_check' where 
  \<open>gc_check' g q (Assert b) = \<^bold>\<top>\<close> |
  \<open>gc_check' g q (Assume b) = g_uni_form g (b \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> q\<close> |
  \<open>gc_check' g q (Var x) = \<^bold>\<top>\<close> |
  \<open>gc_check' g q (Assign x a) = g_uni_form g (psubst x a q) \<^bold>\<longrightarrow> q\<close> |
  \<open>gc_check' g q (Choice s1 s2) = gc_check' g q s1 \<^bold>\<or> gc_check' g q s2\<close> |
  \<open>gc_check' g q (Seq s1 s2) = g_uni_form g (gc_check' g (gwp q s2) s1) \<^bold>\<and> gc_check' g q s2\<close> |
  \<open>gc_check' g q (Ghost s) = gc_check' g q s\<close>

(*this allows ghost assignments to regular variables in very specific circumstances*)

(*I would argue that the following actually corresponds to human intuitive reasoning about ghost code*)
(*test*)
lemma \<open>\<forall> y. y > (0 :: int) \<longrightarrow> x > 0 \<Longrightarrow> x > 0\<close> 
(*proof is basically that there is a way to make the new assumption true without affecting the other stuff*)
  by (simp add: gt_ex)
lemma \<open>x \<noteq> y \<Longrightarrow> 
  {i \<^bold>\<down> (\<lambda> v. v = y) | i. i \<^bold>\<Turnstile> \<^bold>\<not>(V y \<^bold>> N 0 \<^bold>\<longrightarrow> V x \<^bold>> N 0)} \<supseteq> {i \<^bold>\<down> (\<lambda> v. v = y) | i. i \<^bold>\<Turnstile> \<^bold>\<not>(V x \<^bold>> N 0)}\<close> 
proof (clarify)
  fix i
  assume \<open>x \<noteq> y\<close>
  assume \<open>i \<^bold>\<Turnstile> \<^bold>\<not>V x \<^bold>> N 0\<close>
  then have \<open>i(y := 1) \<^bold>\<Turnstile> \<^bold>\<not>V x \<^bold>> N 0\<close> 
    using \<open>x \<noteq> y\<close> by simp
  moreover have \<open>i(y := 1) \<^bold>\<Turnstile> V y \<^bold>> N 0\<close>
    by simp
  moreover have \<open>i \<^bold>\<down> (\<lambda>v. v = y) = i(y := 1) \<^bold>\<down> (\<lambda>v. v = y)\<close>
    unfolding regular_interpretation_def using \<open>x \<noteq> y\<close> by auto
  ultimately show \<open>\<exists> i'. i \<^bold>\<down> (\<lambda>v. v = y) = i' \<^bold>\<down> (\<lambda>v. v = y) \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>(V y \<^bold>> N 0 \<^bold>\<longrightarrow> V x \<^bold>> N 0)\<close> 
    by fastforce
qed

lemma gc_check'_lemma:
  \<open>i \<^bold>\<Turnstile> gc_check' g q s \<Longrightarrow> i \<^bold>\<Turnstile> \<^bold>\<not>q \<Longrightarrow> \<exists> i'.  i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>(gwp q s)\<close>
proof (induct s arbitrary: q i)
  case (Var x)
  moreover have \<open>i \<^bold>\<Turnstile> \<^bold>\<not>q \<Longrightarrow> \<not>(\<forall> v. (i(x := v)) \<^bold>\<Turnstile> q)\<close> for i 
    by (metis psem.simps(1) fun_upd_triv)
  ultimately show ?case 
    by auto
next
  case (Assume b)
  then have \<open>\<not>i \<^bold>\<Turnstile> g_uni_form g (b \<^bold>\<longrightarrow> q)\<close> 
    by auto
  then have \<open>i \<^bold>\<Turnstile> g_exi_form g (\<^bold>\<not>(b \<^bold>\<longrightarrow> q))\<close> 
    using uni_exi_translate by fastforce
  then show ?case 
    by (metis (mono_tags) psem_exi_form_E gwp.simps(2) vs_exists)
next
  case (Assign x a)
  then have \<open>\<not>i \<^bold>\<Turnstile> g_uni_form g (psubst x a q)\<close>
    by auto
  then have \<open>i \<^bold>\<Turnstile> g_exi_form g (\<^bold>\<not>(psubst x a q))\<close> 
    using uni_exi_translate by fastforce
  then show ?case 
    by (metis (mono_tags) psem_exi_form_E gwp.simps(4) vs_exists)
next
  case (Choice s1 s2)
  consider \<open>i \<^bold>\<Turnstile> gc_check' g q s1\<close> | \<open>i \<^bold>\<Turnstile> gc_check' g q s2\<close> 
    using Choice by force
  then show ?case
  proof cases
    case 1
    then obtain i' where \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>gwp q s1\<close> 
      using Choice by blast
    then show ?thesis 
      by auto
  next
    case 2
    then obtain i' where \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>gwp q s2\<close> 
      using Choice by blast
    then show ?thesis 
      by auto
  qed
next
  case (Seq s1 s2)
  then obtain i' where \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close> \<open>i' \<^bold>\<Turnstile> \<^bold>\<not>gwp q s2\<close> 
    by fastforce
  have \<open>regular_p g (g_uni_form g (gc_check' g (gwp q s2) s1))\<close>
    using uni_form_regular vs_exists by presburger
  moreover have \<open>i \<^bold>\<Turnstile> g_uni_form g (gc_check' g (gwp q s2) s1)\<close>
    using Seq by simp
  ultimately have \<open>i' \<^bold>\<Turnstile> g_uni_form g (gc_check' g (gwp q s2) s1)\<close> 
    using \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close> regular_agree_pexp by blast
  then have \<open>i' \<^bold>\<Turnstile> gc_check' g (gwp q s2) s1\<close>
    using psem_uni_form_E by blast
  then obtain i'' where \<open>i' \<^bold>\<down> g = i'' \<^bold>\<down> g \<and> i'' \<^bold>\<Turnstile> \<^bold>\<not>(gwp (gwp q s2) s1)\<close>
    using Seq \<open>i' \<^bold>\<Turnstile> \<^bold>\<not>gwp q s2\<close> by blast
  then show ?case 
    using \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close> by auto
qed auto

corollary gc_check'_corollary:
  \<open>\<forall> i. i \<^bold>\<Turnstile> gc_check' g q s \<Longrightarrow> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>(gwp q s)} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>q}\<close>
  using gc_check'_lemma by auto

primrec rc_check' where
  \<open>rc_check' g q (Assert b) = regular_p g b\<close> |
  \<open>rc_check' g q (Assume b) = regular_p g b\<close> |
  \<open>rc_check' g q (Var x) = (\<not>g x)\<close> |
  \<open>rc_check' g q (Assign x a) = ((\<not>g x) \<and> regular_a g a)\<close> |
  \<open>rc_check' g q (Choice s1 s2) = (rc_check' g q s1 \<and> rc_check' g q s2)\<close> |
  \<open>rc_check' g q (Seq s1 s2) = (rc_check' g (rwp q s2) s1 \<and> rc_check' g q s2)\<close> |
  \<open>rc_check' g q (Ghost s) = ({i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>(gwp q s)} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>q})\<close> (*can be checked by gc_check' f.ex. *)

lemma rc_check'_implies_rc_pure: \<open>rc_check' g q s \<Longrightarrow> rc_pure g s\<close>
  by (induct s arbitrary: q) auto

lemma pure_check: \<open>rc_pure g s \<Longrightarrow> rc_check' g q (erase_ghost s)\<close>
proof (induct s arbitrary: q)
  case (Ghost s)
  then show ?case 
    by (simp add: Eql_def Tru_def)
qed auto

lemma rc_check'_lemma: 
  assumes \<open>rc_check' g p s\<close> \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>p} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>q}\<close> \<open>regular_p g q\<close>
  shows \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp p s} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s)}\<close>
  using assms
proof (induct s arbitrary: p q)
  case (Assert b)
  then have \<open>{i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>b \<or> i \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>b \<or> i \<^bold>\<Turnstile> \<^bold>\<not>p}\<close> 
    by blast
  then show ?case 
    by simp
next
  case (Assume b)
  have \<open>{i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> b \<and> i \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> b \<and> i \<^bold>\<Turnstile> \<^bold>\<not>p}\<close> 
  proof (clarify)
    fix i
    assume \<open>i \<^bold>\<Turnstile> b\<close> 
    assume \<open>i \<^bold>\<Turnstile> \<^bold>\<not>q\<close>
    then obtain i' where \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>p\<close>
      using Assume by auto
    moreover assume \<open>i \<^bold>\<Turnstile> b\<close> 
    moreover have \<open>i' \<^bold>\<Turnstile> b\<close> 
      using calculation Assume(1) by (metis rc_check'.simps(2) regular_agree_pexp)
    ultimately show \<open>\<exists> i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> b \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>p\<close> 
      by auto
  qed
  then show ?case 
    by simp
next
  case (Var x)
  have \<open>{i \<^bold>\<down> g |i. \<exists> v. i(x := v) \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g |i. \<exists> v. i(x := v) \<^bold>\<Turnstile> \<^bold>\<not>p}\<close>
  proof (clarify)
    fix i v
    assume \<open>i(x := v) \<^bold>\<Turnstile> \<^bold>\<not>q\<close>
    with Var obtain i' where *: \<open>i(x := v) \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>p\<close> 
      by auto
    then have **:\<open>i \<^bold>\<down> g = i'(x := i x) \<^bold>\<down> g\<close> 
      unfolding regular_interpretation_def by force
    have \<open>i' x = v\<close>
      using * Var(1) unfolding regular_interpretation_def by force
    then have\<open>(i'(x := i x))(x := v) \<^bold>\<Turnstile> \<^bold>\<not>p\<close>
      using * by auto
    with ** show \<open>\<exists> i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> (\<exists>v. i'(x := v) \<^bold>\<Turnstile> \<^bold>\<not>p)\<close>
      by blast
  qed
  then show ?case 
    by simp
next
  case (Assign x a)
  have \<open>{i \<^bold>\<down> g |i. i(x := i\<lparr>a\<rparr>) \<^bold>\<Turnstile> \<^bold>\<not>q} \<subseteq> {i \<^bold>\<down> g |i. i(x := i\<lparr>a\<rparr>) \<^bold>\<Turnstile> \<^bold>\<not>p}\<close> 
  proof (clarify)
    fix i
    assume \<open>i(x := i\<lparr> a \<rparr>) \<^bold>\<Turnstile> \<^bold>\<not>q\<close>
    with Assign obtain i' where *: \<open>i(x := i\<lparr> a \<rparr>) \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<^bold>\<Turnstile> \<^bold>\<not>p\<close> 
      by auto
    then have **: \<open>i \<^bold>\<down> g = i'(x := i x) \<^bold>\<down> g\<close> 
      unfolding regular_interpretation_def by force
    then have 1: \<open>i\<lparr>a\<rparr> = (i'(x := i x))\<lparr>a\<rparr>\<close>
      using Assign(1) regular_agree_aexp by simp
    with * Assign(1) have \<open>i' x = i\<lparr>a\<rparr>\<close>
      unfolding regular_interpretation_def by force
    then have \<open>(i'(x := i x))(x := i'(x := i x)\<lparr> a \<rparr>) \<^bold>\<Turnstile> \<^bold>\<not>p\<close>
      using * 1 by (metis fun_upd_triv fun_upd_upd)
    then show \<open>\<exists>i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i'(x := i'\<lparr> a \<rparr>) \<^bold>\<Turnstile> \<^bold>\<not>p\<close> 
      using ** by blast
  qed
  then show ?case 
    using psubst_iff_psem by auto
next
  case (Seq s1 s2)
  then have *: \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp p s2} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s2)}\<close> 
    by auto
  have \<open>regular_p g (wp q (erase_ghost s2))\<close>
    using Seq.prems(1) Seq.prems(3) rc_check'_implies_rc_pure rc_pure.simps(6) rc_pure_implies_regular_wp by blast
  then have \<open>regular_p g (rwp q (erase_ghost s2))\<close>  
    using rwp_fv by blast
  moreover have \<open>rc_check' g (rwp p s2) s1\<close> 
    using Seq by auto
  ultimately have \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp (rwp p s2) s1} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp (rwp q (erase_ghost s2)) (erase_ghost s1)}\<close>
    using Seq(1) * by simp
  then show ?case 
    using Seq.prems(1) by auto
next
  case (Choice s1 s2)
  have 
    \<open>{i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost (s1 \<^bold>[\<^bold>] s2))} \<subseteq> 
      {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s1)} \<union> {i \<^bold>\<down> g |i.  i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s2)}\<close> by auto
  moreover have 
    \<open>{i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s1)} \<subseteq> {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp p s1}\<close>
    \<open>{i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s2)} \<subseteq> {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp p s2}\<close> using Choice by auto
  moreover have 
    \<open>{i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp p s1} \<union> {i \<^bold>\<down> g |i.  i \<^bold>\<Turnstile> \<^bold>\<not>rwp p s2} \<subseteq>
      {i \<^bold>\<down> g |i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp p (s1 \<^bold>[\<^bold>] s2)}\<close> by auto
  ultimately show ?case 
    by (meson Un_subset_iff subset_trans)
next
  case (Ghost s)
  then show ?case 
    by auto
qed

corollary rc_check'_implies_well_formed:
  assumes \<open>rc_check' g q s\<close> \<open>regular_p g p\<close> \<open>regular_p g q\<close>
  shows \<open>well_formed p s q\<close>
proof (unfold well_formed_def, rule)
  assume \<open>\<forall>i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> wp q s\<close>
  then have *:\<open>\<forall>i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> rwp q s\<close> 
    using wp_implies_rwp by auto
  have \<open>\<forall>i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> rwp q (erase_ghost s)\<close> 
  proof (rule, rule, rule ccontr)
    fix i 
    have \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q s} \<supseteq> {i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> \<^bold>\<not>rwp q (erase_ghost s)}\<close>
      using rc_check'_lemma assms(1,3) by simp
    moreover assume \<open>\<not> i \<^bold>\<Turnstile> rwp q (erase_ghost s)\<close>
    ultimately obtain i' where i'_def: \<open>\<not> i' \<^bold>\<Turnstile> rwp q s\<close> \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close>
      by auto
    moreover assume \<open>i \<^bold>\<Turnstile> p\<close>
    ultimately have \<open>i' \<^bold>\<Turnstile> p\<close> 
      using assms(2) regular_agree_pexp by blast
    then show False 
      using i'_def(1) * by simp
  qed
  then show \<open>\<forall>i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> wp q (erase_ghost s)\<close> 
    by (simp add: rwp_implies_erased_wp)
qed

section \<open>rc_check' examples\<close>

(*You can ghost assume false if there is nothing to show*)
lemma \<open>
well_formed 
  (\<^bold>\<top>)
  (
    \<^bold>g \<^bold>\<stileturn> \<^bold>\<bottom>
  )
  (\<^bold>\<top>)\<close>
proof-
  have \<open>rc_check' (\<lambda> x. True) \<^bold>\<top> (\<^bold>g \<^bold>\<stileturn> \<^bold>\<bottom>)\<close> 
    by simp
  then show ?thesis 
    by (simp add: rc_check'_implies_well_formed)
qed


section \<open>Verification patterns\<close>
(*the following shows that you don't need the complicated rc_check' analysis if you use just a single assumption at the fron*)
lemma single_ghost_assumption:
  assumes checked: \<open>rc_check g s\<close>
    and regular: \<open>regular_p g p\<close> \<open>regular_p g q\<close>
    and p_non_interference: \<open>set vs = {v \<in> pexp_fv p. g v}\<close> \<open>\<forall> i. i \<^bold>\<Turnstile> exi_form r vs\<close>
  shows \<open>well_formed p (\<^bold>g \<^bold>\<stileturn> r\<^bold>; s) q\<close> 
proof-
  from p_non_interference have *: \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> r} = {i \<^bold>\<down> g| i. True}\<close>
    by (metis (no_types, lifting) psem_uni_form_E exi_form_def foldr_cong mem_Collect_eq regular(1) uni_form_def)
  {
    assume  \<open>\<forall> i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> r \<longrightarrow> i \<^bold>\<Turnstile> wp q s\<close>
    then have **:\<open>\<forall> i. i \<^bold>\<Turnstile> r \<longrightarrow> i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> wp q (erase_ghost s)\<close>
      using checked regular by (simp add: rc_check_lemma)
    fix i
    obtain i' where i'_def: \<open>i \<^bold>\<down> g = i' \<^bold>\<down> g\<close> \<open>i' \<^bold>\<Turnstile> r\<close>
      using * by blast
    moreover assume \<open>i \<^bold>\<Turnstile> p\<close>
    ultimately have \<open>i' \<^bold>\<Turnstile> p\<close>
      using regular(1) regular_agree_pexp by blast
    then have \<open>i' \<^bold>\<Turnstile> wp q (erase_ghost s)\<close>
      using ** i'_def(2) by simp
    then have \<open>i \<^bold>\<Turnstile> wp q (erase_ghost s)\<close> 
      using i'_def(1) checked regular(2) regular_agree_pexp regular_erase by presburger
  }
  then show ?thesis 
    unfolding well_formed_def by simp
qed

notepad begin (*examples from section Evaluating the Type Checker*)
  (*have \<open>\<exists> x y :: int. x > 1 \<and> y > 1 \<and> x * y = 61190113\<close> *)
  have \<open>((7727 :: int) > 1 \<and> (7919 :: int) > 1 \<and> (7727 :: int) * 7919 = 61190113)\<close>
    by simp
  have \<open>((7727 :: int) > 1 \<and> (7919 :: int) > 1 \<and> (7727 :: int) * 7919 = 61190113) \<longrightarrow> (\<exists> x y :: int. x > 1 \<and> y > 1 \<and> x * y = 61190113)\<close> 
    by fast
  have \<open>(\<forall> i j. \<exists> x y :: int. x > 1 \<and> y > 1 \<and> x * y = 61190113) \<longrightarrow> (\<exists> x y :: int. x > 1 \<and> y > 1 \<and> x * y = 61190113)\<close>
    by simp
end

end