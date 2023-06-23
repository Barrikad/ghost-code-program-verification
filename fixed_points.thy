theory fixed_points imports "HOL-Cardinals.Cardinal_Order_Relation"
begin

locale Fix_Lim_Ord =
  fixes r :: \<open>'a rel\<close>
  fixes b :: \<open>'b :: complete_lattice\<close>
  assumes WELL: \<open>Well_order r\<close>
    and isLimOrd_r: \<open>isLimOrd r\<close>
    and ab_card: \<open>\<not>(\<exists> f. \<forall> n \<in> Field r. \<exists> x :: 'b. f x = n)\<close> (*there is no surjective function from the lattice to the set of ordinals*)
begin

lemma wo_rel_r: \<open>wo_rel r\<close>
  by (simp add: WELL wo_rel.intro Kleene_iter_lpfp)

definition iterS where \<open>iterS f \<delta> x \<equiv> f x\<close>

definition iterL where \<open>iterL rec n \<equiv> Sup (rec ` underS r n)\<close>

definition iter where 
  \<open>iter f s \<delta> = worecZSL r s (iterS f) iterL \<delta>\<close>

lemma adm_woL_iterL: \<open>adm_woL r iterL\<close>
  unfolding iterL_def wo_rel.adm_woL_def[OF wo_rel_r] by auto

lemma succ_Field: \<open>n \<in> Field r \<Longrightarrow> succ r n \<in> Field r\<close>  
  by (simp add: isLimOrd_r wo_rel.isLimOrd_succ wo_rel_r)

lemma above_Field: \<open>aboveS r n \<noteq> {} \<Longrightarrow> n \<in> Field r\<close> 
  by (meson FieldI1 wo_rel.succ_in_diff wo_rel_r)

lemma iter_zero[simp]: \<open>iter f s (zero r) = s\<close>
  using iter_def wo_rel.worecZSL_zero wo_rel_r adm_woL_iterL by metis 

lemma iter_succ[simp]: \<open>n \<in> Field r \<Longrightarrow> iter f s (succ r n) = f (iter f s n)\<close>
  using iter_def iterS_def wo_rel.worecZSL_succ wo_rel_r adm_woL_iterL wo_rel.isLimOrd_aboveS isLimOrd_r by metis

lemma iter_lim[simp]: \<open>isLim r n \<Longrightarrow> n \<noteq> zero r \<Longrightarrow> iter f s n = Sup (iter f s ` underS r n)\<close>
proof-
  assume \<open>isLim r n\<close> \<open>n \<noteq> zero r\<close>
  have \<open>worecZSL r s (iterS f) iterL n = iterL (worecZSL r s (iterS f) iterL) n\<close>
    using wo_rel.worecZSL_isLim wo_rel_r adm_woL_iterL \<open>isLim r n\<close> \<open>n \<noteq> zero r\<close> by metis
  moreover have \<open>... = Sup (worecZSL r s (iterS f) iterL ` underS r n)\<close>
    using iterL_def by auto
  ultimately show ?thesis 
    by (simp add: iter_def)
qed

lemma prefixes_iter: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>n \<in> Field r \<Longrightarrow> s \<le> p \<Longrightarrow> f p \<le> p \<Longrightarrow> iter f s n \<le> p\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case by simp
next
  case (2 i)
  then have \<open>i \<in> Field r\<close> 
    by (meson WELL well_order_on_domain wo_rel.succ_in_diff wo_rel_r)
  with 2 show ?case 
    using fmono by (metis dual_order.trans iter_succ monoE)
next
  case (3 i)
  then show ?case
    using iter_lim by (simp add: BNF_Least_Fixpoint.underS_Field SUP_least)
qed

lemma mono_chain_iter_succ: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>n \<in> Field r \<Longrightarrow> s \<le> f s \<Longrightarrow> iter f s n \<le> iter f s (succ r n)\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case 
    by simp
next
  case (2 i)
  then have \<open>iter f s i \<le> iter f s (succ r i)\<close>
    by (simp add: above_Field)
  then have \<open>f (iter f s i) \<le> f (iter f s (succ r i))\<close>
    using 2(4) fmono monotoneD by metis
  then show ?case 
    by (simp add: "2.hyps"(1) "2.prems"(1) above_Field)
next
  case (3 i)
  then have *: \<open>iter f s i = Sup (iter f s ` underS r i)\<close> 
    by simp
  then have **: \<open>\<forall> j \<in> underS r i. iter f s j \<le> iter f s i\<close> 
    by (simp add: SUP_upper)
  have \<open>\<forall> j \<in> underS r i. iter f s j \<le> f (iter f s i)\<close>
  proof safe
    fix j
    assume \<open>j \<in> underS r i\<close>
    then have \<open>j \<in> Field r\<close>
      using 3 by (meson BNF_Least_Fixpoint.underS_Field)
    then have \<open>iter f s j \<le> f (iter f s j)\<close>
      using 3 by (simp add: \<open>j \<in> underS r i\<close>)
    have \<open>iter f s j \<le> iter f s i\<close>
      using ** \<open>j \<in> underS r i\<close> by simp
    then have \<open>f (iter f s j) \<le> f (iter f s i)\<close>
      using 3(5) fmono monotoneD by metis
    with \<open>iter f s j \<le> f (iter f s j)\<close> show \<open>iter f s j \<le> f (iter f s i)\<close> 
      by simp
  qed
  then have \<open>Sup (iter f s ` underS r i) \<le> f (iter f s i)\<close> 
    by (simp add: Sup_le_iff)
  with * show ?case 
    by (simp add: "3.prems"(1))
qed

lemma mono_chain_iter_under: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>m \<in> under r n \<Longrightarrow> s \<le> f s \<Longrightarrow> iter f s m \<le> iter f s n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case 
    by (metis empty_iff order_refl singletonD under_empty wo_rel.under_zero wo_rel_r)
next
  case (2 i)
  then have \<open>m \<in> under r i \<or> m = succ r i\<close> 
    by (metis insertE wo_rel.under_succ wo_rel_r)
  moreover have \<open>iter f s i \<le> iter f s (succ r i)\<close> 
    using 2 above_Field mono_chain_iter_succ fmono by simp
  ultimately show ?case 
    using "2.hyps"(2) "2.prems"(2) by fastforce
next
  case (3 i)
  then show ?case 
    by (metis SUP_upper iter_lim mem_Collect_eq order_class.order_eq_iff underS_I under_def)
qed

lemma reach_fixpoint_succ: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>s \<le> f s \<Longrightarrow> \<exists> n \<in> Field r. iter f s n = iter f s (succ r n)\<close>
proof (rule ccontr)
  assume assms: \<open>s \<le> f s\<close>
  assume \<open>\<not>(\<exists> n \<in> Field r. iter f s n = iter f s (succ r n))\<close>
  then have \<open>\<forall> n \<in> Field r. iter f s n < iter f s (succ r n)\<close>
    using fmono assms mono_chain_iter_succ nless_le by meson
  have \<open>m \<noteq> n \<Longrightarrow> m \<in> underS r n \<Longrightarrow> iter f s m < iter f s n\<close> for m n
  proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case
      by (simp add: wo_rel.underS_zero wo_rel_r)
  next
    case (2 i)
    then show ?case 
      using \<open>\<forall> n \<in> Field r. iter f s n < iter f s (succ r n)\<close> 
      by (metis (no_types, lifting) dual_order.strict_trans local.above_Field underS_E underS_I wo_rel.less_succ wo_rel_r)
  next
    case (3 i)
    then have \<open>succ r m \<in> under r i\<close>
      using underS_subset_under under_def wo_rel.succ_smallest wo_rel_r by fastforce
    then have \<open>iter f s (succ r m) \<le> iter f s i\<close>
      by (simp add: assms fmono mono_chain_iter_under)
    moreover have \<open>iter f s m \<le> iter f s (succ r m)\<close> 
      by (meson fmono BNF_Least_Fixpoint.underS_Field 3(5) assms mono_chain_iter_succ)
    moreover have \<open>m \<in> Field r\<close>  
      by (meson "3.prems"(2) BNF_Least_Fixpoint.underS_Field)
    ultimately show ?case 
      using \<open>\<forall>n\<in>Field r. iter f s n < iter f s (succ r n)\<close> by auto
  qed
  then have \<open>\<forall> n \<in> Field r. \<forall> m \<in> Field r. n \<noteq> m \<longrightarrow> iter f s n \<noteq> iter f s m\<close> 
    by (metis dual_order.irrefl underS_I wo_rel.in_notinI wo_rel_r)
  have \<open>\<forall> n \<in> Field r. \<exists> x :: 'b. (\<lambda> i. THE n. n \<in> Field r \<and> iter f s n = i) x = n\<close> 
  proof 
    fix n
    assume \<open>n \<in> Field r\<close>
    then have \<open>(\<lambda> i. THE n. n \<in> Field r \<and> iter f s n = i) (iter f s n) = n\<close>
      using \<open>\<forall>n\<in>Field r. \<forall>m\<in>Field r. n \<noteq> m \<longrightarrow> iter f s n \<noteq> iter f s m\<close> by auto
    then show \<open>\<exists> x :: 'b. (\<lambda> i. THE n. n \<in> Field r \<and> iter f s n = i) x = n\<close>
      by auto
  qed
  then show False 
    using ab_card by meson
qed

lemma reach_fixpoint_above: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>s \<le> f s \<Longrightarrow> iter f s n = iter f s (succ r n) \<Longrightarrow> n \<in> under r m \<Longrightarrow> iter f s n = iter f s m\<close> 
proof (induct m rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case 
    by (metis emptyE insertE under_empty wo_rel.under_zero wo_rel_r)
next
  case (2 i)
  then show ?case 
    by (metis in_mono insert_iff iter_succ local.above_Field under_Field wo_rel.under_succ wo_rel_r)
next
  case (3 i)
  show ?case
  proof (cases \<open>n = i\<close>)
    case True
    then show ?thesis 
      by simp
  next
    case False
    have \<open>\<forall> j \<in> under r n. iter f s j \<le> iter f s n\<close>
      using 3 fmono mono_chain_iter_under by blast
    moreover have \<open>\<forall> j. n \<in> under r j \<and> j \<in> underS r i \<longrightarrow> iter f s n = iter f s j\<close>
      using 3 by fast
    moreover have \<open>\<forall> j \<in> underS r i. j \<in> underS r n \<or> n \<in> under r j\<close> 
      by (metis (no_types, lifting) "3.prems"(3) isLimOrd_r subsetD underS_I underS_subset_under 
          under_Field wo_rel.TOTALS wo_rel.isLimOrd_aboveS wo_rel.succ_diff wo_rel.succ_in wo_rel.underS_succ wo_rel_r)
    ultimately have \<open>\<forall> x \<in> {iter f s j | j. j \<in> underS r i}. x \<le> iter f s n\<close> 
      using in_mono mem_Collect_eq order_refl underS_subset_under by fastforce
    moreover have \<open>iter f s n \<in> {iter f s j | j. j \<in> underS r i}\<close> 
      using False by (metis (mono_tags, lifting) "3.prems"(3) mem_Collect_eq underS_I under_def)
    moreover have \<open>iter f s i = Sup {iter f s j | j. j \<in> underS r i}\<close> 
      by (simp add: "3.hyps"(1) "3.hyps"(2) Setcompr_eq_image)
    ultimately show ?thesis 
      by (metis (mono_tags, lifting) Sup_least Sup_upper order_antisym_conv)
  qed
qed

definition Fix\<delta> where \<open>Fix\<delta> f s = (SOME n. n \<in> Field r \<and> iter f s n = iter f s (succ r n))\<close>

definition Fix where \<open>Fix f s \<equiv> iter f s (Fix\<delta> f s)\<close>

lemma Fix_in_Field_and_fixed: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>s \<le> f s \<Longrightarrow> Fix\<delta> f s \<in> Field r \<and> iter f s (Fix\<delta> f s) = iter f s (succ r (Fix\<delta> f s))\<close>
proof-
  let ?n = \<open>SOME n. n \<in> Field r \<and> iter f s n = iter f s (succ r n)\<close>
  assume \<open>s \<le> f s\<close>
  then have \<open>\<exists> n. n \<in> Field r \<and> iter f s n = iter f s (succ r n)\<close>
    using reach_fixpoint_succ fmono by blast
  then have \<open>?n \<in> Field r \<and> iter f s ?n = iter f s (succ r ?n)\<close>
    by (metis (mono_tags, lifting) some_eq_imp)
  then show ?thesis 
    unfolding Fix\<delta>_def by meson
qed

lemma Fix_is_fixed: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>s \<le> f s \<Longrightarrow> Fix f s = f (Fix f s)\<close>
  unfolding Fix_def using fmono Fix_in_Field_and_fixed iter_succ by metis

lemma Fix_is_least: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>s \<le> f s \<Longrightarrow> s \<le> x \<Longrightarrow> x = f x \<Longrightarrow> Fix f s \<le> x\<close>
proof-
  assume \<open>s \<le> f s\<close> \<open>s \<le> x\<close> \<open>x = f x\<close>
  then have \<open>iter f s (Fix\<delta> f s) \<le> x\<close>
    using fmono Fix_in_Field_and_fixed by (metis order_refl prefixes_iter)
  then show ?thesis
    unfolding Fix_def by simp
qed

lemma Fix_meet: 
  assumes \<open>mono (f :: 'b \<Rightarrow> 'b)\<close> \<open>s \<le> f s\<close> \<open>mono g\<close> \<open>s \<le> g s\<close> \<open>mono h\<close> \<open>s \<le> h s\<close>
    and \<open>\<forall> n. inf (iter f s n) (iter g s n) \<le> iter h s n\<close>
  shows \<open>inf (Fix f s) (Fix g s) \<le> Fix h s\<close>
proof-
  let ?m2 = \<open>max2 r (Fix\<delta> g s) (Fix\<delta> h s)\<close>
  let ?m = \<open>max2 r (Fix\<delta> f s) ?m2\<close>
  have xField: \<open>Fix\<delta> f s \<in> Field r\<close> 
    using \<open>mono f\<close> \<open>s \<le> f s\<close> by (simp add: Fix_in_Field_and_fixed)
  moreover have yField: \<open>Fix\<delta> g s \<in> Field r\<close> 
    using \<open>mono g\<close> \<open>s \<le> g s\<close> by (simp add: Fix_in_Field_and_fixed)
  moreover have zField: \<open>Fix\<delta> h s \<in> Field r\<close> 
    using \<open>mono h\<close> \<open>s \<le> h s\<close> by (simp add: Fix_in_Field_and_fixed)
  ultimately have mField: \<open>?m \<in> Field r\<close> 
    by (simp add: wo_rel.max2_def wo_rel_r)
  have m2Field: \<open>?m2 \<in> Field r\<close>
    using yField zField by (simp add: wo_rel.max2_def wo_rel_r)

  have xmax: \<open>Fix\<delta> f s \<in> under r ?m\<close>
    by (metis (full_types) Diff_insert_absorb Refl_under_in m2Field subset_Diff_insert under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r xField)

  have ymax: \<open>Fix\<delta> g s \<in> under r ?m\<close>
  proof-
    have \<open>Fix\<delta> g s \<in> under r ?m2\<close> 
      by (meson Refl_under_in in_mono under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater wo_rel_r yField zField)
    moreover have \<open>?m2 \<in> under r ?m\<close> 
      by (meson Refl_under_in in_mono m2Field under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r xField)
    ultimately show ?thesis
      by (meson WELL in_mono m2Field under_mono wo_rel.max2_greater_among wo_rel_r xField)
  qed

  have zmax: \<open>Fix\<delta> h s \<in> under r ?m\<close>
  proof-
    have \<open>Fix\<delta> h s \<in> under r ?m2\<close> 
      by (meson Refl_under_in in_mono under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater wo_rel_r yField zField)
    moreover have \<open>?m2 \<in> under r ?m\<close> 
      by (meson Refl_under_in in_mono m2Field under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r xField)
    ultimately show ?thesis
      by (meson WELL in_mono m2Field under_mono wo_rel.max2_greater_among wo_rel_r xField)
  qed

  from assms have \<open>inf (iter f s ?m) (iter g s ?m) \<le> iter h s ?m\<close> 
    by simp
  moreover have \<open>Fix f s = iter f s ?m\<close> 
    unfolding Fix_def using xmax reach_fixpoint_above Fix_in_Field_and_fixed assms  by blast
  moreover have \<open>Fix g s = iter g s ?m\<close>
    unfolding Fix_def using ymax reach_fixpoint_above Fix_in_Field_and_fixed assms  by blast
  moreover have \<open>Fix h s = iter h s ?m\<close>
    unfolding Fix_def using zmax reach_fixpoint_above Fix_in_Field_and_fixed assms  by blast
  ultimately show ?thesis 
    by simp
qed

lemma Fix_is_lfp: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>Fix f bot = lfp f\<close>
proof-
  have \<open>bot \<le> f bot\<close> 
    by simp
  moreover have \<open>bot \<le> lfp f\<close>
    by simp
  moreover have \<open>lfp f = f (lfp f)\<close> 
    by (simp add: def_lfp_unfold fmono)
  ultimately have \<open>Fix f bot = f (Fix f bot) \<and> Fix f bot \<le> lfp f\<close>
    using fmono Fix_is_fixed Fix_is_least by simp
  then show ?thesis 
    by (simp add: dual_order.eq_iff lfp_lowerbound)
qed

lemma iter_induct_lfp: \<open>mono (f :: 'b \<Rightarrow> 'b) \<Longrightarrow> (\<And> n. P (iter f bot n)) \<Longrightarrow> P (lfp f)\<close> 
  by (metis Fix_def Fix_is_lfp)

text \<open>corresponding theory for gfp\<close>

definition IterL where \<open>IterL rec n \<equiv> Inf (rec ` underS r n)\<close>

definition Iter where 
  \<open>Iter f s \<delta> = worecZSL r s (iterS f) IterL \<delta>\<close>

lemma adm_woL_IterL: \<open>adm_woL r IterL\<close>
  unfolding IterL_def wo_rel.adm_woL_def[OF wo_rel_r] by auto

lemma Iter_zero[simp]: \<open>Iter f s (zero r) = s\<close>
  using Iter_def wo_rel.worecZSL_zero wo_rel_r adm_woL_IterL by metis 

lemma Iter_succ[simp]: \<open>n \<in> Field r \<Longrightarrow> Iter f s (succ r n) = f (Iter f s n)\<close>
  using Iter_def iterS_def wo_rel.worecZSL_succ wo_rel_r adm_woL_IterL wo_rel.isLimOrd_aboveS isLimOrd_r by metis

lemma Iter_lim[simp]: \<open>isLim r n \<Longrightarrow> n \<noteq> zero r \<Longrightarrow> Iter f s n = Inf (Iter f s ` underS r n)\<close>
proof-
  assume \<open>isLim r n\<close> \<open>n \<noteq> zero r\<close>
  have \<open>worecZSL r s (iterS f) IterL n = IterL (worecZSL r s (iterS f) IterL) n\<close>
    using wo_rel.worecZSL_isLim wo_rel_r adm_woL_IterL \<open>isLim r n\<close> \<open>n \<noteq> zero r\<close> by metis
  moreover have \<open>... = Inf (worecZSL r s (iterS f) IterL ` underS r n)\<close>
    using IterL_def by auto
  ultimately show ?thesis
    by (simp add: Iter_def)
qed

lemma postfixes_iter: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>n \<in> Field r \<Longrightarrow> p \<le> s \<Longrightarrow> p \<le> f p \<Longrightarrow> p \<le> Iter f s n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case by simp
next
  case (2 i)
  then have \<open>i \<in> Field r\<close> 
    by (meson WELL well_order_on_domain wo_rel.succ_in_diff wo_rel_r)
  with 2 show ?case 
    using fmono by (metis dual_order.trans Iter_succ monoE)
next
  case (3 i)
  then show ?case
    by (simp add: BNF_Least_Fixpoint.underS_Field INF_greatest)
qed

lemma mono_chain_Iter_succ: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>n \<in> Field r \<Longrightarrow> s \<ge> f s \<Longrightarrow> Iter f s n \<ge> Iter f s (succ r n)\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case 
    by simp
next
  case (2 i)
  then have \<open>Iter f s i \<ge> Iter f s (succ r i)\<close>
    by (simp add: above_Field)
  then have \<open>f (Iter f s i) \<ge> f (Iter f s (succ r i))\<close>
    using 2(4) fmono monotoneD by metis
  then show ?case 
    by (simp add: "2.hyps"(1) "2.prems"(1) above_Field)
next
  case (3 i)
  then have *: \<open>Iter f s i = Inf (Iter f s ` underS r i)\<close> 
    by simp
  then have **: \<open>\<forall> j \<in> underS r i. Iter f s i \<le> Iter f s j\<close> 
    by (simp add: INF_lower) 
  have \<open>\<forall> j \<in> underS r i. Iter f s j \<ge> f (Iter f s i)\<close>
  proof safe
    fix j
    assume \<open>j \<in> underS r i\<close>
    then have \<open>j \<in> Field r\<close>
      using 3 by (meson BNF_Least_Fixpoint.underS_Field)
    then have \<open>Iter f s j \<ge> f (Iter f s j)\<close>
      using 3 by (simp add: \<open>j \<in> underS r i\<close>)
    have \<open>Iter f s j \<ge> Iter f s i\<close>
      using ** \<open>j \<in> underS r i\<close> by simp
    then have \<open>f (Iter f s j) \<ge> f (Iter f s i)\<close>
      using 3(5) fmono monotoneD by metis
    with \<open>Iter f s j \<ge> f (Iter f s j)\<close> show \<open>Iter f s j \<ge> f (Iter f s i)\<close> 
      by simp
  qed
  then have \<open>Inf (Iter f s ` underS r i) \<ge> f (Iter f s i)\<close> 
    by (simp add: INF_greatest)
  with * show ?case 
    by (simp add: "3.prems"(1))
qed

lemma mono_chain_Iter_under: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>m \<in> under r n \<Longrightarrow> f s \<le> s \<Longrightarrow> Iter f s m \<ge> Iter f s n\<close>
proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case 
    by (metis empty_iff order_refl singletonD under_empty wo_rel.under_zero wo_rel_r)
next
  case (2 i)
  then have \<open>m \<in> under r i \<or> m = succ r i\<close> 
    by (metis insertE wo_rel.under_succ wo_rel_r)
  moreover have \<open>Iter f s i \<ge> Iter f s (succ r i)\<close> 
    using 2 above_Field mono_chain_Iter_succ fmono by simp
  ultimately show ?case 
    using "2.hyps"(2) "2.prems"(2) by fastforce
next
  case (3 i)
  then show ?case 
    by (metis INF_lower Iter_lim mem_Collect_eq order_class.order_eq_iff underS_I under_def)
qed

lemma reach_fixpoint_succ': 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>f s \<le> s \<Longrightarrow> \<exists> n \<in> Field r. Iter f s n = Iter f s (succ r n)\<close>
proof (rule ccontr)
  assume assms: \<open>f s \<le> s\<close>
  assume \<open>\<not>(\<exists> n \<in> Field r. Iter f s n = Iter f s (succ r n))\<close>
  then have \<open>\<forall> n \<in> Field r. Iter f s n > Iter f s (succ r n)\<close> 
    using fmono assms mono_chain_Iter_succ by (metis nless_le)
  have \<open>m \<noteq> n \<Longrightarrow> m \<in> underS r n \<Longrightarrow> Iter f s m > Iter f s n\<close> for m n
  proof (induct n rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case
      by (simp add: wo_rel.underS_zero wo_rel_r)
  next
    case (2 i)
    then show ?case 
      using \<open>\<forall> n \<in> Field r. Iter f s n > Iter f s (succ r n)\<close> 
      by (metis (no_types, lifting) dual_order.strict_trans local.above_Field underS_E underS_I wo_rel.less_succ wo_rel_r)
  next
    case (3 i)
    then have \<open>succ r m \<in> under r i\<close>
      using underS_subset_under under_def wo_rel.succ_smallest wo_rel_r by fastforce
    then have \<open>Iter f s (succ r m) \<ge> Iter f s i\<close>
      by (simp add: assms fmono mono_chain_Iter_under)
    moreover have \<open>Iter f s m \<ge> Iter f s (succ r m)\<close> 
      by (meson fmono BNF_Least_Fixpoint.underS_Field 3(5) assms mono_chain_Iter_succ)
    moreover have \<open>m \<in> Field r\<close>  
      by (meson "3.prems"(2) BNF_Least_Fixpoint.underS_Field)
    ultimately show ?case 
      using \<open>\<forall>n\<in>Field r. Iter f s n > Iter f s (succ r n)\<close> by auto
  qed
  then have \<open>\<forall> n \<in> Field r. \<forall> m \<in> Field r. n \<noteq> m \<longrightarrow> Iter f s n \<noteq> Iter f s m\<close> 
    by (metis dual_order.irrefl underS_I wo_rel.in_notinI wo_rel_r)
  have \<open>\<forall> n \<in> Field r. \<exists> x :: 'b. (\<lambda> i. THE n. n \<in> Field r \<and> Iter f s n = i) x = n\<close> 
  proof 
    fix n
    assume \<open>n \<in> Field r\<close>
    then have \<open>(\<lambda> i. THE n. n \<in> Field r \<and> Iter f s n = i) (Iter f s n) = n\<close>
      using \<open>\<forall>n\<in>Field r. \<forall>m\<in>Field r. n \<noteq> m \<longrightarrow> Iter f s n \<noteq> Iter f s m\<close> by auto
    then show \<open>\<exists> x :: 'b. (\<lambda> i. THE n. n \<in> Field r \<and> Iter f s n = i) x = n\<close>
      by auto
  qed
  then show False 
    using ab_card by meson
qed

lemma reach_fixpoint_above': 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>f s \<le> s \<Longrightarrow> Iter f s n = Iter f s (succ r n) \<Longrightarrow> n \<in> under r m \<Longrightarrow> Iter f s n = Iter f s m\<close> 
proof (induct m rule: wo_rel.well_order_inductZSL[OF wo_rel_r])
  case 1
  then show ?case 
    by (metis emptyE insertE under_empty wo_rel.under_zero wo_rel_r)
next
  case (2 i)
  then show ?case 
    by (metis in_mono insert_iff Iter_succ local.above_Field under_Field wo_rel.under_succ wo_rel_r)
next
  case (3 i)
  show ?case
  proof (cases \<open>n = i\<close>)
    case True
    then show ?thesis 
      by simp
  next
    case False
    have \<open>\<forall> j \<in> under r n. Iter f s j \<ge> Iter f s n\<close>
      using 3 fmono mono_chain_Iter_under by blast
    moreover have \<open>\<forall> j. n \<in> under r j \<and> j \<in> underS r i \<longrightarrow> Iter f s n = Iter f s j\<close>
      using 3 by fast
    moreover have \<open>\<forall> j \<in> underS r i. j \<in> underS r n \<or> n \<in> under r j\<close> 
      by (metis (no_types, lifting) "3.prems"(3) isLimOrd_r subsetD underS_I underS_subset_under 
          under_Field wo_rel.TOTALS wo_rel.isLimOrd_aboveS wo_rel.succ_diff wo_rel.succ_in wo_rel.underS_succ wo_rel_r)
    ultimately have \<open>\<forall> x \<in> {Iter f s j | j. j \<in> underS r i}. x \<ge> Iter f s n\<close> 
      using in_mono mem_Collect_eq order_refl underS_subset_under by fastforce
    moreover have \<open>Iter f s n \<in> {Iter f s j | j. j \<in> underS r i}\<close> 
      using False by (metis (mono_tags, lifting) "3.prems"(3) mem_Collect_eq underS_I under_def)
    moreover have \<open>Iter f s i = Inf {Iter f s j | j. j \<in> underS r i}\<close> 
      by (simp add: "3.hyps"(1) "3.hyps"(2) Setcompr_eq_image)
    ultimately show ?thesis 
      by (metis (mono_tags, lifting) Inf_greatest Inf_lower order_antisym_conv)
  qed
qed

definition FIX\<delta> where \<open>FIX\<delta> f s = (SOME n. n \<in> Field r \<and> Iter f s n = Iter f s (succ r n))\<close>

definition FIX where \<open>FIX f s \<equiv> Iter f s (FIX\<delta> f s)\<close>

lemma FIX_in_Field_and_fixed: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>f s \<le> s \<Longrightarrow> FIX\<delta> f s \<in> Field r \<and> Iter f s (FIX\<delta> f s) = Iter f s (succ r (FIX\<delta> f s))\<close>
proof-
  let ?n = \<open>SOME n. n \<in> Field r \<and> Iter f s n = Iter f s (succ r n)\<close>
  assume \<open>f s \<le> s\<close>
  then have \<open>\<exists> n. n \<in> Field r \<and> Iter f s n = Iter f s (succ r n)\<close>
    using reach_fixpoint_succ' fmono by blast
  then have \<open>?n \<in> Field r \<and> Iter f s ?n = Iter f s (succ r ?n)\<close>
    by (metis (mono_tags, lifting) some_eq_imp)
  then show ?thesis 
    unfolding FIX\<delta>_def by meson
qed

lemma FIX_is_fixed: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>f s \<le> s \<Longrightarrow> FIX f s = f (FIX f s)\<close>
  unfolding FIX_def using fmono FIX_in_Field_and_fixed Iter_succ by metis

lemma FIX_is_greatest: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows\<open>f s \<le> s \<Longrightarrow> x \<le> s \<Longrightarrow> x = f x \<Longrightarrow> x \<le> FIX f s\<close>
proof-
  assume \<open>f s \<le> s\<close> \<open>x \<le> s\<close> \<open>x = f x\<close>
  then have \<open>Iter f s (FIX\<delta> f s) \<ge> x\<close>
    using fmono FIX_in_Field_and_fixed by (metis order_refl postfixes_iter)
  then show ?thesis
    unfolding FIX_def by simp
qed

lemma FIX_is_gfp: 
  assumes fmono: \<open>mono (f :: 'b \<Rightarrow> 'b)\<close>
  shows \<open>FIX f top = gfp f\<close>
proof-
  have \<open>f top \<le> top\<close> 
    by simp
  moreover have \<open>top \<ge> gfp f\<close>
    by simp
  moreover have \<open>gfp f = f (gfp f)\<close> 
    by (simp add: def_gfp_unfold fmono)
  ultimately have \<open>FIX f top = f (FIX f top) \<and> FIX f top \<ge> gfp f\<close>
    using fmono FIX_is_fixed FIX_is_greatest by simp
  then show ?thesis 
    by (simp add: dual_order.eq_iff gfp_upperbound)
qed

lemma Iter_induct_gfp: \<open>mono (f :: 'b \<Rightarrow> 'b) \<Longrightarrow> (\<And> n. P (Iter f top n)) \<Longrightarrow> P (gfp f)\<close> 
  by (metis FIX_def FIX_is_gfp)

lemma Iter_induct_gfp2: \<open>mono (f :: 'b \<Rightarrow> 'b) \<Longrightarrow> mono (g :: 'b \<Rightarrow> 'b) \<Longrightarrow> (\<And> n. P (Iter f top n) (Iter g top n)) \<Longrightarrow> P (gfp f) (gfp g)\<close>
proof-
  assume a: \<open>mono f\<close> \<open>mono g\<close> \<open>\<And> n. P (Iter f top n) (Iter g top n)\<close>
  let ?m = \<open>max2 r (FIX\<delta> f top) (FIX\<delta> g top)\<close>
  have *: \<open>FIX\<delta> f top \<in> Field r\<close> \<open>FIX\<delta> g top \<in> Field r\<close>  
    by (simp_all add: FIX_in_Field_and_fixed a)
  then have \<open>FIX\<delta> f top \<in> under r ?m\<close> 
    by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater wo_rel_r)
  then have **: \<open>Iter f top ?m = gfp f\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp a(1) reach_fixpoint_above' top_greatest)
  have \<open>FIX\<delta> g top \<in> under r ?m\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r)
  then have \<open>Iter g top ?m = gfp g\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp a(2) reach_fixpoint_above' top_greatest)
  with ** show ?thesis 
    using a by metis
qed

lemma Iter_induct_gfp3: \<open>mono (f :: 'b \<Rightarrow> 'b) \<Longrightarrow> mono (g :: 'b \<Rightarrow> 'b) \<Longrightarrow> mono (h :: 'b \<Rightarrow> 'b) \<Longrightarrow> 
  (\<And> n. P (Iter f top n) (Iter g top n) (Iter h top n)) \<Longrightarrow> P (gfp f) (gfp g) (gfp h)\<close>
proof-
  assume a: \<open>mono f\<close> \<open>mono g\<close> \<open>mono h\<close> \<open>\<And> n. P (Iter f top n) (Iter g top n) (Iter h top n)\<close>
  let ?m' = \<open>max2 r (FIX\<delta> g top) (FIX\<delta> h top)\<close>
  let ?m = \<open>max2 r (FIX\<delta> f top) ?m'\<close>
  have *: \<open>FIX\<delta> f top \<in> Field r\<close> \<open>FIX\<delta> g top \<in> Field r\<close> \<open>FIX\<delta> h top \<in> Field r\<close>
    by (simp_all add: FIX_in_Field_and_fixed a)
  then have \<open>?m' \<in> Field r\<close> 
    by (simp add: wo_rel.max2_def wo_rel_r)
  then have \<open>FIX\<delta> f top \<in> under r ?m\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater wo_rel_r)
  then have 1: \<open>Iter f top ?m = gfp f\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp a(1) reach_fixpoint_above' top_greatest)
  have \<open>FIX\<delta> g top \<in> under r ?m'\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r)
  then have \<open>FIX\<delta> g top \<in> under r ?m\<close> 
    by (meson "*"(1) WELL \<open>max2 r (FIX\<delta> g top) (FIX\<delta> h top) \<in> Field r\<close> in_mono under_mono wo_rel.max2_greater_among wo_rel_r) 
  then have 2: \<open>Iter g top ?m = gfp g\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp a(2) reach_fixpoint_above' top_greatest)
  have \<open>FIX\<delta> h top \<in> under r ?m'\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r)
  then have \<open>FIX\<delta> h top \<in> under r ?m\<close> 
    by (meson "*"(1) WELL \<open>max2 r (FIX\<delta> g top) (FIX\<delta> h top) \<in> Field r\<close> in_mono under_mono wo_rel.max2_greater_among wo_rel_r) 
  then have \<open>Iter h top ?m = gfp h\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp a(3) reach_fixpoint_above' top_greatest)
  with 1 2 show ?thesis 
    using a by metis
qed

lemma Iter_iter_induct_gfp3: \<open>mono (f :: 'b \<Rightarrow> 'b) \<Longrightarrow> mono (g :: 'b \<Rightarrow> 'b) \<Longrightarrow> mono (h :: 'b \<Rightarrow> 'b) \<Longrightarrow> 
  (\<And> n. P (iter f bot n) (Iter g top n) (iter h bot n)) \<Longrightarrow> P (lfp f) (gfp g) (lfp h)\<close>
proof-
  assume a: \<open>mono f\<close> \<open>mono g\<close> \<open>mono h\<close> \<open>\<And> n. P (iter f bot n) (Iter g top n) (iter h bot n)\<close>
  let ?m' = \<open>max2 r (FIX\<delta> g top) (Fix\<delta> h bot)\<close>
  let ?m = \<open>max2 r (Fix\<delta> f bot) ?m'\<close>
  have *: \<open>Fix\<delta> f bot \<in> Field r\<close> \<open>FIX\<delta> g top \<in> Field r\<close> \<open>Fix\<delta> h bot \<in> Field r\<close>
    by (simp_all add: FIX_in_Field_and_fixed Fix_in_Field_and_fixed a)
  then have \<open>?m' \<in> Field r\<close> 
    by (simp add: wo_rel.max2_def wo_rel_r)
  then have \<open>Fix\<delta> f bot \<in> under r ?m\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater wo_rel_r)
  then have 1: \<open>iter f bot ?m = lfp f\<close> 
    by (metis Fix_def Fix_in_Field_and_fixed Fix_is_lfp a(1) reach_fixpoint_above bot_least)
  have \<open>FIX\<delta> g top \<in> under r ?m'\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r)
  then have \<open>FIX\<delta> g top \<in> under r ?m\<close> 
    by (meson "*"(1) WELL \<open>?m' \<in> Field r\<close>  in_mono under_mono wo_rel.max2_greater_among wo_rel_r) 
  then have 2: \<open>Iter g top ?m = gfp g\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp a(2) reach_fixpoint_above' top_greatest)
  have \<open>Fix\<delta> h bot \<in> under r ?m'\<close> 
    using * by (meson Refl_under_in subset_iff under_incl_iff wo_rel.REFL wo_rel.TRANS wo_rel.max2_greater_among wo_rel_r)
  then have \<open>Fix\<delta> h bot \<in> under r ?m\<close> 
    by (meson "*"(1) WELL \<open>?m' \<in> Field r\<close> in_mono under_mono wo_rel.max2_greater_among wo_rel_r) 
  then have \<open>iter h bot ?m = lfp h\<close> 
    by (metis Fix_def Fix_in_Field_and_fixed Fix_is_lfp a(3) reach_fixpoint_above bot_least)
  with 1 2 show ?thesis 
    using a by metis
qed

end

locale power_set_Fix_Lim_Ord =
  fixes undefined :: \<open>'a :: complete_lattice\<close>
  assumes infinite_univ: \<open>infinite (UNIV :: 'a set)\<close>
sublocale power_set_Fix_Lim_Ord \<subseteq> Fix_Lim_Ord \<open>|UNIV :: ('a set) set |\<close> \<open>bot :: 'a\<close>
proof
  show \<open>Well_order |UNIV|\<close> 
    by (rule card_of_Well_order)
  have \<open>infinite (UNIV :: ('a set) set )\<close>
    using infinite_univ by (simp add: Finite_Set.finite_set)
  then have \<open>infinite ( Field |UNIV :: ('a set) set| )\<close>
    by simp
  then show \<open>isLimOrd |UNIV :: ('a set) set |\<close> 
    using card_order_infinite_isLimOrd card_of_Card_order by metis
  have \<open>Field |UNIV| = UNIV\<close> 
    by simp
  moreover have \<open>\<nexists>f. \<forall>n :: 'a set. \<exists>x :: 'a. f x = n\<close> 
    by force
  ultimately show \<open>\<nexists>f. \<forall>n\<in>Field |UNIV :: ('a set) set |. \<exists>x :: 'a. f x = n\<close> 
    by simp
qed

end