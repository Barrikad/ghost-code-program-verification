theory wp1 imports pl1 regular_interpretation fixed_points HOL.Complete_Partial_Order
begin

section \<open>weakest precondition\<close>

fun wptc where (*weakest precondition for total correctness*)
  \<open>wptc q (Assert r) = {i. i \<in> q \<and> i \<^bold>\<Turnstile> r}\<close> |
  \<open>wptc q (Var x) = {i. \<forall> v. i(x := v) \<in> q}\<close> |
  \<open>wptc q (Assign x a) = {i. i(x := i\<lparr>a\<rparr>) \<in> q}\<close> |
  \<open>wptc q (Choice s1 s2) = wptc q s1 \<inter> wptc q s2\<close> |
  \<open>wptc q (Seq s1 s2) = wptc (wptc q s2) s1\<close> |
  \<open>wptc q (If b s1 s2) = {i. if i \<^bold>\<Turnstile> b then i \<in> wptc q s1 else i \<in> wptc q s2}\<close> |
  \<open>wptc q (While b I s) = lfp (\<lambda> x. {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)})\<close> | 
  \<open>wptc q (Ghost s) = wptc q s\<close>

definition \<open>\<Phi>tc b s q x \<equiv> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>

lemma wp_\<Phi>tc: \<open>wptc q (While b I s) = lfp (\<Phi>tc b s q)\<close> 
  unfolding \<Phi>tc_def by simp

lemma wptc_mono: \<open>mono (\<lambda> q. wptc q s)\<close>
proof (rule monoI, induct rule: wptc.induct)
  case (4 q s1 s2)
  then show ?case 
    by (simp add: le_infI1 le_infI2)
next
  case (6 q b s1 s2)
  show ?case 
  proof
    fix i
    assume *:\<open>i \<in> wptc x (If b s1 s2)\<close>
    show \<open>i \<in> wptc y (If b s1 s2)\<close> 
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then show ?thesis 
        using 6 * by auto
    next
      case False
      then have \<open>wptc x s2 \<subseteq> wptc y s2\<close>
        using 6 by simp
      then show ?thesis 
        using False * by auto
    qed
  qed
next
  case (7 q b I s)
  then have \<open>\<forall> q. \<Phi>tc b s x q \<subseteq> \<Phi>tc b s y q\<close>
    unfolding \<Phi>tc_def by auto
  then have \<open>lfp (\<Phi>tc b s x) \<subseteq> lfp (\<Phi>tc b s y)\<close>
    using lfp_mono by meson
  then show ?case 
    using wp_\<Phi>tc by simp
qed auto

lemma \<Phi>tc_mono: \<open>mono (\<Phi>tc b s q)\<close>
proof (rule monoI)
  fix x y :: \<open>(char list \<Rightarrow> int) set\<close>
  assume \<open>x \<subseteq> y\<close>
  {
    fix i
    assume \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)\<close>
    then have \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc y s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)\<close> 
      using \<open>x \<subseteq> y\<close> wptc_mono monoD by blast
  }
  then show \<open>\<Phi>tc b s q x \<subseteq> \<Phi>tc b s q y\<close> 
    unfolding \<Phi>tc_def by auto
qed

fun wppc where (*weakest precondition for partial correctness*)
  \<open>wppc q (Assert r) = {i. i \<in> q \<and> i \<^bold>\<Turnstile> r}\<close> |
  \<open>wppc q (Var x) = {i. \<forall> v. i(x := v) \<in> q}\<close> |
  \<open>wppc q (Assign x a) = {i. i(x := i\<lparr>a\<rparr>) \<in> q}\<close> |
  \<open>wppc q (Choice s1 s2) = wppc q s1 \<inter> wppc q s2\<close> |
  \<open>wppc q (Seq s1 s2) = wppc (wppc q s2) s1\<close> |
  \<open>wppc q (If b s1 s2) = {i. if i \<^bold>\<Turnstile> b then i \<in> wppc q s1 else i \<in> wppc q s2}\<close> |
  \<open>wppc q (While b I s) = gfp (\<lambda> x. {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)})\<close> | 
  \<open>wppc q (Ghost s) = wptc q s\<close>

definition \<open>\<Phi>pc b s q x \<equiv> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>

lemma wp_\<Phi>pc: \<open>wppc q (While b I s) = gfp (\<Phi>pc b s q)\<close> 
  unfolding \<Phi>pc_def by simp

lemma wppc_mono: \<open>mono (\<lambda> q. wppc q s)\<close>
proof (rule monoI, induct rule: wppc.induct)
  case (4 q s1 s2)
  then show ?case 
    by (simp add: le_infI1 le_infI2)
next
  case (6 q b s1 s2)
  show ?case 
  proof
    fix i
    assume *:\<open>i \<in> wppc x (If b s1 s2)\<close>
    show \<open>i \<in> wppc y (If b s1 s2)\<close> 
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then show ?thesis 
        using 6 * by auto
    next
      case False
      then have \<open>wppc x s2 \<subseteq> wppc y s2\<close>
        using 6 by simp
      then show ?thesis 
        using False * by auto
    qed
  qed
next
  case (7 q b I s)
  then have \<open>\<forall> q. \<Phi>pc b s x q \<subseteq> \<Phi>pc b s y q\<close>
    unfolding \<Phi>pc_def by auto
  then have \<open>gfp (\<Phi>pc b s x) \<subseteq> gfp (\<Phi>pc b s y)\<close>
    using gfp_mono by blast
  then show ?case 
    using wp_\<Phi>pc by simp
next
  case (8 q s)
  then show ?case 
    using wptc_mono by (metis monotoneD wppc.simps(8))
qed auto

lemma wppc_not_continuous: \<open>\<exists> R. R \<noteq> {} \<and> (\<forall> p q. p \<in> R \<and> q \<in> R \<longrightarrow> p \<union> q \<in> R) \<and> (\<Union> r \<in> R. wppc r (Var x)) \<noteq> wppc (\<Union> R) (Var x)\<close> 
proof-
  fix i :: \<open>string \<Rightarrow> int\<close>
  let ?R = \<open>range (\<lambda> v. {i(x := w) | w. w \<le> v})\<close>
  have \<open>?R \<noteq> {}\<close> 
    by simp
  have \<open>(\<forall> p q. p \<in> ?R \<and> q \<in> ?R \<longrightarrow> p \<union> q \<in> ?R)\<close> 
  proof clarify
    fix v1 v2
    have \<open>{i(x := w) |w. w \<le> v1} \<union> {i(x := w) |w. w \<le> v2} = {i(x := w) |w. w \<le> max v1 v2}\<close> 
      by fastforce
    then show \<open>{i(x := w) |w. w \<le> v1} \<union> {i(x := w) |w. w \<le> v2} \<in> range (\<lambda>v. {i(x := w) |w. w \<le> v})\<close>
      by simp
  qed
  moreover have \<open>i \<in> wppc (\<Union> ?R) (Var x)\<close>
    by auto
  moreover have \<open>\<not>i \<in> (\<Union> r \<in> ?R. wppc r (Var x))\<close>
  proof
    assume \<open>i \<in> (\<Union> r \<in> ?R. wppc r (Var x))\<close>
    then obtain v where \<open>i \<in> wppc {i(x := w) | w. w \<le> v} (Var x)\<close> 
      by auto
    have \<open>\<not> v + 1 \<le> v\<close> 
      by auto
    then have \<open>i(x := v + 1) \<notin> {i(x := w) | w. w \<le> v}\<close> 
      using fun_upd_eqD mem_Collect_eq by fastforce
    with \<open>i \<in> wppc {i(x := w) | w. w \<le> v} (Var x)\<close> show False 
      by simp
  qed
  ultimately show ?thesis 
    by blast
qed

lemma \<Phi>pc_mono: \<open>mono (\<Phi>pc b s q)\<close>
proof (rule monoI)
  fix x y :: \<open>(char list \<Rightarrow> int) set\<close>
  assume \<open>x \<subseteq> y\<close>
  {
    fix i
    assume \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)\<close>
    then have \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc y s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)\<close> 
      using \<open>x \<subseteq> y\<close> wppc_mono monoD by blast
  }
  then show \<open>\<Phi>pc b s q x \<subseteq> \<Phi>pc b s q y\<close> 
    unfolding \<Phi>pc_def by auto
qed

lemma wptc_sub_wppc: \<open>p \<subseteq> q \<Longrightarrow> wptc p s \<subseteq> wppc q s\<close> 
proof (induct s arbitrary: p q)
  case (Choice s1 s2)
  then show ?case
    by (simp add: le_infI1 le_infI2)
next
  case (If b s1 s2)
  then have \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc p s1 \<longrightarrow> i \<in> wppc q s1) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc p s2 \<longrightarrow> i \<in> wppc q s2)\<close> for i 
    by (simp add: subset_eq)
  then show ?case 
    by auto
next
  case (While b I s)
  then have \<open>\<forall> x. \<Phi>tc b s p x \<subseteq> \<Phi>pc b s q x\<close> 
    using \<Phi>tc_def \<Phi>pc_def by auto
  then have \<open>lfp (\<Phi>tc b s p) \<subseteq> lfp (\<Phi>pc b s q)\<close> 
    by (simp add: lfp_mono)
  moreover have \<open>... \<subseteq> gfp (\<Phi>pc b s q)\<close>
    using \<Phi>pc_mono by (meson lfp_le_gfp)
  ultimately show ?case
    using wp_\<Phi>pc wp_\<Phi>tc by auto
next
  case (Ghost s)
  then show ?case 
    using wptc_mono monotoneD by (metis wppc.simps(8) wptc.simps(8))
qed auto


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

lemma wp_conjunctive:
  \<open>wppc p s \<inter> wppc q s \<subseteq> wppc (p \<inter> q) s\<close> \<open>wptc p s \<inter> wptc q s \<subseteq> wptc (p \<inter> q) s\<close> 
proof (induct s arbitrary: p q)
  case (Seq s1 s2)
  {
    fix p q
    have 
      \<open>wppc p s2 \<inter> wppc q s2 \<subseteq> wppc (p \<inter> q) s2\<close>
      \<open>wptc p s2 \<inter> wptc q s2 \<subseteq> wptc (p \<inter> q) s2\<close>
      using Seq by auto
    then have 
      \<open>wppc (wppc p s2 \<inter> wppc q s2) s1 \<subseteq> wppc (wppc (p \<inter> q) s2) s1\<close> 
      \<open>wptc (wptc p s2 \<inter> wptc q s2) s1 \<subseteq> wptc (wptc (p \<inter> q) s2) s1\<close> 
      using wppc_mono wptc_mono monotoneD by metis+
    moreover have 
      \<open>wppc (wppc p s2) s1 \<inter> wppc (wppc q s2) s1 \<subseteq> wppc (wppc p s2 \<inter> wppc q s2) s1\<close> 
      \<open>wptc (wptc p s2) s1 \<inter> wptc (wptc q s2) s1 \<subseteq> wptc (wptc p s2 \<inter> wptc q s2) s1\<close> 
      using Seq by auto
    ultimately have *:
      \<open>wppc (wppc p s2) s1 \<inter> wppc (wppc q s2) s1 \<subseteq> wppc (wppc (p \<inter> q) s2) s1\<close> 
      \<open>wptc (wptc p s2) s1 \<inter> wptc (wptc q s2) s1 \<subseteq> wptc (wptc (p \<inter> q) s2) s1\<close> 
      by auto
  }
  then show 
      \<open>wppc p (s1 \<^bold>; s2) \<inter> wppc q (s1 \<^bold>; s2) \<subseteq> wppc (p \<inter> q) (s1 \<^bold>; s2)\<close> 
      \<open>wptc p (s1 \<^bold>; s2) \<inter> wptc q (s1 \<^bold>; s2) \<subseteq> wptc (p \<inter> q) (s1 \<^bold>; s2)\<close> for p q
    by auto
next
  case (Choice s1 s2)
  {
    case 1
    then show ?case 
      using Choice by fastforce
  next
    case 2
    then show ?case 
      using Choice by fastforce
  }
next
  case (If x1a s1 s2)
  {
    case 1
    then show ?case 
      using If by fastforce
  next
    case 2
    then show ?case 
      using If by fastforce
  }
next
  case (While b I s)
  {
    case 1
    {
      fix X Y
      assume \<open>X \<subseteq> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc X s) \<and> (\<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> p)}\<close>
      moreover assume \<open>Y \<subseteq> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc Y s) \<and> (\<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      ultimately have \<open>X \<inter> Y \<subseteq> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc (X \<inter> Y) s) \<and> (\<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> p \<inter> q)}\<close> 
        using While(1) by fast
      then have \<open>X \<inter> Y \<subseteq> \<Union> {x. x \<subseteq> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc x s) \<and> (\<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> p \<inter> q)}}\<close> 
        by auto
    }
    then have \<open>gfp (\<Phi>pc b s p) \<inter> gfp (\<Phi>pc b s q) \<subseteq> gfp (\<Phi>pc b s (p \<inter> q))\<close> 
      unfolding gfp_def \<Phi>pc_def by auto
    then show ?case 
      using wp_\<Phi>pc by blast
  next
    case 2
    let ?r = \<open>|UNIV :: (string \<Rightarrow> int) set set set|\<close>
    have \<open>\<forall> x. x \<in> Field ?r\<close>
      by simp
    have n_iter: \<open>iter (\<Phi>tc b s p) {} n \<inter> iter (\<Phi>tc b s q) {} n \<subseteq> iter (\<Phi>tc b s (p \<inter> q)) {} n\<close> for n
    proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
      case 1
      then show ?case 
        by simp
    next
      case (2 i)
      define \<Phi>p where \<open>\<Phi>p \<equiv> iter (\<Phi>tc b s p) {} i\<close>
      define \<Phi>q where \<open>\<Phi>q \<equiv> iter (\<Phi>tc b s q) {} i\<close>
      define \<Phi>pq where \<open>\<Phi>pq \<equiv> iter (\<Phi>tc b s (p \<inter> q)) {} i\<close>
      from 2 have \<open>\<Phi>p \<inter> \<Phi>q \<subseteq> \<Phi>pq\<close> 
        unfolding \<Phi>p_def \<Phi>q_def \<Phi>pq_def by simp
      moreover have \<open>\<Phi>tc b s p \<Phi>p \<inter> \<Phi>tc b s q \<Phi>q \<subseteq> \<Phi>tc b s (p \<inter> q) (\<Phi>p \<inter> \<Phi>q)\<close> 
        unfolding \<Phi>tc_def using While(2) by auto
      ultimately have \<open>\<Phi>tc b s p \<Phi>p \<inter> \<Phi>tc b s q \<Phi>q \<subseteq> \<Phi>tc b s (p \<inter> q) \<Phi>pq\<close> 
        using \<Phi>tc_mono monotoneD by (metis subset_trans)
      then show ?case
        by (simp add: \<Phi>p_def \<Phi>pq_def \<Phi>q_def)
    next
      case (3 i)
      have \<open>\<Union> (iter (\<Phi>tc b s p) {} ` underS ?r i) \<inter> \<Union> (iter (\<Phi>tc b s q) {} ` underS ?r i) \<subseteq> \<Union> (iter (\<Phi>tc b s (p \<inter> q)) {} ` underS ?r i)\<close>
      proof clarify
        fix x j k
        assume \<open>j \<in> underS ?r i\<close> \<open>k \<in> underS ?r i\<close>
        then have *: \<open>max2 ?r j k \<in> underS ?r i\<close> 
          by (simp add: wo_rel.max2_def wo_rel_r)
        then have \<open>iter (\<Phi>tc b s p) {} (max2 ?r j k) \<inter> iter (\<Phi>tc b s q) {} (max2 ?r j k) \<subseteq> iter (\<Phi>tc b s (p \<inter> q)) {} (max2 ?r j k)\<close> 
          by (simp add: "3.hyps"(3))
        moreover have \<open>iter (\<Phi>tc b s p) {} j \<subseteq> iter (\<Phi>tc b s p) {} (max2 ?r j k)\<close> 
          by (simp add: \<Phi>tc_mono mono_chain_iter_under xfmax)
        moreover have \<open>iter (\<Phi>tc b s q) {} k \<subseteq> iter (\<Phi>tc b s q) {} (max2 ?r j k)\<close> 
          by (simp add: \<Phi>tc_mono mono_chain_iter_under yfmax)
        ultimately have \<open>iter (\<Phi>tc b s p) {} j \<inter> iter (\<Phi>tc b s q) {} k \<subseteq> iter (\<Phi>tc b s (p \<inter> q)) {} (max2 ?r j k)\<close>
          by auto
        moreover assume \<open>x \<in> iter (\<Phi>tc b s p) {} j\<close> \<open>x \<in> iter (\<Phi>tc b s q) {} k\<close>
        ultimately show \<open>x \<in> \<Union> (iter (\<Phi>tc b s (p \<inter> q)) {} ` underS ?r i)\<close> 
          using * by auto
      qed
      then show ?case 
        using 3 by simp
    qed
    then show ?case
      using Fix_meet \<Phi>tc_mono wp_\<Phi>tc Fix_is_lfp by (metis empty_subsetI)
  }
qed auto

section \<open>practical weakest precondition\<close>

fun wpax where (*computable weakest precondition for partial correctness*)
  \<open>wpax q (Assert r) = r \<^bold>\<and> q\<close> |
  \<open>wpax q (Var x) = Uni x q\<close> |
  \<open>wpax q (Assign x a) = psubst x a q\<close> |
  \<open>wpax q (Choice s1 s2) = wpax q s1 \<^bold>\<and> wpax q s2\<close> |
  \<open>wpax q (Seq s1 s2) = wpax (wpax q s2) s1\<close> |
  \<open>wpax q (If b s1 s2) = (b \<^bold>\<longrightarrow> wpax q s1) \<^bold>\<and> (\<^bold>\<not>b \<^bold>\<longrightarrow> wpax q s2)\<close> |
  \<open>wpax q (While b I s) = I \<^bold>\<and> (uni_all (I \<^bold>\<longrightarrow> (b \<^bold>\<longrightarrow> wpax I s) \<^bold>\<and> (\<^bold>\<not>b \<^bold>\<longrightarrow> q)))\<close> |
  \<open>wpax q (Ghost s) = wpax q s\<close>

lemma wpax_mono: \<open>i \<^bold>\<Turnstile> wpax p s \<Longrightarrow> (\<forall> i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> q) \<Longrightarrow> i \<^bold>\<Turnstile> wpax q s\<close>
proof (induct p s arbitrary: i p q rule: wpax.induct)
  case (3 q x a)
  then show ?case 
    using psubst_iff_psem by auto
qed auto

lemma wpax_conjunctive: \<open>i \<^bold>\<Turnstile> wpax p s \<Longrightarrow> i \<^bold>\<Turnstile> wpax q s \<Longrightarrow> i \<^bold>\<Turnstile> wpax (p \<^bold>\<and> q) s\<close> 
proof (induct p s arbitrary: i q rule: wpax.induct)
  case (5 p s1 s2)
  then have \<open>\<forall> i. i \<^bold>\<Turnstile> wpax p s2 \<^bold>\<and> wpax q s2 \<longrightarrow> i \<^bold>\<Turnstile> wpax (p \<^bold>\<and> q) s2\<close> 
    by simp
  then show ?case 
    using wpax_mono 5 by (metis wpax.simps(5))
qed auto


section \<open>termination\<close>

primrec erase_assert where
  \<open>erase_assert (Assert p) = Assert \<^bold>\<top>\<close> |
  \<open>erase_assert (Var x) = Var x\<close> |
  \<open>erase_assert (Assign x a) = Assign x a\<close> |
  \<open>erase_assert (Choice s1 s2) = (erase_assert s1 \<^bold>[\<^bold>] erase_assert s2)\<close> |
  \<open>erase_assert (Seq s1 s2) = (erase_assert s1 \<^bold>; erase_assert s2)\<close> |
  \<open>erase_assert (If b s1 s2) = If b (erase_assert s1) (erase_assert s2)\<close> |
  \<open>erase_assert (While b I s) = While b I (erase_assert s)\<close> |
  \<open>erase_assert (Ghost s) = (\<^bold>g erase_assert s)\<close>


lemma erase_assert_weakens: \<open>wptc q s \<subseteq> wptc q (erase_assert s)\<close>
proof (induct s arbitrary: q)
  case (Seq s1 s2)
  then have \<open>wptc (wptc q s2) s1 \<subseteq> wptc (wptc q s2) (erase_assert s1)\<close>
    by simp
  moreover have \<open>... \<subseteq> wptc (wptc q (erase_assert s2)) (erase_assert s1)\<close>
    using wptc_mono monotoneD Seq by meson
  ultimately show ?case 
    by simp
next
  case (While b I s)
  then have \<open>\<forall> x. \<Phi>tc b s q x \<subseteq> \<Phi>tc b (erase_assert s) q x\<close>
    unfolding \<Phi>tc_def by auto
  then show ?case 
    by (metis erase_assert.simps(7) lfp_mono wp_\<Phi>tc)
qed auto

lemma erase_assert_conjunctive_wptc: \<open>wptc p (erase_assert s) \<inter> wptc q s \<subseteq> wptc (p \<inter> q) s\<close>
proof (induct s arbitrary: p q)
  case (Seq s1 s2)
  then have \<open>wptc (wptc p (erase_assert s2)) (erase_assert s1) \<inter> wptc (wptc q s2) s1 \<subseteq> wptc (wptc p (erase_assert s2) \<inter> wptc q s2) s1\<close>
    by simp
  moreover have \<open>... \<subseteq> wptc (wptc (p \<inter> q) s2) s1\<close>
    using wptc_mono monotoneD Seq by metis
  ultimately show ?case 
    by simp
next
  case (Choice s1 s2)
  then show ?case 
    by fastforce
next
  case (If b s1 s2)
  then show ?case 
    by fastforce
next
  case (While b I s)
  let ?r = \<open>|UNIV :: (string \<Rightarrow> int) set set set|\<close>
  have \<open>iter (\<Phi>tc b (erase_assert s) p) {} n \<inter> iter (\<Phi>tc b s q) {} n \<subseteq> iter (\<Phi>tc b s (p \<inter> q)) {} n\<close> for n 
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?\<Phi>p = \<open>iter (\<Phi>tc b (erase_assert s) p) {} i\<close>
    let ?\<Phi>q = \<open>iter (\<Phi>tc b s q) {} i\<close>
    let ?\<Phi>pq = \<open>iter (\<Phi>tc b s (p \<inter> q)) {} i\<close>
    have \<open>wptc ?\<Phi>p (erase_assert s) \<inter> wptc ?\<Phi>q s \<subseteq> wptc (?\<Phi>p \<inter> ?\<Phi>q) s\<close>
      using While by simp
    moreover have \<open>... \<subseteq> wptc ?\<Phi>pq s\<close>
      using 2 wptc_mono monotoneD by meson
    ultimately have \<open>\<Phi>tc b (erase_assert s) p ?\<Phi>p \<inter> \<Phi>tc b s q ?\<Phi>q \<subseteq> \<Phi>tc b s (p \<inter> q) ?\<Phi>pq\<close>
      using \<Phi>tc_def by auto
    then show ?case
      by simp
  next
    case (3 i)
    have \<open>\<Union> (iter (\<Phi>tc b (erase_assert s) p) {} ` underS ?r i) \<inter> \<Union> (iter (\<Phi>tc b s q) {} ` underS ?r i) \<subseteq> \<Union> (iter (\<Phi>tc b s (p \<inter> q)) {} ` underS ?r i)\<close>
    proof clarify
      fix x j k
      assume \<open>j \<in> underS ?r i\<close> \<open>k \<in> underS ?r i\<close>
      then have \<open>max2 ?r j k \<in> underS ?r i\<close> 
        by (simp add: wo_rel.max2_def wo_rel_r)
      have \<open>iter (\<Phi>tc b (erase_assert s) p) {} j \<subseteq> iter (\<Phi>tc b (erase_assert s) p) {} (max2 ?r j k)\<close> 
        by (simp add: \<Phi>tc_mono mono_chain_iter_under xfmax)
      moreover have \<open>iter (\<Phi>tc b s q) {} k \<subseteq> iter (\<Phi>tc b s q) {} (max2 ?r j k)\<close>
        by (simp add: \<Phi>tc_mono mono_chain_iter_under yfmax)
      moreover have \<open>iter (\<Phi>tc b (erase_assert s) p) {} (max2 ?r j k) \<inter> iter (\<Phi>tc b s q) {} (max2 ?r j k) \<subseteq> iter (\<Phi>tc b s (p \<inter> q)) {} (max2 ?r j k)\<close>
        by (simp add: "3.hyps"(3) \<open>max2 ?r j k \<in> underS ?r i\<close>)
      moreover assume \<open>x \<in> iter (\<Phi>tc b (erase_assert s) p) {} j\<close> \<open>x \<in> iter (\<Phi>tc b s q) {} k\<close>
      ultimately show \<open>x \<in> \<Union> (iter (\<Phi>tc b s (p \<inter> q)) {} ` underS ?r i)\<close> 
        using \<open>max2 ?r j k \<in> underS ?r i\<close> by blast
    qed
    then show ?case 
      by (simp add: "3.hyps"(1) "3.hyps"(2))
  qed
  then show ?case 
    using Fix_meet \<Phi>tc_mono wp_\<Phi>tc Fix_is_lfp by (metis empty_subsetI erase_assert.simps(7))
qed auto

lemma erase_assert_conjunctive_wppc: \<open>wppc p (erase_assert s) \<inter> wppc q s \<subseteq> wppc (p \<inter> q) s\<close>
proof (induct s arbitrary: p q)
  case (Seq s1 s2)
  then have \<open>wppc (wppc p (erase_assert s2)) (erase_assert s1) \<inter> wppc (wppc q s2) s1 \<subseteq> wppc (wppc p (erase_assert s2) \<inter> wppc q s2) s1\<close>
    by simp
  moreover have \<open>... \<subseteq> wppc (wppc (p \<inter> q) s2) s1\<close>
    using wppc_mono monotoneD Seq by metis
  ultimately show ?case 
    by simp
next
  case (Choice s1 s2)
  then show ?case 
    by fastforce
next
  case (If b s1 s2)
  then show ?case 
    by fastforce
next
  case (While b I s)
  let ?fp1 = \<open>gfp (\<Phi>pc b (erase_assert s) p)\<close>
  let ?fp2 = \<open>gfp (\<Phi>pc b s q)\<close>
  have \<open>?fp1 \<inter> ?fp2 \<subseteq> \<Phi>pc b s (p \<inter> q) (?fp1 \<inter> ?fp2)\<close>
  proof -
    have \<open>wppc ?fp1 (erase_assert s) \<inter> wppc ?fp2 s \<subseteq> wppc (?fp1 \<inter> ?fp2) s\<close>
      using While by simp
    then have \<open>\<Phi>pc b (erase_assert s) p ?fp1 \<inter> \<Phi>pc b s q ?fp2 \<subseteq> \<Phi>pc b s (p \<inter> q) (?fp1 \<inter> ?fp2)\<close>
      using \<Phi>pc_def by auto
    then show ?thesis 
      using gfp_fixpoint \<Phi>pc_mono by blast
  qed
  then show ?case
    by (metis erase_assert.simps(7) gfp_upperbound wp_\<Phi>pc)
next 
  case (Ghost s)
  show ?case
    by (simp add: erase_assert_conjunctive_wptc)
qed auto

lemma t_wppc: \<open>wptc t (erase_assert s) \<inter> wppc q s \<subseteq> wptc q s\<close>
proof (induct s arbitrary: q t)
  case (Choice s1 s2)
  then have \<open>wptc t (erase_assert s1) \<inter> wptc t (erase_assert s2) \<inter> wppc q s1 \<inter> wppc q s2 \<subseteq> wptc q s1 \<inter> wptc q s2\<close>
    by fast
  then show ?case 
    by auto
next
  case (If b s1 s2)
  {
    fix i
    assume \<open>i \<in> wptc t (If b (erase_assert s1) (erase_assert s2))\<close> \<open>i \<in> wppc q (If b s1 s2)\<close>
    then have \<open>i \<^bold>\<Turnstile> b \<Longrightarrow> i \<in> wptc q s1\<close> \<open>\<not>i \<^bold>\<Turnstile> b \<Longrightarrow> i \<in> wptc q s2\<close> 
      using If by fastforce+
  }
  then show ?case 
    by auto
next
  case (Seq s1 s2)
  then have \<open>wptc (wptc t (erase_assert s2)) (erase_assert s1) \<inter> wppc (wppc q s2) s1 \<subseteq> 
      wptc (wptc t (erase_assert s2)) (erase_assert s1) \<inter> wptc (wppc q s2) s1\<close> 
    by auto
  moreover have \<open>... \<subseteq> wptc (wptc t (erase_assert s2) \<inter> wppc q s2) s1\<close>
    by (simp add: erase_assert_conjunctive_wptc)
  moreover have \<open>... \<subseteq> wptc (wptc q s2) s1\<close> 
    using Seq wptc_mono monotoneD by meson
  ultimately show ?case 
    by auto
next
  case (While b I s)

  let ?tp = \<open>\<lambda> x. \<Phi>tc b (erase_assert s) t x \<inter> \<Phi>pc b s q x\<close>
  have \<open>\<forall> x. ?tp x \<subseteq> \<Phi>tc b s q x\<close>
    unfolding \<Phi>pc_def \<Phi>tc_def using While by auto
  have \<open>gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q) \<subseteq> ?tp (gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q))\<close>
  proof safe
    fix i
    assume 1: \<open>i \<in> gfp (\<Phi>tc b (erase_assert s) t)\<close>
    assume 2: \<open>i \<in> gfp (\<Phi>pc b s q)\<close>
    then have \<open>\<not>i \<^bold>\<Turnstile> b \<Longrightarrow> i \<in> q\<close>
      using gfp_fixpoint \<Phi>pc_mono \<Phi>pc_def by blast
    moreover have 3: \<open>i \<^bold>\<Turnstile> b \<Longrightarrow> i \<in> wppc (gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q)) s\<close> 
    proof-
      assume \<open>i \<^bold>\<Turnstile> b\<close>
      then have \<open>i \<in> wptc (gfp (\<Phi>tc b (erase_assert s) t)) (erase_assert s)\<close>
        using 1 gfp_fixpoint \<Phi>tc_mono \<Phi>tc_def by blast
      then have \<open>i \<in> wppc (gfp (\<Phi>tc b (erase_assert s) t)) (erase_assert s)\<close>
        using wptc_sub_wppc by auto
      moreover have \<open>i \<in> wppc (gfp (\<Phi>pc b s q)) s\<close>
        using \<open>i \<^bold>\<Turnstile> b\<close> 2 gfp_fixpoint \<Phi>pc_mono \<Phi>pc_def by blast
      ultimately show ?thesis 
        by (meson IntI erase_assert_conjunctive_wppc in_mono)
    qed
    ultimately show \<open>i \<in> \<Phi>pc b s q (gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q))\<close> 
      using \<Phi>pc_def by simp
    have \<open>\<not>i \<^bold>\<Turnstile> b \<Longrightarrow> i \<in> t\<close> 
      using 1 gfp_fixpoint \<Phi>tc_mono \<Phi>tc_def by blast
    moreover have \<open>i \<^bold>\<Turnstile> b \<Longrightarrow> i \<in> wptc (gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q)) (erase_assert s)\<close> 
    proof-
      assume \<open>i \<^bold>\<Turnstile> b\<close>
      then have *: \<open>i \<in> wptc (gfp (\<Phi>tc b (erase_assert s) t)) (erase_assert s)\<close>
        using 1 gfp_fixpoint \<Phi>tc_mono \<Phi>tc_def by blast
      moreover have \<open>i \<in> wppc (gfp (\<Phi>pc b s q)) s\<close>
        using \<open>i \<^bold>\<Turnstile> b\<close> 2 gfp_fixpoint \<Phi>pc_mono \<Phi>pc_def by blast
      ultimately have \<open>i \<in> wptc (gfp (\<Phi>pc b s q)) s\<close> 
        using While by auto
      then have \<open>i \<in> wptc (gfp (\<Phi>pc b s q)) (erase_assert s)\<close> 
        using erase_assert_weakens by auto
      then show ?thesis 
        using * by (meson IntI in_mono wp_conjunctive(2))
    qed
    ultimately show \<open>i \<in> \<Phi>tc b (erase_assert s) t (gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q))\<close>
      by (simp add: \<Phi>tc_def)
  qed
  then have \<open>gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q) \<subseteq> gfp ?tp\<close>
    by (simp add: gfp_upperbound)
  then have **: \<open>gfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>pc b s q) \<subseteq> gfp (\<Phi>tc b s q)\<close> 
    using \<open>\<forall> x. ?tp x \<subseteq> \<Phi>tc b s q x\<close> Int_subset_iff gfp_mono inf.absorb_iff2 by (metis (no_types, lifting))

  let ?r = \<open>|UNIV :: (string \<Rightarrow> int) set set set|\<close>
  have \<open>\<forall> x. x \<in> Field ?r\<close>
    by simp
  have ***: \<open>iter (\<Phi>tc b (erase_assert s) t) {} n \<inter> gfp (\<Phi>tc b s q) \<subseteq> iter (\<Phi>tc b s q) {} n\<close> for n
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?it = \<open>iter (\<Phi>tc b (erase_assert s) t) {} i\<close>
    let ?i\<Phi> = \<open>iter (\<Phi>tc b s q) {} i\<close>
    have \<open>x \<in> gfp (\<Phi>tc b s q) \<Longrightarrow> (\<not>x \<^bold>\<Turnstile> b \<longrightarrow> x \<in> q) \<and> (x \<^bold>\<Turnstile> b \<longrightarrow> x \<in> wptc ?it (erase_assert s) \<longrightarrow> x \<in> wptc ?i\<Phi> s)\<close> for x 
    proof safe
      assume \<open>x \<in> gfp (\<Phi>tc b s q)\<close> \<open>\<not>x \<^bold>\<Turnstile> b\<close>
      then show \<open>x \<in> q\<close> 
        using gfp_fixpoint \<Phi>tc_mono \<Phi>tc_def by blast
    next
      assume \<open>x \<in> gfp (\<Phi>tc b s q)\<close> \<open>x \<^bold>\<Turnstile> b\<close>
      then have \<open>x \<in> wptc (gfp (\<Phi>tc b s q)) s\<close>
        using gfp_fixpoint \<Phi>tc_mono \<Phi>tc_def by blast
      moreover assume \<open>x \<in> wptc ?it (erase_assert s)\<close>
      moreover have \<open>wptc ?it (erase_assert s) \<inter> wptc (gfp (\<Phi>tc b s q)) s \<subseteq> wptc (?it \<inter> gfp (\<Phi>tc b s q)) s\<close> 
        by (simp add: erase_assert_conjunctive_wptc)
      moreover have \<open>... \<subseteq> wptc ?i\<Phi> s\<close>
        using 2 wptc_mono monotoneD by meson
      ultimately show \<open>x \<in> wptc ?i\<Phi> s\<close> 
        by auto
    qed
    then have \<open>\<Phi>tc b (erase_assert s) t ?it \<inter> gfp (\<Phi>tc b s q) \<subseteq> \<Phi>tc b s q ?i\<Phi>\<close> 
      using \<Phi>tc_def by auto
    then show ?case 
      by simp
  next
    case (3 i)
    have \<open>(\<Union> (iter (\<Phi>tc b (erase_assert s) t) {} ` underS ?r i)) \<inter> gfp (\<Phi>tc b s q) \<subseteq> \<Union> (iter (\<Phi>tc b s q) {} ` underS ?r i)\<close>
    proof safe
      fix x j
      assume \<open>j \<in> underS ?r i\<close>
      then have \<open>iter (\<Phi>tc b (erase_assert s) t) {} j \<inter> gfp (\<Phi>tc b s q) \<subseteq> iter (\<Phi>tc b s q) {} j\<close>
        using 3 by simp
      moreover have \<open>... \<subseteq> \<Union> (iter (\<Phi>tc b s q) {} ` underS ?r i)\<close>
        using \<open>j \<in> underS ?r i\<close> by auto
      moreover assume \<open>x \<in> gfp (\<Phi>tc b s q)\<close>
      moreover assume \<open>x \<in> iter (\<Phi>tc b (erase_assert s) t) {} j\<close>
      ultimately show \<open>x \<in> \<Union> (iter (\<Phi>tc b s q) {} ` underS ?r i)\<close> 
        by auto
    qed
    then show ?case 
      using 3 by simp
  qed

  
  let ?m = \<open>max2 ?r (Fix\<delta> (\<Phi>tc b (erase_assert s) t) {}) (Fix\<delta> (\<Phi>tc b s q) {})\<close>
  have \<open>iter (\<Phi>tc b (erase_assert s) t) {} ?m \<inter> gfp (\<Phi>tc b s q) \<subseteq> iter (\<Phi>tc b s q) {} ?m\<close>
    using *** by simp
  then have ****: \<open>lfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>tc b s q) \<subseteq> lfp (\<Phi>tc b s q)\<close> 
    using fmax \<Phi>tc_mono gmax Fix_def Fix_is_lfp by blast

  moreover have \<open>lfp (\<Phi>tc b (erase_assert s) t) \<subseteq> lfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>tc b (erase_assert s) t)\<close> 
    using lfp_le_gfp \<Phi>tc_mono by auto
  moreover have \<open>... \<inter> gfp (\<Phi>pc b s q) \<subseteq> lfp (\<Phi>tc b (erase_assert s) t) \<inter> gfp (\<Phi>tc b s q)\<close>
    using ** by auto
  ultimately show ?case
    using wp_\<Phi>pc wp_\<Phi>tc by fastforce
qed auto

lemma t_wppc': \<open>wppc p (erase_assert s) \<inter> wptc q s \<subseteq> wptc (p \<inter> q) s\<close> 
proof-
  have \<open>wppc p (erase_assert s) \<inter> wptc q s \<subseteq> wppc p (erase_assert s) \<inter> wptc q (erase_assert s) \<inter> wptc q s\<close> 
    by (simp add: erase_assert_weakens inf.coboundedI1 inf_commute)
  moreover have \<open>... \<subseteq> wppc p (erase_assert s) \<inter> wptc q (erase_assert (erase_assert s)) \<inter> wptc q s\<close> 
    using erase_assert_weakens by auto
  moreover have \<open>... \<subseteq> wptc (p) (erase_assert s) \<inter> wptc q s\<close> 
    by (metis inf_commute inf_mono subset_refl t_wppc)
  moreover have \<open>... \<subseteq> wptc (p \<inter> q) s\<close> 
    by (simp add: erase_assert_conjunctive_wptc)
  ultimately show ?thesis
    by fast
qed

section \<open>practical to theoretical weakest precondition\<close>

lemma wpax_to_wppc: \<open>wppc t (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax q s} \<subseteq> wppc {i. i \<^bold>\<Turnstile> q} s\<close>
proof (induct q s arbitrary: t rule: wpax.induct)
  case (3 q x a)
  then show ?case 
    by (simp add: psubst_iff_psem)
next
  case (5 q s1 s2)       
  then have \<open>wppc (wppc t (erase_assert s2)) (erase_assert s1) \<inter> {i. i \<^bold>\<Turnstile> wpax (wpax q s2) s1} \<subseteq> wppc (wppc t (erase_assert s2)) (erase_assert s1) \<inter> wppc {i. i \<^bold>\<Turnstile> wpax q s2} s1\<close> 
    by auto
  moreover have \<open>... \<subseteq> wppc (wppc t (erase_assert s2) \<inter> {i. i \<^bold>\<Turnstile> wpax q s2}) s1\<close>
    by (simp add: erase_assert_conjunctive_wppc)
  moreover have \<open>... \<subseteq> wppc (wppc {i. i \<^bold>\<Turnstile> q} s2) s1\<close>
    using 5(1) wppc_mono monotoneD by meson
  ultimately show ?case
    by auto
next
  case (7 q b I s)
  show ?case 
  proof clarify
    fix i
    assume a1: \<open>i \<in> wppc t (erase_assert (While b I s))\<close>
    assume a2: \<open>i \<^bold>\<Turnstile> wpax q (While b I s)\<close>
    then have \<open>\<forall> i. i \<^bold>\<Turnstile> I \<longrightarrow> i \<^bold>\<Turnstile> b \<longrightarrow> i \<^bold>\<Turnstile> wpax I s\<close>
      by simp
    then have \<open>{i. i \<^bold>\<Turnstile> I \<and> i \<^bold>\<Turnstile> b} \<inter> wppc t (erase_assert s) \<subseteq> wppc {i. i \<^bold>\<Turnstile> I} s\<close> for t
      using 7 by auto
    moreover have \<open>{i. i \<^bold>\<Turnstile> b} \<inter> gfp (\<Phi>pc b (erase_assert s) t) \<subseteq> wppc (gfp (\<Phi>pc b (erase_assert s) t)) (erase_assert s)\<close> 
      using \<Phi>pc_mono gfp_fixpoint \<Phi>pc_def by blast
    ultimately have \<open>{i. i \<^bold>\<Turnstile> I \<and> i \<^bold>\<Turnstile> b} \<inter> gfp (\<Phi>pc b (erase_assert s) t) \<subseteq> wppc {i. i \<^bold>\<Turnstile> I} s \<inter> wppc (gfp (\<Phi>pc b (erase_assert s) t)) (erase_assert s)\<close> 
      by auto
    moreover have \<open>... \<subseteq> wppc ({i. i \<^bold>\<Turnstile> I} \<inter> gfp (\<Phi>pc b (erase_assert s) t)) s\<close>
      by (metis erase_assert_conjunctive_wppc inf_commute)
    moreover have \<open>\<forall> i. i \<^bold>\<Turnstile> I \<longrightarrow> \<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<^bold>\<Turnstile> q\<close> 
      using a2 by simp
    ultimately have \<open>{i. i \<^bold>\<Turnstile> I} \<inter> gfp (\<Phi>pc b (erase_assert s) t) \<subseteq> \<Phi>pc b s {i. i \<^bold>\<Turnstile> q} ({i. i \<^bold>\<Turnstile> I} \<inter> gfp (\<Phi>pc b (erase_assert s) t))\<close> 
      unfolding \<Phi>pc_def by auto
    then have \<open>{i. i \<^bold>\<Turnstile> I} \<inter> gfp (\<Phi>pc b (erase_assert s) t) \<subseteq> gfp (\<Phi>pc b s {i. i \<^bold>\<Turnstile> q})\<close>
      by (simp add: gfp_upperbound)
    moreover have \<open>i \<^bold>\<Turnstile> I\<close>
      using a2 by simp
    moreover have \<open>i \<in> gfp (\<Phi>pc b (erase_assert s) t)\<close> 
      using a1 wp_\<Phi>pc by auto
    ultimately have \<open>i \<in> gfp (\<Phi>pc b s {i. i \<^bold>\<Turnstile> q})\<close>
      by auto
    then show \<open>i \<in> wppc {i. i \<^bold>\<Turnstile> q} (While b I s)\<close> 
      using wp_\<Phi>pc by blast
  qed
next
  case (8 q s)
  have \<open>wptc t (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax q s} \<subseteq> wptc t (erase_assert s) \<inter> wppc t (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax q s}\<close> 
    by (simp add: le_infI1 wptc_sub_wppc)
  moreover have \<open>... \<subseteq> wptc t (erase_assert s) \<inter> wppc {i. i \<^bold>\<Turnstile> q} s\<close>
    using 8 by auto
  moreover have \<open>... \<subseteq> wptc {i. i \<^bold>\<Turnstile> q} s\<close>
    using t_wppc by simp
  ultimately show ?case 
    by auto
qed auto


section \<open>ghost code\<close>

primrec erase_ghost where
  \<open>erase_ghost (Assert b) = Assert b\<close> |
  \<open>erase_ghost (Var x) = Var x\<close> |
  \<open>erase_ghost (Assign x a) = Assign x a\<close> |
  \<open>erase_ghost (Choice s1 s2) = Choice (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (Seq s1 s2) = Seq (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (If b s1 s2) = If b (erase_ghost s1) (erase_ghost s2)\<close> |
  \<open>erase_ghost (While b I s) = While b I (erase_ghost s)\<close> |
  \<open>erase_ghost (Ghost s) = Assert \<^bold>\<top>\<close>



section \<open>ghost code check\<close>

primrec gc_check where 
  \<open>gc_check g (Assert b) = True\<close> |
  \<open>gc_check g (Var x) = True\<close> |
  \<open>gc_check g (Assign x a) = g x\<close> |
  \<open>gc_check g (Choice s1 s2) = (gc_check g s1 \<or> gc_check g s2)\<close> |
  \<open>gc_check g (Seq s1 s2) = (gc_check g s1 \<and> gc_check g s2)\<close> |
  \<open>gc_check g (If b s1 s2) = (gc_check g s1 \<and> gc_check g s2)\<close> | 
  \<open>gc_check g (While b I s) = (gc_check g s)\<close> |
  \<open>gc_check g (Ghost s) = gc_check g s\<close>

lemma gc_check_lemma:
  \<open>gc_check g s \<Longrightarrow> {i \<^bold>\<down> g | i. i \<in> wptc q s} \<subseteq> {i \<^bold>\<down> g | i.  i \<in> q}\<close>
proof (induct s arbitrary: q)
  case (Var x)
  show ?case 
  proof clarify
    fix i
    assume \<open>i \<in> wptc q (Var x)\<close>
    then have \<open>\<forall> v. i(x := v) \<in> q\<close>
      by simp
    then have \<open>i(x := i x) \<in> q\<close> 
      using psem.simps(2) by blast
    then show \<open>\<exists> j. i \<^bold>\<down> g = j \<^bold>\<down> g \<and> j \<in> q \<close>
      by auto
  qed
next
  case (Assign x a)
  then have \<open>i \<^bold>\<down> g = i(x := i\<lparr>a\<rparr>) \<^bold>\<down> g\<close> for i 
    by (simp add: regular_alt)
  then show ?case 
    by auto
next
  case (Choice s1 s2)
  {
    fix i 
    assume \<open>i \<in> wptc q s1\<close> \<open>i \<in> wptc q s2\<close>
    then have \<open>(gc_check g s1 \<longrightarrow> (\<exists> j. i \<^bold>\<down> g = j \<^bold>\<down> g \<and> j \<in> q)) \<and> (gc_check g s2 \<longrightarrow> (\<exists> j. i \<^bold>\<down> g = j \<^bold>\<down> g \<and> j \<in> q))\<close> 
      using Choice by blast
  }
  then show ?case 
    using Choice by auto
next
  case (Seq s1 s2)
  show ?case
  proof clarify
    fix i 
    assume \<open>i \<in> wptc q (s1 \<^bold>; s2)\<close>
    then have \<open>i \<in> wptc (wptc q s2) s1\<close>
      by simp
    moreover have \<open>{i \<^bold>\<down> g |i. i \<in> wptc (wptc q s2) s1} \<subseteq> {i \<^bold>\<down> g |i. i \<in> q}\<close>
      using Seq by (meson dual_order.trans gc_check.simps(5))
    ultimately show \<open>\<exists>i'. i \<^bold>\<down> g = i' \<^bold>\<down> g \<and> i' \<in> q \<close>
      by auto
  qed
next
  case (If b s1 s2)
  {
    fix i
    assume \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc q s1) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc q s2)\<close>
    then have \<open>\<exists> j. i \<^bold>\<down> g = j \<^bold>\<down> g \<and> j \<in> q\<close> 
      using If by (cases \<open>i \<^bold>\<Turnstile> b\<close>, auto, blast) 
  }
  then show ?case  
    by auto
next
  case (While b I s)
  have \<open>{i \<^bold>\<down> g | i. i \<in> lfp (\<Phi>tc b s q)} \<subseteq> {i \<^bold>\<down> g | i.  i \<in> q}\<close> 
  proof (unfold lfp_def, clarify)
    fix i
    have \<open>{i \<^bold>\<down> g |i. i \<in> \<Phi>tc b s q q} \<subseteq> {i \<^bold>\<down> g |i. i \<in> q}\<close>
      unfolding \<Phi>tc_def using While by auto
    have \<open>\<Phi>tc b s q {i. \<exists> j \<in> q. i \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> {i. \<exists> j \<in> q. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close> 
    proof (unfold \<Phi>tc_def, clarify)
      fix i
      assume a:\<open>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc {i. \<exists>j\<in>q. i \<^bold>\<down> g = j \<^bold>\<down> g} s\<close>
      assume \<open>\<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q\<close>
      show \<open>\<exists> j \<in> q. i \<^bold>\<down> g = j \<^bold>\<down> g\<close> 
      proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
        case True
        then have \<open>i \<in> wptc {i. \<exists>j\<in>q. i \<^bold>\<down> g = j \<^bold>\<down> g} s\<close>
          using a by simp
        then obtain j where \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> \<open>j \<in> {i. \<exists>j\<in>q. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
          using While by fastforce
        then show ?thesis 
          by simp
      next
        case False
        then show ?thesis 
          using \<open>\<not> i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q\<close> by auto
      qed
    qed
    moreover assume \<open>i \<in> \<Inter> {x. \<Phi>tc b s q x \<subseteq> x}\<close>
    ultimately show \<open>\<exists> j. i \<^bold>\<down> g = j \<^bold>\<down> g \<and> j \<in> q\<close> 
      by blast
  qed
  then show ?case 
    using wp_\<Phi>tc by simp
qed auto


section \<open>regular code check\<close>

primrec rc_check where
  \<open>rc_check g (Assert b) = regular_p g b\<close> |
  \<open>rc_check g (Var x) = True\<close> |
  \<open>rc_check g (Assign x a) = regular_a g a\<close> |
  \<open>rc_check g (Choice s1 s2) = (rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (Seq s1 s2) = (rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (If b s1 s2) = (regular_p g b \<and> rc_check g s1 \<and> rc_check g s2)\<close> |
  \<open>rc_check g (While b I s) = (regular_p g b \<and> rc_check g s)\<close> |
  \<open>rc_check g (Ghost s) = gc_check g s\<close> 

lemma regular_wp: \<open>regular_s g q \<Longrightarrow> rc_check g s \<Longrightarrow> regular_s g (wppc q (erase_ghost s))\<close>
proof (induct s arbitrary: q)
  case (Assert x)
  then show ?case 
    by (metis (no_types, lifting) erase_ghost.simps(1) mem_Collect_eq rc_check.simps(1) regular_agree_pexp wppc.simps(1))
next
  case (Var x)
  {
    fix i j :: \<open>string \<Rightarrow> int\<close>
    fix v
    assume \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close>
    then have \<open>i(x := v) \<^bold>\<down> g = j(x := v) \<^bold>\<down> g\<close> 
      by (simp add: regular_alt)
    moreover assume \<open>\<forall> v. i(x := v) \<in> q\<close> 
    ultimately have \<open>j(x := v) \<in> q\<close> 
      using Var by auto
  }
  then show ?case 
    by simp
next
  case (Assign x a)
  {
    fix i j :: \<open>string \<Rightarrow> int\<close>
    fix v
    assume \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close>
    then have \<open>i(x := i\<lparr>a\<rparr>) \<^bold>\<down> g = j(x := j\<lparr>a\<rparr>) \<^bold>\<down> g\<close>  
      using Assign by (simp add: regular_agree_aexp regular_alt)
    moreover assume \<open>i(x := i\<lparr>a\<rparr>) \<in> q\<close> 
    ultimately have \<open>j(x := j\<lparr>a\<rparr>) \<in> q\<close> 
      using Assign by auto
  }
  then show ?case
    by simp
next
  case (Choice s1 s2)
  then show ?case 
    by (metis Int_iff erase_ghost.simps(4) rc_check.simps(4) wppc.simps(4))
next
  case (Seq s1 s2)
  then have \<open>rc_check g s2\<close>
    by simp
  then have \<open>regular_s g (wppc q (erase_ghost s2))\<close> 
    using Seq(2,3) by blast
  moreover have \<open>rc_check g s1\<close>
    using Seq by simp
  ultimately have \<open>regular_s g (wppc (wppc q (erase_ghost s2)) (erase_ghost s1))\<close>
    using Seq(1) by blast
  then show ?case 
    by simp
next
  case (If b s1 s2)
  then have \<open>rc_check g s1\<close>
    by simp
  then have 1: \<open>regular_s g (wppc q (erase_ghost s1))\<close> 
    using If(1,3) by blast
  from If have \<open>rc_check g s2\<close>
    by simp
  then have 2: \<open>regular_s g (wppc q (erase_ghost s2))\<close> 
    using If(2,3) by blast
  from If have \<open>regular_p g b\<close> 
    by auto
  with 1 2 show ?case 
    using regular_agree_pexp 
    by (metis (mono_tags, lifting) erase_ghost.simps(6) mem_Collect_eq wppc.simps(6))
next
  case (While b I s)
  let ?phi = \<open>\<Phi>pc b (erase_ghost s) q\<close>
  have *: \<open>\<forall> x. regular_s g x \<longrightarrow> regular_s g (?phi x)\<close>
  proof (rule, rule)
    fix x :: \<open>(string \<Rightarrow> int) set\<close>
    assume \<open>regular_s g x\<close>
    moreover have \<open>rc_check g s\<close>
      using While by auto
    ultimately have \<open>regular_s g (wppc x (erase_ghost s))\<close>
      using While by blast
    then show \<open>regular_s g (?phi x)\<close>
      using \<Phi>pc_def regular_agree_pexp 
      by (metis (mono_tags, lifting) While.prems(1) While.prems(2) mem_Collect_eq rc_check.simps(7))
  qed
  have \<open>regular_s g {j. \<exists> i \<in> gfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close> 
    by auto
  then have 1:\<open>regular_s g (?phi {j. \<exists> i \<in> gfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g})\<close>
    using * by blast
  have \<open>gfp ?phi \<subseteq> {j. \<exists> i \<in> gfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
    by auto
  then have 2:\<open>gfp ?phi \<subseteq> ?phi {j. \<exists> i \<in> gfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
    using gfp_fixpoint \<Phi>pc_mono
    by (metis (no_types, lifting) monotoneD)
  from 1 2 have \<open>{j. \<exists> i \<in> gfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> ?phi {j. \<exists> i \<in> gfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close> 
    by auto
  then have \<open>regular_s g (gfp ?phi)\<close>
    unfolding gfp_def by auto
  then show ?case 
    unfolding \<Phi>pc_def by simp
qed auto

lemma rc_check_lemma_wp:
  assumes \<open>rc_check g s\<close> \<open>regular_s g Q\<close> \<open>q \<subseteq> Q\<close> 
  shows \<open>wppc q s \<subseteq> wppc Q (erase_ghost s)\<close>
  using assms
proof (induct s arbitrary: Q q)
  case (Choice s1 s2)
  then have \<open>rc_check g s1\<close> \<open>rc_check g s2\<close>
    by simp_all
  then have \<open>wppc q s1 \<subseteq> wppc Q (erase_ghost s1)\<close> \<open>wppc q s2 \<subseteq> wppc Q (erase_ghost s2)\<close>
    using Choice by simp_all
  then show ?case 
    by auto
next
  case (Seq s1 s2)
  then have \<open>wppc q s2 \<subseteq> wppc Q (erase_ghost s2)\<close> 
    by auto
  moreover have \<open>regular_s g (wppc Q (erase_ghost s2))\<close> 
    using rc_check.simps(5) regular_wp Seq by blast
  ultimately show ?case 
    using Seq by simp
next
  case (If b s1 s2)
  show ?case 
  proof
    fix i 
    assume a: \<open>i \<in> wppc q (If b s1 s2)\<close>
    show \<open>i \<in> wppc Q (erase_ghost (If b s1 s2))\<close>
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then show ?thesis 
        using a If by auto
    next
      case False
      then have \<open>i \<in> wppc q s2\<close>
        using a by simp
      then have \<open>i \<in> wppc Q (erase_ghost s2)\<close> 
        using If(2-5) False by auto
      then show ?thesis
        using False by simp
    qed
  qed
next
  case (While b I s)
  let ?phi = \<open>\<Phi>pc b (erase_ghost s) Q\<close>
  let ?psi = \<open>\<Phi>pc b s q\<close>
  have \<open>gfp ?psi \<subseteq> gfp ?phi\<close> 
  proof
    fix i
    assume a: \<open>i \<in> gfp ?psi\<close>
    show \<open>i \<in> gfp ?phi\<close> 
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then have \<open>\<forall> x X. x \<subseteq> X \<longrightarrow> regular_s g X \<longrightarrow> wppc x s \<subseteq> wppc X (erase_ghost s)\<close>
        using While by simp
      then have *:\<open>\<forall> x X. x \<subseteq> X \<longrightarrow> regular_s g X \<longrightarrow>?psi x \<subseteq> ?phi X \<close> 
        using While(4) unfolding \<Phi>pc_def by auto
      have \<open>gfp ?psi \<subseteq> ?psi (gfp ?psi)\<close>
        using gfp_fixpoint \<Phi>pc_mono by blast
      then have **:\<open>gfp ?psi \<subseteq> {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
        by auto
      moreover have \<open>regular_s g {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
        by auto
      ultimately have \<open>?psi (gfp ?psi) \<subseteq> ?phi {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
        using * by auto
      then have \<open>gfp ?psi \<subseteq> ?phi {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close> 
        using gfp_fixpoint \<Phi>pc_mono by blast
      moreover have \<open>regular_s g (?phi {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g})\<close>
      proof-
        have \<open>regular_s g {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close> 
          by auto
        moreover have \<open>rc_check g s\<close>
          using While by simp
        ultimately have \<open>regular_s g (wppc {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g} (erase_ghost s))\<close>
          using regular_wp by blast
        moreover have \<open>regular_p g b\<close>
          using While by simp
        ultimately show ?thesis
          using \<Phi>pc_def While(3) regular_agree_pexp by (metis (mono_tags, lifting) mem_Collect_eq)
      qed
      ultimately have \<open>{i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> ?phi {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close>
        by auto
      moreover have \<open>i \<in> {i. \<exists> j \<in> gfp ?psi. i \<^bold>\<down> g = j \<^bold>\<down> g}\<close> 
        using a by auto
      ultimately show ?thesis 
        unfolding gfp_def using a by auto
    next
      case False
      then have \<open>i \<in> q\<close>
        using a gfp_fixpoint \<Phi>pc_mono \<Phi>pc_def by blast
      then have \<open>i \<in> Q\<close>
        using While by auto
      then show ?thesis 
        using gfp_fixpoint \<Phi>pc_mono \<Phi>pc_def False by blast
    qed
  qed
  then show ?case
    using wp_\<Phi>pc by auto
next
  case (Ghost s)
  then have \<open>{i \<^bold>\<down> g | i. i \<in> wptc q s} \<subseteq> {i \<^bold>\<down> g | i. i \<in> q}\<close>
    by (simp add: gc_check_lemma)
  then have \<open>{i \<^bold>\<down> g | i. i \<in> wptc q s} \<subseteq> {i \<^bold>\<down> g | i. i \<in> Q}\<close>
    using Ghost(4) by blast
  then have \<open>wptc q s \<subseteq> Q\<close>
    using Ghost(3) subset_eq by auto
  then show ?case
    by simp
qed auto

lemma rc_check_lemma_wpax:
  assumes \<open>rc_check g s\<close> \<open>regular_s g Q\<close> \<open>\<forall> i. i \<^bold>\<Turnstile> q \<longrightarrow> i \<in> Q\<close>
  shows \<open>wppc UNIV (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax q s} \<subseteq> wppc Q (erase_ghost s)\<close>
proof-
  have \<open>wppc UNIV (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax q s} \<subseteq> wppc {i. i \<^bold>\<Turnstile> q} s\<close> 
    by (simp add: wpax_to_wppc)
  moreover have \<open>... \<subseteq> wppc Q (erase_ghost s)\<close>
    using assms rc_check_lemma_wp by (metis mem_Collect_eq subsetI)
  ultimately show ?thesis 
    by simp
qed

corollary ghost_erase_with_ghost_conditions:
  assumes \<open>rc_check g s\<close> \<open>regular_p g p\<close> \<open>regular_p g q\<close> \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> gp} = {i \<^bold>\<down> g | i. True}\<close>
    and \<open>\<forall> i. i \<^bold>\<Turnstile> gp \<^bold>\<and> p \<longrightarrow> i \<^bold>\<Turnstile> wpax (gq \<^bold>\<and> q) s \<and> i \<in> wppc UNIV (erase_assert s)\<close>
  shows \<open>{i. i \<^bold>\<Turnstile> p} \<subseteq> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close> 
proof-
  from \<open>regular_p g q\<close> have \<open>regular_s g {i. i \<^bold>\<Turnstile> q}\<close>
    using regular_p_then_regular_s by simp
  moreover have \<open>\<forall> i. i \<^bold>\<Turnstile> (gq \<^bold>\<and> q) \<longrightarrow> i \<in> {i. i \<^bold>\<Turnstile> q}\<close>
    by simp
  ultimately have \<open>wppc UNIV (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax (gq \<^bold>\<and> q) s} \<subseteq> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close>
    using \<open>rc_check g s\<close> rc_check_lemma_wpax by simp
  show ?thesis
  proof clarify
    fix i
    assume \<open>i \<^bold>\<Turnstile> p\<close>
    moreover obtain j where \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> \<open>j \<^bold>\<Turnstile> gp\<close>
      using \<open>{i \<^bold>\<down> g | i. i \<^bold>\<Turnstile> gp} = {i \<^bold>\<down> g | i. True}\<close> by blast
    ultimately have \<open>j \<^bold>\<Turnstile> gp \<^bold>\<and> p\<close> 
      using \<open>regular_p g p\<close> psem.simps(2) regular_agree_pexp by blast
    then have \<open>j \<^bold>\<Turnstile> wpax (gq \<^bold>\<and> q) s \<and> j \<in> wppc UNIV (erase_assert s)\<close>
      using \<open>\<forall> i. i \<^bold>\<Turnstile> gp \<^bold>\<and> p \<longrightarrow> i \<^bold>\<Turnstile> wpax (gq \<^bold>\<and> q) s \<and> i \<in> wppc UNIV (erase_assert s)\<close> by simp
    then have \<open>j \<in> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close>
      using \<open>wppc UNIV (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax (gq \<^bold>\<and> q) s} \<subseteq> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close> by auto
    moreover have \<open>regular_s g (wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s))\<close>
      using \<open>regular_s g {i. i \<^bold>\<Turnstile> q}\<close> assms(1) regular_wp by meson
    ultimately show \<open>i \<in> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close>
      using \<open>i \<^bold>\<down> g = j \<^bold>\<down> g\<close> by simp
  qed
qed

definition \<open>ghost_terminates i s \<equiv> i \<in> wppc UNIV (erase_assert s)\<close>

corollary ghost_erase_simple:
  assumes \<open>rc_check g s\<close> \<open>regular_p g q\<close> \<open>ghost_terminates i s\<close>
    and \<open>i \<^bold>\<Turnstile> wpax q s\<close>
  shows \<open>i \<in> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close>
proof-
  have \<open>regular_s g {i. i \<^bold>\<Turnstile> q}\<close>
    using regular_p_then_regular_s \<open>regular_p g q\<close> .
  then have \<open>wppc UNIV (erase_assert s) \<inter> {i. i \<^bold>\<Turnstile> wpax q s} \<subseteq> wppc {i. i \<^bold>\<Turnstile> q} (erase_ghost s)\<close>
    using assms rc_check_lemma_wpax by simp
  then show ?thesis
    using assms ghost_terminates_def by auto
qed


section \<open>alternative analyses\<close>
fun sppc where (*strongest precondition for partial incorrectness*)
  \<open>sppc q (Assert r) = {i. i \<in> q \<or> \<not>i \<^bold>\<Turnstile> r}\<close> |
  \<open>sppc q (Var x) = {i. \<exists> v. i(x := v) \<in> q}\<close> |
  \<open>sppc q (Assign x a) = {i. i(x := i\<lparr>a\<rparr>) \<in> q}\<close> |
  \<open>sppc q (Choice s1 s2) = sppc q s1 \<union> sppc q s2\<close> |
  \<open>sppc q (Seq s1 s2) = sppc (sppc q s2) s1\<close> |
  \<open>sppc q (If b s1 s2) = {i. if i \<^bold>\<Turnstile> b then i \<in> sppc q s1 else i \<in> sppc q s2}\<close> |
  \<open>sppc q (While b I s) = gfp (\<lambda> x. {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> sppc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)})\<close> | 
  \<open>sppc q (Ghost s) = sppc q s\<close>

definition \<open>\<Psi>pc b s q x \<equiv> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> sppc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>

lemma sp_\<Psi>pc: \<open>sppc q (While b I s) = gfp (\<Psi>pc b s q)\<close> 
  unfolding \<Psi>pc_def by simp

lemma sppc_mono: \<open>mono (\<lambda> q. sppc q s)\<close>
proof (rule monoI, induct rule: sppc.induct)
  case (4 q s1 s2)
  then show ?case 
    by (simp add: le_supI1 le_supI2)
next
  case (6 q b s1 s2)
  show ?case 
  proof
    fix i
    assume *:\<open>i \<in> sppc x (If b s1 s2)\<close>
    show \<open>i \<in> sppc y (If b s1 s2)\<close> 
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then show ?thesis 
        using 6 * by auto
    next
      case False
      then have \<open>sppc x s2 \<subseteq> sppc y s2\<close>
        using 6 by simp
      then show ?thesis 
        using False * by auto
    qed
  qed
next
  case (7 q b I s)
  then have \<open>\<forall> q. \<Psi>pc b s x q \<subseteq> \<Psi>pc b s y q\<close>
    unfolding \<Psi>pc_def by auto
  then have \<open>gfp (\<Psi>pc b s x) \<subseteq> gfp (\<Psi>pc b s y)\<close>
    using gfp_mono by meson
  then show ?case 
    using sp_\<Psi>pc by simp
qed auto

lemma \<Psi>pc_mono: \<open>mono (\<Psi>pc b s q)\<close>
proof (rule monoI)
  fix x y :: \<open>(char list \<Rightarrow> int) set\<close>
  assume \<open>x \<subseteq> y\<close>
  {
    fix i
    assume \<open>(i \<^bold>\<Turnstile> b \<and> i \<in> sppc x s) \<or> (\<not>i \<^bold>\<Turnstile> b \<and> i \<in> q)\<close>
    then have \<open>(i \<^bold>\<Turnstile> b \<and> i \<in> sppc y s) \<or> (\<not>i \<^bold>\<Turnstile> b \<and> i \<in> q)\<close> 
      using \<open>x \<subseteq> y\<close> sppc_mono monoD by blast
  }
  then show \<open>\<Psi>pc b s q x \<subseteq> \<Psi>pc b s q y\<close> 
    unfolding \<Psi>pc_def by auto
qed

lemma sppc_wptc: \<open>-sppc (-q) s = wptc q s\<close>
proof (induct s arbitrary: q)
  case (Seq s1 s2)
  then have \<open>wptc (wptc q s2) s1 = wptc (-sppc (-q) s2) s1\<close> 
    by simp
  moreover have \<open>... = -sppc (sppc (-q) s2) s1\<close>
    using Seq by (metis double_complement)
  ultimately show ?case 
    by simp
next
  case (While b I s)
  let ?r = \<open>|UNIV :: (string \<Rightarrow> int) set set set|\<close>
  have *: \<open>-Iter (\<Psi>pc b s (-q)) UNIV n = iter (\<Phi>tc b s q) {} n\<close> for n
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?I = \<open>Iter (\<Psi>pc b s (- q)) UNIV i\<close>
    let ?i = \<open>iter (\<Phi>tc b s q) {} i\<close>
    have \<open>- \<Psi>pc b s (-q) (-(-?I)) = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> -sppc (-(-?I)) s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      unfolding \<Psi>pc_def by auto
    moreover have \<open>... = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc (-?I) s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      using While by blast
    moreover have \<open>... = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc ?i s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      using 2 by simp
    moreover have \<open>... = \<Phi>tc b s q ?i\<close>
      unfolding \<Phi>tc_def by simp
    ultimately show ?case 
      by simp
  next
    case (3 i)
    let ?I = \<open>\<lambda> i. Iter (\<Psi>pc b s (- q)) UNIV i\<close>
    let ?i = \<open>\<lambda> i. iter (\<Phi>tc b s q) {} i\<close>
    have \<open>- ?I i = - \<Inter> {?I j | j. j \<in> underS ?r i}\<close> 
      by (simp add: "3.hyps"(1) "3.hyps"(2) Setcompr_eq_image)
    moreover have \<open>... = \<Union> {- ?I j | j. j \<in> underS ?r i}\<close> 
      by auto
    moreover have \<open>... = \<Union> {?i j | j. j \<in> underS ?r i}\<close> 
      using 3 by auto
    moreover have \<open>... = ?i i\<close> 
      by (simp add: "3.hyps"(1) "3.hyps"(2) Setcompr_eq_image)
    ultimately show ?case 
      by simp
  qed
  let ?m = \<open>max2 ?r (FIX\<delta> (\<Psi>pc b s (-q)) UNIV) (Fix\<delta> (\<Phi>tc b s q) {})\<close>
  from * have \<open>-Iter (\<Psi>pc b s (-q)) UNIV ?m = iter (\<Phi>tc b s q) {} ?m\<close>
    by simp
  then have \<open>-gfp (\<Psi>pc b s (-q)) = lfp (\<Phi>tc b s q)\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp Fix_def Fix_is_lfp \<Phi>tc_mono \<Psi>pc_mono gmax reach_fixpoint_above' top_greatest xfmax)
  then show ?case 
    using sp_\<Psi>pc wp_\<Phi>tc by blast
qed auto

fun sptc where (*strongest precondition for total incorrectness correctness*)
  \<open>sptc q (Assert r) = {i. i \<in> q \<or> \<not>i \<^bold>\<Turnstile> r}\<close> |
  \<open>sptc q (Var x) = {i. \<exists> v. i(x := v) \<in> q}\<close> |
  \<open>sptc q (Assign x a) = {i. i(x := i\<lparr>a\<rparr>) \<in> q}\<close> |
  \<open>sptc q (Choice s1 s2) = sptc q s1 \<union> sptc q s2\<close> |
  \<open>sptc q (Seq s1 s2) = sptc (sptc q s2) s1\<close> |
  \<open>sptc q (If b s1 s2) = {i. if i \<^bold>\<Turnstile> b then i \<in> sptc q s1 else i \<in> sptc q s2}\<close> |
  \<open>sptc q (While b I s) = lfp  (\<lambda> x. {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> sptc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)})\<close> | 
  \<open>sptc q (Ghost s) = sppc q s\<close>

definition \<open>\<Psi>tc b s q x \<equiv> {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> sptc x s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>

lemma sp_\<Psi>tc: \<open>sptc q (While b I s) = lfp (\<Psi>tc b s q)\<close> 
  unfolding \<Psi>tc_def by simp

lemma sptc_mono: \<open>mono (\<lambda> q. sptc q s)\<close>
proof (rule monoI, induct rule: sptc.induct)
  case (4 q s1 s2)
  then show ?case 
    by (simp add: le_supI1 le_supI2)
next
  case (6 q b s1 s2)
  show ?case 
  proof
    fix i
    assume *:\<open>i \<in> sptc x (If b s1 s2)\<close>
    show \<open>i \<in> sptc y (If b s1 s2)\<close> 
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then show ?thesis 
        using 6 * by auto
    next
      case False
      then have \<open>sptc x s2 \<subseteq> sptc y s2\<close>
        using 6 by simp
      then show ?thesis 
        using False * by auto
    qed
  qed
next
  case (7 q b I s)
  then have \<open>\<forall> q. \<Psi>tc b s x q \<subseteq> \<Psi>tc b s y q\<close>
    unfolding \<Psi>tc_def by auto
  then have \<open>lfp (\<Psi>tc b s x) \<subseteq> lfp (\<Psi>tc b s y)\<close>
    using lfp_mono by meson
  then show ?case 
    using sp_\<Psi>tc by simp
next
  case (8 q s)
  then show ?case 
    using sppc_mono monoD by (metis sptc.simps(8))
qed auto

lemma \<Psi>tc_mono: \<open>mono (\<Psi>tc b s q)\<close>
proof (rule monoI)
  fix x y :: \<open>(char list \<Rightarrow> int) set\<close>
  assume \<open>x \<subseteq> y\<close>
  {
    fix i
    assume \<open>(i \<^bold>\<Turnstile> b \<and> i \<in> sptc x s) \<or> (\<not>i \<^bold>\<Turnstile> b \<and> i \<in> q)\<close>
    then have \<open>(i \<^bold>\<Turnstile> b \<and> i \<in> sptc y s) \<or> (\<not>i \<^bold>\<Turnstile> b \<and> i \<in> q)\<close> 
      using \<open>x \<subseteq> y\<close> sptc_mono monoD by blast
  }
  then show \<open>\<Psi>tc b s q x \<subseteq> \<Psi>tc b s q y\<close> 
    unfolding \<Psi>tc_def by auto
qed

lemma sptc_wptc: \<open>-sptc (-q) s = wppc q s\<close>
proof (induct s arbitrary: q)
  case (Seq s1 s2)
  then have \<open>wppc (wppc q s2) s1 = wppc (-sptc (-q) s2) s1\<close> 
    by simp
  moreover have \<open>... = -sptc (sptc (-q) s2) s1\<close>
    using Seq by (metis double_complement)
  ultimately show ?case 
    by simp
next
  case (While b I s)
  let ?r = \<open>|UNIV :: (string \<Rightarrow> int) set set set|\<close>
  have *: \<open>-iter (\<Psi>tc b s (-q)) {} n = Iter (\<Phi>pc b s q) UNIV n\<close> for n
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?I = \<open>iter (\<Psi>tc b s (- q)) {} i\<close>
    let ?i = \<open>Iter (\<Phi>pc b s q) UNIV i\<close>
    have \<open>- \<Psi>tc b s (-q) (-(-?I)) = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> -sptc (-(-?I)) s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      unfolding \<Psi>tc_def by auto
    moreover have \<open>... = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc (-?I) s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      using While by blast
    moreover have \<open>... = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wppc ?i s) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
      using 2 by simp
    moreover have \<open>... = \<Phi>pc b s q ?i\<close>
      unfolding \<Phi>pc_def by simp
    ultimately show ?case 
      by simp
  next
    case (3 i)
    let ?I = \<open>\<lambda> i. iter (\<Psi>tc b s (- q)) {} i\<close>
    let ?i = \<open>\<lambda> i. Iter (\<Phi>pc b s q) UNIV i\<close>
    have \<open>- ?I i = - \<Union> {?I j | j. j \<in> underS ?r i}\<close> 
      by (simp add: "3.hyps"(1) "3.hyps"(2) Setcompr_eq_image)
    moreover have \<open>... = \<Inter> {- ?I j | j. j \<in> underS ?r i}\<close> 
      by auto
    moreover have \<open>... = \<Inter> {?i j | j. j \<in> underS ?r i}\<close> 
      using 3 by auto
    moreover have \<open>... = ?i i\<close> 
      by (simp add: "3.hyps"(1) "3.hyps"(2) Setcompr_eq_image)
    ultimately show ?case 
      by simp
  qed
  let ?m = \<open>max2 ?r (Fix\<delta> (\<Psi>tc b s (-q)) {}) (FIX\<delta> (\<Phi>pc b s q) UNIV)\<close>
  from * have \<open>-iter (\<Psi>tc b s (-q)) {} ?m = Iter (\<Phi>pc b s q) UNIV ?m\<close>
    by simp
  then have \<open>-lfp (\<Psi>tc b s (-q)) = gfp (\<Phi>pc b s q)\<close> 
    by (metis FIX_def FIX_in_Field_and_fixed FIX_is_gfp Fix_def Fix_is_lfp \<Phi>pc_mono \<Psi>tc_mono fmax reach_fixpoint_above' top_greatest yfmax)
  then show ?case 
    using sp_\<Psi>tc wp_\<Phi>pc by blast
next
  case (Ghost s)
  then show ?case 
    by (simp add: sppc_wptc)
qed auto

(*proof that my \<Phi> transformers mean the same as those of the paper Quantitative Strongest Post*)
lemma \<open>{i. (i \<^bold>\<Turnstile> b \<and> i \<in> x) \<or> (\<not>i \<^bold>\<Turnstile> b \<and> i \<in> q)} = {i. (i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> x) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> q)}\<close>
  by auto

(*this also kind of shows that the dual of an if-then-else statement is also an if-then-else statement*)
lemma \<open>(if x then a else b) = (\<not>(if x then \<not>a else \<not>b))\<close> 
  by auto


end