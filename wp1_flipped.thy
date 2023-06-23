theory wp1_flipped imports wp1 
begin

lemma wp_conjunctive':
  \<open>wppc p s \<inter> wppc q s \<supseteq> wppc (p \<inter> q) s\<close> \<open>wptc p s \<inter> wptc q s \<supseteq> wptc (p \<inter> q) s\<close> 
  using wppc_mono wptc_mono monoD by blast+

lemma erase_assert_weakens': \<open>wppc q s \<subseteq> wppc q (erase_assert s)\<close>
proof (induct s arbitrary: q)
  case (Seq s1 s2)
  then have \<open>wppc (wppc q s2) s1 \<subseteq> wppc (wppc q s2) (erase_assert s1)\<close>
    by simp
  moreover have \<open>... \<subseteq> wppc (wppc q (erase_assert s2)) (erase_assert s1)\<close>
    using wppc_mono monotoneD Seq by meson
  ultimately show ?case 
    by simp
next
  case (While b I s)
  then have \<open>\<forall> x. \<Phi>pc b s q x \<subseteq> \<Phi>pc b (erase_assert s) q x\<close>
    unfolding \<Phi>pc_def by auto
  then show ?case 
    by (metis erase_assert.simps(7) gfp_mono wp_\<Phi>pc)
qed (auto simp add: erase_assert_weakens)


primrec gc_check' where 
  \<open>gc_check' g (Assert b) = False\<close> |
  \<open>gc_check' g (Var x) = g x\<close> |
  \<open>gc_check' g (Assign x a) = g x\<close> |
  \<open>gc_check' g (Choice s1 s2) = (gc_check' g s1 \<and> gc_check' g s2)\<close> |
  \<open>gc_check' g (Seq s1 s2) = (gc_check' g s1 \<and> gc_check' g s2)\<close> |
  \<open>gc_check' g (If b s1 s2) = (gc_check' g s1 \<and> gc_check' g s2)\<close> | 
  \<open>gc_check' g (While b I s) = (gc_check' g s)\<close> |
  \<open>gc_check' g (Ghost s) = gc_check' g s\<close>

lemma gc_check_lemma':
  \<open>gc_check' g s \<Longrightarrow> Q \<supseteq> q \<Longrightarrow> regular_s g q \<Longrightarrow> wptc Q s \<supseteq> q \<inter> wptc t (erase_assert s)\<close>
proof (induct s arbitrary: q Q t)
  case (Var x)
  show ?case
  proof clarify
    fix i
    assume \<open>i \<in> q\<close>
    then have \<open>\<forall> v. i(x := v) \<in> q\<close>
      using Var by (simp add: regular_alt)
    then show \<open>i \<in> wptc Q (Var x)\<close>
      using Var by auto
  qed
next
  case (Assign x a)
  then show ?case 
  proof clarify
    fix i
    assume \<open>i \<in> q\<close>
    then have \<open>\<forall> v. i(x := v) \<in> q\<close>
      using Assign by (simp add: regular_alt)
    then have \<open>i(x := i\<lparr>a\<rparr>) \<in> Q\<close>
      using Assign by auto
    then show \<open>i \<in> wptc Q (Assign x a)\<close>
      by auto
  qed
next
  case (Choice s1 s2)
  then have \<open>q \<inter> wptc t (erase_assert s1) \<inter> wptc t (erase_assert s2) \<subseteq> wptc Q s1 \<inter> wptc Q s2\<close> 
    by (smt (verit, ccfv_SIG) Int_Un_distrib2 Int_Un_eq(1) Int_left_absorb Int_mono gc_check'.simps(4) le_supE)
  then show ?case 
    by auto
next
  case (Seq s1 s2)
  then have \<open>q \<inter> wptc t (erase_assert s2) \<subseteq> wptc Q s2\<close>
    by auto
  then have \<open>q \<subseteq> wptc Q s2 \<union> - wptc t (erase_assert s2)\<close> 
    by auto
  then have \<open>q \<inter> wptc (wptc t (erase_assert s2)) (erase_assert s1) \<subseteq> 
    wptc (wptc Q s2 \<union> - wptc t (erase_assert s2)) s1 \<inter> wptc (wptc t (erase_assert s2)) (erase_assert s1)\<close>
    using Seq by simp
  moreover have \<open>... \<subseteq> wptc (wptc Q s2 \<union> - wptc t (erase_assert s2)) s1 \<inter> wptc (wptc t (erase_assert s2)) s1\<close> 
    by (metis Int_commute erase_assert_conjunctive_wptc subset_antisym wp_conjunctive'(2) wp_conjunctive(2))
  moreover have \<open>... \<subseteq> wptc ((wptc Q s2 \<union> - wptc t (erase_assert s2)) \<inter> wptc t (erase_assert s2)) s1\<close> 
    by (simp add: wp_conjunctive(2))
  moreover have \<open>... \<subseteq> wptc (wptc Q s2) s1\<close> 
    by (metis (no_types, opaque_lifting) Compl_disjoint inf.cobounded1 inf.order_iff inf_commute inf_sup_distrib1 wp_conjunctive'(2))
  ultimately show ?case 
    by auto
next
  case (If b s1 s2)
  {
    fix i
    assume \<open>i \<in> q \<inter> (if i \<^bold>\<Turnstile> b then wptc t (erase_assert s1) else wptc t (erase_assert s2))\<close>
    moreover have \<open>q \<inter> wptc t (erase_assert s1) \<subseteq> wptc Q s1\<close> \<open>q \<inter> wptc t (erase_assert s2) \<subseteq> wptc Q s2\<close> 
      using If by auto
    ultimately have \<open>(i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc Q s1) \<and> (\<not>i \<^bold>\<Turnstile> b \<longrightarrow> i \<in> wptc Q s2)\<close> 
      by auto
  }
  then show ?case  
    by auto
next
  case (While b I s)
  let ?r = \<open>|UNIV :: (string \<Rightarrow> int) set set set|\<close>
  have *: \<open>q \<inter> iter (\<Phi>tc b (erase_assert s) t) {} n \<subseteq> iter (\<Phi>tc b s Q) {} n\<close> for n 
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case 1
    then show ?case 
      by simp
  next
    case (2 i)
    let ?it = \<open>iter (\<Phi>tc b (erase_assert s) t) {} i\<close>
    let ?iQ = \<open>iter (\<Phi>tc b s Q) {} i\<close>
    from 2 have \<open>q \<subseteq> ?iQ \<union> - ?it\<close> 
      by auto
    with While have \<open>q \<inter> wptc ?it (erase_assert s) \<subseteq> wptc (?iQ \<union> - ?it) s \<inter> wptc ?it (erase_assert s)\<close> 
      by simp
    moreover have \<open>... \<subseteq> wptc ((?iQ \<union> - ?it) \<inter> ?it) s\<close> 
      by (simp add: Int_commute erase_assert_conjunctive_wptc)
    moreover have \<open>... \<subseteq> wptc ?iQ s\<close> 
      by (metis (no_types, opaque_lifting) Compl_disjoint Int_commute Int_subset_iff boolean_algebra.conj_disj_distrib wp_conjunctive'(2))
    ultimately have \<open>q \<inter> \<Phi>tc b (erase_assert s) t ?it \<subseteq> \<Phi>tc b s Q ?iQ\<close>
      unfolding \<Phi>tc_def using While by blast 
    then show ?case 
      by simp
  next
    case (3 i)
    then have \<open>q \<inter> \<Union> {iter (\<Phi>tc b (erase_assert s) t) {} j | j. j \<in> underS ?r i} \<subseteq> \<Union> {iter (\<Phi>tc b s Q) {} j | j. j \<in> underS ?r i}\<close> 
      by auto
    then show ?case 
      using 3 by auto
  qed
  let ?m = \<open>max2 ?r (Fix\<delta> (\<Phi>tc b (erase_assert s) t) {}) (Fix\<delta> (\<Phi>tc b s Q) {})\<close>
  from * have \<open>q \<inter> iter (\<Phi>tc b (erase_assert s) t) {} ?m \<subseteq> iter (\<Phi>tc b s Q) {} ?m\<close> .
  then have \<open>q \<inter> lfp (\<Phi>tc b (erase_assert s) t) \<subseteq> lfp (\<Phi>tc b s Q)\<close> 
    by (metis Fix_def Fix_is_lfp \<Phi>tc_mono fmax gmax)
  then show ?case 
    using wp_\<Phi>tc by simp
qed auto


primrec rc_check' where
  \<open>rc_check' g (Assert b) = regular_p g b\<close> |
  \<open>rc_check' g (Var x) = True\<close> |
  \<open>rc_check' g (Assign x a) = regular_a g a\<close> |
  \<open>rc_check' g (Choice s1 s2) = (rc_check' g s1 \<and> rc_check' g s2)\<close> |
  \<open>rc_check' g (Seq s1 s2) = (rc_check' g s1 \<and> rc_check' g s2)\<close> |
  \<open>rc_check' g (If b s1 s2) = (regular_p g b \<and> rc_check' g s1 \<and> rc_check' g s2)\<close> |
  \<open>rc_check' g (While b I s) = (regular_p g b \<and> rc_check' g s)\<close> |
  \<open>rc_check' g (Ghost s) = gc_check' g s\<close> 

lemma regular_wp': \<open>regular_s g q \<Longrightarrow> rc_check' g s \<Longrightarrow> regular_s g (wptc q (erase_ghost s))\<close>
proof (induct s arbitrary: q)
  case (Assert x)
  then show ?case 
    by (metis (no_types, lifting) erase_ghost.simps(1) mem_Collect_eq rc_check'.simps(1) regular_agree_pexp wptc.simps(1))
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
    by (metis Int_iff erase_ghost.simps(4) rc_check'.simps(4) wptc.simps(4))
next
  case (Seq s1 s2)
  then have \<open>rc_check' g s2\<close>
    by simp
  then have \<open>regular_s g (wptc q (erase_ghost s2))\<close> 
    using Seq(2,3) by blast
  moreover have \<open>rc_check' g s1\<close>
    using Seq by simp
  ultimately have \<open>regular_s g (wptc (wptc q (erase_ghost s2)) (erase_ghost s1))\<close>
    using Seq(1) by blast
  then show ?case 
    by simp
next
  case (If b s1 s2)
  then have \<open>rc_check' g s1\<close>
    by simp
  then have 1: \<open>regular_s g (wptc q (erase_ghost s1))\<close> 
    using If(1,3) by blast
  from If have \<open>rc_check' g s2\<close>
    by simp
  then have 2: \<open>regular_s g (wptc q (erase_ghost s2))\<close> 
    using If(2,3) by blast
  from If have \<open>regular_p g b\<close> 
    by auto
  with 1 2 show ?case 
    using regular_agree_pexp 
    by (metis (mono_tags, lifting) erase_ghost.simps(6) mem_Collect_eq wptc.simps(6))
next
  case (While b I s)
  let ?phi = \<open>\<Phi>tc b (erase_ghost s) q\<close>
  have \<open>{i. \<exists> j \<in> iter ?phi {} n. i \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> iter ?phi {} n\<close> for n 
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case (2 i)
    then have \<open>regular_s g (iter ?phi {} i)\<close>
      by auto
    then have \<open>regular_s g (wptc (iter ?phi {} i) (erase_ghost s))\<close>
      using While by auto
    then have \<open>{k. \<exists>j\<in> ?phi (iter ?phi {} i). k \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> ?phi (iter ?phi {} i)\<close>
      using \<Phi>tc_def While regular_agree_pexp 
      by (smt (verit, ccfv_SIG) mem_Collect_eq rc_check'.simps(7) subsetI)
    then show ?case 
      by auto
  qed auto
  then have \<open>{i. \<exists> j \<in> lfp ?phi. i \<^bold>\<down> g = j \<^bold>\<down> g} \<subseteq> lfp ?phi\<close> 
    using \<Phi>tc_mono iter_induct_lfp by meson
  then have \<open>regular_s g (lfp ?phi)\<close> 
    by auto
  then show ?case 
    by (metis erase_ghost.simps(7) wp_\<Phi>tc)
qed auto

lemma rc_check_lemma_wp':
  assumes \<open>rc_check' g s\<close> \<open>regular_s g Q\<close> \<open>q \<supseteq> Q\<close> 
  shows \<open>wptc q s \<supseteq> wptc Q (erase_ghost s) \<inter> wppc t (erase_assert s)\<close>
  using assms
proof (induct s arbitrary: Q q t)
  case (Choice s1 s2)
  then have \<open>rc_check' g s1\<close> \<open>rc_check' g s2\<close>
    by simp_all
  then have \<open>wptc q s1 \<supseteq> wptc Q (erase_ghost s1) \<inter> wppc t (erase_assert s1)\<close> \<open>wptc q s2 \<supseteq> wptc Q (erase_ghost s2) \<inter> wppc t (erase_assert s2)\<close>
    using Choice by simp_all
  then show ?case 
    by auto
next
  case (Seq s1 s2)
  then have \<open>wptc q s2 \<supseteq> wptc Q (erase_ghost s2) \<inter> wppc t (erase_assert s2)\<close> 
    by auto
  then have \<open>wptc q s2 \<union> - wppc t (erase_assert s2) \<supseteq> wptc Q (erase_ghost s2)\<close> 
    by auto
  moreover have \<open>regular_s g (wptc Q (erase_ghost s2))\<close> 
    using rc_check'.simps(5) regular_wp' Seq by blast
  ultimately have \<open>wptc (wptc Q (erase_ghost s2)) (erase_ghost s1) \<inter> wppc (wppc t (erase_assert s2)) (erase_assert s1) \<subseteq> 
    wptc (wptc q s2 \<union> - wppc t (erase_assert s2)) s1 \<inter> wppc (wppc t (erase_assert s2)) (erase_assert s1)\<close>
    using Seq by auto
  moreover have \<open>... \<subseteq> wptc ((wptc q s2 \<union> - wppc t (erase_assert s2)) \<inter> wppc t (erase_assert s2)) s1\<close> 
    by (simp add: Int_commute wp1.t_wppc')
  moreover have \<open>... \<subseteq> wptc (wptc q s2) s1\<close> 
    by (metis Int_subset_iff boolean_algebra.conj_cancel_left boolean_algebra.conj_disj_distrib2 sup_bot.right_neutral wp_conjunctive'(2)) 
  ultimately show ?case 
    by auto
next
  case (If b s1 s2)
  show ?case 
  proof (clarify)
    fix i 
    assume a: \<open>i \<in> wptc Q (erase_ghost (If b s1 s2))\<close>
    assume b: \<open>i \<in> wppc t (erase_assert (com.If b s1 s2))\<close>
    show \<open>i \<in> wptc q (If b s1 s2)\<close>
    proof (cases \<open>i \<^bold>\<Turnstile> b\<close>)
      case True
      then show ?thesis 
        using a b If by auto
    next
      case False
      then have \<open>i \<in> wptc Q (erase_ghost s2)\<close> \<open>i \<in> wppc t (erase_assert s2)\<close>
        using a b by simp_all
      then have \<open>i \<in> wptc q s2\<close> 
        using If(2-5) False by auto
      then show ?thesis
        using False by simp
    qed
  qed
next
  case (While b I s)
  let ?Q = \<open>\<Phi>tc b (erase_ghost s) Q\<close>
  let ?q = \<open>\<Phi>tc b s q\<close>
  let ?t = \<open>\<Phi>pc b (erase_assert s) t\<close>
  have Qr: \<open>regular_s g (iter ?Q {} n)\<close> for n
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case (2 i)
    from 2(2) have \<open>regular_s g (wptc (iter ?Q {} i) (erase_ghost s))\<close> 
      using regular_wp' While(2) by auto (*takes a while*)
    moreover have \<open>regular_p g b\<close> 
      using While by auto
    ultimately have \<open>regular_s g (?Q (iter ?Q {} i))\<close>
      unfolding \<Phi>tc_def using regular_agree_pexp  While.prems(2) mem_Collect_eq by blast
    then show ?case 
      by simp
  next
    case (3 i)
    then show ?case 
      by (smt (verit) UN_iff iter_lim)
  qed auto

  have \<open>iter ?Q {} n \<inter> Iter ?t UNIV n \<subseteq> iter ?q {} n\<close> for n 
  proof (induct n rule:  wo_rel.well_order_inductZSL[OF wo_rel_r])
    case (2 i)
    let ?iQ = \<open>iter ?Q {} i\<close>
    let ?iq = \<open>iter ?q {} i\<close>
    let ?it = \<open>Iter ?t UNIV i\<close>
    from 2 have \<open>?iQ \<subseteq> ?iq \<union> - ?it\<close> 
      by auto
    moreover have \<open>regular_s g ?iQ\<close> 
      using Qr by simp
    ultimately have \<open>wptc ?iQ (erase_ghost s) \<inter> wppc ?it (erase_assert s) \<subseteq> wptc (?iq \<union> - ?it) s \<inter> wppc ?it (erase_assert s)\<close>
      using While by auto
    moreover have \<open>... \<subseteq> wptc ((?iq \<union> - ?it) \<inter> ?it) s\<close> 
      by (simp add: Int_commute t_wppc')
    moreover have \<open>... \<subseteq> wptc ?iq s\<close> 
      by (smt (z3) Compl_disjoint Int_commute Int_subset_iff boolean_algebra.conj_disj_distrib wp_conjunctive'(2))
    ultimately have \<open>wptc ?iQ (erase_ghost s) \<inter> wppc ?it (erase_assert s) \<subseteq> wptc ?iq s\<close>
      by auto
    then have \<open>?Q ?iQ \<inter> ?t ?it \<subseteq> ?q ?iq\<close> 
      unfolding \<Phi>tc_def \<Phi>pc_def using While(4) by auto
    then show ?case 
      by simp
  qed auto
  then have \<open>lfp ?Q \<inter> gfp ?t \<subseteq> lfp ?q\<close> 
    using \<Phi>pc_mono \<Phi>tc_mono Iter_iter_induct_gfp3 by meson
  then show ?case 
    using wp_\<Phi>pc wp_\<Phi>tc by auto
next
  case (Ghost s)
  then show ?case
    using gc_check_lemma' by simp
qed auto


fun wpxa where (*computable weakest precondition for partial incorrectness*)
  \<open>wpxa q (Assert r) = r \<^bold>\<and> q\<close> |
  \<open>wpxa q (Var x) = Uni x q\<close> |
  \<open>wpxa q (Assign x a) = psubst x a q\<close> |
  \<open>wpxa q (Choice s1 s2) = wpxa q s1 \<^bold>\<and> wpxa q s2\<close> |
  \<open>wpxa q (Seq s1 s2) = wpxa (wpxa q s2) s1\<close> |
  \<open>wpxa q (If b s1 s2) = (b \<^bold>\<longrightarrow> wpxa q s1) \<^bold>\<and> (\<^bold>\<not>b \<^bold>\<longrightarrow> wpxa q s2)\<close> |
  \<open>wpxa q (While b I s) = uni_all (((b \<^bold>\<longrightarrow> wpxa I s) \<^bold>\<and> (\<^bold>\<not>b \<^bold>\<longrightarrow> q)) \<^bold>\<longrightarrow> I) \<^bold>\<longrightarrow> I\<close> |
  \<open>wpxa q (Ghost s) = wpxa q s\<close>


lemma wpxa_mono: \<open>i \<^bold>\<Turnstile> wpxa p s \<Longrightarrow> (\<forall> i. i \<^bold>\<Turnstile> p \<longrightarrow> i \<^bold>\<Turnstile> q) \<Longrightarrow> i \<^bold>\<Turnstile> wpxa q s\<close>
proof (induct p s arbitrary: i p q rule: wpxa.induct)
  case (3 q x a)
  then show ?case 
    using psubst_iff_psem by auto
qed auto


lemma wpxa_wptc: \<open>{i. i \<^bold>\<Turnstile> wpxa q s} \<supseteq> wptc {i. i \<^bold>\<Turnstile> q} s\<close>
proof (induct s arbitrary: q)
  case (Assign x a)
  then show ?case 
    by (simp add: psubst_iff_psem)
next
  case (Seq s1 s2)
  then have \<open>wptc (wptc {i. i \<^bold>\<Turnstile> q} s2) s1 \<subseteq> wptc {i. i \<^bold>\<Turnstile> wpxa q s2} s1\<close>
    using wptc_mono monoD by metis
  moreover have \<open>... \<subseteq> {i. i \<^bold>\<Turnstile> wpxa (wpxa q s2) s1}\<close>
    using Seq by simp
  ultimately show ?case 
    by simp
next
  case (While b I s)
  show ?case 
  proof (cases \<open>\<forall> i. i \<^bold>\<Turnstile> (b \<^bold>\<longrightarrow> wpxa I s) \<^bold>\<and> (\<^bold>\<not>b \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> I\<close>)
    case True
    then have *: \<open>{i. i \<^bold>\<Turnstile> wpxa q (While b I s)} = {i. i \<^bold>\<Turnstile> I}\<close> 
      by simp
    have \<open>wptc {i. i \<^bold>\<Turnstile> I} s \<subseteq> {i. i \<^bold>\<Turnstile> wpxa I s}\<close>
      using While by simp
    then have \<open>\<Phi>tc b s {i. i \<^bold>\<Turnstile> q} {i. i \<^bold>\<Turnstile> I} \<subseteq> {i. i \<^bold>\<Turnstile> (b \<^bold>\<longrightarrow> wpxa I s) \<^bold>\<and> (\<^bold>\<not>b \<^bold>\<longrightarrow> q)}\<close> 
      unfolding \<Phi>tc_def by auto
    then have \<open>\<Phi>tc b s {i. i \<^bold>\<Turnstile> q} {i. i \<^bold>\<Turnstile> I} \<subseteq> {i. i \<^bold>\<Turnstile> I}\<close>
      using True by auto
    then have \<open>lfp (\<Phi>tc b s {i. i \<^bold>\<Turnstile> q}) \<subseteq> {i. i \<^bold>\<Turnstile> I}\<close> 
      by (simp add: lfp_lowerbound)
    then show ?thesis 
      using * wp_\<Phi>tc by blast
  next
    case False
    then have \<open>\<forall> i. i \<^bold>\<Turnstile> wpxa q (While b I s)\<close>  
      by auto
    then show ?thesis 
      by blast
  qed
qed auto


lemma rc_check_lemma_wpxa:
  assumes \<open>rc_check' g s\<close> \<open>regular_s g Q\<close> \<open>Q \<subseteq> {i. i \<^bold>\<Turnstile> q}\<close>
  shows \<open>{i. i \<^bold>\<Turnstile> wpxa q s} \<supseteq> wptc Q (erase_ghost s) \<inter> wppc t (erase_assert s)\<close>
proof-
  have \<open>{i. i \<^bold>\<Turnstile> wpxa q s} \<supseteq> wptc {i. i \<^bold>\<Turnstile> q} s\<close> 
    using wpxa_wptc by simp
  moreover have \<open>wptc {i. i \<^bold>\<Turnstile> q} s \<supseteq> wptc Q (erase_ghost s) \<inter> wppc t (erase_assert s)\<close>
    using assms rc_check_lemma_wp' by blast
  ultimately show ?thesis 
    by simp
qed

corollary ghost_erase_well_formed:
  assumes \<open>rc_check' g s\<close> \<open>regular_s g p\<close> \<open>regular_p g q\<close>
    and \<open>{i. i \<^bold>\<Turnstile> wpxa q s} \<subseteq> p\<close> \<open>-wppc UNIV (erase_assert s) \<subseteq> p\<close>
  shows \<open>wptc {i. i \<^bold>\<Turnstile> q} (erase_ghost s) \<subseteq> p\<close> 
proof-
  have \<open>regular_s g {i. i \<^bold>\<Turnstile> q}\<close> 
    by (metis assms(3) mem_Collect_eq regular_agree_pexp)
  then have \<open>wptc {i. i \<^bold>\<Turnstile> q} (erase_ghost s) \<inter> wppc UNIV (erase_assert s) \<subseteq> {i. i \<^bold>\<Turnstile> wpxa q s}\<close>
    using assms rc_check_lemma_wpxa by simp
  then have \<open>wptc {i. i \<^bold>\<Turnstile> q} (erase_ghost s) \<subseteq> {i. i \<^bold>\<Turnstile> wpxa q s} \<union> - wppc UNIV (erase_assert s)\<close>
    by auto
  then show ?thesis
    using assms by auto
qed
end