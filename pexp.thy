theory pexp imports Main
begin

datatype aop 
  = Ad
  | Su
  | Mu
  | Di

datatype aexp 
  = N int
  | V string
  | Op aexp aop aexp

definition Add (infixl \<open>\<^bold>+\<close> 211) where \<open>a \<^bold>+ b \<equiv> Op a Ad b\<close>
definition Sub (infixl \<open>\<^bold>-\<close> 210) where \<open>a \<^bold>- b \<equiv> Op a Su b\<close>
definition Mul (infixl \<open>\<^bold>*\<close> 216) where \<open>a \<^bold>* b \<equiv> Op a Mu b\<close>
definition Div (infixl \<open>\<^bold>:\<close> 215) where \<open>a \<^bold>: b \<equiv> Op a Di b\<close>

notation (input) insert (infixr \<open>\<^bold>\<rightarrow>\<close> 160)

primrec aopsem :: \<open>int \<Rightarrow> int \<Rightarrow> aop \<Rightarrow> int\<close> where
  \<open>aopsem x y Ad = x + y\<close> |
  \<open>aopsem x y Su = x - y\<close> |
  \<open>aopsem x y Mu = x * y\<close> |
  \<open>aopsem x y Di = x div y\<close>

primrec asem (\<open>_\<lparr> _ \<rparr>\<close> [102,102] 102) where
  \<open>asem i (N v) = v\<close> |
  \<open>asem i (V x) = i x\<close> |
  \<open>asem i (Op a p b) = aopsem (asem i a) (asem i b) p\<close>

lemma addsem[simp]: \<open>asem i (a \<^bold>+ b) = (asem i a) + (asem i b)\<close> unfolding Add_def by simp
lemma supsem[simp]: \<open>asem i (a \<^bold>- b) = (asem i a) - (asem i b)\<close> unfolding Sub_def by simp
lemma mulsem[simp]: \<open>asem i (a \<^bold>* b) = (asem i a) * (asem i b)\<close> unfolding Mul_def by simp
lemma divsem[simp]: \<open>asem i (a \<^bold>: b) = (asem i a) div (asem i b)\<close> unfolding Div_def by simp

datatype acomp 
  = Eq
  | Lt

datatype pexp
  = Neg pexp (\<open>\<^bold>\<not>_\<close> [199] 200)
  | Con pexp pexp (infixl \<open>\<^bold>\<and>\<close> 150)
  | Uni string pexp (\<open>\<^bold>\<forall> _. _\<close> [102,102] 102)
  | A aexp acomp aexp

definition Eql (infix \<open>\<^bold>=\<close> 205) where \<open>a \<^bold>= b \<equiv> A a Eq b\<close>
definition Ltn (infix \<open>\<^bold><\<close> 205) where \<open>a \<^bold>< b \<equiv> A a Lt b\<close>

definition Dis (infixl \<open>\<^bold>\<or>\<close> 140) where \<open>a \<^bold>\<or> b \<equiv> \<^bold>\<not>(\<^bold>\<not>a \<^bold>\<and> \<^bold>\<not>b)\<close>
definition Imp (infixr \<open>\<^bold>\<longrightarrow>\<close> 120) where \<open>a \<^bold>\<longrightarrow> b \<equiv> \<^bold>\<not>(a \<^bold>\<and> \<^bold>\<not>b)\<close>
definition Tru (\<open>\<^bold>\<top>\<close>) where \<open>\<^bold>\<top> \<equiv> (N 0) \<^bold>= (N 0)\<close>
definition Fls (\<open>\<^bold>\<bottom>\<close>) where \<open>\<^bold>\<bottom> \<equiv> \<^bold>\<not>\<^bold>\<top>\<close>
definition Exi (\<open>\<^bold>\<exists> _. _\<close> [101,101] 100) where \<open>\<^bold>\<exists> x. p \<equiv> \<^bold>\<not>(\<^bold>\<forall> x. \<^bold>\<not>p)\<close>

definition Leq (infix \<open>\<^bold>\<le>\<close> 205) where \<open>a \<^bold>\<le> b \<equiv> a \<^bold>< b \<^bold>\<or> a \<^bold>= b\<close>
definition Gtn (infix \<open>\<^bold>>\<close> 205) where \<open>a \<^bold>> b \<equiv> \<^bold>\<not>a \<^bold>< b \<^bold>\<and> \<^bold>\<not>a \<^bold>= b\<close>
definition Geq (infix \<open>\<^bold>\<ge>\<close> 205) where \<open>a \<^bold>\<ge> b \<equiv> \<^bold>\<not>a \<^bold>< b\<close>

primrec acompsem :: \<open>int \<Rightarrow> int \<Rightarrow> acomp \<Rightarrow> bool\<close> where
  \<open>acompsem x y Eq = (x = y)\<close> |
  \<open>acompsem x y Lt = (x < y)\<close>

primrec psem (infix \<open>\<^bold>\<Turnstile>\<close> 101) where
  \<open>psem i (Neg p) = (\<not>psem i p)\<close> |
  \<open>psem i (Con p q) = (psem i p \<and> psem i q)\<close> |
  \<open>psem i (Uni x p) = (\<forall> v. psem (i(x := v)) p)\<close> |
  \<open>psem i (A a c b) = acompsem (asem i a) (asem i b) c\<close>

term \<open>i \<^bold>\<Turnstile> N 3 \<^bold>> V x\<close>

lemma eqlsem[simp]: \<open>psem i (a \<^bold>= b) = (asem i a = asem i b)\<close> unfolding Eql_def by simp
lemma ltnsem[simp]: \<open>psem i (a \<^bold>< b) = (asem i a < asem i b)\<close> unfolding Ltn_def by simp
lemma dissem[simp]: \<open>psem i (a \<^bold>\<or> b) = (psem i a \<or> psem i b)\<close> unfolding Dis_def by simp
lemma impsem[simp]: \<open>psem i (a \<^bold>\<longrightarrow> b) = (psem i a \<longrightarrow> psem i b)\<close> unfolding Imp_def by simp
lemma trusem[simp]: \<open>psem i \<^bold>\<top>\<close> unfolding Tru_def Eql_def by simp
lemma flssem[simp]: \<open>\<not>psem i \<^bold>\<bottom>\<close> unfolding Fls_def by simp
lemma leqsem[simp]: \<open>psem i (a \<^bold>\<le> b) = (asem i a \<le> asem i b)\<close> unfolding Leq_def by force
lemma gtnsem[simp]: \<open>psem i (a \<^bold>> b) = (asem i a > asem i b)\<close> unfolding Gtn_def by force
lemma geqsem[simp]: \<open>psem i (a \<^bold>\<ge> b) = (asem i a \<ge> asem i b)\<close> unfolding Geq_def by force
lemma exisem[simp]: \<open>psem i (\<^bold>\<exists> x. p) = (\<exists> v. psem (i(x := v)) p)\<close> unfolding Exi_def by force


section \<open>free variables and substitution\<close>

primrec aexp_fv where
  \<open>aexp_fv (N v) = {}\<close> |
  \<open>aexp_fv (V y) = {y}\<close> |
  \<open>aexp_fv (Op b p c) = aexp_fv b \<union> aexp_fv c\<close>

lemma aexp_fv_finite: \<open>finite (aexp_fv a)\<close>
  by (induct a) auto

primrec pexp_fv where
  \<open>pexp_fv (Neg p) = pexp_fv p\<close> |
  \<open>pexp_fv (Con p q) = pexp_fv p \<union> pexp_fv q\<close> |
  \<open>pexp_fv (Uni y p) = pexp_fv p - {y}\<close> |
  \<open>pexp_fv (A b p c) = aexp_fv b \<union> aexp_fv c\<close>

lemma exi_fv[simp]: \<open>pexp_fv (\<^bold>\<exists> v. p) = pexp_fv p - {v}\<close> unfolding Exi_def by auto
lemma dis_fv[simp]: \<open>pexp_fv (a \<^bold>\<or> b) = (pexp_fv a \<union> pexp_fv b)\<close> unfolding Dis_def by auto
lemma imp_fv[simp]: \<open>pexp_fv (a \<^bold>\<longrightarrow> b) = (pexp_fv a \<union> pexp_fv b)\<close> unfolding Imp_def by auto
lemma tru_fv[simp]: \<open>pexp_fv \<^bold>\<top> = {}\<close> unfolding Tru_def Eql_def by simp
lemma fls_fv[simp]: \<open>pexp_fv \<^bold>\<bottom> = {}\<close> unfolding Fls_def by simp

lemma pexp_fv_finite: \<open>finite (pexp_fv b)\<close>
  using aexp_fv_finite by (induct b) auto

definition \<open>fresh ss \<equiv> SOME s. s \<notin> ss\<close>

lemma fresh_finite: \<open>finite (s :: string set) \<Longrightarrow> fresh s \<notin> s\<close>
  unfolding fresh_def by (metis ex_new_if_finite infinite_UNIV_listI tfl_some)

lemma fresh_fv: \<open>fresh (aexp_fv a) \<notin> aexp_fv a\<close> \<open>fresh (pexp_fv b) \<notin> pexp_fv b\<close>
  using fresh_finite by (simp_all add: aexp_fv_finite pexp_fv_finite)

primrec asubst where
  \<open>asubst x a (N v) = N v\<close> |
  \<open>asubst x a (V y) = (if x = y then a else V y)\<close> |
  \<open>asubst x a (Op b p c) = Op (asubst x a b) p (asubst x a c)\<close>

lemma addsubst[simp]: \<open>asubst x a (v \<^bold>+ w) = (asubst x a v \<^bold>+ asubst x a w)\<close> unfolding Add_def by simp
lemma supsubst[simp]: \<open>asubst x a (v \<^bold>- w) = (asubst x a v \<^bold>- asubst x a w)\<close> unfolding Sub_def by simp
lemma mulsubst[simp]: \<open>asubst x a (v \<^bold>* w) = (asubst x a v \<^bold>* asubst x a w)\<close> unfolding Mul_def by simp
lemma dovsubst[simp]: \<open>asubst x a (v \<^bold>: w) = (asubst x a v \<^bold>: asubst x a w)\<close> unfolding Div_def by simp

lemma asubst_iff_asem: \<open>asem i (asubst x a b) = asem (i(x := asem i a)) b\<close>
  by (induct b) auto

primrec pexp_size where
  \<open>pexp_size (Neg p) = (1 :: nat) + pexp_size p\<close> |
  \<open>pexp_size (Con p q) = 1 + pexp_size p + pexp_size q\<close> |
  \<open>pexp_size (Uni v p) = 1 + pexp_size p\<close> |
  \<open>pexp_size (A v c w) = 1\<close>

function (domintros) psubst where
  \<open>psubst x a (Neg p) = \<^bold>\<not>psubst x a p\<close> |
  \<open>psubst x a (Con p q) = psubst x a p \<^bold>\<and> psubst x a q\<close> |
  \<open>psubst x a (Uni y p) = (
    if x = y 
    then Uni y p 
    else (
      if y \<in> aexp_fv a 
      then (let y' = fresh (x \<^bold>\<rightarrow> aexp_fv a \<union> pexp_fv p) in Uni y' (psubst x a (psubst y (V y') p)))
      else Uni y (psubst x a p)))\<close> |
  \<open>psubst x a (A v c w) = A (asubst x a v) c (asubst x a w)\<close>
  by pat_completeness auto
termination 
proof (relation \<open>measure (\<lambda> (_,_,p). pexp_size p)\<close>,clarify)
  fix x :: string 
  fix a :: aexp
  fix y p xa
  assume \<open>psubst_dom (y, V xa, p)\<close>
  then have \<open>pexp_size p = pexp_size (psubst y (V xa) p)\<close> 
  proof (induction p)
    case (3 x a y p)
    then show ?case 
      by (metis (full_types) pexp_size.simps(3) psubst.psimps(3))
  qed (auto simp add: psubst.psimps)
  then show \<open>((x, a, psubst y (V xa) p), x, a, \<^bold>\<forall> y. p) \<in> measure (\<lambda> (_,_,p). pexp_size p)\<close> 
    using in_measure by auto
qed auto

lemma psubst_preserves_pexp_size: \<open>pexp_size p = pexp_size (psubst x a p)\<close>
proof (induct p rule: psubst.induct)
  case (3 x a y p)
  then show ?case 
    by (metis pexp_size.simps(3) psubst.simps(3))
qed (auto simp add: psubst.psimps)

lemma pexp_size_gt_0: \<open>pexp_size p > 0\<close>
  by (induct p) auto

lemma ltnsubst[simp]: \<open>psubst x a (v \<^bold>< w) = (asubst x a v \<^bold>< asubst x a w)\<close> unfolding Ltn_def by simp
lemma eqlsubst[simp]: \<open>psubst x a (v \<^bold>= w) = (asubst x a v \<^bold>= asubst x a w)\<close> unfolding Eql_def by simp
lemma dissubst[simp]: \<open>psubst x a (v \<^bold>\<or> w) = (psubst x a v \<^bold>\<or> psubst x a w)\<close>
  unfolding Dis_def by simp
lemma impsubst[simp]: \<open>psubst x a (v \<^bold>\<longrightarrow> w) = (psubst x a v \<^bold>\<longrightarrow> psubst x a w)\<close>
  unfolding Imp_def by simp
lemma trusubst[simp]: \<open>psubst x a \<^bold>\<top> = \<^bold>\<top>\<close> unfolding Tru_def by simp
lemma flssubst[simp]: \<open>psubst x a \<^bold>\<bottom> = \<^bold>\<bottom>\<close> unfolding Fls_def by simp
lemma exisubst[simp]: \<open>psubst x a (\<^bold>\<exists> y. p) = (
  if x = y 
    then Exi y p 
    else (
      if y \<in> aexp_fv a 
      then (let y' = fresh (x \<^bold>\<rightarrow> aexp_fv a \<union> pexp_fv p) in Exi y' (psubst x a (psubst y (V y') p)))
      else Exi y (psubst x a p)))\<close> 
  unfolding Exi_def by (metis pexp_fv.simps(1) psubst.simps(1) psubst.simps(3))
lemma leqsubst[simp]: \<open>psubst x a (v \<^bold>\<le> w) = (asubst x a v \<^bold>\<le> asubst x a w)\<close> unfolding Leq_def by simp
lemma gtnsubst[simp]: \<open>psubst x a (v \<^bold>> w) = (asubst x a v \<^bold>> asubst x a w)\<close> unfolding Gtn_def by simp
lemma geqsubst[simp]: \<open>psubst x a (v \<^bold>\<ge> w) = (asubst x a v \<^bold>\<ge> asubst x a w)\<close> unfolding Geq_def by simp


lemma agreeing_i_aexp: \<open>y \<notin> aexp_fv a \<Longrightarrow> asem i a = asem (i(y := j)) a\<close>
  by (induct a) auto

lemma agreeing_i_pexp: \<open>y \<notin> pexp_fv p \<Longrightarrow> psem i p = psem (i(y := j)) p\<close>
proof (induct p arbitrary: i)
  case (Uni x p)
  then show ?case 
  proof (cases \<open>x = y\<close>)
    case True
    then show ?thesis 
      by (metis psem.simps(3) fun_upd_upd)
  next
    case False
    then show ?thesis 
      using Uni by (metis pexp_fv.simps(3) psem.simps(3) fun_upd_twist member_remove remove_def)
  qed
next
  case (A x1a x2 x3)
  then show ?case 
    using agreeing_i_aexp by (metis UnI1 UnI2 pexp_fv.simps(4) psem.simps(4))
qed auto

lemma psubst_iff_psem: \<open>psem i (psubst x a p) = psem (i(x := asem i a)) p\<close>
proof (induct \<open>pexp_size p\<close> arbitrary: i x a p rule: less_induct)
  case less
  then show ?case 
  proof (cases p)
    case (Uni y p)
    then show ?thesis 
    proof (cases \<open>x = y\<close>)
      case True
      then have \<open>psem i (psubst x a (\<^bold>\<forall> x. p)) = psem (i(x := asem i a)) (\<^bold>\<forall> y. p)\<close> 
        by simp
      then show ?thesis 
        using True Uni by blast
    next
      case False
      then have *:\<open>x \<noteq> y\<close> .
      show ?thesis
      proof (cases \<open>y \<in> aexp_fv a\<close>)
        case True
        let ?y = \<open>fresh (x \<^bold>\<rightarrow> aexp_fv a \<union> pexp_fv p)\<close>
        have \<open>x \<noteq> ?y\<close>
          using fresh_finite 
          by (metis Un_upper1 aexp_fv_finite pexp_fv_finite finite.insertI finite_UnI insertI1 
              subset_iff)
        have \<open>y \<noteq> ?y\<close>
          using True fresh_finite 
          by (metis UnCI aexp_fv_finite pexp_fv_finite finite.simps finite_Un insertI2)
        have \<open>?y \<notin> pexp_fv p\<close>
          using fresh_finite by (meson UnI2 aexp_fv_finite pexp_fv_finite finite.insertI finite_UnI)
        have \<open>?y \<notin> aexp_fv a\<close> 
          using fresh_finite 
          by (meson UnCI aexp_fv_finite pexp_fv_finite finite_UnI finite_insert insertCI)
        then have 1: \<open>\<forall> v. asem (i(?y := v)) a = asem i a\<close>
          using agreeing_i_aexp by simp
        from True * have \<open>psubst x a (\<^bold>\<forall> y. p) = \<^bold>\<forall> ?y. psubst x a (psubst y (V ?y) p)\<close>
          by (meson psubst.simps(3))
        then have \<open>psem i (psubst x a (\<^bold>\<forall> y. p)) = psem i (\<^bold>\<forall> ?y. psubst x a (psubst y (V ?y) p))\<close>
          by simp
        moreover have \<open>... = (\<forall> v. psem (i(?y := v)) (psubst x a (psubst y (V ?y) p)))\<close> 
          by simp
        moreover have \<open>... = (\<forall> v. psem ((i(?y := v))(x := asem i a)) (psubst y (V ?y) p))\<close>
          using Uni less psubst_preserves_pexp_size 1 by simp
        moreover have \<open>... = (\<forall> v. psem (((i(?y := v))(x := asem i a))(y := v)) p)\<close>
          using \<open>x \<noteq> ?y\<close> Uni * less by simp
        moreover have \<open>... = (\<forall> v. psem (((i(x := asem i a))(y := v))(?y := v)) p)\<close>
          using \<open>x \<noteq> ?y\<close> \<open>y \<noteq> ?y\<close> \<open>x \<noteq> y\<close> by (simp add: fun_upd_twist)
        moreover have \<open>... = (\<forall> v. psem ((i(x := asem i a))(y := v)) p)\<close>
          using \<open>?y \<notin> pexp_fv p\<close> agreeing_i_pexp by simp
        moreover have \<open>... = psem (i(x := asem i a)) (\<^bold>\<forall> y. p)\<close>
          by simp
        ultimately show ?thesis 
          using Uni by presburger
      next
        case False
        then have \<open>psem i (psubst x a (\<^bold>\<forall> y. p)) = psem i (\<^bold>\<forall> y. psubst x a p)\<close>
          using * by simp
        moreover have \<open>... = (\<forall> j. psem (i(y := j)) (psubst x a p))\<close>
          by simp
        moreover have \<open>... = (\<forall> j. psem ((i(y := j))(x := asem (i(y := j)) a)) p)\<close>
          using Uni less psubst_preserves_pexp_size by simp
        moreover have \<open>... = (\<forall> j. psem ((i(y := j))(x := asem i a)) p)\<close>
          using False agreeing_i_aexp by simp
        moreover have \<open>... = (\<forall> j. psem ((i(x := asem i a))(y := j)) p)\<close>
          using * by (simp add: fun_upd_twist)
        moreover have \<open>... = psem (i(x := asem i a)) (\<^bold>\<forall> y. p)\<close>
          by simp
        ultimately show ?thesis 
          using Uni by blast
      qed
    qed
  next
    case (A x41 x42 x43)
    from asubst_iff_asem this show ?thesis
      by (metis psem.simps(4) psubst.simps(4))
  qed auto
qed

lemma no_new_fv_asubst: \<open>aexp_fv (asubst x a' a) \<subseteq> aexp_fv a' \<union> aexp_fv a\<close>
  by (induct a) auto
lemma no_new_fv_psubst: \<open>pexp_fv (psubst x a p) \<subseteq> aexp_fv a \<union> pexp_fv p\<close>
proof (induct p rule: psubst.induct)
  case (3 x a y p)
  then show ?case 
  proof (cases \<open>x = y\<close>)
    case True
    then show ?thesis 
      using 3 by auto
  next
    case False
    then have \<open>x \<noteq> y\<close> .
    show ?thesis 
    proof (cases \<open>y \<in> aexp_fv a\<close>)
      case True
      let ?xa = \<open>fresh (x \<^bold>\<rightarrow> aexp_fv a \<union> pexp_fv p)\<close>
      from True have \<open>pexp_fv (psubst x a (psubst y (V ?xa) p)) \<subseteq> insert ?xa (aexp_fv a \<union> pexp_fv p)\<close>
        using 3 \<open>x \<noteq> y\<close> by auto
      moreover have \<open>psubst x a (\<^bold>\<forall> y. p) = \<^bold>\<forall> ?xa. psubst x a (psubst y (V ?xa) p)\<close> 
        using \<open>x \<noteq> y\<close> True by (meson psubst.simps(3))
      ultimately show ?thesis 
        using Diff_empty True by auto
    next
      case False
      then show ?thesis 
        using 3 \<open>x \<noteq> y\<close> by auto
    qed
  qed
next
  case (4 x a v c w)
  then show ?case 
    using no_new_fv_asubst by auto
qed auto

lemma pexp_size_leq_1: \<open>pexp_size b \<ge> 1\<close>
  by (induct b) auto


lemma elem_asubst_fv: 
  \<open>x \<in> aexp_fv a \<Longrightarrow> aexp_fv (asubst x b a) = (aexp_fv a - {x}) \<union> aexp_fv b\<close> 
  \<open>x \<notin> aexp_fv a \<Longrightarrow> aexp_fv (asubst x b a) = aexp_fv a\<close>
  by (induct a) auto

lemma elem_psubst_fv: 
  \<open>x \<in> pexp_fv p \<Longrightarrow> pexp_fv (psubst x a p) = (pexp_fv p - {x}) \<union> aexp_fv a\<close> 
  \<open>x \<notin> pexp_fv p \<Longrightarrow> pexp_fv (psubst x a p) = pexp_fv p\<close>
proof (induct x a p rule: psubst.induct)
  case (3 x a y p)
  let ?a1 = \<open>x \<in> pexp_fv (\<^bold>\<forall> y. p)\<close>
  let ?a2 = \<open>x \<notin> pexp_fv (\<^bold>\<forall> y. p)\<close>
  let ?g1 = \<open>pexp_fv (psubst x a (\<^bold>\<forall> y. p)) = pexp_fv (\<^bold>\<forall> y. p) - {x} \<union> aexp_fv a\<close>
  let ?g2 = \<open>pexp_fv (psubst x a (\<^bold>\<forall> y. p)) = pexp_fv (\<^bold>\<forall> y. p)\<close>
  consider 
    \<open>x = y\<close> | 
    \<open>x \<noteq> y \<and> y \<notin> aexp_fv a\<close> | 
    \<open>x \<noteq> y \<and> y \<in> aexp_fv a \<and> y \<in> pexp_fv p\<close> | 
    \<open>x \<noteq> y \<and> y \<in> aexp_fv a \<and> y \<notin> pexp_fv p\<close> by auto
  then have \<open>(?a1 \<longrightarrow> ?g1) \<and> (?a2 \<longrightarrow> ?g2)\<close> 
  proof (cases; rule conjI; clarify)
    assume *: \<open>x \<noteq> y\<close> \<open>y \<in> aexp_fv a\<close> 
    let ?f = \<open>fresh (x \<^bold>\<rightarrow> aexp_fv a \<union> pexp_fv p)\<close>
    have sub_p_def: \<open>psubst x a (\<^bold>\<forall> y. p) = \<^bold>\<forall> ?f. psubst x a (psubst y (V ?f) p)\<close>
      using * by (meson psubst.simps(3))
    have f1: \<open>?f \<notin> aexp_fv a\<close>
      using fresh_finite by (meson UnI1 aexp_fv_finite pexp_fv_finite finite.insertI finite_UnI insertI2)
    have f2: \<open>?f \<notin> pexp_fv p\<close>
      using fresh_finite by (metis UnCI aexp_fv_finite pexp_fv_finite finite_Un finite_insert)
    have f3: \<open>x \<noteq> ?f\<close> 
      using fresh_finite by (metis UnCI aexp_fv_finite pexp_fv_finite finite_Un finite_insert insertCI)
    {
      assume \<open>y \<in> pexp_fv p\<close>
      with 3 * have **: \<open>pexp_fv (psubst y (V ?f) p) = pexp_fv p - {y} \<union> {?f}\<close> by force
      {
        assume ?a1
        with 3 * ** sub_p_def have \<open>pexp_fv (psubst x a (\<^bold>\<forall> y. p)) = ((pexp_fv p - {y} \<union> {?f}) - {x} \<union> aexp_fv a) - {?f}\<close>
          by auto
        with f1 f2 have \<open>pexp_fv (psubst x a (\<^bold>\<forall> y. p)) = (pexp_fv p - {x} \<union> aexp_fv a)\<close>
          using * by force
        then show ?g1 
          by fastforce
      next
        assume a: ?a2
        with f3 have \<open>pexp_fv (psubst x a (psubst y (V ?f) p)) = pexp_fv p - {y} \<union> {?f}\<close>
          using 3(4) * ** by force
        with sub_p_def f2 fresh_finite *(2) f1 show ?g2 
          by auto
      }
    next
      assume \<open>y \<notin> pexp_fv p\<close>
      with 3 * have **: \<open>pexp_fv (psubst y (V ?f) p) = pexp_fv p\<close> by metis
      {
        assume ?a1
        with 3 * sub_p_def ** f1 f2 *(2) show ?g1 
          by auto
      next
        assume ?a2
        with f2 f3 3(4) * ** \<open>y \<notin> pexp_fv p\<close> sub_p_def show ?g2 
          by auto
      }
    }
  qed (use 3 in auto)
  then show \<open>?a1 \<Longrightarrow> ?g1\<close> \<open>?a2 \<Longrightarrow> ?g2\<close> 
    by auto
next
  case (4 x a v c w)
  {
    case 1
    then consider 
      \<open>x \<in> aexp_fv v \<and> x \<in> aexp_fv w\<close> | 
      \<open>x \<in> aexp_fv v \<and> x \<notin> aexp_fv w\<close> | 
      \<open>x \<notin> aexp_fv v \<and> x \<in> aexp_fv w\<close> by auto
    then show ?case 
      using elem_asubst_fv by cases auto
  next
    case 2
    then show ?case 
      using elem_asubst_fv by simp
  }
qed auto

lemma subset_psubst_fv: \<open>pexp_fv p \<subseteq> pexp_fv q \<Longrightarrow> pexp_fv (psubst x a p) \<subseteq> pexp_fv (psubst x a q)\<close>
  using elem_psubst_fv by (metis dis_fv dissubst sup.absorb_iff1)


end