theory pl1 imports pexp
begin

datatype com
  = Assert pexp (\<open>\<^bold>\<turnstile> _\<close> [55] 55)
  | Var string 
  | Assign string aexp (\<open>_ \<^bold>\<leftarrow> _\<close> [55,55] 55)
  | Seq com com (\<open>_ \<^bold>; _\<close> [45,45] 45)
  | Choice com com (\<open>_ \<^bold>[\<^bold>] _\<close> [44,44] 44)
  | If pexp com com
  | While pexp pexp com
  | Ghost com (\<open>\<^bold>g _\<close> [46] 46)

fun com_fv where
  \<open>com_fv (Assert r) = pexp_fv r\<close> |
  \<open>com_fv (Var x) = {x}\<close> |
  \<open>com_fv (Assign x a) = insert x (aexp_fv a)\<close> |
  \<open>com_fv (Seq c1 c2) = com_fv c1 \<union> com_fv c2\<close> |
  \<open>com_fv (Choice c1 c2) = com_fv c1 \<union> com_fv c2\<close> |
  \<open>com_fv (If b c1 c2) = pexp_fv b \<union> com_fv c1 \<union> com_fv c2\<close> |
  \<open>com_fv (While b I c) = pexp_fv b \<union> pexp_fv I \<union> com_fv c\<close> |
  \<open>com_fv (Ghost c) = com_fv c\<close>

lemma com_fv_finite: \<open>finite (com_fv s)\<close>
  by (induct s) (auto simp add: pexp_fv_finite aexp_fv_finite)

datatype comres = Terminated \<open>string \<Rightarrow> int\<close> | Error

primrec comres_bind where
  \<open>comres_bind f (Terminated i) = f i\<close> |
  \<open>comres_bind f Error = {Error}\<close>

inductive comsem where
  \<open>comsem i (Assert b) (if psem i b then Terminated i else Error)\<close> |
  \<open>comsem i (Var x) (Terminated (i(x := j)))\<close>  |
  \<open>comsem i (Assign x a) (Terminated (i(x := asem i a)))\<close> |
  \<open>comsem i (Ghost s) i'\<close> if \<open>comsem i s i'\<close> |
  \<open>comsem i (Choice s1 s2) i'\<close> if \<open>comsem i s1 i'\<close> |
  \<open>comsem i (Choice s1 s2) i'\<close> if \<open>comsem i s2 i'\<close> |
  \<open>comsem i (Seq s1 s2) i''\<close> if \<open>comsem i s1 (Terminated i')\<close> and \<open>comsem i' s2 i''\<close> |
  \<open>comsem i (Seq s1 s2) Error\<close> if \<open>comsem i s1 Error\<close> |
  \<open>comsem i (If b s1 s2) i'\<close> if \<open>psem i b \<and> comsem i s1 i'\<close> |
  \<open>comsem i (If b s1 s2) i'\<close> if \<open>\<not>psem i b \<and> comsem i s2 i'\<close> |
  \<open>comsem i (While b I s) (Terminated i)\<close> if \<open>\<not>psem i b\<close> |
  \<open>comsem i (While b I s) Error\<close> if \<open>psem i b \<and> comsem i s Error\<close> |
  \<open>comsem i (While b I s) i''\<close> if \<open>psem i b \<and> comsem i s (Terminated i') \<and> comsem i' (While b I s) i''\<close> 

end