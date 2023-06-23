theory pl0 imports pexp
begin

datatype com
  = Assert pexp (\<open>\<^bold>\<turnstile> _\<close> [55] 55)
  | Assume pexp (\<open>\<^bold>\<stileturn> _\<close> [55] 55)
  | Var string 
  | Assign string aexp (\<open>_ \<^bold>\<leftarrow> _\<close> [55,55] 55)
  | Seq com com (\<open>_ \<^bold>; _\<close> [45,45] 45)
  | Choice com com (\<open>_ \<^bold>[\<^bold>] _\<close> [44,44] 44)
  | Ghost com (\<open>\<^bold>g _\<close> [46] 46)

term \<open>x \<^bold>\<leftarrow> N 3 \<^bold>[\<^bold>] x \<^bold>\<leftarrow> N 4\<^bold>; (\<^bold>g \<^bold>\<stileturn> V x \<^bold>> N 0\<^bold>; \<^bold>\<turnstile> V y \<^bold>> V x \<^bold>[\<^bold>] \<^bold>\<stileturn> V x \<^bold>> V y)\<close>
 
datatype comres = Terminated \<open>string \<Rightarrow> int\<close> | Error | Magic

primrec comres_bind where
  \<open>comres_bind f (Terminated i) = f i\<close> |
  \<open>comres_bind f Error = {Error}\<close> |
  \<open>comres_bind f Magic = {Magic}\<close>

primrec comsem where
  \<open>comsem i (Assert p) = {(if psem i p then Terminated i else Error)}\<close> |
  \<open>comsem i (Assume p) = {(if psem i p then Terminated i else Magic)}\<close> |
  \<open>comsem i (Var x) = { Terminated (i(x := j)) | j. True}\<close> |
  \<open>comsem i (Assign x a) = {Terminated (i(x := asem i a))}\<close> |
  \<open>comsem i (Ghost s) = comsem i s\<close> |
  \<open>comsem i (Choice s1 s2) = comsem i s1 \<union> comsem i s2\<close> |
  \<open>comsem i (Seq s1 s2) = \<Union> (image (comres_bind (\<lambda> i. comsem i s2)) (comsem i s1))\<close>


end