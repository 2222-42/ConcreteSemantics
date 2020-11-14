theory ConcreteSemantics10_1_Fold
  imports Main "~~/src/HOL/IMP/Sem_Equiv"  "~~/src/HOL/IMP/Vars" 
begin 

subsection "Simple folding of arithmetic expressions"

type_synonym tab = "vname \<Rightarrow> val option"

fun afold :: "aexp \<Rightarrow> tab \<Rightarrow> aexp" where
"afold (N n) _ = N n" |
"afold (V x) t = (case t x of None \<Rightarrow> V x | Some k \<Rightarrow> N k)" |
"afold (Plus e1 e2) t = (case (afold e1 t, afold e2 t) of
  (N n1, N n2) \<Rightarrow> N(n1+n2) | (e1',e2') \<Rightarrow> Plus e1' e2')"

definition  "approx t s \<longleftrightarrow> (\<forall> x k. t x = Some k \<longrightarrow> s x = k)"

(*Lemma 10.6 (Correctness of afold).*)
theorem aval_afold[simp]:
assumes "approx t s"
shows "aval (afold a t) s = aval a s"
proof (induction a)
  case (N x)
  then show ?case by auto 
next
  case (V x)
  then show ?case using assms by (auto simp: approx_def split: option.split )
next
  case (Plus a1 a2)
  then show ?case using assms by (auto simp: approx_def split: option.split aexp.split)
qed

definition
  "merge t1 t2 = (\<lambda>m. if t1 m = t2 m then t1 m else None)"

primrec "defs" :: "com \<Rightarrow> tab \<Rightarrow> tab" where
"defs SKIP t = t" |
"defs (x ::= a) t =
  (case afold a t of N k \<Rightarrow> t(x \<mapsto> k) | _ \<Rightarrow> t(x:=None))" |
"defs (c1;;c2) t = (defs c2 o defs c1) t" |
"defs (IF b THEN c1 ELSE c2) t = merge (defs c1 t) (defs c2 t)" |
"defs (WHILE b DO c) t = t |` (-lvars c)"

primrec fold where
"fold SKIP _ = SKIP" |
"fold (x ::= a) t = (x ::= (afold a t))" |
"fold (c1;;c2) t = (fold c1 t;; fold c2 (defs c1 t))" |
"fold (IF b THEN c1 ELSE c2) t = IF b THEN fold c1 t ELSE fold c2 t" |
"fold (WHILE b DO c) t = WHILE b DO fold c (t |` (-lvars c))"

value "fold(''x'' ::= Plus (N 42) (N (- 5))) nil"
value "defs (fold(''x'' ::= Plus (N 42) (N (- 5))) nil ) nil"
value "fold(''y'' ::= Plus (V ''x'') (V ''x'')) (defs (fold(''x'' ::= Plus (N 42) (N (- 5))) nil ) nil)"
value "fold(''x'' ::= Plus (N 42) (N (- 5));;''y'' ::= Plus (V ''x'') (V ''x'')) nil"

end