theory ConcreteSemantics10_1_Fold
  imports Main "~~/src/HOL/IMP/Big_Step"  "~~/src/HOL/IMP/Vars" 
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

theorem aval_afold_N:
assumes "approx t s"
shows "afold a t = N n \<Longrightarrow> aval a s = n"
  by (metis assms aval.simps(1) aval_afold)

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

subsection "Semantic Equivalence up to a Condition"

type_synonym assn = "state \<Rightarrow> bool"

definition
  equiv_up_to :: "assn \<Rightarrow> com \<Rightarrow> com \<Rightarrow> bool" ("_ \<Turnstile> _ \<sim> _" [50,0,10] 50)
where
  "(P \<Turnstile> c \<sim> c') = (\<forall>s s'. P s \<longrightarrow> (c,s) \<Rightarrow> s' \<longleftrightarrow> (c',s) \<Rightarrow> s')"

definition
  bequiv_up_to :: "assn \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bool" ("_ \<Turnstile> _ <\<sim>> _" [50,0,10] 50)
where
  "(P \<Turnstile> b <\<sim>> b') = (\<forall>s. P s \<longrightarrow> bval b s = bval b' s)"

(* Lemma 10.7. *)
lemma equiv_up_to_True:
  "((\<lambda>_. True) \<Turnstile> c \<sim> c') = (c \<sim> c')"
  by (simp add: equiv_up_to_def)

lemma equiv_up_to_weaken:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (\<And>s. P' s \<Longrightarrow> P s) \<Longrightarrow> P' \<Turnstile> c \<sim> c'"
  by (simp add: equiv_up_to_def)

lemma equiv_up_toI:
  "(\<And>s s'. P s \<Longrightarrow> (c, s) \<Rightarrow> s' = (c', s) \<Rightarrow> s') \<Longrightarrow> P \<Turnstile> c \<sim> c'"
  by (unfold equiv_up_to_def) blast

lemma equiv_up_toD1:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> (c', s) \<Rightarrow> s'"
  by (unfold equiv_up_to_def) blast

lemma equiv_up_toD2:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> (c', s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> (c, s) \<Rightarrow> s'"
  by (unfold equiv_up_to_def) blast

(* Lemma 10.8 (Equivalence Relation). *)
lemma equiv_up_to_refl [simp, intro!]:
  "P \<Turnstile> c \<sim> c"
  by (simp add: equiv_up_to_def)

lemma equiv_up_to_sym:
  "(P \<Turnstile> c \<sim> c') = (P \<Turnstile> c' \<sim> c)"
  by (auto simp add: equiv_up_to_def)

lemma equiv_up_to_trans:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> P \<Turnstile> c' \<sim> c'' \<Longrightarrow> P \<Turnstile> c \<sim> c''"
  by(auto simp add: equiv_up_to_def)


lemma bequiv_up_to_refl [simp, intro!]:
  "P \<Turnstile> b <\<sim>> b"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_sym:
  "(P \<Turnstile> b <\<sim>> b') = (P \<Turnstile> b' <\<sim>> b)"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_trans:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> b' <\<sim>> b'' \<Longrightarrow> P \<Turnstile> b <\<sim>> b''"
  by (auto simp: bequiv_up_to_def)

lemma bequiv_up_to_subst:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P s \<Longrightarrow> bval b s = bval b' s"
  by (simp add: bequiv_up_to_def)

(* Congruence rules *)
lemma equiv_up_to_seq:
  "P \<Turnstile> c \<sim> c' \<Longrightarrow> Q \<Turnstile> d \<sim> d' \<Longrightarrow>
  (\<And>s s'. (c,s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> Q s') \<Longrightarrow>
  P \<Turnstile> (c;; d) \<sim> (c';; d')"
  apply(simp add: equiv_up_to_def)
  apply blast
  done

lemma equiv_up_to_if_weak:
  "P \<Turnstile> b <\<sim>> b' \<Longrightarrow> P \<Turnstile> c \<sim> c' \<Longrightarrow> P \<Turnstile> d \<sim> d' \<Longrightarrow>
   P \<Turnstile> IF b THEN c ELSE d \<sim> IF b' THEN c' ELSE d'"
  apply(auto simp: bequiv_up_to_def equiv_up_to_def)
  done


lemma equiv_up_to_while_lemma_weak:
  shows "(d,s) \<Rightarrow> s' \<Longrightarrow>
         P \<Turnstile> b <\<sim>> b' \<Longrightarrow>
         P \<Turnstile> c \<sim> c' \<Longrightarrow>
         (\<And>s s'. (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b s \<Longrightarrow> P s') \<Longrightarrow>
         P s \<Longrightarrow>
         d = WHILE b DO c \<Longrightarrow>
         (WHILE b' DO c', s) \<Rightarrow> s'"
  sorry

lemma equiv_up_to_while_weak:
  assumes b: "P \<Turnstile> b <\<sim>> b'"
  assumes c: "P \<Turnstile> c \<sim> c'"
  assumes I: "\<And>s s'. (c, s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b s \<Longrightarrow> P s'"
  shows "P \<Turnstile> WHILE b DO c \<sim> WHILE b' DO c'"
proof -
  from b have b': "P \<Turnstile> b' <\<sim>> b" 
    by (simp add: bequiv_up_to_sym)
  from c have c': "P \<Turnstile> c' \<sim> c" 
    by (simp add: equiv_up_to_sym)

  from I have I' :"\<And>s s'. (c', s) \<Rightarrow> s' \<Longrightarrow> P s \<Longrightarrow> bval b' s \<Longrightarrow> P s'"
    using b' bequiv_up_to_subst c' equiv_up_to_def by auto

  note equiv_up_to_while_lemma_weak [OF _ b c]
       equiv_up_to_while_lemma_weak [OF _ b' c']
  thus ?thesis using I I' by (auto intro!: equiv_up_toI)
qed


lemma approx_merge:
  "approx t1 s \<or> approx t2 s \<Longrightarrow> approx (merge t1 t2) s"
  by (fastforce simp: merge_def approx_def)

(* Lemma 10.9 (defs approximates execution correctly). *)
lemma big_step_pres_approx:
  "(c,s) \<Rightarrow> s' \<Longrightarrow> approx t s \<Longrightarrow> approx (defs c t) s'"
proof(induction arbitrary: t rule: big_step_induct )
case (Skip s)
  then show ?case by simp
next
  case (Assign x a s)
  then show ?case 
    (*by(simp add: approx_def split: aexp.split)*)
    by(simp add: aval_afold_N approx_def split: aexp.split)
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
(*
  (\<And>t. approx t ?s\<^sub>12 \<Longrightarrow> approx (defs ?c\<^sub>12 t) ?s\<^sub>22) \<Longrightarrow>
  (\<And>t. approx t ?s\<^sub>22 \<Longrightarrow> approx (defs ?c\<^sub>22 t) ?s\<^sub>32) \<Longrightarrow>
*)
  have "approx (defs c\<^sub>1 t) s\<^sub>2" 
    by (simp add: Seq.IH(1) Seq.prems)
  have "approx (defs c\<^sub>2 (defs c\<^sub>1 t)) s\<^sub>3" 
    by (simp add: Seq.IH(2) \<open>approx (defs c\<^sub>1 t) s\<^sub>2\<close>)
  then show ?case 
    by simp
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case sorry
next
case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case sorry
next
  case (WhileFalse b s c)
  then show ?case sorry
next
case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case sorry
qed

lemma approx_eq:
  "approx t \<Turnstile> c \<sim> fold c t"
  sorry

end