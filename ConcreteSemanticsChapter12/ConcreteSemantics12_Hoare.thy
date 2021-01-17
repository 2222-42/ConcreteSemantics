theory ConcreteSemantics12_Hoare
  imports "~~/src/HOL/IMP/Big_Step"
begin

section "Hoare Logic"

subsection "Hoare Logic for Partial Correctness"

type_synonym assn = "state \<Rightarrow> bool"

definition hoare_valid:: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/(_)/{(1_)}" 50)where 
"\<Turnstile> {P} c {Q} = (\<forall> s t. P s \<and> (c, s) \<Rightarrow> t \<longrightarrow> Q t)"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> {(1_)}/(_)/{(1_)}" 50) where
Skip: "\<turnstile> {P} SKIP {P}" |
Assign: "\<turnstile> {\<lambda>s. P (s[a/x])} x ::= a {P}" |
Seq: "\<lbrakk>\<turnstile> {P} c\<^sub>1 {Q}; \<turnstile> {Q} c\<^sub>2 {R}\<rbrakk> \<Longrightarrow> \<turnstile> {P} c\<^sub>1;;c\<^sub>2 {R}" | 
If: "\<lbrakk>\<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q}; \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q}\<rbrakk> \<Longrightarrow> \<turnstile> {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}" |
While: "\<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {P} \<Longrightarrow> \<turnstile> {P} WHILE b DO  c {\<lambda>s. P s \<and> \<not> bval b s}" |
conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile> {P} c {Q}; \<forall> s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow> \<turnstile> {P'} c {Q'}"

end