theory ConcreteSemantics12_Hoare_Total
  imports "~~/src/HOL/IMP/Hoare_Examples"
begin

text\<open>Note that this definition of total validity \<open>\<Turnstile>\<^sub>t\<close> only
works if execution is deterministic (which it is in our case).\<close>

definition hoare_tvalid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t {P}c{Q}  \<longleftrightarrow>  (\<forall>s. P s \<longrightarrow> (\<exists>t. (c,s) \<Rightarrow> t \<and> Q t))"

text\<open>Provability of Hoare triples in the proof system for total
correctness is written \<open>\<turnstile>\<^sub>t {P}c{Q}\<close> and defined
inductively. The rules for \<open>\<turnstile>\<^sub>t\<close> differ from those for
\<open>\<turnstile>\<close> only in the one place where nontermination can arise: the
\<^term>\<open>While\<close>-rule.\<close>

inductive
  hoaret :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>t {P} SKIP {P}"  |

Assign:  "\<turnstile>\<^sub>t {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1 {P\<^sub>2}; \<turnstile>\<^sub>t {P\<^sub>2} c\<^sub>2 {P\<^sub>3} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P\<^sub>1} c\<^sub>1;;c\<^sub>2 {P\<^sub>3}"  |

If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q}; \<turnstile>\<^sub>t {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>t {P} IF b THEN c\<^sub>1 ELSE c\<^sub>2 {Q}"  |

While:
  "(\<And>n::nat.
    \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> T s n} c {\<lambda>s. P s \<and> (\<exists>n'<n. T s n')})
   \<Longrightarrow> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> (\<exists>n. T s n)} WHILE b DO c {\<lambda>s. P s \<and> \<not>bval b s}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"


text\<open>The \<^term>\<open>While\<close>-rule is like the one for partial correctness but it
requires additionally that with every execution of the loop body some measure
relation @{term[source]"T :: state \<Rightarrow> nat \<Rightarrow> bool"} decreases.
The following functional version is more intuitive:\<close>

lemma While_fun:
  "\<lbrakk> \<And>n::nat. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> n = f s} c {\<lambda>s. P s \<and> f s < n}\<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {P} WHILE b DO c {\<lambda>s. P s \<and> \<not>bval b s}"
  by (rule While[where T = "\<lambda> s n. n = f s", simplified])

end