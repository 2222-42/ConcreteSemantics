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

text\<open>The soundness theorem:\<close>

(*Lemma 12.13 (Soundness of \<turnstile>\<^sub>t w.r.t. \<Turnstile>\<^sub>t.*)
theorem hoaret_sound: "\<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"
(*to simplify, we  unfold to induction on hoaret.induct *)
(*
The following two proof is not same.
- proof( unfold hoare_tvalid_def, induction rule: hoaret.induct)
- proof( induction rule: hoaret.induct, unfold hoare_tvalid_def)
*)
proof( unfold hoare_tvalid_def, induction rule: hoaret.induct)
  case (Skip P)
  then show ?case 
    by auto
next
  case (Assign P a x)
  then show ?case by auto
next
  case (Seq P\<^sub>1 c\<^sub>1 P\<^sub>2 c\<^sub>2 P\<^sub>3)
  then show ?case 
    by blast
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  then show ?case by blast
next
  case (While P b T c)
(*
    \<turnstile>\<^sub>t {\<lambda>s. P s \<and> bval b s \<and> T s ?n} c {\<lambda>s. P s \<and> (\<exists>n'<?n. T s n')}
*)
  let ?w = "WHILE b DO c"
  have "\<lbrakk>P s; T s n\<rbrakk> \<Longrightarrow> \<exists> t. (?w, s) \<Rightarrow> t \<and> P t \<and> \<not> bval b t" for s n 
(*  proof (cases)
    assume "bval b s"
    assume "P s" "T s n"
    then obtain s' t' where "(c, s) \<Rightarrow> s'" "P s'" "T s' n'" "n' < n" for n' sledgehammer

    then show ?thesis sorry
  next
    assume "\<not> bval b s"
    then have "(?w, s) \<Rightarrow> t" sledgehammer
    then show ?thesis sledgehammer
    qed*)
  proof (induction n arbitrary: s rule: less_induct)
    case (less x)                            
    then show ?case 
      by (metis While.IH WhileFalse WhileTrue)
    qed
  then show ?case 
    by blast
next
  case (conseq P' P c Q Q')
  then show ?case by blast
qed


end