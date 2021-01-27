theory ConcreteSemantics12_VCG
  imports "~~/src/HOL/IMP/Hoare"
begin

subsection "Verification Condition Generation"

subsubsection "Annotated Commands"

text\<open>Commands where loops are annotated with invariants.\<close>

datatype acom = 
Askip ("SKIP")|
Aassign vname aexp ("(_ ::= _)" [1000,61] 61)|
Aseq acom acom ("(_;;/ _)" [60,61]60)|
Aif bexp acom acom ("(IF _/ THEN _/ ELSE _)" [0, 0, 61] 61)|
Awhile assn bexp acom ("({_}/ WHILE _/ DO _)" [0, 0, 61] 61)

notation com.SKIP ("SKIP")


text\<open>Weakest precondition:\<close>
(*
definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"
*)

fun pre :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"pre SKIP Q = Q" |
"pre (x ::= a) Q = (\<lambda>s. Q(s(x := aval a s)))" |
"pre (C\<^sub>1;; C\<^sub>2) Q = pre C\<^sub>1 (pre C\<^sub>2 Q)" |
"pre (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (\<lambda>s. if bval b s then pre C\<^sub>1 Q s else pre C\<^sub>2 Q s)" |
"pre ({I} WHILE b DO C) Q = I"

text\<open>Verification condition:\<close>

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
"vc SKIP Q = True" |
"vc (x ::= a) Q = True" |
"vc (C\<^sub>1;; C\<^sub>2) Q = (vc C\<^sub>1 (pre C\<^sub>2 Q) \<and> vc C\<^sub>2 Q)" |
"vc (IF b THEN C\<^sub>1 ELSE C\<^sub>2) Q = (vc C\<^sub>1 Q \<and> vc C\<^sub>2 Q)" |
"vc ({I} WHILE b DO C) Q =
  ((\<forall>s. (I s \<and> bval b s \<longrightarrow> pre C I s) \<and>
        (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and>
    vc C I)"

text\<open>Strip annotations:\<close>

fun strip :: "acom \<Rightarrow> com" where
"strip SKIP = SKIP" |
"strip (x ::= a) = (x ::= a)" |
"strip (C\<^sub>1;; C\<^sub>2) = (strip C\<^sub>1;; strip C\<^sub>2)" |
"strip (IF b THEN C\<^sub>1 ELSE C\<^sub>2) = (IF b THEN strip C\<^sub>1 ELSE strip C\<^sub>2)" |
"strip ({_} WHILE b DO C) = (WHILE b DO strip C)"

subsubsection "Soundness"


(*Lemma 12.9*)
lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile> {pre C Q} strip C {Q}"
proof(induction C arbitrary: Q)
case Askip
  then show ?case 
    by simp
next
  case (Aassign x1 x2)
  then show ?case by simp
next
  case (Aseq C1 C2)
  then show ?case 
    by auto
next
  case (Aif x1 C1 C2)
  then show ?case 
    by (auto intro: hoare.conseq)
(*    by (smt If pre.simps(4) strengthen_pre strip.simps(4) vc.simps(4))*)
next
  case (Awhile I b C)
  show ?case 
  proof(simp, rule While')
    have vc: "vc C I" and IQ: "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s" and 
         pre: "\<forall>s. I s \<and> bval b s \<longrightarrow> pre C I s" 
      using Awhile.prems by auto
    show " \<turnstile> {\<lambda>s. I s \<and> bval b s} strip C {I}" 
      using Awhile.IH pre strengthen_pre vc by auto
    show "\<forall> s. I s \<and> \<not> bval b s \<longrightarrow> Q s" 
      using Awhile.prems by auto
  qed
(*
  then show ?case 
    by (smt While' pre.simps(5) strengthen_pre strip.simps(5) vc.simps(5))*)
qed

(*Corollary 12.8.*)
corollary vc_sound':
  "\<lbrakk> vc C Q; \<forall>s. P s \<longrightarrow> pre C Q s \<rbrakk> \<Longrightarrow> \<turnstile> {P} strip C {Q}"
  by (simp add: strengthen_pre vc_sound) 

subsubsection "Completeness"

lemma pre_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> pre C P s \<Longrightarrow> pre C P' s"
proof(induction C arbitrary: P P' s)
case Askip
then show ?case  by simp
next
  case (Aassign x1 x2)
  then show ?case  
    by auto
next
  case (Aseq C1 C2)
  then show ?case  
    by (smt pre.simps(3))
next
  case (Aif x1 C1 C2)
  then show ?case  by simp
next
  case (Awhile x1 x2 C)
  then show ?case by simp
qed

lemma vc_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> vc C P \<Longrightarrow> vc C P'"
proof(induction C arbitrary: P P' )
case Askip
  then show ?case by simp
next
  case (Aassign x1 x2)
  then show ?case by simp
next
  case (Aseq C1 C2)
  then show ?case 
    by (metis pre_mono vc.simps(3))
next
  case (Aif x1 C1 C2)
  then show ?case by simp
next
  case (Awhile x1 x2 C)
  then show ?case by simp
qed

(*Lemma 12.11*)
lemma vc_complete:
 "\<turnstile> {P}c{Q} \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>s. P s \<longrightarrow> pre C Q s)"
  (is "_ \<Longrightarrow> \<exists>C. ?G P c Q C")
proof (induction rule: hoare.induct)
  case (Skip P)
  then show ?case 
    using strip.simps(1) by fastforce
next
  case (Assign P a x)
  then show ?case using strip.simps(2) by fastforce
next
  case (Seq P c\<^sub>1 Q c\<^sub>2 R)
  obtain C1 where ih1: "?G P c\<^sub>1 Q C1" 
    using Seq.IH(1) by auto
  obtain C2 where ih2: "?G Q c\<^sub>2 R C2" 
    using Seq.IH(2) by auto
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aseq C1 C2)"
      using ih1 ih2 by (fastforce elim!: pre_mono vc_mono)
  qed
  (*show ?case using ih1 ih2 
     by (smt pre.simps(3) pre_mono strip.simps(3) vc.simps(3) vc_mono)*)
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
(*
 1. \<And>P b c\<^sub>1 Q c\<^sub>2.
       \<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^sub>1 {Q} \<Longrightarrow>
       \<exists>C. strip C = c\<^sub>1 \<and> vc C Q \<and> (\<forall>s. P s \<and> bval b s \<longrightarrow> pre C Q s) \<Longrightarrow>
       \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^sub>2 {Q} \<Longrightarrow> \<exists>C. strip C = c\<^sub>2 \<and> vc C Q \<and> (\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> pre C Q s) \<Longrightarrow> \<exists>C. strip C = IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<and> vc C Q \<and> (\<forall>s. P s \<longrightarrow> pre C Q s)
*)
  obtain C1 where ih1: "?G (\<lambda>s. P s \<and> bval b s) c\<^sub>1 Q C1" 
    using If.IH(1) by auto
  obtain C2 where ih2: "?G (\<lambda>s. P s \<and> \<not> bval b s) c\<^sub>2 Q C2" 
    using If.IH(2) by auto
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Aif b C1 C2)"
      using ih1 ih2 by (fastforce elim!: pre_mono vc_mono)
  qed
next
  case (While P b c)
(*  \<And>P b c. \<turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow> \<exists>C. strip C = c \<and> vc C P \<and> (\<forall>s. P s \<and> bval b s \<longrightarrow> pre C P s) \<Longrightarrow> \<exists>C. strip C = WHILE b DO c \<and> vc C (\<lambda>a. P a \<and> \<not> bval b a) \<and> (\<forall>s. P s \<longrightarrow> pre C (\<lambda>a. P a \<and> \<not> bval b a) s) *)
  obtain C1 where ih1: "?G (\<lambda>s. P s \<and> bval b s) c P C1" sledgehammer
    using While.IH by auto
  show ?case (is "\<exists>C. ?C C")
  proof
    show "?C(Awhile P b C1)" 
      by (simp add: ih1)
  qed
next
  case (conseq P' P c Q Q')
  then show ?case 
    using pre_mono vc_mono by auto
qed
end