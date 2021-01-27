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
  sorry

(*Corollary 12.8.*)
corollary vc_sound':
  "\<lbrakk> vc C Q; \<forall>s. P s \<longrightarrow> pre C Q s \<rbrakk> \<Longrightarrow> \<turnstile> {P} strip C {Q}"
  by (simp add: strengthen_pre vc_sound)

end