theory ConcreteSemantics12_Hoare_Sound_Complete
  imports "~~/src/HOL/IMP/Hoare"
begin

subsection \<open>Soundness and Completeness\<close>

subsubsection "Soundness"

(* Lemma 12.2 (Soundness of \<turnstile> w.r.t. \<Turnstile>. *)
lemma hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
proof(induction rule: hoare.induct)
case (Skip P)
  then show ?case 
    using hoare_valid_def by auto
next
  case (Assign P a x)
  then show ?case 
    using hoare_valid_def by auto
next
  case (Seq P c\<^sub>1 Q c\<^sub>2 R)
  then show ?case 
    using hoare_valid_def by auto
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  then show ?case 
    using hoare_valid_def by auto
next
  case (While P b c)
  have "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> P s \<Longrightarrow> P t \<and> \<not> bval b t" for s t 
  proof(induction "WHILE b DO c" s t rule: big_step_induct)
    case (WhileFalse s)
    then show ?case 
      by simp
  next
    case (WhileTrue s\<^sub>1 s\<^sub>2 s\<^sub>3)
    then show ?case 
      using While.IH hoare_valid_def by auto
  qed
  then show ?case 
    using hoare_valid_def by auto
next
  case (conseq P' P c Q Q')
  then show ?case 
    using hoare_valid_def by auto
qed 

subsubsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
  apply(auto simp: wp_def)
  done

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
(*  apply(auto simp: wp_def)
  done*)
  by (rule ext) (auto simp: wp_def)

lemma wp_Seq[simp]: "wp (c\<^sub>1;;c\<^sub>2) Q = wp c\<^sub>1 (wp c\<^sub>2 Q)"
(*  apply(auto simp: wp_def)
  done*)
  by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q =
 (\<lambda>s. if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)"
(*  apply(auto simp: wp_def)
  done*)
  by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;;WHILE b DO c ELSE SKIP) Q s"
(*  apply(auto simp: wp_def)
  by (simp add: while_unfold)*)
  unfolding wp_def by (metis unfold_while)

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c;; WHILE b DO c) Q s"
(*    apply(auto simp: wp_def)
  done*)
  by (auto simp: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
(*    apply(auto simp: wp_def)
  done*)
  by (auto simp: wp_While_If)

subsubsection "Completeness"

(* Lemma 12.4. *)
lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof(induction c arbitrary: Q)
case SKIP
  then show ?case 
    by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  then show ?case 
    by auto
next
  case (If x1 c1 c2)
(*
 1. \<And>x1 c1 c2 Q. (\<And>Q. \<turnstile> {wp c1 Q} c1 {Q}) \<Longrightarrow> (\<And>Q. \<turnstile> {wp c2 Q} c2 {Q}) \<Longrightarrow> \<turnstile> {wp (IF x1 THEN c1 ELSE c2) Q} IF x1 THEN c1 ELSE c2 {Q}
*)
(*
conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> {P'} c {Q'}"
*)
  then show ?case by (auto intro: conseq)
next
  case (While b c)
(*
 1. \<And>x1 c Q. (\<And>Q. \<turnstile> {wp c Q} c {Q}) \<Longrightarrow> \<turnstile> {wp (WHILE x1 DO c) Q} WHILE x1 DO c {Q}
*)
  let ?w = "WHILE b DO c"
  show "\<turnstile> {wp ?w Q} ?w {Q}" 
  proof(rule While')
(*
lemma While':
assumes "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P}" and "\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile> {P} WHILE b DO c {Q}"
by(rule weaken_post[OF While[OF assms(1)] assms(2)])
*)
    show "\<turnstile> {\<lambda>s. wp ?w Q s \<and>  bval b s} c {wp ?w Q}" 
      by (smt While.IH strengthen_pre wp_Seq wp_While_True)
(*
    proof(rule strengthen_pre[OF _ While.IH])
      show "\<forall>s. wp ?w Q s \<and> bval b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
*)
    show "\<forall>s. wp ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" 
      by auto
  qed
qed

(*Theorem 12.5 (Completeness of \<turnstile> w.r.t. \<Turnstile>*)
lemma hoare_complete: assumes "\<Turnstile> {P}c{Q}" shows "\<turnstile> {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" 
    using assms hoare_valid_def wp_def by auto
  show "\<turnstile> {wp c Q} c {Q}" 
    by (simp add: wp_is_pre)
qed

(* Corollary 12.6. *)
corollary hoare_sound_complete: "\<turnstile> {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q}"
by (metis hoare_complete hoare_sound)

end