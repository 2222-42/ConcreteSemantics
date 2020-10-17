theory ConcreteSemantics10_1_Def_Init_Small
  imports Main "~~/src/HOL/IMP/Vars" "~~/src/HOL/IMP/Star" "~~/src/HOL/IMP/Def_Init_Exp"  "~~/src/HOL/IMP/Def_Init" 
begin 

subsection "Initialization-Sensitive Small Step Semantics"
inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "aval a s = Some i \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := Some i))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s = Some True \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "bval b s = Some False \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"


subsection "Soundness wrt Small Steps"

(* Lemma 10.3 (D is increasing).*)
lemma D_increase: "D A c A' \<Longrightarrow> A \<subseteq> A'"
  by (simp add: D_incr)

theorem progress:
  "D (dom s) c A' \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induction c arbitrary: s A')
  case SKIP
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by auto (metis aval_Some small_step.Assign)
next
  case (Seq c1 c2)
  then show ?case by (fastforce intro: small_step.intros)
next
  case (If x1 c1 c2)
  then obtain bv where "bval x1 s = Some bv" by (auto dest!:bval_Some)
  then show ?case 
    by (metis (full_types) IfFalse IfTrue)
next
  case (While x1 c)
  then show ?case 
    by (meson small_step.While)
qed
(*
proof(induction arbitrary: s A' rule: D.induct)
case (Skip A)
  then show ?case 
    by simp
next
  case (Assign a A x)
  then obtain i where "aval a s = Some i" sorry
  then show ?case 
    using small_step.Assign by blast
next
  case (Seq A\<^sub>1 c\<^sub>1 A\<^sub>2 c\<^sub>2 A\<^sub>3)
  then show ?case 
    using Seq1 Seq2 by fastforce
next
  case (If b A c\<^sub>1 A\<^sub>1 c\<^sub>2 A\<^sub>2)
  then obtain bv where "bval b s = Some bv" sorry
  then show ?case 
    by (metis (full_types) IfFalse IfTrue)
next
case (While b A c A')
  then show ?case 
    by (meson small_step.While)
qed*)

lemma D_mono:  "D A c M \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> \<exists>M'. D A' c M' & M <= M'"
proof(induction c arbitrary: A A' M)
case SKIP
  then show ?case by (fastforce intro: D.Skip)
next
  case (Assign x1 x2)
  then show ?case by (fastforce intro: D.Assign)
next
  case (Seq c1 c2)
  then show ?case by auto (metis D.intros(3))
(*by (fastforce intro: D.Seq)*)
next
  case (If x1 c1 c2)
(*
 1. \<And>x1 c1 c2 A A' M.
       (\<And>A A' M. D A c1 M \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> \<exists>M'. D A' c1 M' \<and> M \<subseteq> M') \<Longrightarrow>
       (\<And>A A' M. D A c2 M \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> \<exists>M'. D A' c2 M' \<and> M \<subseteq> M') \<Longrightarrow>
       D A (IF x1 THEN c1 ELSE c2) M \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> \<exists>M'. D A' (IF x1 THEN c1 ELSE c2) M' \<and> M \<subseteq> M'
*)
  then obtain M1 M2 where "vars x1 \<subseteq> A" "D A c1 M1" "D A c2 M2" "M = M1 \<inter> M2" 
    by blast
(* use IH Mx to  Mx' and A to A'*)
  then obtain M1' M2' where "D A' c1 M1'" "D A' c2 M2'"  "M1 \<subseteq> M1'" "M2 \<subseteq> M2'" 
    by (meson If.IH(1) If.IH(2) If.prems(2))
(*  then have "D A (IF x1 THEN c1 ELSE c2) M" 
    using If.prems(1) by blast*)
  then have "D A' (IF x1 THEN c1 ELSE c2) (M1' \<inter> M2')" "M \<subseteq> M1' \<inter> M2'" sledgehammer
    using \<open>vars x1 \<subseteq> A\<close> \<open>A \<subseteq> A'\<close> \<open>M = M1 \<inter> M2\<close> by(fastforce intro: D.intros)+
(*    using D.If If.prems(2) \<open>D A' c1 M1'\<close> \<open>D A' c2 M2'\<close> \<open>vars x1 \<subseteq> A\<close> apply blast*)
  then show ?case 
    by meson (*by (fastforce intro: D.If)*)
next
  case (While x1 c)
  then show ?case 
    by auto (metis D.intros(5) subset_trans)
    (*by (fastforce intro: D.While)*)
qed

theorem D_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> D (dom s) c A \<Longrightarrow> \<exists>A'. D (dom s') c' A' & A <= A'"
proof(induction arbitrary: A rule:small_step_induct)
case (Assign a s i x)
  then show ?case by (auto intro: D.intros)
next
  case (Seq1 c s)
  then show ?case by (auto intro: D.intros)
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c\<^sub>2)
  then show ?case 
    by auto (metis D_mono D.intros(3))
next
  case (IfTrue b s c\<^sub>1 c\<^sub>2)
  then show ?case by (auto intro: D.intros)
next
  case (IfFalse b s c\<^sub>1 c\<^sub>2)
  then show ?case by (auto intro: D.intros)
next
  case (While b c s)
(*
proof (state)
this:
  D (dom s) (WHILE b DO c) A

goal (1 subgoal):
 1. \<And>b c s A. D (dom s) (WHILE b DO c) A \<Longrightarrow> \<exists>A'. D (dom s) (IF b THEN c;; WHILE b DO c ELSE SKIP) A' \<and> A \<subseteq> A'
*)
  then obtain A' where A': "vars b \<subseteq> dom s" "A = dom s" "D (dom s) c A'" by blast
  then obtain A'' where "D A' c A''" by (metis D_incr D_mono)
  with A' have "D (dom s) (IF b THEN c;; WHILE b DO c ELSE SKIP) (dom s)" 
    by (metis D.If[OF \<open>vars b \<subseteq> dom s\<close> D.Seq[OF \<open>D (dom s) c A'\<close> D.While[OF _ \<open>D A' c A''\<close>]] D.Skip] D_incr Int_absorb1 subset_trans)
    (* not shown only from sledgehammer *)
  then show ?case 
    by (metis A'(2) D_increase)
(*    by (smt D.simps D_increase While.prems com.distinct(13) com.distinct(17) com.distinct(19)) (*> 1.0s*)*)
qed

(* Theorem 10.4 (D is sound). *)
theorem D_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> D (dom s) c A'
   \<Longrightarrow> (\<exists>cs''. (c',s') \<rightarrow> cs'') \<or> c' = SKIP"
  apply(induction arbitrary: A' rule: star_induct )
   apply(metis progress)
  using D_preservation by blast

end