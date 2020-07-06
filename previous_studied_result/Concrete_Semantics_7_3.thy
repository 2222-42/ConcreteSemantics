theory Concrete_Semantics_7_3
  imports Main "~~/src/HOL/IMP/Com" "HOL-IMP.Star" "HOL-IMP.Big_Step"
begin
(* 7.3 Small-Step Semantics *)

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:   "(x ::= a,s) \<rightarrow> (SKIP, s(x := aval a s))" |
Seq1:     "(SKIP;;c, s) \<rightarrow> (c, s)"|
Seq2:     "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c2,s) \<rightarrow> (c\<^sub>1';;c2,s')" |
IfTrue:   "bval b s  \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>1, s)" |
IfFalse:  "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<rightarrow> (c\<^sub>2, s)" |
While:    "(WHILE b DO c,s) \<rightarrow> 
              (IF b THEN c;; WHILE b DO c ELSE SKIP, s)"


(* abbreviation "\<rightarrow>*":: "com * state \<Rightarrow> com * state \<Rightarrow> bool" where
"x \<rightarrow>* y \<equiv> star small_step x y" *)

abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y == star small_step x y"

code_pred small_step .

values "{(c',map t [''x'',''y'',''z'']) |c' t.
   (''x'' ::= V ''z'';; ''y'' ::= V ''x'',
    <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c',t)}"

lemmas small_step_induct = small_step.induct[split_format(complete)]

(*why simp is needed? 
Where simp is used? *)
declare small_step.intros[simp,intro]

inductive_cases SkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
thm SkipE
inductive_cases AssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
thm AssignE
inductive_cases SeqE[elim]: "(c1;;c2,s) \<rightarrow> ct"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"

lemma deterministic:
  "\<lbrakk>cs \<rightarrow> cs'; cs \<rightarrow> cs''\<rbrakk> \<Longrightarrow> cs'' = cs'"
  apply(induction arbitrary:cs'' rule: small_step.induct)
       apply(blast+)
  done

(* not 'star.induct' *)
lemma star_seq2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;;c2,s) \<rightarrow>* (c1';;c2,s')"
proof(induction rule: star_induct)
  case (refl x)
  then show ?case by simp
next
  case (step x y z)
  then show ?case 
    by (meson Seq2 star.simps)

qed

lemma seq_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;;c2, s1) \<rightarrow>* (SKIP,s3)"
  by (meson Seq1 star.step star_seq2 star_trans)

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof(induction rule: big_step.induct)
  case (Skip s)
  then show ?case 
    by simp
next
  case (Assign x a s)
  then show ?case 
    by blast
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case 
    by (meson Seq1 star_seq2 star_step1 star_trans)
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case 
    by (meson small_step.IfTrue star.step)
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case 
    by (meson small_step.IfFalse star.step)
next
  case (WhileFalse b s c)
  then show ?case 
    by (metis star.step star_step1 small_step.IfFalse small_step.While)
    (* by (meson While small_step.IfFalse star.simps) *)
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case 
    by (metis (no_types, lifting) While seq_comp small_step.IfTrue star.simps)
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
  proof(induction arbitrary: t rule: small_step.induct)
case (Assign x a s)
  then show ?case 
    by auto
next
case (Seq1 c s)
  then show ?case 
    by auto
next
  case (Seq2 c\<^sub>1 s c\<^sub>1' s' c2)
  then show ?case 
    by blast
next
  case (IfTrue b s c\<^sub>1 c\<^sub>2)
  then show ?case 
    by (simp add: big_step.IfTrue)
next
  case (IfFalse b s c\<^sub>1 c\<^sub>2)
  then show ?case 
    by (simp add: big_step.IfFalse)
next
  case (While b c s)
  then show ?case 
    by (simp add: while_unfold)
qed

lemma small_to_big:
  "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
proof(induction cs "(SKIP, t)"rule: star.induct)
  case refl
  then show ?case 
    by (simp add: Skip)
next
  case (step x y)
  then show ?case 
    using small1_big_continue by auto
qed

theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
  
  using big_to_small small_to_big by blast

definition final :: "com * state \<Rightarrow> bool"where
"final cs \<longleftrightarrow> \<not>(\<exists> cs'. cs \<rightarrow> cs')"

lemma finalD: "final (c,s) \<Longrightarrow> c = SKIP"
proof(induction c)
  case SKIP
  then show ?case 
    by simp
next
  case (Assign x1 x2)
  then show ?case 
    using final_def by auto
next
  case (Seq c1 c2)
  then show ?case 
    using final_def by auto
next
  case (If x1 c1 c2)
  then show ?case 
    by (meson final_def small_step.IfFalse small_step.IfTrue)
next
  case (While x1 c)
  then show ?case 
    using final_def by auto
qed


lemma big_iff_small_termination:
  "(\<exists>t. cs \<Rightarrow> t) \<longleftrightarrow> (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
proof(induction cs)
case (Pair a b)
  then show ?case 
    by (metis (full_types) Concrete_Semantics_7_3.SkipE big_to_small finalD final_def old.prod.exhaust small_to_big)
qed
  
end