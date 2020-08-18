theory ConcreteSemantics_7_Ex1
  imports Main "~~/src/HOL/IMP/Big_Step"
begin

(* Exercise 7.1. *)
(* type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp *)

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}" |
"assigned (Assign vname aexp) = {vname}"|
"assigned (Seq com1 com2) = (assigned com1) \<union> (assigned com2)"|
"assigned (If bexp com1 com2) = (assigned com1) \<union> (assigned com2)"|
"assigned (While bexp com) = assigned com"

(* Try to prove by induction on t, but failed. *)
lemma "\<lbrakk>(c, s) \<Rightarrow> t; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
apply(induction rule:big_step_induct)
apply(auto)
done


(* Exercise 7.2. *)
fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True" |
"skip (Assign vname aexp) = False"|
"skip (Seq com1 com2) = (skip com1 \<and> skip com2)"|
"skip (If bexp com1 com2) = (skip com1 \<and> skip com2)"|
"skip (While bexp com) = False"
(* 
証明できないと思ったら、明らかにWhileはskip like じゃないでしょ
"skip (While bexp com) = skip com"
もちろん、bexpの値がfalseだったら、skip likeになるが、しかし、環境がここでは変数に含まれていないので、Falseと一律に判定したほうがいい。
*)

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
apply(induction c)
apply(simp_all)
apply fastforce
apply (meson IfE IfFalse IfTrue)
done


(* Exercise 7.3. *)
fun deskip :: "com \<Rightarrow> com" where
"deskip SKIP = SKIP" |
"deskip (Assign vname aexp) = (Assign vname aexp)"|
"deskip (Seq com1 com2) = (if deskip com1 = SKIP then deskip com2 else (if deskip com2 = SKIP then deskip com1 else (Seq (deskip com1) (deskip com2))))"|
"deskip (If bexp com1 com2) = (If bexp (deskip com1) (deskip com2))"|
"deskip (While bexp com) = While bexp (deskip com)"

lemma "deskip c \<sim> c"
proof(induction c)
  case SKIP
  then show ?case by simp
next
  case (Assign x1 x2)
  then show ?case by simp
next
  case (Seq c1 c2)
  (* deskip c1 \<sim> c1 \<Longrightarrow> deskip c2 \<sim> c2 \<Longrightarrow> deskip (c1;; c2) \<sim> c1;; c2 *)
  (* have "deskip (c1;; c2) \<sim> c1;; c2" sledgehammer *)
  have "deskip (c1;; c2) \<sim> (deskip c1;; deskip c2)" by auto
  moreover have "deskip c1 ;; deskip c2 \<sim> c1 ;; c2 " using Seq.IH(1) Seq.IH(2) by blast
  ultimately show ?case by auto
next
  case (If x1 c1 c2)
  then show ?case by auto
next
  case (While x1 c)
  then show ?case using sim_while_cong_aux by auto
qed
(* apply(induction c rule: deskip.induct)
apply(simp_all)
sledgehammer
apply(simp add: sim_while_cong) *)


(* Exercise 7.4. *)

text \<open> Complete the definition with two rules for Plus that model a left-to-right
evaluation strategy: reduce the first argument with \<leadsto> if possible, reduce the
second argument with \<leadsto> if the first argument is a number \<close>
inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x, s) \<leadsto> N (s x)" |
"(Plus (N i) (N j), s) \<leadsto> N (i + j)" |
"((a, s) \<leadsto> a') \<Longrightarrow> (Plus a b, s) \<leadsto> Plus a' b" |
"((b, s) \<leadsto> b') \<Longrightarrow> (Plus (N i) b, s) \<leadsto> Plus (N i) b'"

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
apply(induction rule: astep.induct[split_format(complete)])
apply(auto)
done

(* 何もわからずに証明が終わった *)


(* Exercise 7.5 *)
lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
using IfTrue by fastforce

(* lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
(* apply(induction "WHILE b2 DO c" rule: big_step_induct) *)
sorry *)
(* `c` が `SKIP` の時は違くないか？ *)

(* lemma "\<not> (WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)"
apply(induction "WHILE b1 DO WHILE b2 DO c" rule: big_step_induct) *)

(* abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)" *)
(* lemma \<exists> s t. (WHILE And b1 b2 DO c, s) \<Rightarrow> t \<and>  *)

(* lemma "\<not> (\<forall> s t c. (WHILE And b1 b2 DO c, s) \<Rightarrow> t = (WHILE b1 DO WHILE b2 DO c, s) \<Rightarrow> t)"
proof 
  assume "\<forall> s t c. (WHILE And b1 b2 DO c, s) \<Rightarrow> t = (WHILE b1 DO WHILE b2 DO c, s) \<Rightarrow> t"

  thus False sorry
qed *)
(* 上記だと束縛が多いからだめ。 *)

lemma "\<not> (WHILE And (Bc True) (Bc False) DO SKIP \<sim> WHILE (Bc True) DO WHILE (Bc False) DO SKIP)"
proof 
assume asm: "(WHILE And (Bc True) (Bc False) DO SKIP \<sim> WHILE (Bc True) DO WHILE (Bc False) DO SKIP)"
have "(WHILE And (Bc True) (Bc False) DO SKIP, s) \<Rightarrow> s" by (simp add: WhileFalse)
then have "(WHILE (Bc True) DO WHILE (Bc False) DO SKIP, s) \<Rightarrow> s" by (simp add: asm)
then show False by (induction "(WHILE (Bc True) DO WHILE (Bc False) DO SKIP)" s s rule: big_step_induct, simp)
qed

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b1 b2 = Not (And (Not b1) (Not b2))"

(* lemma "\<forall> s t. (WHILE Or b1 b2 DO c, s) \<Rightarrow> t \<Longrightarrow> (WHILE b1 DO WHILE b2 DO c,  s) \<Rightarrow> t"
proof -
  assume a1: "\<forall>s t. (WHILE Or b1 b2 DO c, s) \<Rightarrow> t"
  then have "\<forall>f fa fb. fb = f \<or> \<not> (WHILE Or b1 b2 DO c, fa) \<Rightarrow> fb"
    by (metis big_step_determ)
  then have "\<forall>a aa. aa = a"
    using a1 sorry
    (* proof -
      { fix dd :: 'd and dda :: 'd
        have "\<And>e ea. e = ea"
          using \<open>\<forall>f fa fb. fb = f \<or> \<not> (WHILE Or b1 b2 DO c, fa) \<Rightarrow> fb\<close> \<open>\<forall>s t. (WHILE Or b1 b2 DO c, s) \<Rightarrow> t\<close> sorry (* > 1.0 s, timed out *)
        then have "dd = dda"
          by blast (* > 1.0 s, timed out *) }
      then show ?thesis
        by blast (* > 1.0 s, timed out *)
    qed *)
  then have "\<forall>c ca cb b. IF b THEN c ELSE cb \<noteq> ca"
    using com.distinct(11) by fastforce (* > 1.0 s, timed out *)
  then show ?thesis
    by blast
qed  *)

(* lemma "\<forall> s t. (WHILE b1 DO WHILE b2 DO c, s) \<Rightarrow> t \<Longrightarrow> (WHILE Or b1 b2 DO c,  s) \<Rightarrow> t" *)

(* lemma "WHILE Or b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
sledgehammer *)
