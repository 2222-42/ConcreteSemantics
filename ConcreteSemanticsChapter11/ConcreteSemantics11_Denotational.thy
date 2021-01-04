theory ConcreteSemantics11_Denotational
  imports Main "~~/src/HOL/IMP/Big_Step"
begin 

section "Denotational Semantics of Commands"

type_synonym com_den = "(state \<times> state) set"

definition W :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
"W db dc = (\<lambda>dw. {(s,t). if db s then (s, t) \<in> dc O dw else s = t})"

fun D :: "com \<Rightarrow> com_den" where
"D SKIP   = Id" |
"D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"D (c1;;c2)  = D(c1) O D(c2)" |
"D (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> D c1 else (s,t) \<in> D c2}" |
"D (WHILE b DO c) = lfp (W (bval b) (D c))"

lemma W_mono: "mono (W b r)"
  apply(unfold mono_def W_def)
  apply(auto)
  done

lemma D_While_If:
  "D(WHILE b DO c) = D(IF b THEN c;;WHILE b DO c ELSE SKIP)"
proof -
  let ?w = "WHILE b DO c"
  let ?f = "W (bval b) (D c)"
  have "D ?w = lfp ?f" 
    by simp
  also have "... = ?f (lfp ?f)" 
    by (simp add: W_mono def_lfp_unfold)
(*  also have "... = ?f (D ?w)" 
    by simp*)
  also have "... = D(IF b THEN c;;WHILE b DO c ELSE SKIP)" 
    using W_def by auto
  then show ?thesis 
    using calculation by auto
    (*using \<open>lfp (W (bval b) (D c)) = W (bval b) (D c) (lfp (W (bval b) (D c)))\<close> by auto*)
qed

text\<open>Equivalence of denotational and big-step semantics:\<close>

(*Lemma 11.4.*)
lemma D_if_big_step:  "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> D(c)"
proof(induction rule: big_step_induct)
case (Skip s)
  then show ?case 
    by simp
next
  case (Assign x a s)
  then show ?case 
    by auto
next
  case (Seq c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case 
    by auto
next
  case (IfTrue b s c\<^sub>1 t c\<^sub>2)
  then show ?case 
    by simp
next
  case (IfFalse b s c\<^sub>2 t c\<^sub>1)
  then show ?case 
    by simp
next
  case (WhileFalse b s c)
  then show ?case 
    using D_While_If by auto
next
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
  then show ?case 
  proof -
    have "(s\<^sub>1, s\<^sub>3) \<in> D (c;; WHILE b DO c)"
      using D.simps(3) WhileTrue.IH(1) WhileTrue.IH(2) by blast
    then show ?thesis
      using D_While_If WhileTrue.hyps(1) by force
  qed
qed

abbreviation Big_step :: "com \<Rightarrow> com_den" where
"Big_step c \<equiv> {(s,t). (c,s) \<Rightarrow> t}"

(*Lemma 11.5.*)
lemma Big_step_if_D:  "(s,t) \<in> D(c) \<Longrightarrow> (s,t) \<in> Big_step c"
proof(induction c arbitrary: s t)
case SKIP
  then show ?case 
    by auto
next
  case (Assign x1 x2)
  then show ?case by fastforce
next
  case (Seq c1 c2)
  then show ?case by fastforce
next
  case (If x1 c1 c2)
  then show ?case by (auto split: if_splits)
next
  case (While b c)
  let ?B = "Big_step (WHILE b DO c)"
  let ?f = "W (bval b) (D c)"
  have "?f ?B \<subseteq> ?B" using While.IH by (auto simp: W_def)
  then show ?case 
    using D.simps(5) While.prems lfp_lowerbound by blast
qed

(*Theorem 11.6 (Equivalence of denotational and big-step semantics).*)
theorem denotational_is_big_step: "(s, t) \<in> D c = (c, s) \<Rightarrow> t"
  using Big_step_if_D D_if_big_step by blast

(*Corollary 11.7.*)
corollary equiv_c_iff_equal_D: "(c1 \<sim> c2) \<longleftrightarrow> D c1 = D c2"
  apply(simp add: denotational_is_big_step[symmetric])
  apply(simp add: set_eq_iff)
  done

subsection "Continuity"

definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
"chain S = (\<forall>i. S i \<subseteq> S(Suc i))"

(*Lemma 11.10.*)
lemma chain_total: "chain S \<Longrightarrow> S i \<le> S j \<or> S j \<le> S i"
  by (meson ConcreteSemantics11_Denotational.chain_def le_cases lift_Suc_mono_le)

definition cont:: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
"cont f = (\<forall> S. chain S \<longrightarrow> f (\<Union> n. S n) = (\<Union> n. f (S n)))"

(*Lemma 11.11.*)
lemma mono_if_cont: fixes f :: "'a set \<Rightarrow> 'b set"
  assumes "cont f" shows "mono f"
proof
  fix a b :: "'a set" assume "a \<subseteq> b"
  let ?S = "\<lambda>i::nat. if i = 0 then a else b"
  have "chain ?S" using \<open>a \<subseteq> b\<close> 
    by (simp add: ConcreteSemantics11_Denotational.chain_def)
  then have "f (\<Union>n. ?S n) = (\<Union>n. f(?S n))" 
    by (metis assms cont_def)
  moreover have "(\<Union>n. ?S n) = b" using \<open>a \<subseteq> b\<close> by auto
  moreover have "(\<Union>n. f(?S n)) = f a \<union> f b" by (auto split: if_splits)
  ultimately show "f a \<subseteq> f b" 
    by (simp add: subset_Un_eq)
qed

lemma chain_iterates: fixes f :: "'a set \<Rightarrow> 'a set"
  assumes "mono f" shows "chain(\<lambda>n. (f^^n) {})"
proof-
  have "(f ^^ n ) {} \<subseteq> (f ^^ (Suc n)) {} " for n 
    using assms funpow_decreasing le_SucI by blast
  thus ?thesis 
    by (simp add: ConcreteSemantics11_Denotational.chain_def)
qed

(*Theorem 11.12 (Kleene fixpoint theorem).*)
theorem lfp_if_cont:
  assumes "cont f" shows "lfp f = (UN n. (f^^n) {})" (is "_ = ?U")
proof
(* 
 1. lfp f \<subseteq> (\<Union>n. (f ^^ n) {})
 2. (\<Union>n. (f ^^ n) {}) \<subseteq> lfp f
*)
  have "mono f" 
    by (simp add: assms mono_if_cont)
  then have mono: "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" for n 
    using funpow_decreasing order.strict_implies_order by blast
  show "lfp f \<subseteq> ?U" 
  proof (rule lfp_lowerbound)
    have "f ?U = (\<Union>n. (f ^^ (Suc n)) {})" 
      using chain_iterates[OF mono_if_cont[OF assms]] assms
      by(simp add: cont_def)
    also have "\<dots> = (f ^^ 0) {} \<union> (\<Union>n. (f ^^ (Suc n)) {})" 
      by simp
    also have "\<dots> = ?U" using mono by auto (metis funpow_simps_right(2) funpow_swap1 o_apply)
    finally show "f ?U \<subseteq> ?U" 
      by simp
  qed
next
  have "(f^^n){} \<subseteq> p" if "f p \<subseteq> p" for n p
(*  have "(f ^^ n) {} \<subseteq> lfp f" for n *)
(*    using Kleene_iter_lpfp assms lfp_unfold mono_if_cont by blast*)
(*Q: is it good to use Kleene_iter_lpfp ? \<rightarrow> Not good.*)
  proof (induction n)
    case 0
    then show ?case 
      by simp
  next
    case (Suc n)
    from monoD[OF mono_if_cont[OF assms] Suc] \<open>f p \<subseteq> p\<close>
    show ?case 
      by auto
(*    using Kleene_iter_lpfp assms mono_if_cont that by blast*)
(*    by (meson Kleene_iter_lpfp assms lfp_greatest mono_if_cont)*)
qed
  then show "?U \<subseteq> lfp f"  by(auto simp: lfp_def)
(*    by (simp add: UN_least \<open>\<And>n. (f ^^ n) {} \<subseteq> lfp f\<close>)*)
qed

(*Lemma 11.13.*)
lemma cont_W: "cont(W b r)"
  apply(simp add: cont_def)
  apply(simp add: W_def)
  apply(auto)
  done

subsection\<open>The denotational semantics is deterministic\<close>

lemma single_valued_UN_chain:
  assumes "chain S" "(\<And>n. single_valued (S n))"
  shows "single_valued(UN n. S n)"
proof(auto simp: single_valued_def)
(*  \<And>x y xa z xb. (x, y) \<in> S xa \<Longrightarrow> (x, z) \<in> S xb \<Longrightarrow> y = z *)
  fix m n x y z  assume "(x, y) \<in> S m " "(x, z) \<in> S n"
  show "y = z" 
    by (meson \<open>(x, y) \<in> S m\<close> \<open>(x, z) \<in> S n\<close> assms(1) assms(2) chain_total single_valuedD subsetD)
(*    by (meson \<open>(x, y) \<in> S m\<close> \<open>(x, z) \<in> S n\<close> assms(1) assms(2) chain_total single_valued_def subset_iff)*)
(* There also exists an proof using `chain_total`*)
qed

(*Lemma 11.15.*)
lemma single_valued_lfp: fixes f :: "com_den \<Rightarrow> com_den"
assumes "cont f" "\<And>r. single_valued r \<Longrightarrow> single_valued (f r)"
shows "single_valued(lfp f)"
  unfolding lfp_if_cont[OF assms(1)]
proof(rule single_valued_UN_chain)
  from chain_iterates[OF mono_if_cont]
  show "chain (\<lambda>n. (f ^^ n) {})" 
    by (simp add: \<open>\<And>f. cont f \<Longrightarrow> chain (\<lambda>n. (f ^^ n) {})\<close> assms(1))
next
  fix n show " single_valued ((f ^^ n) {})" 
  proof(induction n)
    case 0
    then show ?case 
      by simp
  next
    case (Suc n)
    then show ?case by (auto simp: assms(2) )
  qed
qed
(*
 1. \<forall>x y. (\<exists>xa. (x, y) \<in> (f ^^ xa) {}) \<longrightarrow> (\<forall>z. (\<exists>xa. (x, z) \<in> (f ^^ xa) {}) \<longrightarrow> y = z)
*)
  (*
apply(simp add: single_valued_def)
apply(simp add: lfp_def)
  sledgehammer*)

end