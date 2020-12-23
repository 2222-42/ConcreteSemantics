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
  have "lfp ?f = ?f (lfp ?f)" 
    by (simp add: W_mono def_lfp_unfold)
  have "?f (lfp ?f) = ?f (D ?w)" 
    by simp
  have "?f (D ?w) = D(IF b THEN c;;WHILE b DO c ELSE SKIP)" 
    using W_def by auto
  then show ?thesis 
    using \<open>lfp (W (bval b) (D c)) = W (bval b) (D c) (lfp (W (bval b) (D c)))\<close> by auto
qed

end