theory Concrete_Semantics_3_1
  imports Main
begin
  type_synonym vname = string
  datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x. 0)"
value "aval (Plus (N 3) (V ''x''))((\<lambda>x.  0) (''x'' := 7)) "

fun asimp_const:: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a b) = 
(case (asimp_const a, asimp_const b) of
  (N n, N m) \<Rightarrow> N (n + m) |
  (c, d) \<Rightarrow> Plus c d )"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply(auto split:aexp.split)
  done

fun plus:: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i) (N j) = N(i + j)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a b = Plus a b"

lemma aval_plus: "aval (plus a b) s = aval a s + aval b s"
  apply(induction rule: plus.induct)
      apply(auto split:aexp.split)
  done

fun asimp:: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a b) = plus (asimp a) (asimp b)"

lemma "aval (asimp a) s = aval a s"
  apply(induction rule: asimp.induct)
    apply(auto split: aexp.split)
  by (simp add: aval_plus)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True" |
"optimal (V x) = True" |
"optimal (Plus (N a) (N b)) = False" |
"optimal (Plus a b) = ((optimal a) \<and> (optimal b))"

lemma "optimal (asimp_const a)"
  apply(induction a)
    apply(auto split: aexp.split)
  done

fun full_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"full_plus (N i) (N j) = N(i + j)" |
"full_plus (N i) (Plus a (N j)) = Plus a (N (i + j))" |
"full_plus (N i) (Plus (N j) a) = Plus a (N (i + j))" |
"full_plus a (Plus b (N j)) = Plus (Plus a b) (N j)" |
"full_plus a (Plus (N j) b) = Plus (Plus a b) (N j)" |
"full_plus (Plus a (N i)) (N j) = Plus a (N (i + j))" |
"full_plus (Plus (N i) b) (N j) = Plus b (N (i + j))" |
"full_plus (Plus a (N j)) b = Plus (Plus a b) (N j)" |
"full_plus (Plus (N j) a) b = Plus (Plus a b) (N j)" |
"full_plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"full_plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"full_plus a b = Plus a b"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = N n" |
"full_asimp (V x) = V x" |
"full_asimp (Plus a b) = full_plus(full_asimp a)(full_asimp b)"

lemma aval_full_plus: "aval (full_plus a b) s = aval a s + aval b s"
  apply(induction rule: full_plus.induct)
      apply(auto split:aexp.split)
  done

lemma "aval (full_asimp a) s = aval a s"
  apply(induction a)
    apply(auto split: aexp.split)
  by (simp add: aval_full_plus)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = N n" |
"subst x a (V y) = (if (x = y) then a else V y)" |
"subst x a (Plus b c) = Plus (subst x a b) (subst x a c)"

lemma substitution: "aval (subst x a e) s = aval e (s(x := aval a s))"
    apply(induction e)
  apply(auto)
  done

lemma aval_uniq: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(induction e)
  apply(auto)
  done

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PIncr vname

fun get_first :: "val \<times> state \<Rightarrow> val" where
"get_first (a, s) = a"

fun get_last :: "val \<times> state \<Rightarrow> state" where
"get_last (a, s) = s"

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> val \<times> state" where
"aval2 (N2 n) s = (n, s)" |
"aval2 (V2 x) s = (s x, s)" |
"aval2 (Plus2 a b) s = (get_first (aval2 a s) + get_first (aval2 b s), get_last (aval2 b s))" |
"aval2 (PIncr x) s = (s x, s(x:= (s x + 1))) "

datatype aexp3 = N3 int | V3 vname | Plus3 aexp3 aexp3 | PIncr3 vname | Div aexp3 aexp3 

fun aval3 :: "aexp3 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval3 (N3 n) s = Some(n, s)" |
"aval3 (V3 x) s = Some(s x, s)" |
"aval3 (Plus3 a b) s = (case (aval3 a s) of Some (a', s') \<Rightarrow> 
  (case (aval3 b s) of Some (b', s'') \<Rightarrow> Some(a' + b', s'') |
     None \<Rightarrow> None) | 
  None \<Rightarrow> None)" |
"aval3 (PIncr3 x) s = Some (s x, s(x:= (s x + 1))) " |
"aval3 (Div a b) s = (case (aval3 b s) of Some(b', s') \<Rightarrow> 
  (if b' = 0 then None else 
    (case (aval3 a s) of Some(a', s'') \<Rightarrow> Some(a' div b', s'') | None \<Rightarrow> None  )) | 
  None \<Rightarrow> None)"

lemma "aval3 (Div (N3 3) (N3 0)) (\<lambda>x. 1) = None"
  by auto


datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) s = n" |
"lval (Vl x) s = s x" |
"lval (Plusl a b) s = (lval a s) + (lval b s)" |
"lval (LET x a b) s = lval b (s (x := lval a s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = (N n)" |
"inline (Vl x) = (V x)" |
"inline (Plusl a b) = (Plus (inline a) (inline b))" |
"inline (LET x a b) = subst x (inline a) (inline b)"

lemma "aval (inline e) s = lval e s"
  apply(induction e arbitrary: s)
     apply(auto split:lexp.split)
  by (simp add: substitution)




end