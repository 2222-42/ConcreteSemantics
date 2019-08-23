theory Concrete_Semantics_3_2
  imports Main
begin
(* from 3.1 *)
type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N(i1+i2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x ) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

(* from 3.1 *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b =  Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc(n1 < n2)" |
"less a1 a2 = Less a1 a2"

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq (N n1) (N n2) = Not(Bc(n1 < n2)) \<and>  Not(Bc(n2 < n1))"

end