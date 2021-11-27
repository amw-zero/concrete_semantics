theory IMPExpMult

imports Main

begin

type_synonym vname = string

datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a1 a2) s = aval a1 s + aval a2 s"

definition exp :: "aexp" where "exp = (Plus (N 5) (V ''x''))"

value "aval exp ((\<lambda> x. 0)(''x'' := 1))"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus a1 a2) = 
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N(n1 + n2) |
    (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply(auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow>  aexp" where
"plus (N i1) (N i2) = N(i1 + i2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction rule: plus.induct)
    apply(auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply(induction a)
    apply(auto simp add: aval_plus)
  done

fun optimal_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> bool" where
"optimal_plus (N _) (N _) = False" |
"optimal_plus a1 a2 = True"

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N _) = True" |
"optimal (V _) = True" |
"optimal (Plus a1 a2) = ((optimal a1) \<and> (optimal a2) \<and> (optimal_plus a1 a2))"

theorem "optimal(asimp_const a)"
  apply(induction a)
    apply(auto split: aexp.split)
  done

fun full_plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"full_plus (N n1) (N n2) = N (n1 + n2)" |
"full_plus (N n1) (Plus a (N n2)) = (Plus a (N (n1 + n2)))" |
"full_plus (Plus a (N n1)) (N n2) = (Plus a (N (n1 + n2)))" |
"full_plus a1 a2 = (Plus a1 a2)"

lemma full_plus_aval: "aval (full_plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction rule: full_plus.induct)
    apply(auto)
  done

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = N n" |
"full_asimp (V x) = V x" |
"full_asimp (Plus a1 a2) = full_plus (full_asimp a1) (full_asimp a2)"

value "full_asimp (Plus (N 1) (Plus (V ''x'') (N 2)))"
    
theorem "aval (full_asimp a) s = aval a s"
  apply(induction a arbitrary: s)
    apply(auto simp add: full_plus_aval)
  done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst v e (V x) = (if v = x then e else (V x))" |
"subst v e (Plus a1 a2) = (Plus (subst v e a1) (subst v e a2))" |
"subst v e a = a"

value "subst ''x''  (N 2) (Plus (V ''x'') (N 1))"

lemma subst_preserves_semantics: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e)
    apply(auto)
  done

theorem "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(simp add: subst_preserves_semantics)
  done

end