theory ConcretePoly

imports Main

begin

fun pad_lists_r :: "int list \<Rightarrow> int list \<Rightarrow> (int list * int list) \<Rightarrow> (int list * int list)" where
"pad_lists_r [] [] out = out" |
"pad_lists_r (x # xs) [] (xso, yso) = pad_lists_r xs [] (x # xso, 0 # yso)" |
"pad_lists_r [] (y # ys) (xso, yso) = pad_lists_r [] ys (0 # xso, y # yso)" |
"pad_lists_r (x # xs) (y # ys) (xso, yso) = pad_lists_r xs ys (x # xso, y # yso)"

fun pad_lists :: "int list \<Rightarrow> int list \<Rightarrow> (int list * int list)" where
"pad_lists xs ys = (let (xp, yp) = pad_lists_r xs ys ([], []) in (rev xp, rev yp))"

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const i) _ = i" |
"eval (Add l r) x = (eval l x) + (eval r x)" |
"eval (Mult l r) x = (eval l x) * (eval r x)"

fun var_to_exp :: "nat \<Rightarrow> exp" where
"var_to_exp n = (
  if n = 0 then (Const 1) 
  else if n < 2 then Var 
  else Mult Var (var_to_exp (n - 1))
)"

fun make_polynomial_r :: "int list \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> exp" where
"make_polynomial_r [] _ e = e" |
"make_polynomial_r (c # cs) n e = 
  make_polynomial_r cs (n + 1) (Add e (Mult (Const c) (var_to_exp n)))"

fun make_polynomial :: "int list \<Rightarrow> exp" where
"make_polynomial cs = make_polynomial_r (tl cs) 1 (Const (hd cs))"

value "make_polynomial [5, 0, 1]"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp cs x = (
  let poly = make_polynomial cs in
  eval poly x
)"

fun sum_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"sum_coeffs xs ys = (let (xsp, ysp) = pad_lists xs ys in map (\<lambda>(x, y). x + y) (zip xsp ysp))"

fun mult_coeffs :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"mult_coeffs [] ys = []" |
"mult_coeffs (x # xs) ys = sum_coeffs (map (\<lambda>y. y * x) ys) (0 # (mult_coeffs xs ys))"

fun coeffs_r :: "exp \<Rightarrow> int list" where
"coeffs_r (Const i) = [i]" |
"coeffs_r Var = [0, 1, 2]" |
"coeffs_r (Add l r) = sum_coeffs (coeffs_r l) (coeffs_r r)" | 
"coeffs_r (Mult l r) = mult_coeffs (coeffs_r l) (coeffs_r r)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs e = coeffs_r e"

fun evalc :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalc [] v = 0" |
"evalc (x # xs) v = x + v * (evalc xs v)"

value "evalc [4,3,1] 2"

(*
lemma coefficients_produce_correct_polynomial[simp]:
"make_polynomial (coeffs e) = e"
  apply(induction e)
  apply(simp)
*)

theorem "evalp (coeffs e) x = eval e x"
  by smt
  (* apply(induction e)*)

(*
lemma evalc_add: "evalc (sum_coeffs

theorem "evalc (coeffs e) x = eval e x"
  apply(induction e)  
  apply(simp add: algebra_simps)
 
*)
end