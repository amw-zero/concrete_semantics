theory Concrete
imports Main

begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"

theorem add_02[simp]: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done

theorem add_associative[simp]: "add (add x y) z = add x (add y z)"
  apply(induction x)
  apply(auto)
  done

lemma add_comm_sub[simp]: "Suc (add y x) = add y (Suc x)"
  apply(induction y)
  apply(auto)
  done

theorem add_commutative: "add x y = add y x"
  apply(induction x)
  apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double x = 2 * x"

theorem double_two_additions: "double x = add x x"
  apply(induction x)
  apply(auto)
  done
  
fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

(*
fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"
*)

value "rev(Cons True (Cons False Nil))"

lemma app_Nil2 [simp]: "app xs Nil = xs"
apply(induction xs)
apply(auto)
  done

lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply(induction xs)
apply(auto)
done

lemma rev_app[simp]: "rev(app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
  apply(auto)
  done

theorem rev_rev [simp]: "rev(rev xs) = xs"
  apply(induction xs)
  apply(auto)
  done

value "1 + (2::nat)"

value "1 + (2::int)"

value "1 -(2::nat)"

value "1 - (2::int)"

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count _ Nil = 0" |
"count e (Cons x xs) = 1 + count e xs"

theorem count_lte_length: "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] e = [e]" | 
"snoc (Cons x xs) e = (Cons x (snoc xs e))"

fun reverse_snoc :: "'a list \<Rightarrow> 'a list" where
"reverse_snoc Nil = Nil" |
"reverse_snoc (Cons x xs) = snoc (reverse_snoc xs) x"

theorem snoc_prepend[simp]: "reverse_snoc (snoc xs a) = a # (reverse_snoc xs)"
  apply(induction xs)
  apply(auto)
  done

theorem rev_rev_snoc: "reverse_snoc (reverse_snoc xs) = xs"
  apply(induction xs)
   apply(auto)
  done

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto x = x + (sum_upto (x - 1))"

theorem sum_formula: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node l v r) = append (contents l) (v # (contents r))"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node l v r) = sum_tree l + v + sum_tree r"

theorem sum_tree_works: "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

value "sum_list [1,2,(3::nat)]"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node l a r) = Node (mirror r) a (mirror l)"

lemma "mirror(mirror t) = t"
  apply(induction t)
   apply(auto)
  done

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order Tip = []" |
"pre_order (Node l a r) = (a # (pre_order l)) @ (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order Tip = []" |
"post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

fun mirror_2 :: "'a tree \<Rightarrow> 'a tree" where
  "mirror_2 Tip = Tip" |
  "mirror_2 (Node l a r) = Node (mirror_2 r) a (mirror_2 l)"  

fun pre_order_2 :: "'a tree \<Rightarrow> 'a list" where
  "pre_order_2 Tip = []" |
  "pre_order_2 (Node l a r) = a # (pre_order_2 l @ pre_order_2 r)"

fun post_order_2 :: "'a tree \<Rightarrow> 'a list" where
  "post_order_2 Tip = []" |
  "post_order_2 (Node l a r) = (post_order_2 l) @ (post_order_2 r) @ [a]"

lemma reversing_stuff: "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

(* 3 *)
(* |-- 4 *)
(* |--  *)

value "rev (post_order ((Node (Node Tip 4 Tip) 3 (Node Tip 7 Tip)) ::nat tree))" 
value "pre_order (mirror (Node (Node Tip 4 Tip) 3 (Node Tip 7 Tip))::nat tree)"

value "pre_order (
(Node 
  (Node Tip 1 Tip) 
  2 
  (Node Tip 3 Tip)) :: nat tree)"


value "post_order (
(Node 
  (Node Tip 1 Tip) 
  2 
  (Node Tip 3 Tip)) :: nat tree)"

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = [a]" |
"intersperse a (x # xs) = x # (a # (intersperse a xs))"

theorem interspersing: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs)
   apply(auto)
  done

(* 2 *)
value "Suc(Suc Zero)"
(* 3 *)
value "Suc(Suc (Suc Zero))"

fun my_add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"my_add 0 n = n" |
"my_add (Suc m) n = Suc(add m n)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem tail_rec_add: "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

value "intersperse 5 [1,2,3::nat]"

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 0" |
"nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

(*
  explode 1 t
   explode 0 (Node t t)

  explode 2 t
    explode 1 (Node t t)
     explode 0 (Node (Node t t) (Node t t))

  explode 3 t
    explode 2 (Node t t)
      explode 1 (Node (Node t t) (Node t t))
        explode 0 (Node (Node (Node t t) (Node t t)) (Node (Node t t) (Node t t)))
*)

value "nodes (Node (Node Tip Tip) (Node Tip Tip))"

value "nodes (explode 4  (Node (Node Tip Tip) (Node Tip Tip)))"

value "explode 0 Tip"

(* by nitpick *)
(* by quickcheck *)
theorem "nodes (explode n t) = (2 ^ n) * (nodes t) + 2^n - 1"
  apply(induction n arbitrary: t)
   apply(auto simp add: algebra_simps)
  done

end


  