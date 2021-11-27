theory Chapter2
imports Main
begin

value  "1 + (2::nat)"

value "1 + (2::int)"
  
value "1 - (2::nat)"
  
value "1 - (2::int)"

value "[a,b] @ [c,d]"

 

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc(add m n)"


lemma add_assoc : "add (add m n) p = add m (add n p)"
  apply (induction m)
  apply auto
  done  
  
lemma add_aux1 [simp] : "n = add n 0"
  apply (induction n)
  apply auto
  done

lemma add_aux2 [simp] : "Suc (add n m) = add n (Suc m)"
  apply (induction n)
  apply auto
  done
lemma add_comm: "add m n = add n m"
  apply (induction m)
  apply auto
  done 

fun double :: "nat \<Rightarrow> nat" where
"double 0 = 0" |
"double (Suc n) = Suc (Suc (double n))"

lemma double_add: "double m = add m m"
  apply (induction m)
  apply auto  
  done
    

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] x = 0" |
"count (x#xs) y = (if x = y then (1+ count xs y) else (count xs y))"



theorem "count xs x \<le> length xs"
  apply (induction xs)
  apply auto  
  done

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] y = [y]" |
  "snoc (x#xs) y = x#(snoc xs y)"  
 


value "snoc [1,2,3] (4::int)"
  
fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x#xs) =  snoc (reverse xs) x"


value "reverse [1,2,3,(4::int)]"  
value "reverse [(4::int)]"

lemma [simp]:"reverse (snoc xs a) = a # reverse xs"
  apply (induction xs)
  apply auto
  done   
  
theorem rev_1: "reverse (reverse xs) = xs"
  apply (induction xs)
  apply auto
  done  
    
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto n = n + sum_upto (n-1)"


lemma "sum_upto n = n * (n+1) div 2"
  apply (induction n)
  apply auto
  done  

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l a r) = a#(contents l @ contents r)"


fun sum_tree :: "nat tree \<Rightarrow> nat" where
  "sum_tree Tip = 0" |
  "sum_tree (Node l a r) = a + sum_tree l + sum_tree r"



lemma "sum_tree t = sum_list(contents t)"
  apply (induction t)
  apply auto
  done  

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"  
  
fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Tip a) = Tip a" |
  "mirror (Node l a r) = Node (mirror r) a (mirror l)"  
  
fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip a) = [a]" |
  "pre_order (Node l a r) = a # (pre_order l @ pre_order r)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip a) = [a]" |
  "post_order (Node l a r) = (post_order l) @ (post_order r) @ [a]"

  
value "rev (post_order (Node (Node (Tip 1) 4 (Tip 2)) 3 (Node (Tip 0) 7 (Tip (4::int)))))"  
value "pre_order (mirror (Node (Node (Tip 1) 4 (Tip 2)) 3 (Node (Tip 0) 7 (Tip (4::int)))))"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply (induction t)
  apply auto  
  done
    
end
