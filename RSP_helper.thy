section {* General-purpose stuff *}

theory RSP_helper imports 
  Main 
begin

text {* Forward function composition *}
notation fcomp (infixl ";;" 55)

value "(plus 1 ;; times 2) (3::int)"
value "(plus 1 \<circ> times 2) (3::int)"
text {* Functions that are unspecified except for a small number of input/output
pairs. *}

fun singleton_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("{ _ \<mapsto> _ }")
where
  "{x \<mapsto> v} = undefined (x := v)"
  
fun doubleton_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("{ _ \<mapsto> _ , _ \<mapsto> _ }")
where
  "{x1 \<mapsto> v1, x2 \<mapsto> v2} = undefined (x1 := v1, x2 := v2)"
  
fun tripleton_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" 
  ("{ _ \<mapsto> _ , _ \<mapsto> _ , _ \<mapsto> _ }")
where
  "{x1 \<mapsto> v1, x2 \<mapsto> v2, x3 \<mapsto> v3} = undefined (x1 := v1, x2 := v2, x3 := v3)"
  
fun quadrupleton_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 
  'a \<Rightarrow> 'b" ("{ _ \<mapsto> _ , _ \<mapsto> _ , _ \<mapsto> _, _ \<mapsto> _ }")
where
  "{x1 \<mapsto> v1, x2 \<mapsto> v2, x3 \<mapsto> v3, x4 \<mapsto> v4} = 
  undefined (x1 := v1, x2 := v2, x3 := v3, x4 := v4)"
  
fun quintupleton_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 
  'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" ("{ _ \<mapsto> _ , _ \<mapsto> _ , _ \<mapsto> _, _ \<mapsto> _ , _ \<mapsto> _}")
where
  "{x1 \<mapsto> v1, x2 \<mapsto> v2, x3 \<mapsto> v3, x4 \<mapsto> v4, x5 \<mapsto> v5} = 
  undefined (x1 := v1, x2 := v2, x3 := v3, x4 := v4, x5 := v5)"
  
fun sextupleton_fun :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 
  'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" 
  ("{ _ \<mapsto> _ , _ \<mapsto> _ , _ \<mapsto> _, _ \<mapsto> _ , _ \<mapsto> _, _ \<mapsto> _}")
where
  "{x1 \<mapsto> v1, x2 \<mapsto> v2, x3 \<mapsto> v3, x4 \<mapsto> v4, x5 \<mapsto> v5, x6 \<mapsto> v6} = 
  undefined (x1 := v1, x2 := v2, x3 := v3, x4 := v4, x5 := v5, x6 := v6)"

text {* Disjoint union of functions. The domains @{text A} and @{text B} are
assumed disjoint. *}

fun combine_fun :: "(('a \<Rightarrow> 'b) \<times> 'a set) \<Rightarrow> (('a \<Rightarrow> 'b) \<times> 'a set) \<Rightarrow> 'a \<Rightarrow> 'b"
  (infix "\<oplus>" 100)
where
  "(f,A) \<oplus> (g,B) = (\<lambda>x. if x \<in> A then f x else g x)"

text {* The given binary predicate @{text f} must hold between each pair of
consecutive elements in a given list. *}
  
fun list_all_pairs :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where 
  "list_all_pairs _ [] = True"
| "list_all_pairs _ [x] = True"
| "list_all_pairs f (x # y # xs) = (f x y \<and> list_all_pairs f (y # xs))"

text {* Convert a list into a total order. *}

fun total_order_of :: "'a list \<Rightarrow> ('a \<times> 'a) set"
where
  "total_order_of [] = {}"
| "total_order_of (x # ys) = {(x,y) | y. y \<in> set ys} \<union> total_order_of ys"

lemma "total_order_of [1::int, 2, 3] = {(1,2),(1,3),(2,3)}"
by auto

text {* First/second/third component of a triple *}
fun fst3 where "fst3 (x,_,_) = x"
fun snd3 where "snd3 (_,y,_) = y"
fun thd3 where "thd3 (_,_,z) = z"

text {* First/second/third/fourth component of a quadruple *}
fun fst4 where "fst4 (w,_,_,_) = w"
fun snd4 where "snd4 (_,x,_,_) = x"
fun thd4 where "thd4 (_,_,y,_) = y"
fun fou4 where "fou4 (_,_,_,z) = z"

text {* Indexed map. *}

fun mapi_helper :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "mapi_helper f _ [] = []"
| "mapi_helper f n (x # xs) = f n x # mapi_helper f (Suc n) xs"

fun mapi :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "mapi f xs = mapi_helper f 0 xs"

text {* Remove the Nones from a list of optional elements *}

fun rm_Nones :: "'a option list \<Rightarrow> 'a list"
where
  "rm_Nones [] = []"
| "rm_Nones (None # xs) = rm_Nones xs"
| "rm_Nones (Some x # xs) = x # rm_Nones xs"

text {* We shall define the @{text span} of a relation as the set of all
elements it relates. *}

type_synonym 'a relation = "('a \<times> 'a) set"

fun span :: "'a relation \<Rightarrow> 'a set"
where
  "span R = (fst ` R) \<union> (snd ` R)"
  
value "span {(''a'', ''b''), (''a'', ''c'')}"

text {* Two functions give the same output for all inputs in the given set. *}
fun equal_over :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" 
  ("_ \<langle>=, _\<rangle>/ _" [50, 0, 51] 50)
where
  "f \<langle>=, xs\<rangle> g = (\<forall>x \<in> xs. f x = g x)"
  
text {* Holds if the intersection of two given sets is empty. *}
fun disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<not>\<inter>" 50)
where
  "xs \<not>\<inter> ys = (xs \<inter> ys = {})"

end
