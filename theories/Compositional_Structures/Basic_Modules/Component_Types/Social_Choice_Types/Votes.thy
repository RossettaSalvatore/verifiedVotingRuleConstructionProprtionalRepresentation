


section \<open>Votes\<close>

theory Votes
  imports Complex_Main
HOL.List
"HOL-Combinatorics.Multiset_Permutations"
"HOL-Combinatorics.List_Permutation"
(*Smart_Isabelle.Smart_Isabelle*)
Preference_Relation
Profile
Result

begin

(* \<equiv> *)

definition above_set :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "above_set r a \<equiv> above (set r) a"

lemmas [code] = above_set_def[symmetric]
lemma [code]:
  \<open>above_set [] a = {}\<close>
  \<open>above_set ((x,y)#xs) a = (if x=a then {y} else {}) \<union> above_set xs a\<close>
  by (auto simp: above_set_def above_def)

(* returns the position of the ranking
 ex: a>b>c>d with ''c'' as input will return 3 *)
fun count_above :: "('a rel) \<Rightarrow> 'a \<Rightarrow> nat" where
  "count_above r a = card (above r a)"

value "count_above {(''partyA'', ''partyB''), (''partyA'', ''partyC'')} ''partyC''"

subsection  \<open>Definition\<close>
text  \<open>Parties is the list of parties, that can be of any type. 
       Votes is a function used to assign a rational number (indeed, the votes) to each party. \<close>

type_synonym 'b Parties = "'b list"
type_synonym 'b Votes = "'b \<Rightarrow> rat"
                
text  \<open>Every seat is unique and identified and has a set of parties to which it is assigned.\<close>
type_synonym ('a, 'b) Seats = "'a \<Rightarrow> 'b set"
type_synonym Params = "nat list"

primrec first_pos :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"first_pos P [] = 0"
| "first_pos P (x # xs) = (if P x then 0 else Suc (first_pos P xs))"

value "first_pos (\<lambda>x. x = ''1'') [''0'', ''0'', ''1'']"

fun retrieve_votes :: "'b \<Rightarrow> 'b Parties \<Rightarrow> rat list \<Rightarrow> rat" where
"retrieve_votes party parties votes = votes ! (first_pos(\<lambda>x. x = party) parties)"

value "retrieve_votes ''partyB'' [''partyA'', ''partyB''] [4, 5]"

(* function to generate the list of parameters *)
fun generate_list :: "bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "generate_list True n = [1..<n]" |
  "generate_list False n = filter (\<lambda>x. x mod 2 = 1) [1..<n]"

text \<open> This function counts votes for one party and add correspondence to Votes function \<close>


fun cnt_votes :: "'a \<Rightarrow> 'a Profile \<Rightarrow> nat \<Rightarrow> rat list \<Rightarrow> rat \<Rightarrow> rat list" where
  "cnt_votes p [] index votes n = votes @ [n]" |
  "cnt_votes p (px # profil) index votes n = 
     (case (count_above px p) of
        0 \<Rightarrow> cnt_votes p profil index votes (n + 1)
      | _ \<Rightarrow> cnt_votes p profil index votes n)"

value "cnt_votes ''partyB'' [{(''partyA'', ''partyB'')}]
         (first_pos (\<lambda>x. x = ''partyB'') [''partyB'', ''partyA'']) [0, 0] 0"

fun empty_v :: "('b \<Rightarrow> rat)" where
  "empty_v b = 0"

text \<open> This function receives in input the list of parties and the list of preferation 
       relations. The output is the function Votes, in which every party has the 
       correspondent number of votes.  \<close>

(* multiset version

inductive fold_graph :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool"
  for f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and z :: 'b
  where
    emptyI [intro]: "fold_graph f z {} z"
  | insertI [intro]: "x \<notin> A \<Longrightarrow> fold_graph f z A y \<Longrightarrow> fold_graph f z (insert x A) (f x y)"

definition fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a set \<Rightarrow> 'b"
  where "fold f z A = (if finite A then (THE y. fold_graph f z A y) else z)"

definition fold_mset :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a multiset \<Rightarrow> 'b"
where
  "fold_mset f s M = Finite_Set.fold (\<lambda>x. f x ^^ count M x) s (set_mset M)"
*)

definition remove_some :: "'a multiset \<Rightarrow> 'a" where
"remove_some M = (SOME x. x \<in> set_mset M)"

definition my_fold :: "('b \<Rightarrow> 'b \<Rightarrow> rat) \<Rightarrow> 'b Votes \<Rightarrow> 'a set \<Rightarrow> 'b Votes"
  where "my_fold f z A = (if finite A then z else z)"

fun calc_votes_mset :: "'b multiset \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes \<Rightarrow> 'b Votes" where
  "calc_votes_mset party_mset pr vot = 
      my_fold (\<lambda>party. cnt_votes party pr vot 0) vot (set_mset party_mset)"

(* EXAMPLE *)
(* Define the party multiset *)
definition party_multiset :: "char list multiset" where
  "party_multiset = {#''a'', ''b'', ''c'', ''d''#}"

(* Define the initial votes *)
fun empty_votes :: "char list \<Rightarrow> rat" where
  "empty_votes p = 0"

(* Calculate the votes *)
definition pref_rel_a :: "char list Preference_Relation" where
"pref_rel_a = {(''b'', ''a''), (''d'', ''c''), 
                (''d'',''a''), (''c'', ''b''), 
                (''c'',''a''), (''d'', ''b'')}"

definition pref_rel_b :: "char list Preference_Relation" where
"pref_rel_b = {(''a'', ''b''), (''c'', ''b''), 
                (''d'', ''b''), (''a'', ''c''), 
                (''c'', ''d''), (''a'', ''d'')}"

definition pref_rel_c :: "char list Preference_Relation" where
"pref_rel_c = {(''a'', ''c''), (''b'', ''c''), 
                (''d'', ''c''), (''a'', ''b''), 
                (''b'', ''d''), (''a'', ''d'')}"

definition pref_rel_b2 :: "char list Preference_Relation" where
"pref_rel_b2 = {(''a'', ''b''), (''c'', ''b''), 
                 (''d'', ''b''), (''c'', ''a''), 
                 (''a'', ''d''), (''c'', ''d'')}"

definition pref_rel_b3 :: "char list Preference_Relation" where
"pref_rel_b3 = {(''a'', ''b''), (''c'', ''b''), 
                 (''d'', ''b''), (''c'', ''a''), 
                 (''a'', ''d''), (''c'', ''d'')}"

definition pref_rel_d :: "char list Preference_Relation" where
"pref_rel_d = {(''a'', ''d''), (''b'', ''d''), 
                (''c'', ''d''), (''a'', ''c''), 
                (''c'', ''b''), (''a'', ''b'')}"

definition pref_rel_a2 :: "char list Preference_Relation" where
"pref_rel_a2 = {(''b'', ''a''), (''c'', ''a''), 
                 (''d'', ''a''), (''b'', ''d''), 
                 (''b'', ''c''), (''d'', ''c'')}"

(* Define the profile *)
definition profile_list :: "char list Profile" where
"profile_list = [pref_rel_a, pref_rel_b, pref_rel_c, pref_rel_b2, 
                 pref_rel_b3, pref_rel_d, pref_rel_a2]"

fun calc_votes :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a Profile \<Rightarrow> rat list \<Rightarrow> rat list" where
  "calc_votes [] fixed_parties prof votes = votes" |
  "calc_votes (party # parties) fixed_parties prof votes = 
      (let ix = first_pos (\<lambda>x. x = party) fixed_parties in
      calc_votes parties fixed_parties prof (cnt_votes party prof ix votes 0))"

(* this works 09/03/24 *)
value "calc_votes [''a'', ''b''] [''a'', ''b''] profile_list []"

(*prove "p1 <~~> p2 \<Longrightarrow> (calc_votes p1 profl votes = calc_votes p2 profl votes)"
*)
lemma calc_votes_permutation:
  fixes
    p1 :: "'b Parties" and
    p2 ::"'b Parties" and
    profl ::"'b Profile" and
    votes::"rat list"
  assumes "p1 <~~> p2"
  shows "calc_votes p1 p1 profl votes = calc_votes p2 p2 profl votes"
  using assms
proof (induction p1 arbitrary: p2)
  case Nil
  then show ?case by simp
next
  case (Cons a p1)
  obtain p2' where "p2 <~~> (a # p2')" using assms by (metis Cons.prems)
  then have "(a # p1) <~~> (a # p2')" using assms Cons.prems by auto
  then have "calc_votes (a # p1) p1 profl votes = 
             calc_votes p1 p1 profl (cnt_votes a profl [] 0)" using assms by simp
  then have "\<dots> = 
             calc_votes p2' profl (cnt_votes a profl empty_v 0)" using assms
  by (metis Cons.IH Cons.prems \<open>mset p2 = mset (a # p2')\<close> calc_votes.simps(2) cons_perm_imp_perm list.exhaust mset_zero_iff_right)
  then have "... = calc_votes (a # p2') profl votes" using assms by simp
  then have "... = calc_votes p2 profl votes" by simp
  then show ?case by simp
qed


text \<open> This function receives in input the function Votes and the list of parties. The 
       output is the list of parties with the maximum number of votes.  \<close>

(* adapted to list. works 09/03 *)
fun max_val:: "rat list \<Rightarrow> rat \<Rightarrow> rat" where 
"max_val [] m = m" | 
"max_val (px # p) m = max_val p (if px > m then px else m)"

value "max_val [1, 4, 2] 0"

fun max_parties:: "rat \<Rightarrow> rat list \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties
                     \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
"max_parties m v fixed_p [] output = output" | 
"max_parties m v fixed_p (px # p) output = 
        max_parties m v fixed_p p (if (retrieve_votes px fixed_p v) = m then (output @ [px])
                                   else output)"

(* works 09/03 *)
value "max_parties (max_val [7, 4, 7] 0) [7, 4, 7]
                     [''partyA'', ''partyB'', ''partyC''] 
                     [''partyA'', ''partyB'', ''partyC'']
                     []"

lemma max_parties_not_empty:
  fixes
  m::"rat" and
  mvp::"'b Parties" and
  v::"'b Votes" and
  p::"'b Parties"
  assumes "p \<noteq> []"
  shows "max_parties m v p mvp \<noteq> []"
  using assms
proof (cases)
  case True
  then show ?thesis sorry
next
  case False
  then show ?thesis sorry
qed

fun find_max_votes :: "rat list \<Rightarrow> 'b Parties \<Rightarrow> 'b list" where
  "find_max_votes v p = max_parties (max_val v 0) v p p []"


lemma find_max_votes_not_empty:
  fixes
  v::"rat list" and
  p::"'b Parties"
  assumes "p \<noteq> []"
  shows "find_max_votes v p \<noteq> []"
  using assms
  sorry

fun assign_seat :: "'a::linorder \<Rightarrow> 'b  \<Rightarrow> ('a::linorder, 'b) Seats 
                    \<Rightarrow> ('a::linorder, 'b) Seats" where
  "assign_seat seat_n winner seats = (\<lambda>n. if n = seat_n then {winner} else seats n)"

text \<open> This function counts seats of a given party. \<close>

fun count_seats :: "'b set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "count_seats p s i = 
    (card {ix. ix \<in> i \<and> s ix = p})"

text \<open> This function updates the "fractional votes" of the winning party, dividing the starting
       votes by the i-th parameter, where i is the number of seats won by the party. \<close>

(* works adapted *)
fun update_votes :: "'b \<Rightarrow> 'b list \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                            'a::linorder set \<Rightarrow> rat list \<Rightarrow> 
                            rat list \<Rightarrow> rat list \<Rightarrow> rat list" where 
"update_votes party parties seats i votes fractv factors = 
    (let ix = first_pos(\<lambda>x. x = party) parties in
     list_update fractv ix ((retrieve_votes party parties votes) / (List.nth factors (count_seats {party} seats i))))"

end
