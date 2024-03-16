


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
type_synonym ('a, 'b) Seats = "'a \<Rightarrow> 'b list"
type_synonym Params = "nat list"

primrec get_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"get_index P [] = 0"
| "get_index P (x # xs) = (if P x then 0 else Suc (get_index P xs))"

value "get_index (\<lambda>x. x = ''1'') [''0'', ''0'', ''1'']"

fun get_votes :: "'b \<Rightarrow> 'b Parties \<Rightarrow> rat list \<Rightarrow> rat" where
"get_votes party parties votes = votes ! (get_index(\<lambda>x. x = party) parties)"

value "get_votes ''partyB'' [''partyA'', ''partyB''] [4, 5]"

(* function to generate the list of parameters *)
fun generate_list :: "bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "generate_list True n = [1..<n]" |
  "generate_list False n = filter (\<lambda>x. x mod 2 = 1) [1..<n]"

text \<open> This function counts votes for one party and add returns the number of votes \<close>

fun cnt_votes :: "'a \<Rightarrow> 'a Profile \<Rightarrow> rat \<Rightarrow> rat" where
  "cnt_votes p [] n = n" |
  "cnt_votes p (px # profil) n = 
     (case (count_above px p) of
        0 \<Rightarrow> cnt_votes p profil (n + 1)
      | _ \<Rightarrow> cnt_votes p profil n)"

value "cnt_votes ''partyB'' [{(''partyA'', ''partyB'')}] 0"

fun empty_v :: "('b \<Rightarrow> rat)" where
  "empty_v b = 0"

(* lemma from zulip *)
lemma perm_induct:
  assumes "P [] []"
  assumes "\<And>x xs ys. P (x # xs) (x # ys)"
  assumes "\<And>x y xs ys. P (x # y # xs) (y # x # ys)"
  assumes "\<And>xs ys zs. P xs ys \<Longrightarrow> P ys zs \<Longrightarrow> P xs zs"
  shows "mset xs = mset ys \<Longrightarrow> P xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms
    by (metis neq_Nil_conv perm_empty2)
qed

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
fun update_at_index :: "rat list \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> rat list" where
  "update_at_index [] _ _ = []" |
  "update_at_index (x # xs) 0 n = n # xs" |
  "update_at_index (x # xs) (Suc i) n = x # update_at_index xs i n"

value "update_at_index [] 1 5"

definition remove_some :: "'a multiset \<Rightarrow> 'a" where
"remove_some M = (SOME x. x \<in> set_mset M)"

definition my_fold :: "('b \<Rightarrow> 'b \<Rightarrow> rat) \<Rightarrow> 'b Votes \<Rightarrow> 'a set \<Rightarrow> 'b Votes"
  where "my_fold f z A = (if finite A then z else z)"

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

(* update_at_index added here bring error in full_module *)
fun calc_votes :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a Profile \<Rightarrow> rat list \<Rightarrow> rat list" where
  "calc_votes [] ps prof votes = votes" |
  "calc_votes (party # parties) ps prof votes = 
      (let n = cnt_votes party prof 0;
       i = get_index(\<lambda>x. x = party) ps;
       new_v = update_at_index votes i n in
      calc_votes parties ps prof (votes @ [n]))"

lemma simp_votes:
  fixes
    parties:: "'b Parties" and
    fparties::"'b Parties" and
    party::"'b" and
    profile:: "'b Profile"
  assumes "party \<in> set parties"
  shows "calc_votes parties fparties profile [] ! get_index(\<lambda>x. x = party) fparties =
         cnt_votes party profile 0"
  sorry

lemma votes_perm:
  fixes
    parties:: "'b Parties" and
    parties':: "'b Parties" and
    profile:: "'b Profile"
  assumes "mset parties = mset parties'"
  shows "\<forall> party. party \<in> set parties \<longrightarrow> (calc_votes parties parties profile []) !
                                            get_index(\<lambda>x. x = party) parties
 = calc_votes parties' parties' profile [] ! get_index(\<lambda>x. x = party) parties'"
  by (metis assms perm_set_eq simp_votes) 

(* this works 09/03/24 *)
value "(calc_votes [''a'', ''b''] profile_list [])! (get_index(\<lambda>x. x = ''a'') [''a'', ''b''])"
value "(calc_votes [''b'', ''a''] profile_list [])! (get_index(\<lambda>x. x = ''a'') [''b'', ''a''])"

(*prove "p1 <~~> p2 \<Longrightarrow> (calc_votes p1 profl votes = calc_votes p2 profl votes)"
*)

lemma calc_votes_permutation:
  fixes
    p1 :: "'b Parties" and
    p2 ::"'b Parties" and
    profl ::"'b Profile" and
    votes:: "rat list"
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
  then have "calc_votes (a # p1) (a # p1) profl votes = 
             calc_votes p1 (a # p1) profl (cnt_votes a profl [] 0)" using assms by simp
  also have "\<dots> = 
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
        max_parties m v fixed_p p (if (get_votes px fixed_p v) = m then (output @ [px])
                                   else output)"

lemma max_parties_perm:
  fixes
parties::"'b Parties" and
parties'::"'b Parties" and
v::"rat list" and
v'::"rat list"
assumes "mset parties = mset parties'"
assumes "length parties = length v"
assumes "mset v = mset v'"
shows "max_parties m v parties parties output = max_parties m v' parties' parties' output"
  using assms

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

fun get_winners :: "rat list \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
  "get_winners v p = max_parties (max_val v 0) v p p []"
                                                    

lemma find_max_votes_not_empty:
  fixes
  v::"rat list" and
  p::"'b Parties"
  assumes "p \<noteq> []"
  shows "get_winners v p \<noteq> []"
  using assms
  sorry

fun update_seat :: "'a::linorder \<Rightarrow> 'b list \<Rightarrow> ('a::linorder, 'b) Seats 
                    \<Rightarrow> ('a::linorder, 'b) Seats" where
  "update_seat seat_n winner seats = seats(seat_n := winner)"

text \<open> This function counts seats of a given party. \<close>

fun count_seats :: "'b list \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "count_seats p s i = 
    (card {ix. ix \<in> i \<and> s ix = p})"

lemma anonymous_total:
  fixes
parties::"'b Parties" and
parties'::"'b Parties" and
votes::"rat list" and
votes'::"rat list"
assumes "mset parties = mset parties'"
assumes "mset votes = mset votes'"
shows "get_winners votes parties = get_winners votes' parties'"
  sorry


(* ----------- Prova anonimita con votes function -------------- *)
fun calc_votes_VARIANT :: "'a list \<Rightarrow> 'a Profile \<Rightarrow> 'a Votes \<Rightarrow> 'a Votes" where
  "calc_votes_VARIANT [] prof votes = votes" |
  "calc_votes_VARIANT (party # parties) prof votes = 
      (let n = cnt_votes party prof 0 in
      calc_votes_VARIANT parties prof (votes(party := n)))"


fun max_val_VARIANT:: "'b Votes \<Rightarrow> 'b Parties \<Rightarrow> rat \<Rightarrow> rat" where 
"max_val_VARIANT v [] m = m" | 
"max_val_VARIANT v (px # p) m = max_val_VARIANT v p (if v px > m then v px else m)"


fun max_parties_VARIANT:: "rat \<Rightarrow> 'b Votes \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties
                     \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
"max_parties_VARIANT m v fixed_p [] output = output" | 
"max_parties_VARIANT m v fixed_p (px # p) output = 
        max_parties_VARIANT m v fixed_p p (if v px = m then (output @ [px])
                                   else output)"

lemma votes_equal:
  fixes
  prof::"'b Profile" and
  parties::"'b Parties" and
  parties'::"'b Parties"
assumes "parties = parties'"
  shows "(calc_votes_VARIANT parties prof votes)
                                 =  (calc_votes_VARIANT parties' prof votes)"
  using assms
  by simp

lemma max_parties_perm_VARIANT:
  fixes
  parties::"'b Parties" and
  parties'::"'b Parties" and
  votes::"'b Votes" and
  votes'::"'b Votes"
assumes "mset parties = mset parties'"
assumes "votes = votes'" 
shows "max_parties_VARIANT m (calc_votes_VARIANT parties prof votes)
         parties parties =
       max_parties_VARIANT m (calc_votes_VARIANT parties' prof votes')
         parties' parties'"

end
