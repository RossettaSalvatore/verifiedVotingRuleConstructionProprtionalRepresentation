


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
"List-Index.List_Index"
begin

(* \<equiv> *)

value "remove_nth 1 [''0'', ''1'']"

value "index [0::nat, 4, 5, 1] 1"

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

text  \<open>Every seat is unique and identified and has a set of parties to which it is assigned.\<close>
type_synonym ('a, 'b) Seats = "'a \<Rightarrow> 'b list"
type_synonym 'b Votes = "'b \<Rightarrow> rat"

type_synonym Params = "nat list"


primrec get_index :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> nat" where
"get_index P [] = 0"
| "get_index P (x # xs) = (if P x then 0 else Suc (get_index P xs))"

fun get_index_upd :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"get_index_upd px p = index p px"

lemma index_correct:
  fixes
  p::"'a list"
assumes "index p px < size p"
  shows "p ! (index p px) = px"
  by (meson assms index_eq_iff)

lemma get_index_upd_correct:
  assumes "get_index_upd px p < size p"
  shows "p ! (get_index_upd px p) = px"
by (metis assms get_index_upd.elims index_correct)


lemma get_index_upd_diff_elements:
  fixes 
  p1::"'a" and p2::"'a" and p::"'a list"
assumes "p1 \<in> set p"
  assumes "p1 \<noteq> p2" 
  assumes "p \<noteq> []"
  shows "get_index_upd p1 p \<noteq> get_index_upd p2 p"
proof (rule ccontr)
  assume "\<not> (get_index_upd p1 p \<noteq> get_index_upd p2 p)"
  then have "get_index_upd p1 p = get_index_upd p2 p" by simp
  from this obtain n1 n2 where "get_index_upd p1 p = n1" and "get_index_upd p2 p = n2" by blast
  hence "n1 = n2"
    by (meson \<open>\<not> get_index_upd p1 p \<noteq> get_index_upd p2 p\<close>)
  hence "p ! n1 = p1" 
    using assms get_index_upd_correct \<open>get_index_upd p1 p = n1\<close> by fastforce
  hence "p ! n2 = p2" 
    using assms get_index_upd_correct \<open>get_index_upd p2 p = n2\<close>
  using \<open>get_index_upd p1 p = get_index_upd p2 p\<close> by force
  hence "p1 = p2" 
    using assms \<open>\<not> get_index_upd p1 p \<noteq> get_index_upd p2 p\<close>
          \<open>n1 = n2\<close> \<open>p ! n1 = p1\<close> by blast
  with assms show False by simp
qed

fun get_votes :: "'b \<Rightarrow> 'b Parties \<Rightarrow> nat list \<Rightarrow> nat" where
"get_votes party parties votes = votes ! (get_index_upd party parties)"

(* function to generate the list of parameters *)
fun generate_list :: "bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "generate_list True n = [1..<n]" |
  "generate_list False n = filter (\<lambda>x. x mod 2 = 1) [1..<n]"

text \<open> This function counts votes for one party and add returns the number of votes \<close>

fun cnt_votes :: "'a \<Rightarrow> 'a Profile \<Rightarrow> nat \<Rightarrow> nat" where
  "cnt_votes p [] n = n" |
  "cnt_votes p (px # profil) n = 
     (case (count_above px p) of
        0 \<Rightarrow> cnt_votes p profil (n + 1)
      | _ \<Rightarrow> cnt_votes p profil n)"


value "cnt_votes ''partyA'' [{(''partyA'', ''partyB'')}] 0"

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

lemma working. implement this with assumptions on later lemmas

lemma update_at_index_nat_lemma:
  fixes
  xs::"nat list" and
  i::"nat" and
  n::"nat"
assumes "i < length xs"
assumes "xs \<noteq> []"
  shows "(update_at_index_nat xs i n) ! i = n"
proof - 
  have "update_at_index_nat xs i n = list_update xs i n" using assms
    by (metis update_at_index_nat.elims)
  then have "update_at_index_nat xs i n ! i = list_update xs i n ! i" by simp
  then have "... = n" using nth_list_update_eq assms by simp
  then show ?thesis
  by (simp add: \<open>update_at_index_nat xs i n = xs[i := n]\<close>)
qed
*)
(* usa list update mannaggia alla madonna *)

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
"profile_list = [pref_rel_a, pref_rel_b, pref_rel_c, pref_rel_b, 
                 pref_rel_b, pref_rel_d, pref_rel_a]"

(* update_at_index added here bring error in full_module *)
fun calc_votes :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a Profile \<Rightarrow> nat list \<Rightarrow> nat list" where
  "calc_votes [] ps prof votes = votes" |
  "calc_votes (party # parties) ps prof votes = 
      (let n = cnt_votes party prof 0;
       i = get_index_upd party ps in
      calc_votes parties ps prof (list_update votes i (n::nat)))"

lemma simp_votes:
  fixes
    parties:: "'b Parties" and
    fparties::"'b Parties" and
    party::"'b" and
    profile:: "'b Profile" and
    votes::"nat list"
  assumes "party \<in> set parties"
  assumes "parties = fparties"
  assumes "votes ! get_index_upd party fparties = cnt_votes party profile 0"
  shows "calc_votes parties fparties profile votes ! get_index_upd party fparties =
         cnt_votes party profile 0" 
  by sorry

lemma votes_perm:
  fixes
    parties:: "'b Parties" and
    parties':: "'b Parties" and
    profile:: "'b Profile"
  assumes "mset parties = mset parties'"
  assumes "party \<in> set parties"
  assumes "get_index_upd party parties < size parties"
  shows "(calc_votes parties parties profile []) !
                                            get_index_upd party parties
 = calc_votes parties' parties' profile [] ! get_index_upd party parties'"
  by sorry 

(* this works 09/03/24 *)
value "(calc_votes [''a'', ''b''] [''a'', ''b''] profile_list [0, 0])! (get_index_upd ''a'' [''a'', ''b''])"
value "(calc_votes [''b'', ''a''] [''a'', ''b''] profile_list [0, 0])! (get_index_upd ''a'' [''b'', ''a''])"

(*prove "p1 <~~> p2 \<Longrightarrow> (calc_votes p1 profl votes = calc_votes p2 profl votes)"
*)

(*
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
             calc_votes p1 (a # p1) profl  (votes @ [cnt_votes a profl 0])" using assms by simp
  also have "\<dots> = 
             calc_votes p2' (a # p2') profl  (votes @ [cnt_votes a profl 0])" using assms
  by (metis Cons.IH Cons.prems \<open>mset p2 = mset (a # p2')\<close> calc_votes.simps(2) cons_perm_imp_perm list.exhaust mset_zero_iff_right)
  then have "... = calc_votes (a # p2') profl votes" using assms by simp
  then have "... = calc_votes p2 profl votes" by simp
  then show ?case by simp
qed
*)

text \<open> This function receives in input the function Votes and the list of parties. The 
       output is the list of parties with the maximum number of votes.  \<close>

(* adapted to list. works 09/03 
fun max_val:: "rat list \<Rightarrow> rat \<Rightarrow> rat" where 
"max_val [] m = m" | 
"max_val (px # p) m = max_val p (if px > m then px else m)"

fun max_val_2::"rat set \<Rightarrow> rat" where
"max_val_2 lisc = Max lisc"

value "max_val_2 {4, 3, 6, 2}"

lemma max_val_2_lemma:
  fixes fvv::"rat list" and fv1::"rat"
  assumes "fv1 \<in> set fvv"
  shows "Max (set fvv) \<ge> fv1"
  by (simp add: assms)
*)
fun max_val_wrap:: "rat list \<Rightarrow> rat" where 
"max_val_wrap v = Max (set v)"

lemma max_val_wrap_lemma:
  fixes fvv::"rat list" and fv1::"rat"
  assumes "fv1 = fvv ! i1" and "i1 < length fvv"
  shows "max_val_wrap fvv \<ge> fv1"
  by (simp add: assms)

fun func1:: "char list list \<Rightarrow> char list list \<Rightarrow> char list list" where
"func1 [] w = w" | 
"func1 (px # p) w = 
        func1 p (if px = ''y'' then (w @ [px])
                                   else w)"

lemma lemma1:
  assumes "px \<notin> set sw" and "px \<noteq> ''y''"
  shows "px \<notin> set (func1 ps sw)"
  using assms by (induction ps sw rule: func1.induct) auto

fun max_p:: "rat \<Rightarrow> rat list \<Rightarrow> 'b Parties
                     \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
"max_p m v ps w = w @ filter (\<lambda>x. v ! (get_index_upd x ps) = m) ps" 

lemma max_p_hd_is_in_set:
  shows "hd (max_p m v p []) \<in> set p"
  by sledgehammer

(* forse questo lemma prova che se il partito non ha il massimo dei voti allora non finisce
   nella lista dei vincitori *)
lemma max_parties_not_winner_not_in_winners:
  assumes "px \<notin> set sw"
  assumes "m > 0"
  assumes "v ! (get_index_upd px ps) \<noteq> m"
  shows "px \<notin> set (max_p m v ps sw)"
  using assms by (induction ps sw rule: max_p.induct) auto

lemma max_parties_no_in:
  assumes "px \<notin> set sw"
  assumes "m > 0"
  assumes "v ! (get_index_upd px ps) = 0"
  shows "px \<notin> set (max_p m v ps sw)"
  using assms by (induction ps sw rule: max_p.induct) auto


fun get_winners :: "rat list \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
  "get_winners v p = 
    (let m = max_val_wrap v in max_p m v p [])"

lemma get_winners_hd_is_in_set:
  shows "hd (get_winners v p) \<in> set p"
  by sorry

lemma get_winners_not_winner_not_in_winners:
  fixes fv::"rat list" and m::"rat"
  defines "m \<equiv> max_val_wrap fv"
  assumes "fv ! (get_index_upd px ps) \<noteq> m"
  assumes "get_winners fv ps \<noteq> []"
  shows "px \<noteq> hd (get_winners fv ps)"
proof - 
  have "get_winners fv ps = (let m = max_val_wrap fv in max_p m fv ps [])" 
    using get_winners.simps by blast
  then have "px \<notin> set (max_p m fv ps [])" 
    using assms by simp
  then show ?thesis 
    using m_def hd_in_set assms 
          \<open>get_winners fv ps = (let m = max_val_wrap fv in max_p m fv ps [])\<close> by metis
qed

(* lemma from max parties 0 votes \<Rightarrow> not in winners *)
lemma get_winners_not_in:
fixes 
  v::"rat list" and
  p::"'b Parties" and
  px::"'b" and
  m::"rat"
assumes "m > 0"
assumes "v ! (get_index_upd px p) = 0"
shows "px \<notin> set (get_winners v p)"
  sorry

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


lemma max_parties_concordant:
  assumes "fp = p"
  assumes "ns1 = ns2"
  assumes "votes1 = cnt_votes fp prof 0 / ns1"
  assumes "votes2 = cnt_votes fp prof 0 / ns2"
  assumes "votes1 > votes2"
  assumes "(v ! (get_index_upd party1 fp)) = votes1"
  assumes "(v ! (get_index_upd party2 fp)) = votes2"
  shows "party1 \<in> set output \<longrightarrow> party2 \<in> set output"
  by (metis (full_types) assms(5) diff_gt_0_iff_gt get_index_upd.simps(1) max_p.simps(1) max_parties_no_in nth_Cons_0)

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


end