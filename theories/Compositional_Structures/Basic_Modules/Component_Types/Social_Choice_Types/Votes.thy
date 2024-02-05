


section \<open>Votes\<close>

theory Votes
  imports Complex_Main
HOL.List
"HOL-Combinatorics.Multiset_Permutations"
"HOL-Combinatorics.List_Permutation"
Preference_Relation
Profile
Result

begin

(* \<equiv> *)

subsection  \<open>Definition\<close>
text  \<open>Parties is the list of parties, that can be of any type. 
       Votes is a function used to assign a rational number (indeed, the votes) to each party. \<close>

type_synonym 'b Parties = "'b list"
type_synonym 'b Votes = "'b \<Rightarrow> rat"
                
text  \<open>Every seat is unique and identified and has a set of parties to which it is assigned.\<close>
type_synonym ('a, 'b) Seats = "'a \<Rightarrow> 'b set"
type_synonym Params = "nat list"

(* function to generate the list of parameters *)
fun generate_list :: "bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "generate_list True n = [1..<n]" |
  "generate_list False n = filter (\<lambda>x. x mod 2 = 1) [1..<n]"

(* returns set of elements above "'a" 
definition above_set :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "above_set r a \<equiv> above (set r) a"

lemmas [code] = above_set_def[symmetric]
lemma [code]:
  \<open>above_set [] a = {}\<close>
  \<open>above_set ((x,y)#xs) a = (if x=a then {y} else {}) \<union> above_set xs a\<close>
  by (auto simp: above_set_def above_def)
*)

text \<open> this function counts votes for one party and add correspondence to Votes function \<close>
fun count_votes :: "'b \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes \<Rightarrow> rat
                                      \<Rightarrow> 'b Votes" where
  "count_votes party [] votes n = votes(party:= n)" |
  "count_votes party (px # p) votes n =
   count_votes party p votes (if card (above px party) = 0 
                                      then n+1 
                                  else n)"

fun empty_votes :: "('b \<Rightarrow> rat)" where
  "empty_votes b = 0"

text \<open> This function receives in input the list of parties and the list of preferation 
       relations. The output is the function Votes, in which every party has the 
       correspondent number of votes.  \<close>

fun calculate_votes :: "'b list \<Rightarrow> 'b Profile \<Rightarrow>'b Votes \<Rightarrow> 'b Votes" where
  "calculate_votes [] profile_list votes = votes" |
  "calculate_votes (px # p) profile_list votes = 
      calculate_votes p profile_list (count_votes px profile_list empty_votes 0)"

lemma calculate_votes_permutation:
  fixes
    p1 :: "'b Parties" and
    p2 ::"'b Parties" and
    profile ::"'b Profile" and
    votes::"'b Votes"
  assumes "p1 <~~> p2"
  shows "calculate_votes p1 profile votes = calculate_votes p2 profile votes"
proof (cases)
  assume "p1 = []"
  then have "p2 = []" using perm_empty_imp
  using assms by auto
  then show ?thesis using assms by simp
next
  assume "p1 \<noteq> []"
  then obtain x p1' where "p1 = x # p1'"
    by (meson list.exhaust)
  then obtain p2' where "p2 <~~> x # p2'"
    using assms by metis
  then have "p2' <~~> p1'"
  using \<open>p1 = x # p1'\<close> assms by auto
  then have "calculate_votes p1 profile votes = calculate_votes (x # p1') profile votes"
    using assms
  by (simp add: \<open>p1 = x # p1'\<close>)
  also have "... = calculate_votes p1' profile (count_votes x profile empty_votes 0)"
    by simp
  also have "... = calculate_votes p2' profile (count_votes x profile empty_votes 0)"
    using assms by simp
  also have "... = calculate_votes p2 profile votes"
    using \<open>p2 <~~> x # p2'\<close> by simp
  finally show ?thesis .
qed

lemma calculate_votes_permutation_invariant:
  assumes "mset p1 = mset p2"
  shows "calculate_votes p1 profil votes = calculate_votes p2 profil votes"
proof (induct p1 arbitrary: p2 votes)
  case Nil
  then show ?case by (simp add: assms)
next
  case (Cons px p1')
  then obtain p2' where "p2 = px # p2'" "mset p1' = mset p2'"
    using assms by (metis mset_eq_setD perm_Cons perm_set_eq set_mset_mset)
  then show ?case
    by (simp add: Cons.hyps)
qed
text \<open> This function receives in input the function Votes and the list of parties. The 
       output is the list of parties with the maximum number of votes.  \<close>

fun find_max_votes :: "'b Votes \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "find_max_votes votes parties =
    (if parties = [] then parties
     else let max_votes = foldr (\<lambda>party acc. max acc (votes party)) parties 0;
              mylist = filter (\<lambda>party. votes party = max_votes) parties
          in if mylist = [] then parties else mylist)"

lemma find_max_votes_not_empty:
  assumes "parties \<noteq> []"
  shows "filter (\<lambda>party. votes party = foldr (\<lambda>party acc. max acc (votes party)) parties 0) parties \<noteq> []"
  using assms
  sorry

fun assign_seat :: "'a::linorder \<Rightarrow> 'b  \<Rightarrow> ('a::linorder, 'b) Seats 
                    \<Rightarrow> ('a::linorder, 'b) Seats" where
  "assign_seat seat_n winner seats = (\<lambda>n. if n = seat_n then {winner} else seats n)"

text \<open> This function counts seats of a given party. \<close>

fun count_seats :: "'b set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "count_seats party seats indexes = 
    (card {i. i \<in> indexes \<and> seats i = party})"

text \<open> This function updates the "fractional votes" of the winning party, dividing the starting
       votes by the i-th parameter, where i is the number of seats won by the party. \<close>

fun update_votes :: "'b \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                            'a::linorder set \<Rightarrow> 'b Votes \<Rightarrow> 
                            'b Votes \<Rightarrow> nat list \<Rightarrow> 'b Votes" where 
"update_votes party seats indexes votes fract_votes p = 
     (let
       ns = count_seats {party} seats indexes;
       px = List.nth p ns;
       v = votes party
     in
       fract_votes(party := v / rat_of_nat px))"

end
