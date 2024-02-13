


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

text \<open> This function counts votes for one party and add correspondence to Votes function \<close>
fun cnt_votes :: "'b \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes \<Rightarrow> rat \<Rightarrow> 'b Votes" where
  "cnt_votes party [] votes n = votes(party:= n)" |
  "cnt_votes party (px # profilee) votes n = 
     (case card (above px party) of
        0 \<Rightarrow> cnt_votes party profilee votes (n + 1)
      | _ \<Rightarrow> cnt_votes party profilee votes n)"

fun empty_v :: "('b \<Rightarrow> rat)" where
  "empty_v b = 0"

text \<open> This function receives in input the list of parties and the list of preferation 
       relations. The output is the function Votes, in which every party has the 
       correspondent number of votes.  \<close>

fun calc_votes :: "'b list \<Rightarrow> 'b Profile \<Rightarrow>'b Votes \<Rightarrow> 'b Votes" where
  "calc_votes [] prof votes = votes" |
  "calc_votes (party # parties) prof votes = 
      calc_votes parties prof (cnt_votes party prof empty_v 0)"


lemma calc_votes_permutation:
  fixes
    p1 :: "'b Parties" and
    p2 ::"'b Parties" and
    profl ::"'b Profile" and
    votes::"'b Votes"
  assumes "p1 <~~> p2"
  shows "calc_votes p1 profl votes = calc_votes p2 profl votes"
  using assms
proof (induction p1 arbitrary: p2)
  case Nil
  then show ?case by simp
next
  case (Cons a p1)
  have "calc_votes (a # p1) profl votes = 
             calc_votes p1 profl (cnt_votes a profl empty_v 0)" using assms by simp
  then have "calc_votes (a # p2) profl votes = 
             calc_votes p2 profl (cnt_votes a profl empty_v 0)" using assms by simp
  then obtain v' where "v' = (cnt_votes a profl empty_v 0)" using assms by simp
  then have "calc_votes p1 profl v' = 
             calc_votes p2 profl v'" using assms by simp
  then have "calc_votes (a # p1) profl votes =
             calc_votes (a # p2) profl votes" by simp
  then show ?case by simp
qed
  case True
  with assms show ?thesis by (simp add: perm_empty_imp)
next
  case False
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
    using step by simp
  also have "... = calculate_votes p2 profile votes"
    using \<open>p2 <~~> x # p2'\<close> by simp
  finally show ?thesis .
qed

text \<open> This function receives in input the function Votes and the list of parties. The 
       output is the list of parties with the maximum number of votes.  \<close>

fun max_val:: "'b Votes \<Rightarrow> 'b list \<Rightarrow> rat \<Rightarrow> rat" where 
"max_val v [] m = m" | 
"max_val v (px # p) m = max_val v p (if v px > m then (v px) else m)"

fun max_parties::"rat \<Rightarrow> 'b Votes \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
"max_parties m v [] mvp = mvp" | 
"max_parties m v (px # p) mvp = max_parties m v p (if (v px) = m then (mvp @ [px]) else mvp)"

lemma max_parties_not_empty:
  fixes
  m::"rat" and
  mvp::"'b Parties" and
  v::"'b Votes" and
  p::"'b Parties"
  assumes "p \<noteq> []"
  shows "max_parties m v p mvp \<noteq> []"
  using assms
  sorry

fun find_max_votes :: "'b Votes \<Rightarrow> 'b Parties \<Rightarrow> 'b list" where
  "find_max_votes v p = max_parties (max_val v p 0) v p []"

lemma find_max_votes_not_empty:
  fixes
  v::"'b Votes" and
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

fun update_votes :: "'b \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                            'a::linorder set \<Rightarrow> 'b Votes \<Rightarrow> 
                            'b Votes \<Rightarrow> rat list \<Rightarrow> 'b Votes" where 
"update_votes party seats i votes fractv factors = 
     fractv(party := votes party / (List.nth factors (count_seats {party} seats i)))"

end
