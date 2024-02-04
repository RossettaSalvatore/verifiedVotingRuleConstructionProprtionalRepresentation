


section \<open>Votes\<close>

theory Votes
  imports Complex_Main
HOL.List
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

(* returns set of elements above "'a" *)
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
  "count_above r a = card (above r a) + 1"

text \<open> This function adds a new correspondence in function Votes between
       'a and nat in already existing Votes \<close>
fun add_new_vote :: "'b => rat => 'b Votes => 'b Votes" where
  "add_new_vote party cnt votes = (votes(party := cnt))"

text \<open> this function counts votes for one party and add correspondence to Votes function \<close>
fun count_votes_for_party :: "'b \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes 
                                      \<Rightarrow> 'b Votes" where
  "count_votes_for_party party profile_list votes =
  (let n_votes = foldr (\<lambda>pref acc. if count_above pref party = 1 
                                      then acc+1 
                                  else acc) profile_list 0
   in add_new_vote party n_votes votes)"

fun empty_struct_votes :: "('b \<Rightarrow> rat)" where
  "empty_struct_votes b = 0"

text \<open> This function receives in input the list of parties and the list of preferation 
       relations. The output is the function Votes, in which every party has the 
       correspondent number of votes.  \<close>
fun calculate_votes_for_election :: "'b list \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes" where
  "calculate_votes_for_election parties prof =
      (let votes = empty_struct_votes in (if parties = [] then empty_struct_votes else
      (foldr (\<lambda>party acc_votes. 
              count_votes_for_party party prof acc_votes) 
              parties votes)))"

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
