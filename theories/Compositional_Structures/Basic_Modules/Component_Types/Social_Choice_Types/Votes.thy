theory Votes
  imports Complex_Main
HOL.List
Preference_Relation
Profile
Result

begin

(* \<equiv> *)
type_synonym 'b Parties = "'b list"
type_synonym 'b Votes = "'b \<Rightarrow> rat"
                
(* Seats function with each seat numbered assigned to a party or list of parties. *)
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

(* this adds a new correspondence between 'a and nat in already existing 
Votes. It is used inside "count_votes_for_election" to update Votes. *)
fun add_new_vote :: "'b => rat => 'b Votes => 'b Votes" where
  "add_new_vote party cnt votes = (votes(party := cnt))"

(* this function counts votes for one party and add correspondence to Votes. *)
fun count_votes_for_party :: "'b \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes 
                                      \<Rightarrow> 'b Votes" where
  "count_votes_for_party party profile_list votes =
  (let n_votes = foldr (\<lambda>pref acc. if count_above pref party = 1 
                                      then acc+1 
                                  else acc) profile_list 0
   in add_new_vote party n_votes votes)"

fun empty_struct_votes :: "('b \<Rightarrow> rat)" where
  "empty_struct_votes b = 0"

(* this calculate votes and returns "Votes" *)
fun calculate_votes_for_election :: "'b Parties \<Rightarrow> 'b Profile \<Rightarrow> 'b Votes" where
  "calculate_votes_for_election parties_list profile_list =
      (let votes = empty_struct_votes in (if parties_list = [] then empty_struct_votes else
      (foldr (\<lambda>party acc_votes. 
              count_votes_for_party party profile_list acc_votes) 
              parties_list votes)))"

(* Step 1: function to find maximum in "Votes" and returns both winner and votes *)
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

(* Step 2: assign one seat to winner party of step above *)
fun assign_seat :: "'a::linorder \<Rightarrow> 'b  \<Rightarrow> ('a::linorder, 'b) Seats 
                    \<Rightarrow> ('a::linorder, 'b) Seats" where
  "assign_seat seat_n winner seats = (\<lambda>n. if n = seat_n then {winner} else seats n)"

(* Step 3: Define a function count_seats *)
(* function to count the seats of a given party (the winner). *)
fun count_seats :: "'b set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "count_seats party seats indexes = 
    (card {i. i \<in> indexes \<and> seats i = party})"

(* Step 4: Update Fract-Votes which is a StructVotes type. 
In this function I have the winner party of this round ('a), the seats at the moment
('a Seats), the normal votes function (the first 'a StructVotes), the fract_votes (the 
second 'a StructVotes) and the parameters (params).
*)

fun update_votes :: "'b \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                            'a::linorder set \<Rightarrow> 'b Votes \<Rightarrow> 
                            'b Votes \<Rightarrow> nat list \<Rightarrow> 'b Votes" where 
"update_votes party seats indexes votes fract_votes params = 
     (let
       ns = count_seats {party} seats indexes;
       p = List.nth params ns;
       v = votes party
     in
       fract_votes(party := v / rat_of_nat p))"




end
