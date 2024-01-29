theory Divisor_Module
  imports Complex_Main
HOL.List

"Component_Types/Social_Choice_Types/Preference_Relation"
"Component_Types/Social_Choice_Types/Profile"
"Component_Types/Social_Choice_Types/Result"
"Component_Types/Social_Choice_Types/Votes"
"Component_Types/Termination_Condition"
"HOL-Combinatorics.Multiset_Permutations"
"Component_Types/Consensus_Class"
"Component_Types/Distance"
begin

type_synonym 'a Divisor_Term_Condition = "('a Parties \<Rightarrow> bool)"

(*
- set of seats assigned and to assign in form (assigned, {}, to_assign);
- fv, fract votes (Votes function);
- list of parties;
- list of indexes to iterate (maybe can be removed);
- seats (Seats function);
- number of seats to assign;
- votes, "starting" votes (Votes function);
- list of divisors ([1, 2, 3, ...] or [1, 3, 5, ...])
*)
record ('a::linorder, 'b) Divisor_Module =
  res :: "'a::linorder Result"
  p :: "'b Parties"
  i :: "'a::linorder set"
  s :: "('a::linorder, 'b) Seats"
  ns :: nat
  v :: "'b Votes"
  fv :: "'b Votes"
  d :: "nat list"

locale types = 
  fixes dmp :: "('a::linorder, 'b) Divisor_Module"
  and em :: "'a::linorder Electoral_Module"

fun divisor_module :: "_ \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where 
"divisor_module rec =
  (let 
    ni = Min (snd (snd (res rec)));
    a = (fst (res rec) \<union> {ni});
    dis =  snd (snd (res rec)) - {ni}
     in rec\<lparr> res := (a, {}, dis),
             p := tl (p rec),
             s := assign_seat ni (hd(p rec)) (s rec),
             fv := update_votes (hd(p rec)) (s rec) (i rec) (v rec) (fv rec) (d rec)
            \<rparr>)"

lemma divisor_module_length:
  assumes non_empty_parties: "p rec \<noteq> []"
  shows "length (p (divisor_module rec)) < length (p rec)"
  using assms by (simp add:Let_def)

function loop_divisor ::
    "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
  "(p rec = []) \<Longrightarrow> loop_divisor rec = rec" |
  "\<not>(p rec = []) \<Longrightarrow> loop_divisor rec = loop_divisor (divisor_module rec)" 
  by auto
termination by (relation "measure (\<lambda>rec. length (p rec))") (auto simp add: divisor_module_length Let_def)

fun defer_divisor :: "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"defer_divisor r = r"

fun create_seats :: "'a::linorder set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 'b set \<Rightarrow> ('a::linorder, 'b) Seats" where
  "create_seats def seats p_set=
    (\<lambda>x. if x \<in> def then p_set else seats x)"

(*
fun apply_divisor_module_list ::
  "'a::linorder Result \<times> 'b StructVotes \<times> ('a::linorder, 'b) Seats \<Rightarrow>
   'b list \<Rightarrow> 'a::linorder set \<Rightarrow>
   'b StructVotes \<Rightarrow> 'b StructVotes \<Rightarrow> nat list \<Rightarrow> 
   ('a::linorder Result \<times> 'b StructVotes \<times> ('a::linorder, 'b) Seats)" where
"apply_divisor_module_list input [] indexes votes fract_votes ps = input" |
"apply_divisor_module_list input (party # parties) indexes votes fract_votes ps = 
    (let res = fst (input);
     seats = snd(snd(input));
              (result, new_fractvotes, new_seats) = 
                  divisor_module res party indexes seats votes fract_votes ps
          in
        apply_divisor_module_list (result, new_fractvotes, new_seats) parties indexes votes new_fractvotes ps)"
*)

(* divisor module for tie breaking: assigns all remaining seats to all tied parties 
in another Seats function and returns  *)
fun tie_breaking :: 
"('a::linorder, 'b) Divisor_Module \<Rightarrow>  
 ('a::linorder, 'b) Divisor_Module" where 
"tie_breaking rec = 
  (let fs = create_seats (snd (snd (res rec))) (s rec) (set (p rec));
    new_rec = rec\<lparr> s := fs \<rparr>
in 
     rec)"

fun assigning_seats :: "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"assigning_seats rec = (
      if length (p rec) \<le> (ns rec) then
        loop_divisor rec\<lparr>ns := ns rec - length (p rec)\<rparr>
      else
        tie_breaking rec\<lparr>ns := 0\<rparr>)"

lemma nseats_decreasing:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes n_positive: "(ns rec) > 0"
  shows "ns (assigning_seats rec) < ns rec"
proof (cases "length (p rec) \<le> ns rec")
  case True
  then have "ns (assigning_seats rec) = ns rec - length (p rec)"
    by (auto simp add: Let_def)
  also have "... < ns rec" using True n_positive non_empty_parties
    by simp
  finally show ?thesis .
next
  case False
  then have "ns (assigning_seats rec) = 0"
    by (auto simp add: Let_def)
  also have "... < ns rec" using n_positive
    by simp
  finally show ?thesis .
qed

(*
main function is the whole method. After creating the starting structures, 
this function assigns the seats.
*)
fun main_function :: "('a::linorder, 'b) Divisor_Module \<Rightarrow>
   ('a::linorder, 'b) Divisor_Module" where
"main_function rec = 
      assigning_seats (rec\<lparr>p := ( find_max_votes (fv rec) (p rec))\<rparr>)"

lemma nseats_decreasing_main:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes n_positive: "ns rec > 0"
  shows "ns (assigning_seats rec) < ns rec"
proof (cases "length (p rec) \<le> ns rec")
  case True
  then have "ns (assigning_seats rec) = ns rec - length (p rec)"
    by (auto simp add: Let_def)
  also have "... < ns rec" using True n_positive non_empty_parties
    by simp
  finally show ?thesis .
next
  case False
  then have "ns (assigning_seats rec) = 0"
    by (auto simp add: Let_def)
  also have "... < ns rec" using n_positive
    by simp
  finally show ?thesis .
qed

lemma nseats_decreasing_main_function:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes n_positive: "ns rec > 0"
  shows "ns (main_function rec) < ns rec"
proof -
  have "main_function rec = assigning_seats (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)"
    by simp
  also have "ns ( assigning_seats (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)) < ns rec" using non_empty_parties n_positive
    by (simp add: Let_def)
  finally show ?thesis
    using assms nseats_decreasing_main nseats_decreasing by auto
qed

function loop_divisor_outer ::
  "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where  
  "ns r = 0 \<Longrightarrow> loop_divisor_outer r = r" |
  "ns r > 0 \<Longrightarrow> loop_divisor_outer r = loop_divisor_outer (main_function r)"
  by auto

termination
proof (relation "measure (\<lambda>rec. ns rec)", goal_cases)
  case (1)
  then show ?case by simp
next
  case (2 rec)
  assume "p rec \<noteq> []"
  then have "ns (main_function rec) < ns (rec)" 
    using nseats_decreasing_main_function by simp
  then show ?case by simp
qed

fun seats_assigned :: "char list Termination_Condition" where 
  "seats_assigned result = (
    case result of 
      (f, _, _) \<Rightarrow> f = {} 
  )"

fun t_inner :: "'b Termination_Condition" where 
  "t_inner result = (
    case result of 
      (lp, _, _) \<Rightarrow> lp = {} 
  )"
fun create_empty_seats :: "'a::linorder set \<Rightarrow> 'b Parties \<Rightarrow> ('a::linorder, 'b) Seats" where
  "create_empty_seats indexes parties =
    (\<lambda>i. if i \<in> indexes then set parties else {})"

(* Returns two elements: (Result, Seats)
Result contains the assigned and disputed Seats
Seats is a function assigning every seat to a party or a list of parties *)
type_synonym ('a, 'b) full_module_params = "'b Parties \<Rightarrow> 'b Profile \<Rightarrow> 'a set \<Rightarrow> Params \<Rightarrow> (('a Result) \<times> ('a, 'b) Seats)"
fun full_module:: "('a::linorder, 'b::linorder) full_module_params" where
"full_module parties profile_l indexes params = (
    let votes = calculate_votes_for_election parties profile_l;
    n = card indexes;
    empty_seats = create_empty_seats indexes parties;
    outcome = main_function (({}, {}, indexes), votes, empty_seats) parties n indexes votes params 
    in outcome)"

(* to prove *)
theorem full_module_anonymity:
  assumes "finite indexes"
  shows "\<forall>profile_l parties1 parties2 indexes params.
           set parties1 = set parties2 \<longrightarrow>
           full_module parties1 profile_l indexes params =
           full_module parties2 profile_l indexes params"
  sorry

definition example_multiset :: "nat multiset" where
  "example_multiset = {#1, 2, 3#}"
(* Example usage *)
value "permutations_of_multiset example_multiset"


(* Define a set *)
definition my_set :: "nat set" where
  "my_set = {1, 2, 3, 4, 5}"

(*
fun profile_permutations :: "nat \<Rightarrow> 'a set \<Rightarrow> ('a Profile) set" where
  "profile_permutations n A =
    (if permutations_of_set A = {}
      then {} else listset (replicate n (pl_\<alpha> ` permutations_of_set A)))"

value "profile_permutations "
*)

(* works *)
fun list_to_multiset :: "'a list \<Rightarrow> 'a multiset" where
  "list_to_multiset [] = {#}" |
  "list_to_multiset (x # xs) = {#x#} + list_to_multiset xs"

(* with this function i get all permutations *)
fun get_perms :: "'a list \<Rightarrow> 'a list set" where
  "get_perms list = permutations_of_multiset (list_to_multiset list)"

value "get_perms [''a'', ''b'', ''c'']"

(*
function take_one_element :: "'a set \<Rightarrow> 'a option" where
"take_one_element my_et = (if my_et = {} then None else Some (SOME x. x \<in> my_et))"
value "take_one_element {''a'',''bb'', ''c''}"
*)

(* to check *)
theorem find_max_votes_anonymous:
  "\<forall>votes1 votes2 parties.
    (\<forall>party. party \<in> set parties \<longrightarrow> votes1 party = votes2 party) \<longrightarrow>
    find_max_votes votes1 parties = find_max_votes votes2 parties"

(*
subsubsection \<open>Anonymity\<close>

definition anonymity :: "'a Electoral_Module \<Rightarrow> bool" where
  "anonymity m \<equiv>
    electoral_module m \<and>
      (\<forall> A p q. profile A p \<and> profile A q \<and> p <~~> q \<longrightarrow> m A p = m A q)"
*)

(*definition anonymity :: "'a multiset \<Rightarrow> 'a multiset \<Rightarrow> bool" where
  "anonymity f \<equiv> \<forall>V1 V2. V2 \<in> permutations_of_multiset V1 \<longrightarrow> f V1 = f V2"
*)

(* example values *)
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

definition profile_list :: "char list Profile" where
"profile_list = [pref_rel_a, pref_rel_b, pref_rel_c, pref_rel_b2, 
                 pref_rel_b3, pref_rel_d, pref_rel_a2]"

definition parties_list :: "char list list" where
"parties_list = [''a'', ''b'', ''c'', ''d'']"

definition parties_list_perm :: "char list list" where
"parties_list_perm = [''b'', ''d'', ''c'', ''a'']"

definition parameters_list :: "nat list" where
"parameters_list = [1, 2, 3]"

definition seats_set :: "nat set" where
"seats_set = {1, 2, 3}"

(* full_module *)
value "full_module parties_list profile_list seats_set parameters_list"

(* Result *)
value "fst(full_module parties_list profile_list seats_set parameters_list)"

(* Seats *)
value "snd(full_module parties_list profile_list seats_set parameters_list)"

(* full_module permuted *)
value "full_module parties_list_perm profile_list seats_set parameters_list"
value "snd(full_module parties_list_perm profile_list seats_set parameters_list)"

end
