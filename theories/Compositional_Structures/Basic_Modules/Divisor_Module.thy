

section \<open> Divisor Module \<close>

theory Divisor_Module
  imports Complex_Main
Main
"Component_Types/Social_Choice_Types/Preference_Relation"
"Component_Types/Social_Choice_Types/Profile"
"Component_Types/Social_Choice_Types/Result"
"Component_Types/Electoral_Module"
"Component_Types/Social_Choice_Types/Votes"
"Component_Types/Termination_Condition"
"HOL-Combinatorics.Multiset_Permutations"
"Component_Types/Consensus_Class"
"Component_Types/Distance"

begin

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

text \<open> This record contains the list of parameters used in the whole divisor module.  \<close>
record ('a::linorder, 'b) Divisor_Module =
  res :: "'a::linorder Result"
  p :: "'b Parties"
  i :: "'a::linorder set"
  s :: "('a::linorder, 'b) Seats"
  ns :: nat
  v :: "rat list"
  fv :: "rat list"
  d :: "rat list"

locale typesl = 
  fixes dm :: "('a::linorder, 'b) Divisor_Module"
  and em :: "'a::linorder Electoral_Module"

locale l2 = 
  typesl + fixes n :: nat

abbreviation ass_r :: "'a Result \<Rightarrow> 'a set" where
  "ass_r r \<equiv> fst r"

abbreviation disp_r :: "'a Result \<Rightarrow> 'a set" where
  "disp_r r \<equiv> snd (snd r)"

subsection \<open> Definition \<close>

text \<open> This function moves one seat from the disputed set to the assigned set. Moreover,
       returns the record with updated Seats function and "fractional" Votes entry 
       for the winning party. \<close>

fun divisor_module :: "('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       ('a::linorder, 'b) Divisor_Module" where 
"divisor_module rec =
  (let 
    seat = Min (ass_r (res rec));
    new_as = ass_r (res rec) \<union> {seat};
    new_di =  disp_r (res rec) - {seat}
     in rec\<lparr> res := (new_as, {}, new_di),
             p := tl (p rec),
             s := assign_seat seat (hd(p rec)) (s rec),
             fv := update_votes (hd(p rec)) (p rec) (s rec) (i rec) (v rec) (fv rec) (d rec)
            \<rparr>)"

lemma divisor_module_not_changing:
  shows "ns rec = ns (divisor_module rec)"

(* try if divisor module works *)
(* Example instantiation of the Divisor_Module record 
definition example_divisor_module :: "(nat, string) Divisor_Module" where
  "example_divisor_module \<equiv> 
    \<lparr> res = undefined, 
      p = [''PartyA'', ''PartyB''],
      i = {1, 2, 3},
      s = empty_seats,
      ns = 5,
      v = [1/2, 3/4, 2/5],
      fv = [4/5, 3/5, 1/4],
      d = [5/6, 1/3, 2/7] \<rparr>"
*)
lemma divisor_module_length:
  assumes non_empty_parties: "p rec \<noteq> []"
  shows "length (p (divisor_module rec)) < length (p rec)"
  using assms by (simp add:Let_def)


fun defer_divisor :: "('a::linorder, 'b) Divisor_Module 
                      \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"defer_divisor r = r"
(*
text \<open> This function takes the list of winning parties and assigns a seat to each of team.
       The output is the record updated.  \<close>
function loop_divisor ::
    "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
  "ns rec = 0 \<Longrightarrow> loop_divisor rec = rec" |
  "\<not>(ns rec = 0) \<Longrightarrow> loop_divisor rec = loop_divisor (divisor_module rec)" 
  by auto
termination by (relation "measure (\<lambda>rec. ns rec)")
               (auto simp add: divisor_module_length Let_def)
*)
fun create_seats :: "'a::linorder set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 'b set \<Rightarrow>
                      ('a::linorder, 'b) Seats" where
  "create_seats def seats p_set=
    (\<lambda>x. if x \<in> def then p_set else seats x)"

text \<open>This function checks whether there are enough seats for all the winning parties.
      - If yes, assign one seat to each party.
      - If not, assign all remaining seats to the winning parties, making these seats 
        "disputed".\<close>
(*
fun assigning_seats :: "('a::linorder, 'b) Divisor_Module
                        \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"assigning_seats rec = (
      if length (p rec) \<le> (ns rec) then
        loop_divisor rec\<lparr>ns := ns rec - length (p rec)\<rparr>
      else
         rec\<lparr> s := create_seats (disp_r (res rec)) (s rec) (set (p rec)), ns := 0 \<rparr>)"
*)
fun assigning_seats :: "('a::linorder, 'b) Divisor_Module
                        \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"assigning_seats rec = (
      let winners = find_max_votes (fv rec) (p rec) in
      if length winners \<le> (ns rec) then
         (divisor_module rec)\<lparr>ns := ns rec - 1\<rparr>
      else
         rec\<lparr> s := create_seats (disp_r (res rec)) (s rec) (set (p rec)), ns := 0 \<rparr>)"

(* questo lemma funziona mannaggia tutto finalmente godo *)
lemma nseats_decreasing:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes n_positive: "(ns rec) > 0"
  shows "ns (assigning_seats rec) < ns rec"
proof (cases "length (find_max_votes (fv rec) (p rec)) \<le> ns rec")
  case True
  then have "ns (assigning_seats rec) = ns rec - 1"
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

text \<open>This function finds the parties with the tied-maximum number of "fractional" votes 
      and assigns to each of them a seat, if possible. \<close>
(*fun main_function :: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Parties \<Rightarrow>
   ('a::linorder, 'b) Divisor_Module" where
"main_function rec lp = 
      (let winners = find_max_votes (fv rec) lp in 
      assigning_seats rec\<lparr>p := winners\<rparr>)"

lemma lemma_3:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes non_empty_parties_f: "find_max_votes (fv rec) lp \<noteq> []"
  assumes n_positive: "ns rec > 0"
  shows "ns (assigning_seats (rec\<lparr>p := find_max_votes (fv rec) lp\<rparr>))
         < ns (rec\<lparr>p := find_max_votes (fv rec) lp\<rparr>)"
proof - 
  have "ns (assigning_seats (rec\<lparr>p := find_max_votes (fv rec) lp\<rparr>)) =
             ns (rec\<lparr>p := find_max_votes (fv rec) lp\<rparr>) -
                   length (p (rec\<lparr>p := find_max_votes (fv rec) lp\<rparr>))" using assms by simp
  also have "... <  ns (rec\<lparr>p := find_max_votes (fv rec) lp\<rparr>)" using assms by simp
  finally show ?thesis by simp

(* to adapt *)
lemma nseats_decreasing_main_function:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes n_positive: "ns rec > 0"
  shows "ns (main_function rec) < ns rec"
proof -
  have "main_function rec = assigning_seats (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)"
    by simp
  also have "ns(main_function rec) = ns (assigning_seats (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>))"
    by simp
  also have "ns (assigning_seats rec) < ns rec"
    using nseats_decreasing n_positive non_empty_parties by blast
  also have "ns rec = ns (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)"
    by simp
  also have "ns ( assigning_seats (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)) < ns (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)"
    using nseats_decreasing_main n_positive non_empty_parties 
    by simp    
  also have "ns(main_function rec) < ns ((rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>))"
    by sledgehammer
  also have "ns ( assigning_seats (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)) < ns (rec\<lparr>p := find_max_votes (fv rec) (p rec)\<rparr>)"
    using nseats_decreasing_main n_positive non_empty_parties find_max_votes_not_empty
    by simp
  finally show ?thesis
    using assms nseats_decreasing_main nseats_decreasing by auto
qed
  sorry
text \<open>This loop assigns all the seats until either there are no more seats available or
      there are not enough seats for all winning parties (tie). \<close>

(*  (let winners = find_max_votes (fv rec) lp in 
      assigning_seats rec\<lparr>p := winners\<rparr>)"
*)
*)

function loop_outer ::
  "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where  
  "ns r = 0  \<Longrightarrow>loop_outer r = defer_divisor r" |
  "ns r > 0 \<Longrightarrow> loop_outer r = loop_outer (assigning_seats r)"
  by auto
termination by (relation "measure (\<lambda>r. ns r)")
               (auto simp add:  divisor_module_length Let_def)

(* to adapt after adapting lemma used *)
termination
proof (relation "measure (\<lambda>r. ns r)", goal_cases)
  case (1)
  then show ?case by simp
next
  case (2 r)
  then have "loop_outer r = loop_outer (assigning_seats r\<lparr>p :=  find_max_votes (fv r) (p r)\<rparr>)" by simp
  then have "ns (assigning_seats r\<lparr>p :=  find_max_votes (fv r) (p r)\<rparr>) <  ns r\<lparr>p :=  find_max_votes (fv r) (p r)\<rparr>" by simp
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


(* full divisor module function *) 
fun full_module:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"full_module rec pl = (
    let sv = calc_votes (p rec) (p rec) pl [];
    empty_seats = create_empty_seats (i rec) (p rec)
    in loop_outer (rec\<lparr>
             s := empty_seats,
             fv := sv
            \<rparr>))"



(* Define a set *)
definition my_set :: "nat set" where
  "my_set = {1, 2, 3, 4, 5}"

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
fun empty_votes :: "('b \<Rightarrow> rat)" where
  "empty_votes b = 0"

fun empty_seats :: "('a::linorder \<Rightarrow> 'b list)" where
  "empty_seats b = []"

theorem votes_anonymous:
  "\<forall>p2 p1 profile.
    mset p1 = mset p2 \<longrightarrow>
    calculate_votes_for_election p1 profile = 
    calculate_votes_for_election p2 profile"
  sorry
(*proof (intro allI impI)
  fix p2 p1 profile
  assume "mset p1 = mset p2"
  then show "calculate_votes p1 profile = calculate_votes p2 profile"
  proof -
    have "calculate_votes p1 profile = calculate_votes p2 profile"
      by (simp add: calculate_votes_def)
    then show ?thesis using `mset p1 = mset p2` by simp
  qed
qed*)

(* to prove *)
theorem full_module_anonymity:
  assumes "finite indexes"
  shows "\<forall>profile_l dm dm_perm.
           (p dm) <~~> (p dm_perm) \<longrightarrow>
           full_module dm profile_l =
           full_module dm_perm profile_l"
  sorry

(* Define the concordant property *)
definition concordant :: "(('a, 'b) Divisor_Module \<Rightarrow> ('a, 'b) Divisor_Module) \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow> bool" where
  "concordant D dm = (\<forall>party1 party2 i.
    retrieve_votes party1 (p dm) (v dm) > retrieve_votes party2 (p dm) (v dm) \<longrightarrow>
    count_seats {party1} (s (D dm)) (i dm) \<ge> count_seats {party2} (s (D dm)) (i dm))"

value "retrieve_votes ''partyB'' [''partyA'', ''partyB''] [4, 5]"
(*
fun count_seats :: "'b set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "count_seats p s i = 
    (card {ix. ix \<in> i \<and> s ix = p})"

theorem loop_comp_sound:
  fixes
    m :: "'a Electoral_Module" and
    t :: "'a Termination_Condition"
  assumes "electoral_module m"
  shows "electoral_module (m \<circlearrowleft>\<^sub>t)"
  using def_mod_sound loop_comp_helper_imp_partit assms
        loop_composition.simps electoral_module_def
  by metis

*)

(* Define monotonicity property *)
theorem monotonicity_property:
  fixes
  p :: "'a" and
  v :: "rat list" and
  v' :: "rat list" and
  s :: "('a, 'b) Seats" and
  s' :: "('a, 'b) Seats"
  shows "\<forall>p parties v v' s s' i. retrieve_votes p parties v' \<ge> retrieve_votes p parties v \<longrightarrow>
             count_seats {p} s' i \<ge>
              count_seats {p} s i"
  sorry

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

definition create_divisor_module :: "nat Result \<Rightarrow> char list Parties \<Rightarrow> nat set \<Rightarrow> (nat, char list) Seats \<Rightarrow> nat \<Rightarrow> rat list \<Rightarrow> rat list \<Rightarrow> rat list \<Rightarrow> (nat, char list) Divisor_Module" where
  "create_divisor_module resu pu iu su nsu vu fvu du = \<lparr> res = resu, p = pu, i = iu, s = su, ns = nsu, v = vu, fv = fvu, d = du \<rparr>"

(* value "full_module (create_divisor_module ({1}, {1}, {1, 2, 3}) parties_list seats_set (create_empty_seats seats_set parties_list) 3 empty_votes empty_votes parameters_list) profile_list" *)
end
