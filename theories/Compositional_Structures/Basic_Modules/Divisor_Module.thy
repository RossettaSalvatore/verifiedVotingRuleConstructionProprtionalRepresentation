

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
  sl :: "nat list" 
  d :: "nat list"

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


text \<open> This function updates the "fractional votes" of the winning party, dividing the starting
       votes by the i-th parameter, where i is the number of seats won by the party. \<close>

(* works adapted *)
fun update_votes2 ::  "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       rat list" where 
"update_votes2 winner r = 
    (let index = get_index(\<lambda>x. x = (hd winner)) (p r);
     n_seats = count_seats winner (s r) (i r);
     new_v = get_votes (hd winner) (p r) (v r) / of_int(d r ! n_seats) in
     list_update (fv r) index new_v)"

fun update_votes22 ::  "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow> nat \<Rightarrow>
                       rat list" where 
"update_votes22 winner r n = 
    (let index = get_index(\<lambda>x. x = (hd winner)) (p r);
     n_seats = count_seats winner (s r) (i r);
     new_v = get_votes (hd winner) (p r) (v r) / of_int n in
     list_update (fv r) index new_v)"

text \<open> This function moves one seat from the disputed set to the assigned set. Moreover,
       returns the record with updated Seats function and "fractional" Votes entry 
       for the winning party. \<close>

fun divisor_module :: "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       ('a::linorder, 'b) Divisor_Module" where 
"divisor_module winner rec =
  (let 
    seat = Min (disp_r (res rec));
    new_s = update_seat seat winner (s rec);
    new_as = ass_r (res rec) \<union> {seat};
    new_fv = update_votes2 winner (rec\<lparr>s:= new_s\<rparr>);
    index =  get_index_upd (hd winner) (p rec);
    curr_ns = (sl rec) ! index;
    new_sl = update_at_index_nat (sl rec) index ( (sl rec) ! index + 1);
    new_di =  disp_r (res rec) - {seat}
     in \<lparr>res = (new_as, {}, new_di),
             p = (p rec),
             i = (i rec),
             s = new_s,
             ns = (ns rec),
             v = (v rec),
             fv = new_fv,
             sl = new_sl,
             d = (d rec)
            \<rparr>)"

(* should work *)
lemma divisor_module_sl_update:
  fixes winner :: "'b list" and 
        rec :: "('a::linorder, 'b) Divisor_Module" and
        index::"nat"
      assumes i_def "index = get_index_upd (hd winner) (p rec)"
  shows "sl (divisor_module winner rec) = 
         update_at_index_nat (sl rec) index ((sl rec) ! index + 1)"
proof -
  define seat new_s new_as new_fv index curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat winner (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = update_votes2 winner (rec\<lparr>s:= new_s\<rparr>)" and
          "index =  get_index_upd (hd winner) (p rec)" and
          "curr_ns = (sl rec) ! index" and
          "new_sl = update_at_index_nat (sl rec) index (curr_ns + 1)" and
          "new_di =  disp_r (res rec) - {seat}"
  have "(divisor_module winner rec) =  \<lparr>res = (new_as, {}, new_di),
             p = (p rec),
             i = (i rec),
             s = new_s,
             ns = (ns rec),
             v = (v rec),
             fv = new_fv,
             sl = new_sl,
             d = (d rec)
            \<rparr>" 
    unfolding divisor_module.simps new_sl_def Let_def
  using curr_ns_def index_def new_as_def new_di_def new_fv_def new_s_def seat_def by fastforce
  then have "sl(divisor_module winner rec) = new_sl" 
    by simp
  also have "... = update_at_index_nat (sl rec) index (curr_ns + 1)" 
    unfolding new_sl_def by simp
  also have "... =  update_at_index_nat (sl rec) index ((sl rec) ! index + 1)"
      unfolding new_sl_def using curr_ns_def by simp
  finally show ?thesis
  using index_def assms by blast
qed

(* should work *)
lemma divisor_module_increase_seats:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
assumes i_def: "index = get_index_upd (hd winner) (p rec)"
shows "(sl (divisor_module winner rec)) ! index =
       (sl rec) ! index + 1"
proof -
  have "sl (divisor_module winner rec) =  update_at_index_nat (sl rec) index ((sl rec) ! index + 1)" 
    using divisor_module_sl_update assms by blast
  then have "sl (divisor_module winner rec) ! index = 
        update_at_index_nat (sl rec) index ((sl rec) ! index + 1) ! index" using assms by simp
  then have "... = ((sl rec) ! index + 1)" using update_at_index_nat_lemma by simp
  then show ?thesis
  using \<open>sl (divisor_module winner rec) ! index = update_at_index_nat (sl rec) index (sl rec ! index + 1) ! index\<close> by auto
qed

fun break_tie :: "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       ('a::linorder, 'b) Divisor_Module" where 
"break_tie winners rec =
          \<lparr>res = (res rec),
             p = (p rec),
             i = (i rec),
             s = update_seat (Min (disp_r (res rec))) winners (s rec),
             ns = (ns rec),
             v = (v rec),
             fv = (fv rec),
             sl = (sl rec),
             d = (d rec)
            \<rparr>"

lemma break_tie_lemma:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
shows "sl (break_tie winner rec) = sl rec" by simp

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
(*lemma divisor_module_length:
  assumes non_empty_parties: "p rec \<noteq> []"
  shows "length (p (divisor_module rec)) < length (p rec)"
  using assms by (simp add:Let_def)
*)

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
fun create_seats :: "'a::linorder set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 'b list \<Rightarrow>
                      ('a::linorder, 'b) Seats" where
  "create_seats def seats pa =
    (\<lambda>x. if x \<in> def then pa else seats x)"
                          
text \<open>This function checks whether there are enough seats for all the winning parties.
      - If yes, assign one seat to the first party in the queue.
      - If not, assign all remaining seats to the winning parties, making these seats 
        "disputed".\<close>
fun assign_seats :: "('a::linorder, 'b) Divisor_Module
                        \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"assign_seats rec = (
      let winners = get_winners (fv rec) (p rec) in
      if length winners \<le> ns rec then
         (divisor_module [hd winners] rec)\<lparr>ns := (ns rec) - 1\<rparr>
      else
         (break_tie winners rec)\<lparr>ns := 0\<rparr>)"

(* write proof that under assumption that length winners < ns rec
   the winner (the head of winners) gets its seats increased,
   while the other parties will have the same number of seats
*)

(* are assumptions enough? check 
   pretty sure i should change assign seat not to have (ns := ns - 1).
   posso mettere divisor_module in un rec' e poi creare alla fine 
   \<lparr> \<rparr> passando tutti i parametri da rec' e per ns metto ns = ns rec' - 1 
*)
lemma assign_seats_seats_increased:
   fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  party::"'b" and
  winners::"'b list" and
  votes::"rat list" and
  index::"nat"
assumes "length winners \<le> ns rec"  
assumes "party = hd winners"
assumes i_def "index = get_index_upd party (p rec)"
shows "sl (assign_seats rec) ! index = sl rec ! index + 1"
  sorry

lemma assign_seats_major:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  party1::"'b" and
  party2::"'b" and
  parties::"'b list" and
  votes::"rat list" and
  votes1::"rat" and
  votes2::"rat" and
  i::"'a::linorder set"
assumes "votes1 > votes2"
assumes "\<not>(i = {})"
assumes "count_seats [party1] (s rec) i = count_seats [party2] (s rec) i"
assumes "votes1 = get_votes party1 parties votes"
assumes "votes2 = get_votes party2 parties votes"
shows "count_seats [party1] (s (assign_seats rec)) i \<ge> count_seats [party2] (s (assign_seats rec)) i"
  sorry
(*
fun a_seat :: "my_rec \<Rightarrow> my_rec" where
"a_seat r =
      let win = \<dots> in
        (div r\<lparr>p := win\<rparr>)\<lparr>ns := ns r - 1\<rparr>"

function loop_o ::
  "my_rec \<Rightarrow> my_rec"
  where  
  "ns r = 0  \<Longrightarrow> loop_o r = r" |
  "\<not>(ns r = 0) \<Longrightarrow> loop_o r = loop_o (a_seat r)"
  by auto
termination by (relation "measure (\<lambda>r. ns r)")
               (auto simp add: lemma1)
lemma [code]: \<open>loop_o r = (if ns r = 0 then r else loop_o (a_seat r))\<close>
  by (cases r) auto
*)

lemma nseats_decreasing:
  assumes non_empty_parties: "p rec \<noteq> []"
  assumes n_positive: "(ns rec) > 0"
  shows "ns (assign_seats rec) < ns rec"
proof (cases "length (get_winners (fv rec) (p rec)) \<le> ns rec")
  case True
  then have "ns (assign_seats rec) = ns rec - 1"
    by (auto simp add: Let_def)
  also have "... < ns rec" using True n_positive non_empty_parties
    by simp
  finally show ?thesis .
next
  case False
  then have "ns (assign_seats rec) = 0"
    by (auto simp add: Let_def)
  also have "... < ns rec" using n_positive
    by simp
  finally show ?thesis .
qed


(* termination condition *)
text \<open>This loop applies the same functions until no more seats are available.\<close>
function loop_o ::
  "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where  
  "ns r = 0  \<Longrightarrow> loop_o r = r" |
  "\<not>(ns r = 0) \<Longrightarrow> loop_o r = loop_o (assign_seats r)"
  by auto
termination by (relation "measure (\<lambda>r. ns r)")
               (auto simp add: Let_def nseats_decreasing)
lemma [code]: \<open>loop_o r = (if ns r = 0 then r else loop_o (assign_seats r))\<close>
  by (cases r) auto


(* termination loop_outer
proof (relation "measure (ns :: ('a::linorder, 'b) Divisor_Module \<Rightarrow> nat)")
  show "wf (measure (ns :: ('a::linorder, 'b) Divisor_Module \<Rightarrow> nat))"
    by simp
next
  fix r :: "('a::linorder, 'b) Divisor_Module"
  assume "ns r > 0"
  then have "ns (assigning_seats r) < ns r"
    by (simp add:nseats_decreasing)
  then show "(assigning_seats r, r) \<in> measure ns"
    by auto
qed *)

lemma loop_decreasing:
  shows "ns (loop_outer r) < ns (loop_outer (assigning_seats r))"   
  sorry
(* to adapt after adapting lemma used 
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
*)

fun t_inner :: "'b Termination_Condition" where 
  "t_inner result = (
    case result of 
      (lp, _, _) \<Rightarrow> lp = {} 
  )"

fun create_empty_seats :: "'a::linorder set \<Rightarrow> 'b Parties \<Rightarrow> ('a::linorder, 'b) Seats" where
  "create_empty_seats indexes parties =
    (\<lambda>i. if i \<in> indexes then parties else [])"


(* full divisor module function
  calcola voti correttamente  *) 
text \<open>This function takes in input the parameters and calculates
       the final output of the election.\<close>

fun full_module:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where

"full_module rec pl = (
    let sv = calc_votes (p rec) (p rec) pl [0, 0, 0, 0, 0];
    empty_seats = create_empty_seats (i rec) (p rec)
    in loop_o (rec\<lparr>
             s := empty_seats,
             v := sv,
             fv := sv
            \<rparr>))"

(* ns è un numero naturale *)
(* i divisor sono numeri interi *)
fun dhondt :: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"dhondt rec pr = full_module (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr"

fun saintelague:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"saintelague rec pr = full_module (rec\<lparr>d := (filter (\<lambda>x. x mod 2 = 1)
 (upt 1 ( 2 * (ns rec))))\<rparr>) pr"

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

(* Define the concordant property *)
definition concordant :: "(('a, 'b) Divisor_Module \<Rightarrow> ('a, 'b) Divisor_Module) \<Rightarrow>
                           ('a::linorder, 'b) Divisor_Module \<Rightarrow> bool" where
  "concordant D dm = (\<forall>party1 party2 i.
    get_votes party1 (p dm) (v dm) > get_votes party2 (p dm) (v dm) \<longrightarrow>
    count_seats [party1] (s (D dm)) (i dm) \<ge> count_seats [party2] (s (D dm)) (i dm))"

theorem full_module_concordant:
  fixes
    rec:: "('a::linorder, 'b) Divisor_Module" and
    pl::"'b Profile" and 
    indexes::"'a::linorder set" and
    se::"('a::linorder, 'b) Seats" and
    party::"'b" and
    fparties::"'b Parties" 
  assumes "se = (s (full_module rec pl))"
  assumes "votes ! get_index_upd party fparties = cnt_votes party pl 0"
  shows "cnt_votes p1 pl 0 > cnt_votes p2 pl 0 ==> 
          count_seats [p1] se indexes \<ge> count_seats [p2] se indexes"

value "get_votes ''partyB'' [''partyA'', ''partyB''] [4, 5]"
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
  shows "\<forall>p parties v v' s s' i. get_votes p parties v' \<ge> get_votes p parties v \<longrightarrow>
             count_seats [p] s' i \<ge>
              count_seats [p] s i"
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

definition pref_rel_d :: "char list Preference_Relation" where
"pref_rel_d = {(''a'', ''d''), (''b'', ''d''), 
                (''c'', ''d''), (''a'', ''c''), 
                (''c'', ''b''), (''a'', ''b'')}"

definition pref :: "char list Profile" where
"pref = [pref_rel_a, pref_rel_b, pref_rel_c,
                 pref_rel_d, pref_rel_a, pref_rel_a, 
                 pref_rel_a, pref_rel_b]"

definition parties :: "char list list" where
"parties = [''a'', ''b'', ''c'', ''d'']"

definition parties_list_perm :: "char list list" where
"parties_list_perm = [''b'', ''d'', ''c'', ''a'']"

definition factors :: "nat list" where
"factors = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]"

definition seats_set :: "nat set" where
"seats_set = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}"

fun start_votes :: "'a list \<Rightarrow> rat list" where
  "start_votes [] = []" |
  "start_votes (x # xs) = 0 # start_votes xs"

fun start_seats_list :: "'a list \<Rightarrow> nat list" where
  "start_seats_list [] = []" |
  "start_seats_list (x # xs) = 0 # start_seats_list xs"

definition new_record :: "char list Parties \<Rightarrow> nat \<Rightarrow> (nat, char list) Divisor_Module"
  where
  "new_record cp cns = \<lparr> res =  ({}, {}, {1..cns}), p = cp, i = {1..cns}, 
                               s = create_empty_seats {1..cns} cp, ns = cns, 
                               v = start_votes cp, fv = start_votes cp,
                               sl = start_seats_list cp, d = [] \<rparr>"

(* - se i partiti è una lista vuota c'è un errore
  - al momento assegna tutti i seat indicati a tutti i partiti. (RISOLTO)
  - ho cambiato in assigning_seats quando chiamo divisor module a p passo i winners (RISOLTO)
  - adesso ho aggiustato che passa i seat correttamente dai disputed agli assegnati (RISOLTO)
  - bisogna fare in modo che si assegni correttamente al partito vincitore (RISOLTO)
  - sto cercando di assegnare il seat al winner (RISOLTO)
*)

value "dhondt (new_record parties 10) pref"

value "saintelague (new_record parties 10) pref"
end
