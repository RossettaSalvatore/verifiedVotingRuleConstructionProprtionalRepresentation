

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
"Component_Types/Assign_Seats"
begin


text \<open>This loop applies the assign_seats function until no more seats are available.\<close>
function loop_o ::
  "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where
  "ns r = 0  \<Longrightarrow> loop_o r = r" |
  "ns r > 0 \<Longrightarrow> loop_o r = loop_o (assign_seats r)"
  by auto
termination by (relation "measure (\<lambda>r. ns r)")
               (auto simp add: Let_def nseats_decreasing)
lemma loop_o_lemma[code]: \<open>loop_o r = (if ns r = 0 then r else loop_o (assign_seats r))\<close>
  by (cases r) auto

lemma loop_o_concordant_one_case:
fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  party1::"'b" and 
  party2::"'b" and 
  parties::"'b Parties"
assumes
     "sl rec ! (index  parties party1) \<ge> sl rec ! (index parties party2)" and "ns rec = 0"
shows "sl (loop_o rec) ! (index parties party1) \<ge> 
       sl (loop_o rec) ! (index parties party2)"
  using assms by simp

lemma loop_o_concordant:
fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  m::"rat" and 
  v1::"rat" and 
  v2::"rat" and
  party1::"'b" and 
  party2::"'b" and 
  parties::"'b Parties" and
  di::"nat list"
assumes
  "sl rec ! (index  parties party1) \<ge> sl rec ! (index  parties party2)"
shows "sl (loop_o rec) ! (index parties party1) \<ge> 
       sl (loop_o rec) ! (index parties party2)"
proof (induction "rec" rule:loop_o.induct)
  case (1 r)
  then show ?case sorry
next
  case (2 r)
  then show ?case sorry
qed

fun create_empty_seats :: "'a::linorder set \<Rightarrow> 'b Parties \<Rightarrow> ('a::linorder, 'b) Seats" 
  where 
"create_empty_seats indexes parties =
    (\<lambda>i. if i \<in> indexes then parties else [])"

fun start_fract_votes :: "nat list \<Rightarrow> rat list" where
  "start_fract_votes [] = []" |
  "start_fract_votes (nn # nns) = (of_nat nn) # start_fract_votes nns"

text \<open>This function takes in input the parameters and calculates
       the final output of the election.\<close>

fun full_module:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"full_module rec pl = (
    let sv = calc_votes (p rec) (p rec) pl (v rec);
    sfv = start_fract_votes sv
    in loop_o \<lparr> 
             res = res rec,
             p = p rec,
             i = i rec,
             s = s rec,
             ns = ns rec,
             v = sv,
             fv = sfv,
             sl = sl rec,
             d = d rec
            \<rparr>)"

theorem full_module_concordant:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  m::"rat" and 
  v1::"rat" and 
  v2::"rat" and
  party1::"'b" and 
  party2::"'b" and 
  parties::"'b Parties" and
  winners::"'b list"
assumes 
  "winners = get_winners (fv rec) parties" and
  "index parties party1 = index (p (assign_seats rec)) party1" and
  "index parties party2 = index (p (assign_seats rec)) party2" and
  "p (assign_seats (assign_seats rec)) = p rec" and
  "get_winners (fv rec) parties \<noteq> []" and
  "party1 \<in> set parties" and
  "party2 \<in> set parties" and
  "v1 > v2" and
  "party1 \<noteq> party2" and
  "(fv rec) ! (index parties party1) \<equiv> v1 / (of_int ((d rec) ! ((sl rec) ! (index parties party1))))" and
  "(fv rec) ! (index parties party2) \<equiv> v2 / (of_int ((d rec) ! ((sl rec) ! (index parties party1))))" and
  "(d rec) ! ((sl rec) ! (index parties party1)) \<noteq> 0" and
  "(index parties party1) \<noteq> ( index parties party2)" and
  "(index parties party1) < length (sl rec)" and
  "(index parties party1) < length (sl rec)" and
  "length winners \<le> ns rec"
  shows "sl (full_module rec pl) ! ( index parties party1) \<ge> sl (full_module rec pl) ! ( index parties party2)"
  using loop_o_concordant assms sorry

fun start_votes :: "'a list \<Rightarrow> nat list" where
  "start_votes [] = []" |
  "start_votes (x # xs) = 0 # start_votes xs"

fun start_seats_list :: "'a list \<Rightarrow> nat list" where
  "start_seats_list [] = []" |
  "start_seats_list (x # xs) = 0 # start_seats_list xs"

fun new_record :: "'b Parties \<Rightarrow> nat \<Rightarrow> (nat, 'b) Divisor_Module"
  where
  "new_record cp cns = \<lparr> res =  ({}, {}, {1..cns}), p = cp, i = {1..cns}, 
                               s = create_empty_seats {1..cns} cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats_list cp, d = [] \<rparr>"

fun new_record_generic :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where
  "new_record_generic l cp cns = \<lparr> res =  ({}, {}, (set l)), p = cp, i = (set l), 
                               s = create_empty_seats (set l) cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats_list cp, d = [] \<rparr>"

fun dhondt_method :: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"dhondt_method partiti nseats pr =
    (let rec = new_record partiti nseats in full_module (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr)"

fun dhondt_method_generic :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"dhondt_method_generic l partiti nseats pr =
    (let rec = new_record_generic l partiti nseats in full_module (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr)"

fun saintelague_method:: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"saintelague_method partiti nseats pr = 
  (let rec = new_record partiti nseats in full_module (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1)
                                            (upt 1 (2*ns rec))\<rparr>) pr)"

fun saintelague_method_generic:: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"saintelague_method_generic l partiti nseats pr = 
  (let rec = new_record_generic l partiti nseats in full_module (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1)
                                            (upt 1 (2*ns rec))\<rparr>) pr)"

(* Define a set *)
definition my_set :: "nat set" where
  "my_set = {1, 2, 3, 4, 5}"

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

value "dhondt_method parties 10 pref"

value "saintelague_method parties 10 pref"

end
