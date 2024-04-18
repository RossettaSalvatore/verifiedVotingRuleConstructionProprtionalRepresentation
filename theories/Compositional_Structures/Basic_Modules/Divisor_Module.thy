

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


text \<open>This recursive loop applies the assign_seats function until no more seats are 
      available.\<close>
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

text \<open>This function is executing the whole divisor method, taking in input the 
       already initialized record and calculates the final output of the election.
      The Divisor Method is allocating a number of seats based on the number of votes of
      the candidates. Moreover, it is scaling the number of votes of every party with a 
      factor proportional to the number of seats already assigned to that given party,
      to avoid unfairness and predominance of bigger parties. If there is a tie, the 
      remaining seats will not be assigned and will remain "disputed". \<close>

fun divisor_method:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"divisor_method rec pl = (
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

fun new_record :: "'b Parties \<Rightarrow> nat \<Rightarrow> (nat, 'b) Divisor_Module"
  where
  "new_record cp cns = \<lparr> res =  ({}, {}, {1..cns}), p = cp, i = {1..cns}, 
                               s = create_empty_seats {1..cns} cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats cp, d = [] \<rparr>"

fun new_record_generic :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where
  "new_record_generic l cp cns = \<lparr> res =  ({}, {}, (set l)), p = cp, i = (set l), 
                               s = create_empty_seats (set l) cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats cp, d = [] \<rparr>"

text \<open> The D'Hondt method is the most classic variant of the Divisor Method, in which the
       factors used to scale the votes are natural number (1, 2, 3, ...). 
       The function starts from a list of candidates, a list of ballots and the number 
       of seats and fully executes the D'Hondt method. In this function, seats are 
       identified by natural numbers. \<close>
fun dhondt_method :: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"dhondt_method partiti nseats pr =
    (let rec = new_record partiti nseats in divisor_method (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr)"

text \<open> This is a more generic version of the D'Hondt method, in which it is possible to
       choose the way to identify the seats, as long as it is a linearly ordered type. \<close>
fun dhondt_method_generic :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"dhondt_method_generic l partiti nseats pr =
    (let rec = new_record_generic l partiti nseats in divisor_method (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr)"

text \<open> The Sainte-Laguë method is a variant of the Divisor Method, in which the
       factors used to scale the votes are odd natural numbers (1, 3, 5, ...). 
       The function starts from a list of candidates, a list of ballots and the number 
       of seats and fully executes the Sainte-Laguë method. In this function, the seats
       are identified with natural numbers. \<close>
fun saintelague_method:: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"saintelague_method partiti nseats pr = 
  (let rec = new_record partiti nseats in divisor_method (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1)
                                            (upt 1 (2*ns rec))\<rparr>) pr)"

text \<open> This is a more generic version of the Sainte-Laguëmethod, in which it is possible to
       choose the way to identify the seats, as long as it is a linearly ordered type. \<close>
fun saintelague_method_generic:: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where
"saintelague_method_generic l partiti nseats pr = 
  (let rec = new_record_generic l partiti nseats in divisor_method (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1)
                                            (upt 1 (2*ns rec))\<rparr>) pr)"

(* Example *)
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
"pref = [pref_rel_a, pref_rel_b, pref_rel_c, pref_rel_d, pref_rel_a, pref_rel_a, 
         pref_rel_a, pref_rel_b]"

definition parties :: "char list list" where
"parties = [''a'', ''b'', ''c'', ''d'']"

value "dhondt_method parties 10 pref"

value "saintelague_method parties 10 pref"

end
