

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

text \<open> This record contains the list of parameters used in the whole divisor module.  \<close>
record ('a::linorder, 'b) Divisor_Result =
  seats :: "'a::linorder Result"
  parties :: "'b Parties"
  seats_fun :: "('a::linorder, 'b) Seats"
  seats_list :: "nat list" 

text \<open>This recursive loop applies the assign_seats function until no more seats are 
      available.\<close>
function loop_div ::
  "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where
  "ns r = 0  \<Longrightarrow> loop_div r = r" |
  "ns r > 0 \<Longrightarrow> loop_div r = loop_div (assign_seat r)"
  by auto
termination by (relation "measure (\<lambda>r. ns r)")
               (auto simp add: Let_def nseats_decreasing)
lemma loop_div_lemma[code]: \<open>loop_div r = (if ns r = 0 then r else loop_div (assign_seat r))\<close>
  by (cases r) auto

text \<open>This function is executing the whole divisor method, taking in input the 
       already initialized record and calculates the final output of the election.
      The Divisor Method is allocating a number of seats based on the number of votes of
      the candidates. Moreover, it is scaling the number of votes of every party with a 
      factor proportional to the number of seats already assigned to that given party,
      to avoid unfairness and predominance of bigger parties. If there is a tie, the 
      remaining seats will not be assigned and will remain "disputed". \<close>

fun divisor_method:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" 
  where
"divisor_method rec pl = (
    let sv = calc_votes (p rec) (p rec) pl (v rec);
    sfv = start_fract_votes sv
    in loop_div \<lparr> 
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

fun build_record :: "'b Parties \<Rightarrow> nat \<Rightarrow> (nat, 'b) Divisor_Module"
  where
  "build_record cp cns = \<lparr> res =  ({}, {}, {1..cns}), p = cp, i = {1..cns}, 
                               s = create_empty_seats {1..cns} cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats cp, d = [] \<rparr>"

fun build_record_generic :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 
                            ('a::linorder, 'b) Divisor_Module"
  where
  "build_record_generic l cp cns = \<lparr> res =  ({}, {}, (set l)), p = cp, i = (set l), 
                               s = create_empty_seats (set l) cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats cp, d = [] \<rparr>"

text \<open> The D'Hondt method is the most classic variant of the Divisor Method, in which the
       factors used to scale the votes are natural number (1, 2, 3, ...). 
       The function starts from a list of candidates, a list of ballots and the number 
       of seats and fully executes the D'Hondt method. In this function, seats are 
       identified by natural numbers. \<close>
fun dhondt_method :: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Result" 
  where
"dhondt_method partiti nseats pr =
    (let rec = build_record partiti nseats; 
      result = divisor_method (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr in 
        \<lparr> seats = res result, 
           parties = p result, 
           seats_fun = s result,
           seats_list = sl result\<rparr>)"

text \<open> This is a more generic version of the D'Hondt method, in which it is possible to
       choose the way to identify the seats, as long as it is a linearly ordered type. \<close>
fun dhondt_method_generic :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Result" 
  where
"dhondt_method_generic l partiti nseats pr =
    (let rec = build_record_generic l partiti nseats; 
      result = divisor_method (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr in 
        \<lparr> seats = res result, 
           parties = p result, 
           seats_fun = s result,
           seats_list = sl result\<rparr>)"

text \<open> The Sainte-Laguë method is a variant of the Divisor Method, in which the
       factors used to scale the votes are odd natural numbers (1, 3, 5, ...). 
       The function starts from a list of candidates, a list of ballots and the number 
       of seats and fully executes the Sainte-Laguë method. In this function, the seats
       are identified with natural numbers. \<close>
fun saintelague_method:: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Result" 
  where
"saintelague_method partiti nseats pr = 
  (let rec = build_record partiti nseats; 
      result = divisor_method (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1) (upt 1 (2*ns rec))\<rparr>) pr in 
        \<lparr> seats = res result, 
           parties = p result, 
           seats_fun = s result,
           seats_list = sl result\<rparr>)"


text \<open> This is a more generic version of the Sainte-Laguëmethod, in which it is possible to
       choose the way to identify the seats, as long as it is a linearly ordered type. \<close>
fun saintelague_method_generic:: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Result" 
  where
"saintelague_method_generic l partiti nseats pr = 
  (let rec = build_record_generic l partiti nseats; 
      result = divisor_method (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1) (upt 1 (2*ns rec))\<rparr>) pr in 
        \<lparr> seats = res result, 
           parties = p result, 
           seats_fun = s result,
           seats_list = sl result\<rparr>)"

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
