
section \<open> Assign Seats \<close>

theory Assign_Seats
  imports Complex_Main
Main
"Social_Choice_Types/Preference_Relation"
"Social_Choice_Types/Profile"
"Social_Choice_Types/Result"
"Electoral_Module"
"Social_Choice_Types/Votes"
"Termination_Condition"
"HOL-Combinatorics.Multiset_Permutations"
"Consensus_Class"
"Distance"

begin

text \<open> This record contains the list of parameters used in the whole divisor module.  \<close>
record ('a::linorder, 'b) Divisor_Module =
  res :: "'a::linorder Result"
  p :: "'b Parties"
  i :: "'a::linorder set"
  s :: "('a::linorder, 'b) Seats"
  ns :: nat
  v :: "nat list"
  fv :: "rat list"
  sl :: "nat list" 
  d :: "nat list"

text \<open> Abbreviation to retrieve the assigned seats from the Result type. \<close>
abbreviation ass_r :: "'a Result \<Rightarrow> 'a set" where
  "ass_r r \<equiv> fst r"

text \<open> Abbreviation to retrieve the disputed seats from the Result type. \<close>
abbreviation disp_r :: "'a Result \<Rightarrow> 'a set" where
  "disp_r r \<equiv> snd (snd r)"

subsection \<open> Definition \<close>
text \<open> This function updates the "fractional votes" of the winning party, dividing 
       the starting votes by the i-th parameter, where i is the number of seats won 
       by the party. \<close>

fun upd_votes ::  "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       rat list" where 
"upd_votes w r = 
    (let ix = index (p r) (hd w);
     n_seats = cnt_seats w (s r) (i r);
     n_v = of_nat(get_votes (hd w) (p r) (v r)) / of_int(d r ! n_seats) in
     list_update (fv r) ix n_v)"

text \<open> This function moves one seat from the disputed set to the assigned set. Moreover,
       returns the record with updated Seats function and "fractional" Votes entry 
       for the winning party. \<close>

fun upd_round :: "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       ('a::linorder, 'b) Divisor_Module" where 
"upd_round w rec =
  (let 
    seat = Min (disp_r (res rec));
    new_s = update_seat seat w (s rec);
    new_as = ass_r (res rec) \<union> {seat};
    new_fv = upd_votes w (rec\<lparr>s:= new_s\<rparr>);
    ix = index (p rec) (hd w);
    curr_ns = (sl rec) ! ix;
    new_sl = list_update (sl rec) ix ( (sl rec) ! ix + 1);
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

text \<open> This function is handling the case of a tie. It will just defer the record
       assigning the disputed seats to ALL winners. \<close>

fun break_tie :: "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       ('a::linorder, 'b) Divisor_Module" where 
"break_tie ws rec =
          \<lparr>res = (res rec),
             p = (p rec),
             i = (i rec),
             s = update_seat (Min (disp_r (res rec))) ws (s rec),
             ns = (ns rec),
             v = (v rec),
             fv = (fv rec),
             sl = (sl rec),
             d = (d rec)
            \<rparr>"

text \<open>This function checks whether there are enough seats for all the winning parties.
      - If yes, assign the seat to the first party in the list.
      - If not, assign the seat to the winning parties, making these seats 
        "disputed".\<close>
fun assign_seats :: "('a::linorder, 'b) Divisor_Module
                        \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"assign_seats rec = (
      let ws = get_winners (fv rec) (p rec) in
      if length ws \<le> ns rec then 
        let rec' =  (upd_round [hd ws] rec) in
                    \<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>
      else
         let rec'' = (break_tie ws rec) in
                       \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>)"

text \<open> Auxiliary lemmas \<close>

text \<open> This lemma states that non-winner parties mantain their number of seats after
       assignment of the new seat.  \<close>

lemma assign_seat_mantain_seats_lemma:
  assumes 
"ix \<noteq> index (p rec) (hd w)"
shows "sl (upd_round w rec) ! ix = sl rec ! ix"
proof - 
   define seat new_s new_as new_fv ind curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat w (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = upd_votes w (rec\<lparr>s:= new_s\<rparr>)" and
          "ind =  index (p rec) (hd w)" and
          "curr_ns = (sl rec) ! ind" and
          "new_sl = list_update (sl rec) ind (curr_ns + 1)" and
          "new_di =  disp_r (res rec) - {seat}"
  have "(upd_round w rec) =  \<lparr>res = (new_as, {}, new_di),
             p = (p rec),
             i = (i rec),
             s = new_s,
             ns = (ns rec),
             v = (v rec),
             fv = new_fv,
             sl = new_sl,
             d = (d rec)
            \<rparr>" 
    unfolding upd_round.simps new_sl_def Let_def
    using nth_list_update_eq curr_ns_def ind_def new_as_def new_di_def new_fv_def 
          new_s_def seat_def by fastforce
  then have "sl (upd_round w rec) = new_sl" 
    by simp
  then have "... =  list_update (sl rec) ind (curr_ns + 1)" 
    using new_sl_def by simp
  then have "sl (upd_round w rec) ! ix = list_update (sl rec) ind (curr_ns + 1) ! ix"
    using \<open>sl (upd_round w rec) = new_sl\<close> by presburger
  then have "... = (sl rec) ! ix" 
    using nth_list_update_neq ind_def assms(1) by metis
  then show ?thesis
  using \<open>sl (upd_round w rec) ! ix = (sl rec)[ind := curr_ns + 1] ! ix\<close> by presburger
qed

lemma assign_seat_sl_update:
  fixes 
winner :: "'b list" and 
rec :: "('a::linorder, 'b) Divisor_Module"
defines i_def: "ind \<equiv> index (p rec) (hd winner)"
shows "sl (upd_round winner rec) = list_update (sl rec) ind (sl rec ! ind + 1)"
proof - 
  define seat new_s new_as new_fv ind curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat winner (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = upd_votes winner (rec\<lparr>s:= new_s\<rparr>)" and
          "ind =  index (p rec) (hd winner)" and
          "curr_ns = (sl rec) ! ind" and
          "new_sl = list_update (sl rec) ind (curr_ns + 1)" and
          "new_di =  disp_r (res rec) - {seat}"
  have "(upd_round winner rec) =  \<lparr>res = (new_as, {}, new_di),
             p = (p rec),
             i = (i rec),
             s = new_s,
             ns = (ns rec),
             v = (v rec),
             fv = new_fv,
             sl = new_sl,
             d = (d rec)
            \<rparr>" 
    unfolding upd_round.simps new_sl_def Let_def
    using assms nth_list_update_eq curr_ns_def ind_def 
          new_as_def new_di_def new_fv_def new_s_def seat_def by fastforce
  then have "sl(upd_round winner rec) = new_sl" 
    by simp
  also have "... = list_update (sl rec) ind (curr_ns + 1)" 
    using new_sl_def by simp
  also have "... =  list_update (sl rec) ind ((sl rec) ! ind + 1)"
    using new_sl_def curr_ns_def by simp
  finally show ?thesis
    using ind_def nth_list_update_eq i_def by blast
qed

text \<open> This lemma states that the winner gets its seats increased. \<close>

lemma assign_seat_increase_seats:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
defines i_def: "inde \<equiv> index (p rec) (hd winner)"
assumes "inde < length (sl rec)"
shows "sl (upd_round winner rec) ! inde = sl rec ! inde + 1"
proof -
  have "sl (upd_round winner rec) =  list_update (sl rec) inde ((sl rec) ! inde + 1)" 
    using assign_seat_sl_update local.i_def by blast
  then have "sl (upd_round winner rec) ! inde = 
             list_update (sl rec) inde (sl rec ! inde + 1) ! inde" 
    using local.i_def by simp
  then have "... = ((sl rec) ! inde + 1)" 
    using nth_list_update_eq assms by simp
  then show ?thesis
    using \<open>sl (upd_round winner rec) ! inde = 
           list_update (sl rec) inde (sl rec ! inde + 1) ! inde\<close> by auto
qed

text \<open>This lemma states that with assignment of a seat the number of seats won't decrease.\<close>

lemma assign_seat_mon:
assumes "ind < length (sl rec)"
  shows "sl (upd_round winner rec) ! ind \<ge> (sl rec) ! ind"
proof -
    define seat new_s new_as new_fv ind curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat winner (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = upd_votes winner (rec\<lparr>s:= new_s\<rparr>)" and
          "ind =  index (p rec) (hd winner)" and
          "curr_ns = (sl rec) ! ind" and
          "new_sl = list_update (sl rec) ind (curr_ns + 1)" and
          "new_di =  disp_r (res rec) - {seat}"
  have "(upd_round winner rec) =  \<lparr>res = (new_as, {}, new_di),
             p = (p rec),
             i = (i rec),
             s = new_s,
             ns = (ns rec),
             v = (v rec),
             fv = new_fv,
             sl = new_sl,
             d = (d rec)
            \<rparr>" 
    unfolding upd_round.simps new_sl_def Let_def
    using nth_list_update_eq curr_ns_def ind_def new_as_def new_di_def 
          new_fv_def new_s_def seat_def by fastforce
  then have "sl (upd_round winner rec) = new_sl" 
    by simp
  then have "sl (upd_round winner rec) ! ind = new_sl ! ind" 
    by simp
  then have "... = (list_update (sl rec) ind (curr_ns + 1)) ! ind" 
    using new_sl_def nth_list_update_eq by blast
  then show ?thesis 
    using \<open>sl (upd_round winner rec) = new_sl\<close> assms(1) curr_ns_def le_add1 new_sl_def 
          nth_list_update_eq nth_list_update_neq order_refl by metis
qed

lemma break_tie_lemma:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
shows "sl (break_tie winner rec) = sl rec" by simp
 
lemma break_tie_lemma_party:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
shows "sl (break_tie winner rec) ! ind \<ge> sl rec ! ind" by simp

lemma assign_seats_break_tie_case:
  assumes 
    "winners = get_winners (fv rec) (p rec)" and
    "length winners > ns rec"
  shows "sl rec = sl (assign_seats rec)" using assms by simp

text \<open>This lemma states that all the parties besides the winner keep their number of seats.\<close>

lemma assign_seats_not_winner_mantains_seats:
assumes "winners = get_winners (fv rec) (p rec)" and
  "i1 = index (p rec) (hd winners)" and
  "i1 \<noteq> i2" and
  "i2 < length (sl rec)"
  shows "sl rec ! i2 = sl (assign_seats rec) ! i2"
proof (cases "(length winners) \<le> ns rec")
  case True
  define rec' 
   where 
     "rec'= (upd_round [hd winners] rec)"  
  have "assign_seats rec = \<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>" 
    using rec'_def assms True assign_seats.simps by (smt (verit, best))
  then have "sl (assign_seats rec) = sl (rec')" 
    by simp
  then have "sl (assign_seats rec) ! i2 
             = sl (upd_round [hd winners] rec) ! i2" 
    using \<open>sl (assign_seats rec) = sl rec'\<close> rec'_def by presburger
  then have "... = (sl rec) ! i2" 
    using assign_seat_mantain_seats_lemma list.sel(1) assms(2) assms(3) by metis
  then show ?thesis
    using \<open>sl (assign_seats rec) ! i2 = sl (upd_round [hd winners] rec) ! i2\<close> by linarith
next
  case False
 define rec''
    where 
     "rec''= break_tie winners rec"  
   then have "assign_seats rec = \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>" 
     using False rec''_def assms assign_seats.simps by auto
  then have "sl (assign_seats rec) ! i2 = sl (rec'') ! i2" 
    by simp
  then have "... = sl (break_tie winners rec) ! i2" 
    using break_tie_lemma rec''_def by simp
  then have "... = (sl rec) ! i2" 
    by simp
  then show ?thesis
    using \<open>sl (assign_seats rec) ! i2 = sl rec'' ! i2\<close> 
          \<open>sl rec'' ! i2 = sl (break_tie winners rec) ! i2\<close> by force
qed

text \<open> This lemma states that if a party gets its votes increase (v' > v) and it is not
       winning a round with v' votes, then it is not winning also with the first number of
        votes v. \<close>
lemma get_winners_mon:
  fixes 
    v::"rat"
  assumes 
  "party \<in> set (p rec)" and
  "ip = index (p rec) party" and
  "v' > v" and
  "fv rec ! ip = v / of_nat dp" and
  "fv rec' ! ip = v' / of_nat dp" and
  "max_v (fv rec) = max_v (fv rec')" and
  "max_v (fv rec') > (fv rec') ! ip"
shows "party \<notin> set (get_winners (fv rec) (p rec))"
proof - 
  have "max_v (fv rec') > (fv rec') ! ip" 
    using assms(7) by auto
  then have "... > (fv rec) ! ip"
    using  divide_le_cancel dual_order.strict_trans2 nless_le of_nat_less_0_iff
     assms(3) assms(4) assms(5) by metis
  then have "max_v (fv rec) = max_v (fv rec')"
    using assms(6) by blast
  then have "max_v (fv rec) > (fv rec) ! ip" 
    using \<open>fv rec ! ip < max_v (fv rec')\<close> by linarith
  then show ?thesis 
    using add.comm_neutral add_le_same_cancel1 get_winners_loss le_numeral_extra(3) 
          max_v.simps verit_comp_simplify1(3) assms(1) assms(2) by metis
qed

text \<open> This lemma states that the number of seats is not decreasing after assign_seats. \<close>

lemma assign_seats_mon:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and 
  winners::"'b Parties" 
assumes 
"inde < length (sl rec)" and
"winners = get_winners (fv rec) (p rec)"
shows "sl (assign_seats rec) ! inde \<ge> sl rec ! inde"
proof -
  define rec' rec''
    where 
     "rec'= (upd_round [hd winners] rec)" and
     "rec''= (break_tie winners rec)"  
have "assign_seats rec =  (
      let winners = get_winners (fv rec) (p rec) in
      if length winners \<le> ns rec then 
        let rec' =  (upd_round [hd winners] rec) in
                    \<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>
      else
         let rec'' = (break_tie winners rec) in
                       \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>)" using rec''_def by simp
then show ?thesis proof(cases "length winners \<le> ns rec")
  case True
  then have "assign_seats rec = \<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>" using rec'_def assms
  by (smt (verit) assign_seats.simps)
  then have "sl (assign_seats rec) ! inde= sl (upd_round [hd winners] rec) ! inde" 
    using rec'_def by simp
  then have "... \<ge> (sl rec) ! inde" 
    using assms assign_seat_mon by blast
  then show ?thesis 
    using assms rec'_def
  by (metis \<open>sl (assign_seats rec) ! inde = sl (upd_round [hd winners] rec) ! inde\<close>)
  next
  case False
  define rec'' 
    where 
     "rec''= (break_tie winners rec)"  
  then have "assign_seats rec = \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>" 
    using rec''_def assms False by force
  then have "sl (assign_seats rec) ! inde = sl (break_tie winners rec) ! inde" 
    using rec''_def by simp
  then show ?thesis
    using \<open>sl (assign_seats rec) ! inde = sl (break_tie winners rec) ! inde\<close> by fastforce
qed
qed

lemma assign_seats_update:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module"
  defines winners_def: "winners \<equiv> get_winners (fv rec) (p rec)"
  defines rec'_def: "rec' \<equiv> upd_round [hd winners] rec"
  assumes "length winners \<le> ns rec"
  shows "assign_seats rec = \<lparr>res = (res rec'),
                            p = (p rec'),
                            i = (i rec'),
                            s = (s rec'),
                            ns = ((ns rec') - 1),
                            v = (v rec'),
                            fv = (fv rec'),
                            sl = (sl rec'),
                            d = (d rec')\<rparr>" using assms
  by (smt (verit) assign_seats.simps)

text \<open> This lemma states that the winner gets its seats increased \<close>
lemma assign_seats_seats_increased:
   fixes
  rec::"('a::linorder, 'b) Divisor_Module"
assumes 
"winners = get_winners (fv rec) (p rec)" and
"length winners \<le> ns rec" and
"index (p rec) (hd winners) < length (sl rec)"
shows "sl (assign_seats rec) ! index (p rec) (hd winners) = 
       sl rec ! index (p rec) (hd winners) + 1"
proof - 
  define rec' where  "rec' \<equiv> (upd_round [hd winners] rec)"
  have "sl (assign_seats rec) =  sl (\<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>)"    
    using rec'_def assign_seats_update assms(1) assms(2) by metis
  then have "sl (assign_seats rec) ! ( index (p rec) (hd winners)) 
             = (sl rec') ! index (p rec) (hd winners)"
    by simp 
  also have "... = sl (upd_round [hd winners] rec) ! ( index (p rec) (hd winners))" 
    using rec'_def by simp
  also have "... = sl rec ! ( index  (p rec) (hd winners)) + 1" 
    using assign_seat_increase_seats assms(3) list.sel(1) by metis
  finally have "sl (assign_seats rec) ! index (p rec) (hd winners) 
                = sl rec ! index (p rec) (hd winners) + 1" by simp 
  then show ?thesis 
    using \<open>sl (assign_seats rec) ! index  (p rec) (hd winners) = 
           sl rec ! index  (p rec) (hd winners) + 1\<close> by simp
qed

text \<open> This lemma states that in case of two parties with one stronger than the other, 
       then the weaker will not be in the list of winners. \<close>

lemma assign_seats_helper_lemma_helper:
  fixes 
  v1::"rat"
assumes
  "m \<equiv> max_v (fv rec)" and
  "i2 \<equiv> index (p rec) party2" and
  "fv1 \<equiv> fv rec ! i1" and
  "fv2 \<equiv> fv rec ! i2" and
  "winners \<equiv> get_winners (fv rec) (p rec)" and
  "winners \<noteq> []" and
  "i1 < length (fv rec)" and
  "v1 > v2" and
  "fv1 \<equiv> v1 / (of_int (d rec ! (sl rec ! i1)))" and
  "fv2 \<equiv> v2 / (of_int (d rec ! (sl rec ! i2)))" and
  "(d rec) ! ((sl rec) ! i2) \<noteq> 0" and
  "sl rec ! i1 = sl rec ! i2" and
  "i1 \<noteq> i2" and
  "i1 < length (sl rec)" and
  "i2 < length (sl rec)"
  shows "party2 \<noteq> hd (winners)"
proof (cases "fv1 = max_v (fv rec)")
  case True
  then have "fv1 > fv2" 
    using divide_strict_right_mono assms(10) assms(11) assms(12) assms(8) assms(9) by force
  then have "fv2 \<noteq> max_v (fv rec)" 
    using True dual_order.irrefl by simp
  then have "fv rec ! index (p rec) party2 \<noteq> m" 
  using assms(1) assms(2) assms(4) by blast
  then have "fv2 \<noteq> m" 
  using assms(2) assms(4) by blast
  then have "party2 \<noteq> hd winners" 
    using \<open>fv rec ! index (p rec) party2 \<noteq> m\<close> get_winners_not_in_win assms(1) assms(6) 
      assms(5) by metis
  then show ?thesis 
    by simp
next
  case False
  then have "max_v (fv rec) > fv1" 
    using False less_eq_rat_def max_val_wrap_lemma assms(3) assms(7) by blast
  then have "max_v (fv rec) \<noteq> fv2" 
    using divide_right_mono less_le_not_le negative_zle of_int_nonneg assms(10) assms(12) 
      assms(8) assms(9) by (smt (z3))
  then show ?thesis
    using assms(6) assms(2) assms(4) assms(5) get_winners_not_in_win by metis 
qed


lemma assign_seats_helper_lemma_cond_ver:
  fixes
  v1::"rat"
assumes 
  "index (p rec) party1 < length (fv rec)" and
  "v1 > v2" and
  "party2 = hd (get_winners (fv rec) (p rec))" and
  "fv rec ! index (p rec) party1 \<equiv> v1 / of_int (d rec ! (sl rec ! index (p rec) party1))" and
  "fv rec ! index (p rec) party2 \<equiv> v2 / of_int (d rec ! (sl rec ! index (p rec) party2))" and
  "(d rec) ! (sl rec !  index (p rec) party2) \<noteq> 0" and
  "sl rec ! index (p rec) party1 \<ge> sl rec ! index (p rec) party2" and
  "length (get_winners (fv rec) (p rec)) \<le> ns rec" and
  "get_winners (fv rec) (p rec) \<noteq> []" and 
  "index (p rec) party1 < length (sl rec)" and
  "index (p rec) party2 < length (sl rec)"
shows "sl (assign_seats rec) ! index (p rec) party1 \<ge> 
       sl (assign_seats rec) ! index (p rec) party2"
proof(cases "sl rec ! index (p rec) party1 = sl rec ! index (p rec) party2")
  case True
 then have "fv rec ! index (p rec) party1 = v1 / (d rec) ! (sl rec ! index (p rec) party2)" 
   using True of_int_of_nat_eq of_rat_divide of_rat_of_nat_eq assms(4) 
   by (metis (no_types, lifting))
  also have "fv rec ! index (p rec) party1 = v2 / (d rec) ! (sl rec ! index (p rec) party2)" 
    using True divide_le_cancel 
          get_winners_not_in_win max_val_wrap_lemma of_int_of_nat_eq 
          of_nat_le_0_iff verit_comp_simplify1(3) assms(1) assms(9) assms(2) assms(3) 
          assms(4) assms(5) assms(6) by metis
  also have "party2 \<noteq> hd ( get_winners (fv rec) (p rec))"
    using True divide_cancel_right of_nat_0 of_nat_eq_iff of_rat_eq_iff 
          verit_comp_simplify1(1) max_val_wrap_lemma assms(2) assms(6) calculation by auto
  then show ?thesis
    using assms(3) by blast
next
  case False
  have "sl rec ! index (p rec) party1 > sl rec ! index (p rec) party2" 
    using False le_neq_implies_less assms(7) leI le_antisym by linarith
  then have "index (p rec) party2 = index (p rec) (hd ( get_winners (fv rec) (p rec)))" 
    using assms(3) by blast
  then have "sl (assign_seats rec) ! index (p rec) party2 = 
             sl rec ! index (p rec) party2 + 1" 
    using \<open>index (p rec) party2 = index (p rec) (hd (get_winners (fv rec) (p rec)))\<close> 
          assign_seats_seats_increased False assms(8) assms(11) by metis
  then have "sl (assign_seats rec) ! index (p rec) party1 = sl rec ! index (p rec) party1" 
    using assign_seats_not_winner_mantains_seats False assms(10) assms(3) by metis
  then show ?thesis 
    using \<open>sl (assign_seats rec) ! index (p rec) party2 = sl rec ! index (p rec) party2 + 1\<close> 
          \<open>sl rec ! index (p rec) party2 < sl rec ! index (p rec) party1\<close> by linarith
qed

lemma assign_seats_ccontr:
  fixes
  v1::"rat" and v2::"rat"
assumes 
  "index (p rec) party1 < length (fv rec)" and
  "v1 > v2" and
  "party2 = hd ( get_winners (fv rec) (p rec))" and
  "fv rec ! index (p rec) party1 = v1 / of_int (d rec ! (sl rec ! index (p rec) party1))" and
  "fv rec ! index (p rec) party2 = v2 / of_int (d rec ! (sl rec ! index (p rec) party2))" and
  "d rec ! (sl rec ! index (p rec) party2) \<noteq> 0" and
  "sl rec ! index (p rec) party1 \<ge> sl rec ! index (p rec) party2" and
  "get_winners (fv rec) (p rec) \<noteq> []" and
  "index (p rec) party1 < length (sl rec)" and
  "index (p rec) party2 < length (sl rec)"
shows "sl (assign_seats rec) ! index (p rec) party1 \<ge> 
       sl (assign_seats rec) ! index (p rec) party2"
proof(cases "length (get_winners (fv rec) (p rec)) \<le> ns rec")
  case True
  then show ?thesis 
    using True assign_seats_helper_lemma_cond_ver assms(1) assms(8) assms(9) 
          assms(10) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) by metis
next
  case False
   define rec''
    where 
     "rec''= break_tie ( get_winners (fv rec) (p rec)) rec" 
   have "sl (assign_seats rec) = sl rec''"  
     using False rec''_def by simp
   then show ?thesis 
     using assms(7) break_tie_lemma rec''_def by metis
qed

text \<open> Concordance Theorem. 
       The concordance theorem states that if there are two candidates, the "stronger" 
       will end with at least the same number of seats of the "weaker" party. \<close>
 
theorem assign_seats_concordant:
  fixes
  v1::"rat"
assumes 
  "index (p rec) party1 < length (fv rec)" and
  "index (p rec) party2 < length (fv rec)" and
  "v1 > v2" and
  "party1 \<in> set (p rec)" and
  "party2 \<in> set (p rec)" and
  "get_winners (fv rec) (p rec) \<noteq> []" and
  "fv rec ! index (p rec) party1 = 
    v1 / of_int (d rec ! (sl rec ! index (p rec) party1))" and
  "fv rec ! index (p rec) party2 = 
    v2 / of_int (d rec ! (sl rec ! index (p rec) party2))" and
  "sl rec ! (index  (p rec) party1) \<ge> sl rec ! (index  (p rec) party2)" and
  "d rec ! (sl rec ! (index  (p rec) party2)) \<noteq> 0" and
  "index (p rec) party1 < length (sl rec)" and
  "index (p rec) party2 < length (sl rec)"
shows "sl (assign_seats rec) ! index (p rec) party1 \<ge> 
       sl (assign_seats rec) ! index (p rec) party2"
proof(cases "length (get_winners (fv rec) (p rec)) \<le> ns rec")
  case True  \<comment> \<open>commment\<close> 
  (* let ?x = *)
  then show ?thesis 
      proof(cases "party1 = hd (get_winners (fv rec)  (p rec))")
        case True
        have "sl (assign_seats rec) ! ( index (p rec) party1) = 
              (sl rec) ! (index (p rec) party1) + 1" 
          using  \<open>length ( get_winners (fv rec)  (p rec)) \<le> ns rec\<close> 
                  True assign_seats_seats_increased assms(11) by blast
        also have "sl (assign_seats  rec) ! index (p rec) party2 = 
                   sl rec ! index (p rec) party2"
          using True assign_seats_not_winner_mantains_seats add.right_neutral 
                add_less_same_cancel1 divide_cancel_right divide_less_cancel 
                of_int_of_nat_eq of_nat_eq_0_iff assms(10) assms(12) assms(3) 
                assms(6) assms(7) assms(8) get_winners_not_in_win
        by (metis (no_types, lifting))
        then show ?thesis
          using calculation trans_le_add1 assms(9) by presburger
      next
        case False
        then show ?thesis
        proof(cases "party2 = hd ( get_winners (fv rec) (p rec))")
          case True
          then show ?thesis 
            using True assign_seats_ccontr assms(1) assms(10) assms(11) assms(12)
                  assms(2) assms(3) assms(6) assms(7) assms(8) assms(9) by metis
        next
          case False
          have "party2 \<noteq> hd ( get_winners (fv rec) (p rec))" 
            using False by simp
          then have "index (p rec) (hd ( get_winners (fv rec) (p rec))) \<noteq>  
                     index (p rec) party2" 
            using False index_diff_elements assms(5) by metis
          then have "sl (assign_seats rec) ! ( index (p rec) party2) = 
                     (sl rec) ! ( index (p rec) party2)"
            using False assms(12)
                  assign_seats_not_winner_mantains_seats by metis
          have "party1 \<noteq> hd (get_winners (fv rec) (p rec))" 
            using \<open>party1 \<noteq> hd (get_winners (fv rec) (p rec))\<close> by simp
          then have "index (p rec) (hd (get_winners (fv rec) (p rec))) \<noteq> 
                      index (p rec) party1" 
            using index_diff_elements False assms(4) by metis           
        then have "sl (assign_seats rec) ! ( index (p rec) party1) = 
                    (sl rec) ! ( index (p rec) party1)"
            using \<open>party1 \<noteq> hd ( get_winners (fv rec)  (p rec))\<close> 
                  assign_seats_not_winner_mantains_seats assms(11) by metis
          then show ?thesis
            using \<open>sl (assign_seats rec) ! index (p rec) party2 = 
                   sl rec ! index (p rec) party2\<close> assms(9) by presburger
        qed
      qed
next
  case False
  define rec''
    where 
     "rec''= break_tie ( get_winners (fv rec) (p rec)) rec" 
  have "assign_seats rec = \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>" 
    using rec''_def assign_seats.simps False by auto
  then have "sl (assign_seats rec) = sl rec''"  
    using False rec''_def by simp
  then have "sl (assign_seats rec) ! index (p rec) party1 = 
              sl rec'' ! index (p rec) party1" 
    by simp
  then have "... = sl rec ! (index (p rec) party1)"
    using break_tie_lemma rec''_def by metis
  also have "sl (assign_seats rec) ! (index (p rec) party2) = 
              sl rec ! index (p rec) party2"
     using \<open>sl (assign_seats rec) = sl rec''\<close> break_tie_lemma rec''_def by metis
  then show ?thesis
  using False assms \<open>sl (assign_seats rec) ! index (p rec) party1 = 
          sl rec'' ! index (p rec) party1\<close> calculation by metis
qed

lemma assign_seats_incre_case_helper:
assumes 
  "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> fv rec ! y \<le> Max(set (fv rec))"
  and  
  "Max(set (fv rec')) > Max(set (fv rec))"
shows 
  "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> fv rec ! y < Max(set (fv rec'))"
  using assms dual_order.trans leD linorder_le_less_linear by meson

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party after 
       increasing votes wins the round. \<close>
lemma assign_seats_incre_case_TTTq:
assumes 
  "p rec = p rec'" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec')" and
  "party \<in> set (p rec)" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (sl rec')" and 
  "length winners' \<le> ns rec'" and
  "length winners \<le> ns rec" and
  "party = hd (winners')"
shows "sl (assign_seats rec') ! (index (p rec) party) \<ge> 
       sl (assign_seats rec) ! (index (p rec) party)"
proof(cases "party = hd winners")
  case True
  have "sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1"
    using assign_seats_seats_increased assms(1) assms(10) assms(3) assms(7) assms(8) 
    by metis
  have "sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party + 1" 
    using True assign_seats_seats_increased assms(2) assms(6) assms(9) by blast
  then show ?thesis
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1\<close>
    assms(5) by linarith
next
  case False
  have "sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1" 
  using assign_seats_seats_increased assms(1) assms(10) assms(3) assms(7) assms(8)
  by metis
  have "sl (assign_seats  rec) ! index (p rec) party = sl rec ! index (p rec) party" 
    using False assign_seats_not_winner_mantains_seats assms(2) assms(4) assms(6) 
          index_eq_index_conv by metis
  then show ?thesis
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1\<close>
         using assms(5) by linarith 
qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case there is a tie in both 
       between the cases, before and after increasing votes of the party. \<close>
lemma assign_seats_incre_case_FFqq:
assumes 
  "p rec = p rec'" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "length winners' > ns rec'" and
  "length winners > ns rec"
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
  using assign_seats_break_tie_case assms by metis

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party wins the round 
       both before and after increasing its votes. \<close>
lemma assign_seats_incre_case_TqTT:
  fixes
    v::"rat"
assumes 
  "p rec = p rec'" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "sl rec = sl rec'" and
   "index (p rec) party < length (sl rec')" and 
  "length winners' \<le> ns rec'" and
  "party = hd (winners')" and
  "party = hd (winners)"
shows "sl (assign_seats rec') ! (index (p rec) party) \<ge> 
       sl (assign_seats rec) ! (index (p rec) party)"
proof(cases "length winners \<le> ns rec")
  case True
  have "sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1"
    using assign_seats_seats_increased assms(1) assms(3) assms(5) assms(6) assms(7)
    by metis 
  then have "sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party + 1"
    using True assign_seats_seats_increased assms(2) assms(4) assms(5) assms(8) by metis 
  then show ?thesis
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1\<close> 
    order_refl assms(4) by presburger
  next
  case False
  have "sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1"
    using assign_seats_seats_increased assms(1) assms(3) assms(5) assms(6) assms(7)
    by metis
  then have "sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party"
    using False assign_seats_break_tie_case assms(2) less_or_eq_imp_le linorder_neqE_nat 
    by metis 
  then show ?thesis 
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party + 1\<close> 
    le_add1 assms(4) by presburger
qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party is winning 
       the round after increasing votes. \<close>

lemma assign_seats_incre_case_TqTq:
assumes 
  "p rec = p rec'" and
  "winners' = get_winners (fv rec') (p rec)" and
  "party \<in> set (p rec)" and
  "sl rec = sl rec'" and
  "sl rec' ! (index (p rec) party) \<ge> sl rec ! (index (p rec) party)" and
  "index (p rec) party < length (sl rec')" and 
  "length winners' \<le> ns rec'" and
  "party = hd (winners')"
shows "sl (assign_seats rec') ! (index (p rec) party) \<ge> 
       sl (assign_seats rec) ! (index (p rec) party)"
  using assign_seats_break_tie_case assign_seats_incre_case_TTTq assign_seats_mon 
        linorder_le_less_linear assms by metis

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party before 
       increasing votes wins the round and after increasing votes ends in a tie. 
       This is a particular case of the following lemma. \<close>
lemma assign_seats_incre_case_FTqT:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec')" and
  "winners \<noteq> []" and "winners' \<noteq> []" and
  "p rec \<noteq> []" and
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "length (fv rec) = length (fv rec')" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index  (p rec) party" and
  "d rec ! (sl rec ! index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' ! index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = 
   length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow> (fv rec') ! x \<le> (fv rec) ! x" and
  "ns rec = ns rec'" and
  "length winners' > ns rec'" and
  "length winners \<le> ns rec" and
  "party = hd winners" and
  "p rec = p rec'"
shows "sl (assign_seats rec') ! index  (p rec) party \<ge> 
       sl (assign_seats rec) ! index  (p rec) party"
proof - 
  have "sl (assign_seats rec') = sl rec'"
    using assign_seats_break_tie_case assms(24) assms(3) by metis
  then show ?thesis 
  proof(cases "sl rec' ! index  (p rec) party > sl rec ! index  (p rec) party")
   case True
   then have "sl rec' ! index (p rec) party = sl (assign_seats rec') ! index (p rec) party"
     using \<open>sl (assign_seats rec') = sl rec'\<close> by presburger
   then have "sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party + 1" 
     using assign_seats_seats_increased assms(2) assms(20) assms(25) assms(26) by blast
   then show ?thesis 
     using Suc_eq_plus1 True \<open>sl (assign_seats rec') = sl rec'\<close> less_eq_Suc_le by metis
  next
   case False \<comment> \<open> per assurdo \<close>
   then have "(fv rec) ! index (p rec) party = Max(set (fv rec))" 
     using assms(2) assms(26) assms(4) get_winners_not_in_win max_v.elims by metis
   then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> 
              fv rec ! y \<le> Max(set (fv rec))" 
      by auto
   then have "Max(set (fv rec')) = (fv rec') ! index (p rec) party" 
     using \<open>fv rec ! index (p rec) party = Max(set (fv rec))\<close> max_eqI False 
            Fract_of_int_eq Fract_of_nat_eq divide_less_cancel int_ops(1) 
            nat_less_le negative_eq_positive of_nat_less_0_iff of_nat_less_of_int_iff
            assms(11) assms(12) assms(13) assms(14) assms(16) assms(21) assms(22) assms(9)
      by (smt (verit, ccfv_threshold))
   then have "fv rec' ! index (p rec') party = m'"
     using assms(1) assms(27) by presburger 
   then have "Max(set (fv rec')) > Max(set (fv rec))"
     using False \<open>fv rec ! index (p rec) party = Max (set (fv rec))\<close> assms(1) assms(11) 
       assms(12) assms(13) assms(14) assms(16) assms(27) divide_strict_right_mono 
       of_nat_le_0_iff by force
   then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
              \<Longrightarrow> (fv rec) ! y < Max(set (fv rec'))"
     using \<open>Max(set (fv rec')) > Max(set (fv rec))\<close> assign_seats_incre_case_helper
      \<open>\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
              \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))\<close>    
     by metis
   then have "\<And>x. x \<noteq> index (p rec') party \<Longrightarrow> x < length (fv rec') \<Longrightarrow> (fv rec') ! x < m'" 
     using assms(1) assms(22) assms(27) assms(9) leD linorder_le_less_linear 
      max_v.simps max_val_wrap_lemma order_antisym_conv by metis
  then have "length (winners') = 1"
    using assms \<open>Max(set (fv rec')) = (fv rec') ! index (p rec) party\<close>
      \<open>fv rec' ! index (p rec') party = m'\<close> 
      \<open>\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> (fv rec') ! y < m'\<close>
      filter_size_is_one_helper_my_case_3 by metis
  then have "length winners' \<le> length winners" 
    using assms(4) leI length_0_conv less_one by metis
  then show ?thesis
    using linorder_not_less assms(10) assms(23) assms(24) assms(25) by linarith
 qed
qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party before 
       increasing votes wins the round and after increasing votes ends in a tie. \<close>
lemma assign_seats_incre_case_FT:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec')" and
  "winners \<noteq> []" and "winners' \<noteq> []" and
  "p rec \<noteq> []" and
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "length (fv rec) = length (fv rec')" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "d rec ! (sl rec ! index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' ! index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) 
   = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow> fv rec' ! x \<le> fv rec ! x" and
  "ns rec = ns rec'" and
  "length winners' > ns rec'" and
  "length winners \<le> ns rec" and
  "p rec = p rec'"
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "party = hd winners")
  case True \<comment> \<open>FTTT \<close>
  then show ?thesis 
    using assms True assign_seats_incre_case_FTqT by metis
    next
  case False \<comment> \<open>FTTF\<close>
  then show ?thesis 
    using assign_seats_break_tie_case assign_seats_not_winner_mantains_seats 
          index_correct  assms(14) assms(2) assms(20) assms(21) assms(24) assms(3) assms(7) 
    by metis 
qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party before 
       increasing votes ends in a tie. \<close>
lemma assign_seats_case_TFqq:
assumes
  "winners = get_winners (fv rec) (p rec)" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "index (p rec) party < length (sl rec')" and 
  "length winners > ns rec"
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof -
  have "sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party" 
    using assign_seats_break_tie_case assms(1) assms(4) by metis
  then have "sl (assign_seats rec') ! index (p rec) party \<ge> sl rec' ! index (p rec) party"
    using assign_seats_mon assms(3) by blast
  then show ?thesis
    using \<open>sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party\<close>
          assms(2) by linarith
qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party before 
       increasing votes wins but it does not after increasing votes. \<close>
lemma assign_seats_incre_case_T:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "winners \<noteq> []" and 
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "d rec ! (sl rec' !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) 
   = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow>fv rec' ! x \<le> fv rec ! x" and
  "length winners \<le> ns rec" and
  "party \<noteq> hd (winners')" and
  "party = hd winners" and
  "p rec = p rec'" 
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "(sl rec) ! index (p rec) party = (sl rec') ! index (p rec) party")
  case True
  have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
        \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))" 
    by simp
    then have "fv rec' ! index (p rec) party > fv rec ! index (p rec) party" 
      using divide_strict_right_mono True of_int_0_less_iff of_nat_le_0_iff
            assms(8) assms(9) assms(10) assms(12) by fastforce
    then have "fv rec ! index (p rec) party = Max(set (fv rec))" 
      using \<open>party = hd winners\<close> assms(2)assms(21) assms(7) assms(20) assms(4) assms(8) 
        get_winners_loss hd_in_set by metis
     then have "Max(set (fv rec')) > Max(set (fv rec))"
       using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> assms(15) 
             assms(21) max_v.elims dual_order.strict_trans1 
             get_winners_weak_winner_implies_helper
     by metis
     then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
                \<Longrightarrow> fv rec ! y < Max(set (fv rec'))"
    using \<open>Max(set (fv rec')) > Max(set (fv rec))\<close>
      \<open>\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
            \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))\<close>    
    assign_seats_incre_case_helper by metis
  then have "\<And>x. x \<noteq> index (p rec') party \<Longrightarrow> x < length (fv rec') \<Longrightarrow> (fv rec') ! x < m'" 
    using assms(1) assms(17) assms(21) assms(5) assms(6) leD linorder_le_less_linear 
      max_v.simps max_val_wrap_lemma order_antisym_conv by metis
  then have "(fv rec') ! index (p rec') party = m'"
    using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> 
          \<open>fv rec ! index (p rec) party = Max (set (fv rec))\<close> assms(1) assms(15) assms(17) 
          assms(21) assms(5) assms(6) max_eqI by metis
  then have "party = hd (get_winners (fv rec') (p rec))"
    using assms(7) assms(15) assms(1) assms(14) \<open>(fv rec') ! index (p rec') party = m'\<close>
          \<open>\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> (fv rec') ! y < m'\<close>
          get_winners_size_one assms(21) by metis
  then show ?thesis
  using assms(19) assms(3) by blast
next
  case False
  then have "sl rec' ! (index  (p rec) party) > sl rec ! index (p rec) party" 
    using False assms(11) le_neq_implies_less by blast
  then have "sl (assign_seats rec') ! index  (p rec) party = sl rec' ! index (p rec) party"
    using assign_seats_not_winner_mantains_seats assms(13) assms(19) 
      assms(21) assms(3) assms(7) index_eq_index_conv by metis
  then have "sl (assign_seats rec) ! index  (p rec) party = sl rec ! index (p rec) party + 1"
    using assign_seats_seats_increased assms(16) assms(2) assms(18) \<open>party = hd winners\<close> 
    by blast
  then show ?thesis
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party\<close> 
          \<open>sl rec ! index (p rec) party < sl rec' ! index (p rec) party\<close> by linarith
  qed 

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party does not win
       in both cases. \<close>
lemma assign_seats_incre_case_F:
  fixes
  v::"rat"
assumes 
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "party \<in> set (p rec')" and
  "sl rec' ! (index  (p rec) party) \<ge> sl rec ! (index  (p rec) party)" and
  "index (p rec) party < length (sl rec')" and 
  "index (p rec) party < length (sl rec)" and
  "party \<noteq> hd (winners')" and
  "party \<noteq> hd (winners)" and
  "p rec = p rec'" 
shows "sl (assign_seats rec') ! (index  (p rec) party) \<ge> 
       sl (assign_seats rec) ! (index  (p rec) party)"
proof - 
 have "sl (assign_seats rec') ! (index  (p rec) party) = sl rec' ! index (p rec) party" 
   using assign_seats_not_winner_mantains_seats assms(7) assms(9) assms(2) assms(3) 
         assms(5) index_diff_elements by metis
  then have "sl (assign_seats rec) ! (index  (p rec) party) = sl rec ! index (p rec) party" 
    using assign_seats_not_winner_mantains_seats assms(1) assms(8) assms(9) assms(3) 
          assms(6) index_diff_elements by metis
  then show ?thesis
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party\<close> 
      assms(4) by presburger
qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is proving monotonicity property holds in the case the party is not the 
       winner after increasing the votes. \<close>
lemma assign_seats_incre_case_TTFq:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "winners \<noteq> []" and "winners' \<noteq> []" and
  "p rec \<noteq> []" and
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index  (p rec) party \<ge> sl rec ! index  (p rec) party" and
  "d rec ! (sl rec !  index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) 
   = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow>(fv rec') ! x \<le> (fv rec) ! x" and
  "length winners' \<le> ns rec'" and
  "length winners \<le> ns rec" and
  "party \<noteq> hd (winners')" and
  "p rec = p rec'" 
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "party = hd winners")
  case True \<comment> \<open>T\<close>
  then show ?thesis 
proof(cases "(sl rec) ! index (p rec) party = (sl rec') ! index (p rec) party")
  case True
  have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
        \<Longrightarrow> fv rec ! y \<le> Max(set (fv rec))" 
    by simp
    then have "fv rec' ! index (p rec) party > fv rec ! index (p rec) party" 
      using divide_strict_right_mono True of_int_0_less_iff of_nat_le_0_iff
            assms(10) assms(11) assms(12) assms(15) by fastforce
    then have "fv rec ! index (p rec) party = Max(set (fv rec))" using \<open>party = hd winners\<close>
      using assms(2) assms(25) assms(4) assms(9) get_winners_loss hd_in_set by metis
     then have "Max(set (fv rec')) > Max(set (fv rec))"
       using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> assms(18) 
             assms(25) max_v.elims get_winners_weak_winner_implies_helper 
             order_less_le_trans by metis
     then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
                \<Longrightarrow> (fv rec) ! y < Max(set (fv rec'))"
       using \<open>Max(set (fv rec')) > Max(set (fv rec))\<close> assign_seats_incre_case_helper
       \<open>\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
        \<Longrightarrow> fv rec ! y \<le> Max(set (fv rec))\<close>    
       by metis
  then have "\<And>x. x \<noteq> index (p rec') party \<Longrightarrow> x < length (fv rec') \<Longrightarrow> fv rec' ! x < m'" 
    using assms(1) assms(21) assms(25) assms(7) assms(8) leD linorder_le_less_linear 
          max_v.simps max_val_wrap_lemma order_antisym_conv by metis
  then have "(fv rec') ! index (p rec') party = m'"
    using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> 
          \<open>fv rec ! index (p rec) party = Max (set (fv rec))\<close> assms(1) assms(18) assms(21) 
          assms(25) assms(7) assms(8) max_eqI by metis 
  then have "party = hd (get_winners (fv rec') (p rec))"
    using assms(9) assms(18) assms(1) \<open>(fv rec') ! index (p rec') party = m'\<close>
          \<open>\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> (fv rec') ! y < m'\<close>
          assms(17) assms(25) get_winners_size_one filter_cong by metis
  then show ?thesis
    using assms(24) assms(3) by blast
next
  case False
  then have "sl rec' ! (index  (p rec) party) > sl rec ! index (p rec) party" 
    using False assms(13) le_neq_implies_less by blast
  then have "sl (assign_seats rec') ! (index  (p rec) party) = sl rec' ! index (p rec) party"
    using assign_seats_not_winner_mantains_seats assms(16) assms(24) assms(25) assms(3) 
          assms(9) index_eq_index_conv by metis
  then have "sl (assign_seats rec) ! index (p rec) party = sl rec ! index (p rec) party + 1"
    using assign_seats_seats_increased assms(19) assms(2) assms(23) \<open>party = hd winners\<close> 
    by blast
  then show ?thesis
    using \<open>sl (assign_seats rec') ! index (p rec) party = sl rec' ! index (p rec) party\<close> 
          \<open>sl rec ! index (p rec) party < sl rec' ! index (p rec) party\<close> by linarith
  qed 
next
  case False \<comment> \<open>F\<close>
  then show ?thesis
    using assign_seats_incre_case_F False 
        assms(13) assms(16) assms(19) assms(2) assms(24) assms(25) assms(3) assms(9)
    by (metis (no_types, lifting))
  qed

text \<open> This lemma is one specific case of the monotonicity property written later. 
       It is grouping some of the lemmas above in a more generic structure than the 
       ones above, to help the final lemma. \<close>
lemma assign_seats_incre_case_TTqq:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "winners \<noteq> []" and "winners' \<noteq> []" and
  "p rec \<noteq> []" and
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index  (p rec) party \<ge> sl rec ! index (p rec) party" and
  "d rec ! (sl rec ! index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' ! index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) 
   = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow>(fv rec') ! x \<le> (fv rec) ! x" and
  "length winners' \<le> ns rec'" and
  "length winners \<le> ns rec" and
  "p rec = p rec'" 
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "party = hd winners'")
  case True
  then show ?thesis 
    using True assign_seats_incre_case_TTTq assms(13) assms(16) assms(19) assms(2) 
          assms(22) assms(23) assms(24) assms(3) assms(9) by metis
next
  case False
  then show ?thesis 
    using \<open>party \<noteq> hd winners'\<close> assms assign_seats_incre_case_TTFq by metis
qed

text \<open> This lemma is one specific case of the monotonicity property written later, 
       it is a more generic case that will use some lemmas above and will be used in the 
       most generic lemma later. \<close>
lemma assign_seats_monotone_case_T:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec)" and
  "winners \<noteq> []" and "winners' \<noteq> []" and
  "p rec \<noteq> []" and
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "d rec ! (sl rec ! index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' ! index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = 
   length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])" and
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow>(fv rec') ! x \<le> (fv rec) ! x" and
  "length winners' \<le> ns rec'" and
  "p rec = p rec'"
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "length winners \<le> ns rec")
  case True
  then show ?thesis using \<open>length winners \<le> ns rec\<close> assms 
                    assign_seats_incre_case_TTqq by metis
next
  case False
  then show ?thesis
    using assign_seats_case_TFqq assms(13) assms(16) assms(2) linorder_le_less_linear 
    by metis
qed

text \<open> Monotonicity Theorem.
       The monotonicity property states that if one party gets the votes increased, then it
       cannot end with less number of seats it had before the increase. \<close>
lemma assign_seats_monotone:
  fixes
  v::"rat"
assumes 
  "m' = Max(set (fv rec'))" and
  "winners = get_winners (fv rec) (p rec)" and
  "winners' = get_winners (fv rec') (p rec')" and
  "winners \<noteq> []" and "winners' \<noteq> []" and
  "p rec \<noteq> []" and
  "size (fv rec) = size (p rec)" and 
  "size (fv rec') = size (p rec)" and
  "length (fv rec) = length (fv rec')" and
  "party \<in> set (p rec')" and
  "v' > v" and
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index (p rec) party))" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "(d rec) ! ((sl rec) !  index (p rec) party) \<noteq> 0" and
  "(d rec) ! ((sl rec') !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) 
    = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])" and
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow> fv rec' ! x \<le> fv rec ! x" and
  "ns rec = ns rec'" and
  "p rec = p rec'"
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "length winners' \<le> ns rec'")
  case True \<comment> \<open>T\<close>
  then show ?thesis using \<open>length winners' \<le> ns rec'\<close> assms 
                          assign_seats_monotone_case_T by metis
  next
  case False  \<comment> \<open>F\<close>
  then have "length winners' > ns rec'" 
    using False by simp
  then show ?thesis 
  proof(cases "length winners \<le> ns rec")
    case True  \<comment> \<open>FT\<close>
    then show ?thesis 
      using \<open>length winners'>ns rec'\<close> \<open>length winners \<le> ns rec\<close> assms 
        assign_seats_incre_case_FT by metis
  next
    case False \<comment> \<open>FF\<close>
    then show ?thesis 
      using False assign_seats_break_tie_case assms
            linorder_le_less_linear assign_seats_case_TFqq 
      by metis
  qed
qed

text \<open> This lemma states that the number of available seats is decreasing after calling
       assign seats function. It helps the termination proof of the loop of Divisor Module. \<close>

lemma nseats_decreasing:
  assumes 
   non_empty_parties: "p rec \<noteq> []" and
   n_positive: "(ns rec) > 0"
  shows "ns (assign_seats rec) < ns rec"
proof (cases "length (get_winners (fv rec) (p rec)) \<le> ns rec")
  case True
  then have "ns (assign_seats rec) = ns rec - 1"
    by (auto simp add: Let_def)
  also have "... < ns rec" 
    using True n_positive non_empty_parties by simp
  finally show ?thesis .
next
  case False
  then have "ns (assign_seats rec) = 0"
    by (auto simp add: Let_def)
  also have "... < ns rec" using n_positive
    by simp
  finally show ?thesis .
qed

end