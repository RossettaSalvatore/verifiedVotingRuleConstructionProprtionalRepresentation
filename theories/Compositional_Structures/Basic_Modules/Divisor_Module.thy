

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

abbreviation ass_r :: "'a Result \<Rightarrow> 'a set" where
  "ass_r r \<equiv> fst r"

abbreviation disp_r :: "'a Result \<Rightarrow> 'a set" where
  "disp_r r \<equiv> snd (snd r)"

subsection \<open> Definition \<close>

text \<open> This function updates the "fractional votes" of the winning party, dividing 
       the starting votes by the i-th parameter, where i is the number of seats won 
       by the party. \<close>

fun upd_votes ::  "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       rat list" where 
"upd_votes winner r = 
    (let ind = index (p r) (hd winner);
     n_seats = cnt_seats winner (s r) (i r);
     n_v = of_nat(get_votes (hd winner) (p r) (v r)) / of_int(d r ! n_seats) in
     list_update (fv r) ind n_v)"

text \<open> This function moves one seat from the disputed set to the assigned set. Moreover,
       returns the record with updated Seats function and "fractional" Votes entry 
       for the winning party. \<close>

fun upd_round :: "'b list \<Rightarrow> ('a::linorder, 'b) Divisor_Module \<Rightarrow>
                       ('a::linorder, 'b) Divisor_Module" where 
"upd_round winner rec =
  (let 
    seat = Min (disp_r (res rec));
    new_s = update_seat seat winner (s rec);
    new_as = ass_r (res rec) \<union> {seat};
    new_fv = upd_votes winner (rec\<lparr>s:= new_s\<rparr>);
    index = index (p rec) (hd winner);
    curr_ns = (sl rec) ! index;
    new_sl = list_update (sl rec) index ( (sl rec) ! index + 1);
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

(* this lemma shows that for every update of assign_seat, all the other 
   parties still have the same seats *)
lemma assign_seat_mantain_seats_lemma:
  assumes 
"i1 = index (p rec) (hd winner)" and
"i2 \<noteq> i1"
shows "sl (upd_round winner rec) ! i2 = sl rec ! i2"
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
    using nth_list_update_eq curr_ns_def ind_def new_as_def new_di_def new_fv_def 
          new_s_def seat_def by fastforce
  then have "sl (upd_round winner rec) = new_sl" 
    by simp
  then have "... =  list_update (sl rec) ind (curr_ns + 1)" 
    using new_sl_def by simp
  then have "sl (upd_round winner rec) ! i2 = list_update (sl rec) ind (curr_ns + 1) ! i2"
    using \<open>sl (upd_round winner rec) = new_sl\<close> by presburger
  then have "... = (sl rec) ! i2" 
    using nth_list_update_neq ind_def assms(1) assms(2) by metis
  then show ?thesis
  using \<open>sl (upd_round winner rec) ! i2 = (sl rec)[ind := curr_ns + 1] ! i2\<close> by presburger
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
 
lemma break_tie_lemma_party:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
shows "sl (break_tie winner rec) ! ind \<ge> sl rec ! ind" by simp

fun create_seats :: "'a::linorder set \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 'b list \<Rightarrow>
                      ('a::linorder, 'b) Seats" where
  "create_seats def seats pa = (\<lambda>x. if x \<in> def then pa else seats x)"
                          
text \<open>This function checks whether there are enough seats for all the winning parties.
      - If yes, assign one seat to the first party in the queue.
      - If not, assign all remaining seats to the winning parties, making these seats 
        "disputed".\<close>
fun assign_seats :: "('a::linorder, 'b) Divisor_Module
                        \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"assign_seats rec = (
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
                        \<rparr>)"

lemma assign_seats_break_tie_case:
  assumes 
    "winners = get_winners (fv rec) (p rec)" and
    "length winners > ns rec"
  shows "sl rec = sl (assign_seats rec)" using assms by simp

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

(* increase vote v \<rightarrow> v' if v' does not get seat then also v does not *)
lemma get_winners_mon:
  fixes 
    v::"rat"
  assumes 
  "party \<in> set (p rec)" and
  "ip = index (p rec) party" and
  "v' > v" and
  "(fv rec) ! ip = v / of_nat dp" and
  "(fv rec') ! ip = v' / of_nat dp" and
  "max_val_wrap (fv rec) = max_val_wrap (fv rec')" and
  "max_val_wrap (fv rec') > (fv rec') ! ip"
shows "party \<notin> set (get_winners (fv rec) (p rec))"
proof - 
  have "max_val_wrap (fv rec') > (fv rec') ! ip" 
    using assms(7) by auto
  then have "... > (fv rec) ! ip"
    using  divide_le_cancel dual_order.strict_trans2 nless_le of_nat_less_0_iff
     assms(3) assms(4) assms(5) by metis
  then have "max_val_wrap (fv rec) = max_val_wrap (fv rec')"
    using assms(6) by blast
  then have "max_val_wrap (fv rec) > (fv rec) ! ip" 
    using \<open>fv rec ! ip < max_val_wrap (fv rec')\<close> by linarith
  then show ?thesis 
    using add.comm_neutral add_le_same_cancel1 get_winners_loss le_numeral_extra(3) 
          max_val_wrap.simps verit_comp_simplify1(3) assms(1) assms(2) by metis
qed

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

(* lemma che dice che se ho gli stessi seat (sl rec ! i1) = (sl rec ! i2) 
ma v1 > v2 allora party2 non può essere il vincitore *)
lemma assign_seats_helper_lemma_helper:
  fixes 
  v1::"rat"
assumes
  "m \<equiv> max_val_wrap (fv rec)" and
  "i2 \<equiv> index  (p rec) party2" and
  "fv1 \<equiv> (fv rec) ! i1" and
  "fv2 \<equiv> (fv rec) ! i2" and
  "winners \<equiv> get_winners (fv rec) (p rec)" and
  "winners \<noteq> []" and
  "i1 < length (fv rec)" and
  "v1 > v2" and
  "fv1 \<equiv> v1 / (of_int ((d rec) ! ((sl rec) ! i1)))" and
  "fv2 \<equiv> v2 / (of_int ((d rec) ! ((sl rec) ! i2)))" and
  "(d rec) ! ((sl rec) ! i2) \<noteq> 0" and
  "sl rec ! i1 = sl rec ! i2" and
  "i1 \<noteq> i2" and
  "i1 < length (sl rec)" and
  "i2 < length (sl rec)"
  shows "party2 \<noteq> hd (winners)"
proof (cases "fv1 = max_val_wrap (fv rec)")
  case True
  then have "fv1 > fv2" 
    using divide_strict_right_mono assms(10) assms(11) assms(12) assms(8) assms(9) by force
  then have "fv2 \<noteq> max_val_wrap (fv rec)" 
    using True dual_order.irrefl by simp
  then have "(fv rec) ! (index  (p rec) party2) \<noteq> m" 
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
  then have "max_val_wrap (fv rec) > fv1" 
    using False less_eq_rat_def max_val_wrap_lemma assms(3) assms(7) by blast
  then have "max_val_wrap (fv rec) \<noteq> fv2" 
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
  "party2 = hd ( get_winners (fv rec) (p rec))" and
  "fv rec ! index  (p rec) party1 \<equiv> v1 / of_int ((d rec) ! (sl rec ! index (p rec) party1))" and
  "fv rec ! index  (p rec) party2 \<equiv> v2 / of_int ((d rec) ! (sl rec ! index (p rec) party2))" and
  "(d rec) ! (sl rec !  index (p rec) party2) \<noteq> 0" and
  "sl rec ! index (p rec) party1 \<ge> sl rec ! index (p rec) party2" and
  "length (get_winners (fv rec) (p rec)) \<le> ns rec" and
  "get_winners (fv rec) (p rec) \<noteq> []" and 
  "index (p rec) party1 < length (sl rec)" and
  "index (p rec) party2 < length (sl rec)"
shows "sl (assign_seats rec) ! index (p rec) party1 \<ge> 
       sl (assign_seats rec) ! index (p rec) party2"
proof(cases "sl rec ! index (p rec) party1 = sl rec ! index (p rec) party2")
  case True \<comment> \<open> prova per assurdo  \<close>
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
  have "sl rec ! (index (p rec) party1) > sl rec ! (index (p rec) party2)" 
    using False le_neq_implies_less assms(7) leI le_antisym by linarith
  then have "(index (p rec) party2) = index (p rec) (hd ( get_winners (fv rec) (p rec)))" 
    using assms(3) by blast
  then have "sl (assign_seats rec) ! ((index (p rec) party2)) = sl rec ! ((index (p rec) party2)) + 1" 
    using \<open>(index (p rec) party2) = index (p rec) (hd (get_winners (fv rec) (p rec)))\<close> 
          assign_seats_seats_increased False assms(8) assms(11) by metis
  then have "sl (assign_seats rec) ! ( (index (p rec) party1)) = sl rec ! ( (index (p rec) party1))" 
    using assign_seats_not_winner_mantains_seats False assms(10) assms(3) by metis
  then show ?thesis 
    using \<open>sl (assign_seats rec) ! ( (index (p rec) party2)) = sl rec ! ( (index (p rec) party2)) + 1\<close> 
          \<open>sl rec ! ( (index (p rec) party2)) < sl rec ! ( (index (p rec) party1))\<close> by linarith
qed

lemma assign_seats_ccontr:
  fixes
  v1::"rat" and v2::"rat"
assumes 
  "index (p rec) party1 < length (fv rec)" and
  "v1 > v2" and
  "party2 = hd ( get_winners (fv rec) (p rec))" and
  "fv rec ! index (p rec) party1 = v1 / of_int ((d rec) ! (sl rec ! index (p rec) party1))" and
  "fv rec ! index (p rec) party2 = v2 / of_int ((d rec) ! (sl rec ! index (p rec) party2))" and
  "(d rec) ! ((sl rec) ! index (p rec) party2) \<noteq> 0" and
  "sl rec ! index (p rec) party1 \<ge> sl rec ! index (p rec) party2" and
  "get_winners (fv rec) (p rec) \<noteq> []" and
  "index (p rec) party1 < length (sl rec)" and
  "index (p rec) party2 < length (sl rec)"
shows "sl (assign_seats rec) ! index (p rec) party1 \<ge> 
       sl (assign_seats rec) ! index (p rec) party2"
proof(cases "length ( get_winners (fv rec) (p rec)) \<le> ns rec")
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

lemma assign_seats_concordant:
  fixes
  v1::"rat"
assumes 
  "index (p rec) party1 < length (fv rec)" and
  "index (p rec) party2 < length (fv rec)" and
  "v1 > v2" and
  "party1 \<in> set (p rec)" and
  "party2 \<in> set (p rec)" and
  "get_winners (fv rec) (p rec) \<noteq> []" and
  "(fv rec) ! (index  (p rec) party1) = 
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
  then have "sl (assign_seats  rec) = sl rec''"  
    using False rec''_def by simp
  then have "sl (assign_seats rec) ! (index (p rec) party1) = 
              sl rec'' ! index (p rec) party1" 
    by simp
  then have "... = sl rec ! (index (p rec) party1)"
    using break_tie_lemma rec''_def by metis
  also have "sl (assign_seats rec) ! (index (p rec) party2) = 
              sl rec ! index (p rec) party2"
     using \<open>sl (assign_seats rec) = sl rec''\<close> break_tie_lemma rec''_def by metis
  then show ?thesis
  using False assms \<open>sl (assign_seats rec) ! ( index (p rec) party1) = 
          sl rec'' ! ( index (p rec) party1)\<close> calculation by metis
qed

lemma assign_seats_incre_case_helper:
assumes 
  "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> fv rec ! y \<le> Max(set (fv rec))"
  and  
  "Max(set (fv rec')) > Max(set (fv rec))"
shows 
  "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> fv rec ! y < Max(set (fv rec'))"
  using assms dual_order.trans leD linorder_le_less_linear by meson

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
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index  (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index  (p rec) party))" and
  "sl rec' ! index  (p rec) party \<ge> sl rec ! index  (p rec) party" and
  "d rec ! (sl rec !  index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
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
     using assms(2) assms(26) assms(4) get_winners_not_in_win max_val_wrap.elims by metis
   then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> 
              fv rec ! y \<le> Max(set (fv rec))" 
      by auto
   then have "Max(set (fv rec')) = (fv rec') ! index (p rec) party" 
     using \<open>fv rec ! index (p rec) party = Max(set (fv rec))\<close> max_eqI_5 False 
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
   then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y < Max(set (fv rec'))"
     using \<open>Max(set (fv rec')) > Max(set (fv rec))\<close> assign_seats_incre_case_helper
      \<open>\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))\<close>    
     by metis
   then have "\<And>x. x \<noteq> index (p rec') party \<Longrightarrow> x < length (fv rec') \<Longrightarrow> (fv rec') ! x < m'" 
     using assms(1) assms(22) assms(27) assms(9) leD linorder_le_less_linear 
      max_val_wrap.simps max_val_wrap_lemma order_antisym_conv by metis
  then have "length (winners') = 1"
    using assms \<open>Max(set (fv rec')) = (fv rec') ! index (p rec) party\<close>
      \<open>index (p rec') party < length (fv rec')\<close>
      \<open>m' = Max(set (fv rec'))\<close>
      \<open>fv rec' ! index (p rec') party = m'\<close> 
      \<open>\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> (fv rec') ! y < m'\<close>
    \<open>length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])\<close>
    filter_size_is_one_helper_my_case_3 by metis
  then have "length winners' \<le> length winners" 
    using assms(4) leI length_0_conv less_one by metis
  then show ?thesis
    using linorder_not_less assms(10) assms(23) assms(24) assms(25) by linarith
 qed
qed

lemma assign_seats_incre_case_FTqq:
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
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
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

lemma filter_size_is_one_helper_my_case_4:
  fixes
  rec'::"('a::linorder, 'b) Divisor_Module"
assumes
"party \<in> set (p rec')" and
"index (p rec') party < length (fv rec')" and
"(fv rec') ! index (p rec') party = Max(set (fv rec'))" and
"\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> fv rec' ! y < Max(set (fv rec'))" and 
"length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. fv rec' ! x = Max(set (fv rec'))) [0..<length (fv rec')])"
shows "party = hd (get_winners (fv rec') (p rec'))"
  using filter_size_is_one_helper_my_case_4 assms by metis

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
  "fv rec ! index  (p rec) party = v / of_int ((d rec) ! (sl rec ! index  (p rec) party))" and
  "fv rec' ! index  (p rec) party = v' / of_int ((d rec) ! (sl rec' ! index  (p rec) party))" and
  "sl rec' ! (index  (p rec) party) \<ge> sl rec ! (index  (p rec) party)" and
  "(d rec) ! ((sl rec') !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow>(fv rec') ! x \<le> (fv rec) ! x" and
  "length winners \<le> ns rec" and
  "party \<noteq> hd (winners')" and
  "party = hd winners" and
  "p rec = p rec'" 
shows "sl (assign_seats rec') ! (index  (p rec) party) \<ge> 
       sl (assign_seats rec) ! (index  (p rec) party)"
proof(cases "(sl rec) ! index (p rec) party = (sl rec') ! index (p rec) party")
  case True
  have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))" 
    by simp
    then have "fv rec' ! index (p rec) party > fv rec ! index (p rec) party" 
      using divide_strict_right_mono True of_int_0_less_iff of_nat_le_0_iff
            assms(8) assms(9) assms(10) assms(12) by fastforce
    then have "fv rec ! index (p rec) party = Max(set (fv rec))" 
      using \<open>party = hd winners\<close> assms(2)assms(21) assms(7) assms(20) assms(4) assms(8) 
        get_winners_loss hd_in_set by metis
     then have "Max(set (fv rec')) > Max(set (fv rec))"
       using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> assms(15) 
             assms(21) max_val_wrap.elims max_val_wrap_eqI_3 nth_mem by metis
     then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y < Max(set (fv rec'))"
    using \<open>Max(set (fv rec')) > Max(set (fv rec))\<close>
      \<open>\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))\<close>    
    assign_seats_incre_case_helper by metis
  then have "\<And>x. x \<noteq> index (p rec') party \<Longrightarrow> x < length (fv rec') \<Longrightarrow> (fv rec') ! x < m'" 
    using assms(1) assms(17) assms(21) assms(5) assms(6) leD linorder_le_less_linear 
      max_val_wrap.simps max_val_wrap_lemma order_antisym_conv by metis
  then have "(fv rec') ! index (p rec') party = m'"
    using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> 
          \<open>fv rec ! index (p rec) party = Max (set (fv rec))\<close> assms(1) assms(15) assms(17) 
          assms(21) assms(5) assms(6) max_eqI_4 by metis
  then have "party = hd (get_winners (fv rec') (p rec))"
    using assms(7) assms(15) assms(1) assms(14) \<open>(fv rec') ! index (p rec') party = m'\<close>
          \<open>\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> (fv rec') ! y < m'\<close>
          filter_size_is_one_helper_my_case_4 assms(21) by metis
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
  "fv rec ! index (p rec) party = v / of_int ((d rec) ! (sl rec ! index  (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int ((d rec) ! (sl rec' ! index  (p rec) party))" and
  "sl rec' ! index  (p rec) party \<ge> sl rec ! index  (p rec) party" and
  "d rec ! (sl rec !  index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
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
  have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))" 
    by simp
    then have "fv rec' ! index (p rec) party > fv rec ! index (p rec) party" 
      using divide_strict_right_mono True of_int_0_less_iff of_nat_le_0_iff
            assms(10) assms(11) assms(12) assms(15) by fastforce
    then have "fv rec ! index (p rec) party = Max(set (fv rec))" using \<open>party = hd winners\<close>
      using assms(2) assms(25) assms(4) assms(9) get_winners_loss hd_in_set by metis
     then have "Max(set (fv rec')) > Max(set (fv rec))"
       using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> assms(18) 
             assms(25) max_val_wrap.elims max_val_wrap_eqI_3 nth_mem by metis
     then have "\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) 
                \<Longrightarrow> (fv rec) ! y < Max(set (fv rec'))"
       using \<open>Max(set (fv rec')) > Max(set (fv rec))\<close> assign_seats_incre_case_helper
       \<open>\<And>y. y \<noteq> index (p rec) party \<Longrightarrow> y < length (fv rec) \<Longrightarrow> (fv rec) ! y \<le> Max(set (fv rec))\<close>    
       by metis
  then have "\<And>x. x \<noteq> index (p rec') party \<Longrightarrow> x < length (fv rec') \<Longrightarrow> fv rec' ! x < m'" 
    using assms(1) assms(21) assms(25) assms(7) assms(8) leD linorder_le_less_linear 
          max_val_wrap.simps max_val_wrap_lemma order_antisym_conv by metis
  then have "(fv rec') ! index (p rec') party = m'"
    using \<open>fv rec ! index (p rec) party < fv rec' ! index (p rec) party\<close> 
          \<open>fv rec ! index (p rec) party = Max (set (fv rec))\<close> assms(1) assms(18) assms(21) 
          assms(25) assms(7) assms(8) max_eqI_4 by metis 
  then have "party = hd (get_winners (fv rec') (p rec))"
    using assms(9) assms(18) assms(1) \<open>(fv rec') ! index (p rec') party = m'\<close>
          \<open>\<And>y. y \<noteq> index (p rec') party \<Longrightarrow> y < length (fv rec') \<Longrightarrow> (fv rec') ! y < m'\<close>
          assms(17) assms(25) filter_size_is_one_helper_my_case_4 filter_cong by metis
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
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
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

lemma assign_seats_monotone_case_Tqqq:
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
  "fv rec ! index (p rec) party = v / of_int (d rec ! (sl rec ! index  (p rec) party))" and
  "fv rec' ! index (p rec) party = v' / of_int (d rec ! (sl rec' ! index  (p rec) party))" and
  "sl rec' ! index (p rec) party \<ge> sl rec ! index (p rec) party" and
  "d rec ! (sl rec ! index (p rec) party) \<noteq> 0" and
  "d rec ! (sl rec' ! index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
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
  "fv rec ! index  (p rec) party = v / of_int ((d rec) ! (sl rec ! index  (p rec) party))" and
  "fv rec' ! index  (p rec) party = v' / of_int ((d rec) ! (sl rec' ! index  (p rec) party))" and
  "sl rec' ! (index  (p rec) party) \<ge> sl rec ! (index  (p rec) party)" and
  "(d rec) ! ((sl rec) !  index (p rec) party) \<noteq> 0" and
  "(d rec) ! ((sl rec') !  index (p rec) party) \<noteq> 0" and
  "index (p rec) party < length (sl rec')" and 
  "length (get_winners (fv rec') (p rec')) = length (filter (\<lambda>x. (fv rec') ! x = m') [0..<length (fv rec')])"
  "index (p rec') party < length (fv rec')" and 
  "index (p rec) party < length (sl rec)" and
  "index (p rec) party < length (fv rec)" and 
  "\<And>x. x \<noteq> index (p rec) party \<Longrightarrow> (fv rec') ! x \<le> (fv rec) ! x" and
  "ns rec = ns rec'" and
  "p rec = p rec'"
shows "sl (assign_seats rec') ! index (p rec) party \<ge> 
       sl (assign_seats rec) ! index (p rec) party"
proof(cases "length winners' \<le> ns rec'")
  case True \<comment> \<open>T\<close>
  then show ?thesis using \<open>length winners' \<le> ns rec'\<close> assms 
                          assign_seats_monotone_case_Tqqq by metis
  next
  case False  \<comment> \<open>F\<close>
  then have "length winners' > ns rec'" 
    using False by simp
  then show ?thesis 
  proof(cases "length winners \<le> ns rec")
    case True  \<comment> \<open>FT\<close>
    then show ?thesis 
      using \<open>length winners'>ns rec'\<close> \<open>length winners \<le> ns rec\<close> assms 
        assign_seats_incre_case_FTqq by metis
  next
    case False \<comment> \<open>FF\<close>
    then show ?thesis 
      using False assign_seats_break_tie_case assms
            linorder_le_less_linear assign_seats_case_TFqq 
      by metis
  qed
qed

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

text \<open>This loop applies the same functions until no more seats are available.\<close>
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
(*
lemma loop_o_concordant_gt_case:
fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  party1::"'b" and 
  party2::"'b" and 
  parties::"'b Parties"
assumes 
  "ns rec > 0"
shows "sl (loop_o parties rec) ! (index parties party1) \<ge> 
       sl (loop_o parties rec) ! (index parties party2)"
  apply (induction rec rule:loop_o.induct)
  subgoal premises p for r parties
    using p(1) apply (auto simp: Let_def split: if_splits simp del: assign_seats.simps)
    done
  subgoal premises p for r parties
    using p(1) proof - have "ns r = 0" using p(1) assms by simp
    done
*)

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
(*
  subgoal for r parties
    apply (auto simp: Let_def split: if_splits simp del: assign_seats.simps)
    done
  subgoal premises p for r parties
    apply (auto simp: Let_def split: if_splits simp del: assign_seats.simps)
    done
  sorry
*)
fun create_empty_seats :: "'a::linorder set \<Rightarrow> 'b Parties \<Rightarrow> ('a::linorder, 'b) Seats" where
  "create_empty_seats indexes parties =
    (\<lambda>i. if i \<in> indexes then parties else [])"

text \<open>This function takes in input the parameters and calculates
       the final output of the election.\<close>

fun start_fract_votes :: "nat list \<Rightarrow> rat list" where
  "start_fract_votes [] = []" |
  "start_fract_votes (nn # nns) = (of_nat nn) # start_fract_votes nns"

fun full_module:: "('a::linorder, 'b) Divisor_Module \<Rightarrow> 'b Profile \<Rightarrow>
                   ('a::linorder, 'b) Divisor_Module" where

"full_module rec pl = (
    let sv = calc_votes (p rec) (p rec) pl (v rec);
    sfv = start_fract_votes sv;
    empty_seats = create_empty_seats (i rec) (p rec)
    in loop_o \<lparr> 
             res = res rec,
             p = p rec,
             i = i rec,
             s = empty_seats,
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

(* Define a set *)
definition my_set :: "nat set" where
  "my_set = {1, 2, 3, 4, 5}"
              
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

fun empty_seats :: "('a::linorder \<Rightarrow> 'b list)" where
  "empty_seats b = []"

theorem votes_anonymous:
  "\<forall>p2 p1 profile.
    mset p1 = mset p2 \<longrightarrow>
    calculate_votes_for_election p1 profile = 
    calculate_votes_for_election p2 profile"
  sorry

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

fun start_votes :: "'a list \<Rightarrow> nat list" where
  "start_votes [] = []" |
  "start_votes (x # xs) = 0 # start_votes xs"

fun start_seats_list :: "'a list \<Rightarrow> nat list" where
  "start_seats_list [] = []" |
  "start_seats_list (x # xs) = 0 # start_seats_list xs"

definition new_record :: "'b Parties \<Rightarrow> nat \<Rightarrow> (nat, 'b) Divisor_Module"
  where
  "new_record cp cns = \<lparr> res =  ({}, {}, {1..cns}), p = cp, i = {1..cns}, 
                               s = create_empty_seats {1..cns} cp, ns = cns, 
                               v = start_votes cp, fv = [],
                               sl = start_seats_list cp, d = [] \<rparr>"

(* - se i partiti è una lista vuota c'è un errore
  - al momento assegna tutti i seat indicati a tutti i partiti. (RISOLTO)
  - ho cambiato in assigning_seats quando chiamo divisor module a p passo i winners (RISOLTO)
  - adesso ho aggiustato che passa i seat correttamente dai disputed agli assegnati (RISOLTO)
  - bisogna fare in modo che si assegni correttamente al partito vincitore (RISOLTO)
  - sto cercando di assegnare il seat al winner (RISOLTO)
*)

fun dhondt_method :: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"dhondt_method partiti nseats pr = 
    (let rec = new_record partiti nseats in full_module (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr)"

theorem dhont_method_concordant:
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
  shows "sl (dhondt_method parties n pl) ! ( index parties party1) \<ge> sl (dhondt_method parties n pl) ! ( index parties party2)"
  using full_module_concordant assms by sorry

fun saintelague_method:: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"saintelague_method partiti nseats pr = 
  (let rec = new_record partiti nseats in full_module (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1)
                                            (upt 1 (2*ns rec))\<rparr>) pr)"

theorem saintelague_method_concordant:
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
  shows "sl (saintelague_method parties n pl) ! ( index parties party1) \<ge> sl (saintelague_method parties n pl) ! ( index parties party1)"
  using full_module_concordant assms by force
qed
value "dhondt_method parties 10 pref"

value "saintelague_method parties 10 pref"

end
