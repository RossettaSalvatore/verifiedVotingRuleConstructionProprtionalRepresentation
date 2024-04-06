

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
  v :: "nat list"
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
    (let index = get_index_upd(hd winner)(p r);
     n_seats = count_seats winner (s r) (i r);
     new_v = of_nat(get_votes (hd winner) (p r) (v r)) / of_int(d r ! n_seats) in
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

(* this lemma shows that for every update of divisor_module, all the other 
   parties still have the same seats *)
lemma divisor_module_mantain_seats_lemma:
  assumes "i1 = get_index_upd (hd winner) (p rec)"
  assumes "i2 \<noteq> i1"
  assumes "i2 < length (sl rec)"
  shows "sl (divisor_module winner rec) ! i2 =
         (sl rec) ! i2"
proof - 
   define seat new_s new_as new_fv index curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat winner (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = update_votes2 winner (rec\<lparr>s:= new_s\<rparr>)" and
          "index =  get_index_upd (hd winner) (p rec)" and
          "curr_ns = (sl rec) ! index" and
          "new_sl = list_update (sl rec) index (curr_ns + 1)" and
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
    using nth_list_update_eq curr_ns_def index_def new_as_def new_di_def new_fv_def new_s_def seat_def 
    by fastforce
  then have "sl (divisor_module winner rec) = new_sl" 
    by simp
  then have "... =  list_update (sl rec) index (curr_ns + 1)" 
    using new_sl_def by simp
  then have "sl (divisor_module winner rec) ! i2 = 
             (list_update (sl rec) index (curr_ns + 1)) ! i2"
    using \<open>sl (divisor_module winner rec) = new_sl\<close> by presburger
  then have "... = (sl rec) ! i2" 
    using nth_list_update_neq assms by (metis index_def)
  then show ?thesis
  using \<open>sl (divisor_module winner rec) ! i2 = (sl rec)[index := curr_ns + 1] ! i2\<close> by presburger
qed

lemma divisor_module_sl_update:
  fixes winner :: "'b list" and 
        rec :: "('a::linorder, 'b) Divisor_Module" and
        index::"nat"
  defines i_def: "index \<equiv> get_index_upd (hd winner) (p rec)"
  shows "sl (divisor_module winner rec) = 
         list_update (sl rec) index ((sl rec) ! index + 1)"
proof -
  define seat new_s new_as new_fv index curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat winner (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = update_votes2 winner (rec\<lparr>s:= new_s\<rparr>)" and
          "index =  get_index_upd (hd winner) (p rec)" and
          "curr_ns = (sl rec) ! index" and
          "new_sl = list_update (sl rec) index (curr_ns + 1)" and
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
  using nth_list_update_eq curr_ns_def index_def new_as_def new_di_def new_fv_def new_s_def seat_def by fastforce
  then have "sl(divisor_module winner rec) = new_sl" 
    by simp
  also have "... = list_update (sl rec) index (curr_ns + 1)" 
    unfolding new_sl_def by simp
  also have "... =  list_update (sl rec) index ((sl rec) ! index + 1)"
      unfolding new_sl_def using curr_ns_def by simp
  finally show ?thesis
      using index_def nth_list_update_eq assms
      by blast
qed

lemma divisor_module_increase_seats:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  winner::"'b list"
defines i_def: "index \<equiv> get_index_upd (hd winner) (p rec)"
assumes "index < length (sl rec)"
shows "(sl (divisor_module winner rec)) ! index =
       (sl rec) ! index + 1"
proof -
  have "sl (divisor_module winner rec) =  list_update (sl rec) index ((sl rec) ! index + 1)" 
    using divisor_module_sl_update assms by blast
  then have "sl (divisor_module winner rec) ! index = 
        (list_update (sl rec) index ((sl rec) ! index + 1)) ! index" 
    using assms by simp
  then have "... = ((sl rec) ! index + 1)" 
    using nth_list_update_eq assms by simp
  then show ?thesis
    using \<open>sl (divisor_module winner rec) ! index = list_update (sl rec) index (sl rec ! index + 1) ! index\<close> by auto
qed


lemma divisor_module_mon:
  fixes
  winner::"'b list" and
  rec::"('a::linorder, 'b) Divisor_Module" and
  index::"nat" and
  parties::"'b Parties" 
assumes "index < length (sl rec)"
  shows "sl (divisor_module winner rec) ! index \<ge> 
         (sl rec) ! index"
proof -
    define seat new_s new_as new_fv index curr_ns new_sl new_di 
    where "seat = Min (disp_r (res rec))" and
          "new_s = update_seat seat winner (s rec)" and
          "new_as = ass_r (res rec) \<union> {seat}" and
          "new_fv = update_votes2 winner (rec\<lparr>s:= new_s\<rparr>)" and
          "index =  get_index_upd (hd winner) (p rec)" and
          "curr_ns = (sl rec) ! index" and
          "new_sl = list_update (sl rec) index (curr_ns + 1)" and
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
  using nth_list_update_eq curr_ns_def index_def new_as_def new_di_def new_fv_def new_s_def seat_def by fastforce
  then have "sl (divisor_module winner rec) = new_sl" 
    by simp
  then have "sl (divisor_module winner rec) ! index  
              = new_sl ! index" by simp
  then have "... = (list_update (sl rec) index (curr_ns + 1)) ! index" 
    using new_sl_def nth_list_update_eq by blast
  then show ?thesis
  by (metis \<open>sl (divisor_module winner rec) = new_sl\<close> assms(1) curr_ns_def le_add1 new_sl_def nth_list_update_eq nth_list_update_neq order_refl)
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
  winner::"'b list" and
  index::"nat"
shows "(sl (break_tie winner rec)) ! index \<ge> sl rec ! index" by simp

fun defer_divisor :: "('a::linorder, 'b) Divisor_Module 
                      \<Rightarrow> ('a::linorder, 'b) Divisor_Module" where
"defer_divisor r = r"

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
        let rec' =  (divisor_module [hd winners] rec) in
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

(* proof that for every candidate, the number of seats after 
   calling the function cannot decrease *)
lemma assign_seats_mon:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and 
  winners::"'b Parties" 
assumes "index < length (sl rec)"
assumes "winners = get_winners (fv rec) (p rec)"
shows "sl (assign_seats rec) ! index \<ge> sl rec ! index"
proof(cases "length winners \<le> ns rec")
  case True
  define rec' 
    where 
     "rec'= (divisor_module [hd winners] rec)"  
  then have "assign_seats rec =  (
      let winners = get_winners (fv rec) (p rec) in
      if length winners \<le> ns rec then 
        let rec' =  (divisor_module [hd winners] rec) in
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
                        \<rparr>)" using rec'_def by simp
  then have "... = \<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>" using rec'_def assms
    by (smt (verit, best) True)
  then have "sl (assign_seats rec) ! index = sl rec' ! index" 
    by simp
  then have "... = (sl (divisor_module [hd winners] rec)) ! index" 
    using rec'_def by simp
  then have "... \<ge> (sl rec) ! index" 
    using assms divisor_module_mon by blast
  then show ?thesis 
    using assms rec'_def by (metis \<open>sl (assign_seats rec) ! index = sl rec' ! index\<close>)
next
  case False
  define rec'' 
    where 
     "rec''= (break_tie winners rec)"  
   then have "assign_seats rec =  (
      let winners = get_winners (fv rec) (p rec) in
      if length winners \<le> ns rec then 
        let rec' =  (divisor_module [hd winners] rec) in
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
  then have "... = \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>" using rec''_def assms
    by (smt (verit, best) False)
  then have "sl (assign_seats rec) ! index = sl (break_tie winners rec) ! index" 
    using rec''_def by simp
  then have "... \<ge> sl rec ! index" 
    by simp
  then show ?thesis
    using \<open>sl (assign_seats rec) ! index = sl (break_tie winners rec) ! index\<close> by fastforce
qed

(* proof that after calling assign_seats, the other parties not winning have 
  the same number of seats *)
lemma assign_seats_not_winner_mantains_seats:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and 
  winners::"'b list" and 
  i2::"nat"
  defines "winners \<equiv> get_winners (fv rec) (p rec)"
  defines "i1 \<equiv> get_index_upd (hd winners) (p rec)"
  assumes "i1 \<noteq> i2"
  assumes "i2 < length (sl rec)"
  shows "(sl rec) ! i2 = (sl (assign_seats rec)) ! i2"
proof (cases "(length winners) \<le> ns rec")
  case True
  define rec' 
   where 
     "rec'= (divisor_module [hd winners] rec)"  
  have "assign_seats rec = \<lparr>res = (res rec'),
                         p = (p rec'),
                         i = (i rec'),
                         s = (s rec'),
                         ns = ((ns rec') - 1),
                         v = (v rec'),
                         fv = (fv rec'),
                         sl = (sl rec'),
                         d = (d rec')
                        \<rparr>" using rec'_def assms
  by (smt (verit, best) True assign_seats.simps)
  then have "sl (assign_seats rec) = sl (rec')" 
    by simp
  then have "sl (assign_seats rec) ! i2 = sl (divisor_module [hd winners] rec) ! i2" 
    using assms \<open>sl (assign_seats rec) = sl rec'\<close> using rec'_def by presburger
  then have "... = (sl rec) ! i2" 
    using divisor_module_mantain_seats_lemma assms list.sel(1) by metis
  then show ?thesis
  using \<open>sl (assign_seats rec) ! i2 = sl (divisor_module [hd winners] rec) ! i2\<close> by linarith
next
  case False
 define rec''
    where 
     "rec''= break_tie winners rec"  
  then have "assign_seats rec =  (
      let winners = get_winners (fv rec) (p rec) in
      if length winners \<le> ns rec then 
        let rec' =  (divisor_module [hd winners] rec) in
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
  then have "... = \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>" using rec''_def assms
    by (smt (verit, best) False)
  then have "sl (assign_seats rec) = sl (rec'')" 
    by simp
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

lemma assign_seats_update:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module"
  defines winners_def: "winners \<equiv> get_winners (fv rec) (p rec)"
  defines rec'_def: "rec' \<equiv> divisor_module [hd winners] rec"
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

(* proof that after assign seats the winner gets its seats
   increased by one *)
lemma assign_seats_seats_increased:
   fixes
  rec::"('a::linorder, 'b) Divisor_Module"
defines "winners \<equiv> get_winners (fv rec) (p rec)" 
defines "index \<equiv> get_index_upd (hd winners) (p rec)"
assumes "length winners \<le> ns rec" 
assumes "index < length (sl rec)"
shows "sl (assign_seats rec) ! index = sl rec ! index + 1"
proof - 
  define rec' where  "rec' \<equiv> (divisor_module [hd winners] rec)"
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
    using assms assign_seats_update rec'_def by metis
  then have "sl (assign_seats rec) ! index = (sl rec') ! index"
    by simp 
  also have "... = sl (divisor_module [hd winners] rec) ! index" using assms rec'_def by simp
  also have "... = (list_update (sl rec) index ((sl rec) ! index + 1))
                   ! index" using assms divisor_module_sl_update
    by (metis list.sel(1)) 
  also have "... = sl rec ! index + 1" 
    using nth_list_update_eq assms by simp
  finally have "sl (assign_seats rec) ! index = sl rec ! index + 1" by simp 
  then show ?thesis using \<open>sl (assign_seats rec) ! index = sl rec ! index + 1\<close>
  by simp
qed

(* lemma che dice che se ho gli stessi seat (sl rec ! i1) = (sl rec ! i2) 
ma v1 > v2 allora party2 non può essere il vincitore *)
lemma assign_seats_helper_lemma_helper:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  i2::"nat" and 
  i1::"nat" and
  party1::"'b" and 
  party2::"'b" and 
  v1::"rat" and 
  v2::"rat" and
  parties::"'b Parties" and
  fv1::"rat" and
  fv2::"rat" and 
  winners::"'b list"
defines 
  "fv1 \<equiv> (fv rec) ! (get_index_upd party1 parties)" and
  "fv2 \<equiv> (fv rec) ! (get_index_upd party2 parties)" and
  "winners \<equiv> get_winners (fv rec) (p rec)"
assumes 
  "v1 > v2" and
  "fv1 \<equiv> v1 / (of_int ((d rec) ! ((sl rec) ! i1)))" and
  "fv2 \<equiv> v2 / (of_int ((d rec) ! ((sl rec) ! i2)))" and
  "party1 \<noteq> party2" and
  "(d rec) ! ((sl rec) ! i2) \<noteq> 0" and
  "sl rec ! i1 = sl rec ! i2" and
  "i1 \<noteq> i2" and
  "i1 < length (sl rec)" and
  "i2 < length (sl rec)"
  shows "party2 \<noteq> hd (winners)"
proof (cases "fv1 = max_val_wrap (fv rec)")
  case True
  then have "fv1 > fv2" 
    using assms divide_strict_right_mono by fastforce
  then have "fv2 \<noteq> max_val_wrap (fv rec)" 
    using assms True by force
  then have "party2 \<noteq> hd (get_winners (fv rec) (p rec))" using assms
  by (metis get_index_upd.simps(1) get_index_upd_correct)
  then show ?thesis using assms by simp
next
  case False
  then have "max_val_wrap (fv rec) > fv1" using assms
    by (metis get_index_upd.simps(1) get_index_upd_correct)
  then have "max_val_wrap (fv rec) \<noteq> fv2" using assms divide_right_mono less_le_not_le negative_zle of_int_nonneg
    by (smt (z3))
  then show ?thesis
  by (metis get_index_upd.simps(1) get_index_upd_correct)
qed

(*
lemma assign_seats_ccontr:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  i2::"nat" and i1::"nat" and
  m::"rat" and winners::"'b list" and
  party1::"'b" and party2::"'b" and parties::"'b Parties"
assumes "v1 > v2"
assumes "party1 \<noteq> party2"
  defines "i1 \<equiv> get_index_upd party1 (p rec)"
  defines "i2 \<equiv> get_index_upd party2 (p rec)"
  defines "fv1 \<equiv> v1 / (d rec) ! ((sl rec) ! i1)"
  defines "fv2 \<equiv> v2 / (d rec) ! ((sl rec) ! i2)"
  defines "winners \<equiv> get_winners (fv rec) (p rec)"
  assumes "sl rec ! i1 \<ge> sl rec ! i2" 
  assumes "i1 \<noteq> i2" 
  assumes "i1 < length (sl rec)"
  assumes "i2 < length (sl rec)"
  assumes "party2 = hd winners"
  assumes "length winners \<le> ns rec"
  assumes "(d rec) ! ((sl rec) ! i2) \<noteq> 0"
  assumes "sl rec ! i1 = sl rec ! i2"
  shows "sl (assign_seats rec) ! i1 \<ge> sl (assign_seats rec) ! i2"
proof (rule ccontr)
*)

(* voglio provare un singolo caso di quello che verrà dopo, il caso che voglio 
  provare è che se il partito2 vince allora comunque non supera i seat di partito1 *)
lemma assign_seats_helper_lemma:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  i2::"nat" and i1::"nat" and
  m::"rat" and winners::"'b list" and v1::"rat" and v2::"rat" and
  party1::"'b" and party2::"'b" and parties::"'b Parties"
defines 
  "fv1 \<equiv> (fv rec) ! (get_index_upd party1 parties)" and
  "fv2 \<equiv> (fv rec) ! (get_index_upd party2 parties)" and
  "winners \<equiv> get_winners (fv rec) (p rec)" and
  "i1 \<equiv> get_index_upd party1 (p rec)" and
  "i2 \<equiv> get_index_upd party2 (p rec)"
assumes 
  "v1 > v2" and
  "party2 = hd winners" and
  "fv1 \<equiv> v1 / (of_int ((d rec) ! ((sl rec) ! i1)))" and
  "fv2 \<equiv> v2 / (of_int ((d rec) ! ((sl rec) ! i2)))" and
  "party1 \<noteq> party2" and
  "(d rec) ! ((sl rec) ! i2) \<noteq> 0" and
  "sl rec ! i1 \<ge> sl rec ! i2" and
  "length winners \<le> ns rec" and
  "i1 \<noteq> i2" and
  "i1 < length (sl rec)" and
  "i2 < length (sl rec)"
  shows "sl (assign_seats rec) ! i1 \<ge> sl (assign_seats rec) ! i2"
proof(cases "sl rec ! i1 = sl rec ! i2")
  case True \<comment> \<open> prova per assurdo  \<close>
  have "sl rec ! i1 = sl rec ! i2" using True by simp
 then have "fv1 = v1 / (d rec) ! ((sl rec) ! i2)" 
    using assms True
  by (metis of_int_of_nat_eq of_rat_divide of_rat_of_nat_eq)
  then have "fv2 = v2 / (d rec) ! ((sl rec) ! i2)" 
    using assms  by (metis of_int_of_nat_eq of_rat_divide of_rat_of_nat_eq)
  then have "fv1 > fv2" 
    using \<open>fv1 = v1 / (d rec) ! ((sl rec) ! i2)\<close> 
          \<open>fv2 = v2 / (d rec) ! ((sl rec) ! i2)\<close> \<open>v1 > v2\<close> assms
  by (metis True assign_seats_helper_lemma_helper)
  then have "party2 \<noteq> hd winners"
    using True assign_seats_helper_lemma_helper assms fv1_def fv2_def winners_def by metis
  then show ?thesis
  using assms by blast
next
  case False
  have "sl rec ! i1 > sl rec ! i2" using assms False
  using le_neq_implies_less by presburger
  then have "i2 = get_index_upd (hd winners) (p rec)" using assms by blast
  then have "sl (assign_seats rec) ! i2 = sl rec ! i2 + 1" 
    using \<open>i2 = get_index_upd (hd winners) (p rec)\<close> assms 
          assign_seats_seats_increased False by blast
  then have "sl (assign_seats rec) ! i1 = sl rec ! i1" 
    using assms assign_seats_not_winner_mantains_seats False by metis
  then show ?thesis 
    using \<open>sl (assign_seats rec) ! i2 = sl rec ! i2 + 1\<close> 
          \<open>sl rec ! i2 < sl rec ! i1\<close> by linarith
qed

lemma assign_seats_concordant:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  i2::"nat" and i1::"nat" and
  m::"rat" and winners::"'b list" and v1::"rat" and v2::"rat" and
  party1::"'b" and party2::"'b" and parties::"'b Parties"
defines 
  "fv1 \<equiv> (fv rec) ! (get_index_upd party1 parties)" and
  "fv2 \<equiv> (fv rec) ! (get_index_upd party2 parties)" and
  "winners \<equiv> get_winners (fv rec) (p rec)" and
  "i1 \<equiv> get_index_upd party1 (p rec)" and
  "i2 \<equiv> get_index_upd party2 (p rec)"
assumes 
  "v1 > v2" and
  "party1 \<noteq> party2" and
  "fv1 \<equiv> v1 / (of_int ((d rec) ! ((sl rec) ! i1)))" and
  "fv2 \<equiv> v2 / (of_int ((d rec) ! ((sl rec) ! i2)))" and
  "sl rec ! i1 \<ge> sl rec ! i2" and
  "(d rec) ! ((sl rec) ! i2) \<noteq> 0" and
  "i1 \<noteq> i2" and
  "i1 < length (sl rec)" and
  "i2 < length (sl rec)" and
  "length winners \<le> ns rec"
shows "sl (assign_seats rec) ! i1 \<ge> sl (assign_seats rec) ! i2"
proof(cases "length winners \<le> ns rec")
  case True  \<comment> \<open>commment\<close> 
  (* let ?x = *)
  then show ?thesis 
      proof(cases "party1 = hd winners")
        case True
             have "sl (assign_seats rec) ! i1 = (sl rec) ! i1 + 1"
             using  \<open>length winners \<le> ns rec\<close> True assign_seats_seats_increased assms i1_def winners_def by blast
           also have "sl (assign_seats rec) ! i2 = (sl rec) ! i2"
           using True assign_seats_not_winner_mantains_seats assms i1_def winners_def by metis 
              then show ?thesis
              using assms calculation by linarith
      next
        case False
        then show ?thesis
        proof(cases "party2 = hd winners")
          case True
          then show ?thesis sorry
        next
          case False
          have "party2 \<noteq> hd winners" using False by simp
          then have "winners = (get_winners (fv rec) (p rec))" using assms by simp
          then have "get_index_upd (hd winners) (p rec) \<noteq> i2" 
            using assms False get_index_upd_correct by metis
          then have "sl (assign_seats rec) ! i2 = (sl rec) ! i2"
            using False assms i2_def i1_def 
                  assign_seats_not_winner_mantains_seats[of rec i2] by metis
          have "party1 \<noteq> hd winners" using \<open>party1 \<noteq> hd winners\<close> by simp
          then have "get_index_upd (hd winners) (p rec) \<noteq> i1" 
            using assms False get_index_upd_correct by metis            
          then have "sl (assign_seats rec) ! i1 = (sl rec) ! i1"
            using \<open>party1 \<noteq> hd winners\<close> assms i2_def i1_def 
                  assign_seats_not_winner_mantains_seats[of rec i1] by metis
          then show ?thesis
          using \<open>sl (assign_seats rec) ! i2 = sl rec ! i2\<close> assms by linarith
        qed
      qed
next
  case False
  define rec''
    where 
     "rec''= break_tie winners rec" 
   have "assign_seats rec =  (
      let winners = get_winners (fv rec) (p rec) in
      if length winners \<le> ns rec then 
        let rec' =  (divisor_module [hd winners] rec) in
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
   then have "... =  \<lparr>res = (res rec''),
                         p = (p rec''),
                         i = (i rec''),
                         s = (s rec''),
                         ns = 0,
                         v = (v rec''),
                         fv = (fv rec''),
                         sl = (sl rec''),
                         d = (d rec'')
                        \<rparr>"
     using False rec''_def winners_def by simp
   then have "sl (assign_seats rec) = sl rec''" by simp
   then have "sl (assign_seats rec) ! i1 = sl rec'' ! i1" by simp
   then have "... = sl rec ! i1"
     using break_tie_lemma rec''_def by metis
   also have "sl (assign_seats rec) ! i2 = sl rec ! i2"
     using \<open>sl (assign_seats rec) = sl rec''\<close> break_tie_lemma rec''_def by metis
  then show ?thesis
  using False assms
  using \<open>sl (assign_seats rec) ! i1 = sl rec'' ! i1\<close> calculation by linarith
qed

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

text \<open>This loop applies the same functions until no more seats are available.\<close>
function loop_o ::
  "('a::linorder, 'b) Divisor_Module \<Rightarrow> ('a::linorder, 'b) Divisor_Module"
  where  
  "ns r = 0  \<Longrightarrow> loop_o r = r" |
  "ns r > 0 \<Longrightarrow> loop_o r = loop_o (assign_seats r)"
  by auto
termination by (relation "measure (\<lambda>r. ns r)")
               (auto simp add: Let_def nseats_decreasing)
lemma [code]: \<open>loop_o r = (if ns r = 0 then r else loop_o (assign_seats r))\<close>
  by (cases r) auto


lemma lemma1:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  m::"rat" and
  party1::"'b" and party2::"'b" and parties::"'b Parties"
assumes "v1 > v2"
assumes "party1 \<noteq> party2"
  defines "i1 \<equiv> get_index_upd party1 (p rec)"
  defines "i2 \<equiv> get_index_upd party2 (p rec)"
  defines "fv1 \<equiv> v1 / (d rec) ! ((sl rec) ! i1)"
  defines "fv2 \<equiv> v2 / (d rec) ! ((sl rec) ! i2)"
  defines "winners \<equiv> get_winners (fv rec) (p rec)"
  assumes "sl rec ! i1 \<ge> sl rec ! i2" 
  assumes "i1 \<noteq> i2" 
  assumes "i1 < length (sl rec)"
  assumes "i2 < length (sl rec)"
shows "sl (assign_seats rec) ! i1 \<ge> sl (assign_seats rec) ! i2"
  sorry

lemma loop_o_concordant:
  fixes
  rec::"('a::linorder, 'b) Divisor_Module" and
  m::"rat" and
  party1::"'b" and party2::"'b" and parties::"'b Parties"
assumes "v1 > v2"
assumes "party1 \<noteq> party2"
  defines "i1 \<equiv> get_index_upd party1 (p rec)"
  defines "i2 \<equiv> get_index_upd party2 (p rec)"
  defines "fv1 \<equiv> v1 / (d rec) ! ((sl rec) ! i1)"
  defines "fv2 \<equiv> v2 / (d rec) ! ((sl rec) ! i2)"
  defines "winners \<equiv> get_winners (fv rec) (p rec)"
  assumes "i1 \<noteq> i2" 
  assumes "i1 < length (sl rec)"
  assumes "i2 < length (sl rec)"
  shows "sl (loop_o rec) ! i1 \<ge> sl (loop_o rec) ! i2"
  using assms lemma1
  by (induction rec rule:loop_o.induct)
    auto

fun create_empty_seats :: "'a::linorder set \<Rightarrow> 'b Parties \<Rightarrow> ('a::linorder, 'b) Seats" where
  "create_empty_seats indexes parties =
    (\<lambda>i. if i \<in> indexes then parties else [])"

(* full divisor module function
  calcola voti correttamente  *) 
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

fun empty_seats :: "('a::linorder \<Rightarrow> 'b list)" where
  "empty_seats b = []"

theorem votes_anonymous:
  "\<forall>p2 p1 profile.
    mset p1 = mset p2 \<longrightarrow>
    calculate_votes_for_election p1 profile = 
    calculate_votes_for_election p2 profile"
  sorry

(* Define the concordant property *)
definition concordant :: "(('a, 'b) Divisor_Module \<Rightarrow> ('a, 'b) Divisor_Module) \<Rightarrow>
                           ('a::linorder, 'b) Divisor_Module \<Rightarrow> bool" where
  "concordant D dm = (\<forall>party1 party2 i.
    get_votes party1 (p dm) (v dm) > get_votes party2 (p dm) (v dm) \<longrightarrow>
    count_seats [party1] (s (D dm)) (i dm) \<ge> count_seats [party2] (s (D dm)) (i dm))"

(* if one party has more votes than another than it will have at least the same seats *)
theorem full_module_concordant:
  fixes
    rec:: "('a::linorder, 'b) Divisor_Module" and
    pl::"'b Profile" and 
    indexes::"'a::linorder set" and
    se::"('a::linorder, 'b) Seats" and
    party::"'b" and
    parties::"'b Parties" 
  defines "sl' \<equiv> sl (full_module rec pl)"
  assumes "party1 \<in> set parties"
  assumes "party2 \<in> set parties"
  defines "rec' \<equiv> full_module rec pl"
  defines "index1 \<equiv> get_index_upd party1 parties"
  defines "index2 \<equiv> get_index_upd party2 parties"
  shows "cnt_votes party1 pl 0 > cnt_votes party2 pl 0 \<Longrightarrow> 
          sl' ! index1 \<ge> sl' ! index2"
sorry
 
value "get_votes ''partyA'' [''partyA'', ''partyB''] [4, 5]"

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

(* ns è un numero naturale *)
(* i divisor sono numeri interi *)
fun dhondt_method :: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"dhondt_method partiti nseats pr = 
    (let rec = new_record partiti nseats in full_module (rec\<lparr>d := upt 1 (ns rec)\<rparr>) pr)"

fun saintelague_method:: "'b Parties \<Rightarrow> nat \<Rightarrow> 'b Profile \<Rightarrow>
                   (nat, 'b) Divisor_Module" where
"saintelague_method partiti nseats pr = 
  (let rec = new_record partiti nseats in full_module (rec\<lparr>d := filter (\<lambda>x. x mod 2 = 1)
                                            (upt 1 (2*ns rec))\<rparr>) pr)"


value "dhondt_method parties 10 pref"

value "saintelague_method parties 10 pref"

end
