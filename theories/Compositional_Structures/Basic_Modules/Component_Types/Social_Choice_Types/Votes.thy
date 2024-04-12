


section \<open>Votes\<close>

theory Votes
  imports Complex_Main
HOL.List
"HOL-Combinatorics.Multiset_Permutations"
"HOL-Combinatorics.List_Permutation"
Preference_Relation
Profile
Result
"List-Index.List_Index"
begin

(* lemma perm induction *)
lemma perm_induct:
  assumes "P [] []"
  assumes "\<And>x xs ys. P (x # xs) (x # ys)"
  assumes "\<And>x y xs ys. P (x # y # xs) (y # x # ys)"   
  assumes "\<And>xs ys zs. P xs ys \<Longrightarrow> P ys zs \<Longrightarrow> P xs zs" (* transitiva? *)
  shows "mset xs = mset ys \<Longrightarrow> P xs ys"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case
    using assms by auto
next
  case (Cons x xs)
  then show ?case
    using assms
    by (metis neq_Nil_conv perm_empty2)
qed

definition extract_element :: "'a multiset \<Rightarrow> 'a"
where
  "extract_element xs = fold_mset (\<lambda>x acc. x) undefined xs"

fun blabla::"'a multiset \<Rightarrow> 'a multiset"
  where 
  "blabla xs = xs - mset ([(fold_mset (\<lambda>x acc. x) undefined xs)])"

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
  "count_above r a = card (above r a)"

fun count_above_mset :: "('a multiset rel) \<Rightarrow>'a multiset \<Rightarrow> nat" where
  "count_above_mset r a = card (above r a)"

subsection  \<open>Definition\<close>
text  \<open>Parties is the list of parties, that can be of any type. 
       Votes is a function used to assign a rational number (indeed, the votes) to each party. \<close>

type_synonym 'b Parties = "'b list"

text  \<open>Every seat is unique and identified and has a set of parties to which it is assigned.\<close>
type_synonym ('a, 'b) Seats = "'a \<Rightarrow> 'b list"

type_synonym 'b Votes = "'b \<Rightarrow> rat"

type_synonym Params = "nat list"

lemma index_correct:
  fixes
  p::"'a list"
assumes "index p px < size p"
  shows "p ! (index p px) = px"
  by (meson assms index_eq_iff)

lemma index_diff_elements:
  assumes 
    "p1 \<in> set p" and 
    "p1 \<noteq> p2"
  shows "index p p1 \<noteq> index p p2"
proof (rule ccontr)
  assume "\<not> (index p p1 \<noteq> index p p2)"
  then have "index p p1 = index p p2" 
    by simp
  then obtain n1 n2 where "index p p1 = n1" and "index p p2 = n2" 
    by blast
  hence "n1 = n2"
    by (meson \<open>\<not> index p p1 \<noteq> index p p2\<close>)
  hence "p ! n1 = p1" 
    using assms index_correct \<open>index p p1 = n1\<close> by fastforce
  hence "p ! n2 = p2" 
    using assms index_correct \<open>index p p2 = n2\<close> 
          \<open>index p p1 = index p p2\<close> by force
  hence "p1 = p2" 
    using assms \<open>\<not> index p p1 \<noteq> index p p2\<close> \<open>n1 = n2\<close> \<open>p ! n1 = p1\<close> by blast
  with assms show False by simp
qed

fun get_votes :: "'b \<Rightarrow> 'b Parties \<Rightarrow> nat list \<Rightarrow> nat" where
"get_votes party parties votes = votes ! (index parties party)"

(* function to generate the list of parameters *)
fun generate_list :: "bool \<Rightarrow> nat \<Rightarrow> nat list" where
  "generate_list True n = [1..<n]" |
  "generate_list False n = filter (\<lambda>x. x mod 2 = 1) [1..<n]"

text \<open> This function counts votes for one party and add returns the number of votes \<close>

fun cnt_votes :: "'a \<Rightarrow> 'a Profile \<Rightarrow> nat \<Rightarrow> nat" where
  "cnt_votes p [] n = n" |
  "cnt_votes p (px # profil) n = 
     (case (count_above px p) of
        0 \<Rightarrow> cnt_votes p profil (n + 1)
      | _ \<Rightarrow> cnt_votes p profil n)"

definition convert_to_element :: "'a multiset \<Rightarrow> 'a" where
  "convert_to_element M = (SOME x. x \<in># M)"

fun cnt_votes_mset :: "'a multiset \<Rightarrow> (('a multiset \<times> 'a multiset) set) list \<Rightarrow> nat \<Rightarrow> nat" where
  "cnt_votes_mset p [] n = n" |
  "cnt_votes_mset p (px # profil) n = 
     (case (count_above_mset px p) of
        0 \<Rightarrow> cnt_votes_mset p profil (n + 1)
      | _ \<Rightarrow> cnt_votes_mset p profil n)"


text \<open> This function receives in input the list of parties and the list of preferation 
       relations. The output is the function Votes, in which every party has the 
       correspondent number of votes.  \<close>

definition remove_some :: "'a multiset \<Rightarrow> 'a" where
"remove_some M = (SOME x. x \<in> set_mset M)"

definition my_fold :: "('b \<Rightarrow> 'b \<Rightarrow> rat) \<Rightarrow> 'b Votes \<Rightarrow> 'a set \<Rightarrow> 'b Votes"
  where "my_fold f z A = (if finite A then z else z)"

(* Define the party multiset *)
definition party_multiset :: "char list multiset" where
  "party_multiset = {#''a'', ''b'', ''c'', ''d''#}"

(* Define the initial votes *)
fun empty_votes :: "char list \<Rightarrow> rat" where
  "empty_votes p = 0"

(* update_at_index added here bring error in full_module *)
fun calc_votes :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a Profile \<Rightarrow> nat list \<Rightarrow> nat list" where
  "calc_votes [] fp prof votes = votes" |
  "calc_votes (px # ps) fp prof votes = 
      (let n = cnt_votes px prof 0;
       i = index fp px in
      calc_votes ps fp prof (list_update votes i n))"

(*
fun calc_votes_mset :: "'a multiset \<Rightarrow>'a multiset \<Rightarrow>  ('a multiset \<times> 'a multiset) set list \<Rightarrow> 'a Votes \<Rightarrow> 'a Votes" where
  "calc_votes_mset empty_mset fp prof votes = votes" |
  "calc_votes_mset ps fp prof votes = 
      (let px = (extract_element ps); 
       mn = ps - px;
       n = cnt_votes_mset px prof 0 in
      calc_votes_mset ps fp prof votes)"
*)

(*
lemma calc_votes_permutation:
  fixes
    p1 :: "'b Parties" and
    p2 ::"'b Parties" and
    profl ::"'b Profile" and
    votes:: "rat list"
  assumes "p1 <~~> p2"
  shows "calc_votes p1 p1 profl votes = calc_votes p2 p2 profl votes"
  using assms
proof (induction p1 arbitrary: p2)
  case Nil
  then show ?case by simp
next
  case (Cons a p1)
  obtain p2' where "p2 <~~> (a # p2')" using assms by (metis Cons.prems)
  then have "(a # p1) <~~> (a # p2')" using assms Cons.prems by auto
  then have "calc_votes (a # p1) (a # p1) profl votes = 
             calc_votes p1 (a # p1) profl  (votes @ [cnt_votes a profl 0])" using assms by simp
  also have "\<dots> = 
             calc_votes p2' (a # p2') profl  (votes @ [cnt_votes a profl 0])" using assms
  by (metis Cons.IH Cons.prems \<open>mset p2 = mset (a # p2')\<close> calc_votes.simps(2) cons_perm_imp_perm list.exhaust mset_zero_iff_right)
  then have "... = calc_votes (a # p2') profl votes" using assms by simp
  then have "... = calc_votes p2 profl votes" by simp
  then show ?case by simp
qed
*)

text \<open> This function receives in input the function Votes and the list of parties. The 
       output is the list of parties with the maximum number of votes.  \<close>

fun max_val_wrap:: "rat list \<Rightarrow> rat" where 
"max_val_wrap v = Max (set v)"

(* i have to prove that for different votes almost the same but with m > v' > v
   then m = m' *)
lemma minus_max:
 assumes "ip = index parties party"
  "size v = size parties" and
  "max_val_wrap v \<noteq> v ! ip" and
  "finite (set v)"
shows "Max(set v) = Max ((set v) - {v ! ip})" 
  by (metis Diff_empty Diff_insert0 Max.remove assms(3) assms(4) max_def max_val_wrap.simps)

(*
lemma max_val_helper_list_helper:
  assumes "parties \<noteq> []"
  assumes "size v = size v'"
  assumes "party \<in> set parties"
  assumes "ip = index parties party" and "x \<noteq> party" 
  assumes "v ! index parties x = v' ! index parties x"
  shows "remove_nth ip v = remove_nth ip v'" using assms by sledgehammer 
 *)
(*
lemma max_val_helper_helper:
  shows "xs ! i \<noteq> x"
  sorry
*)
lemma max_val_helper:
  fixes
  ip::"nat"
  assumes "ip = index parties party"
  "size v = size parties" and "size v' = size parties"
shows "max_val_wrap v = max_val_wrap v'" 
  by sorry

(*
lemma max_val_helper:
  fixes
  ip::"nat"
  assumes "ip = index parties party"
  assumes "x \<noteq> party \<Longrightarrow> v ! index parties x = v' ! index parties x"
  assumes "v' ! ip > v ! ip" and "finite (set v)" and "finite (set v')" and
  "size v = size parties" and "size v' = size parties" and
  "max_val_wrap v \<noteq> v ! ip" and "max_val_wrap v' \<noteq> v' ! ip"
shows "max_val_wrap v = max_val_wrap v'" 
proof - 
  assume "max_val_wrap v \<noteq> max_val_wrap v'" 
  also have "max_val_wrap v = (Max(set v))" by simp
  also have "max_val_wrap v' = (Max(set v'))" by simp
  also obtain x where "v ! x = Max(set v)" 
    using assms by (metis Max_in calculation empty_iff nth_equalityI nth_last_index nth_mem)
  then obtain x' where "v' ! x' = Max(set v')" 
   using assms by (metis Max_in calculation empty_iff nth_equalityI nth_last_index nth_mem)
   then have "x \<noteq> ip" using assms
  by (metis \<open>v ! x = Max (set v)\<close> max_val_wrap.simps)
  then have "x' \<noteq> ip" using assms
  by (metis \<open>v' ! x' = Max (set v')\<close> max_val_wrap.simps)
  then have "v ! x \<noteq> v' ! x'" using assms \<open>v! x = Max(set v)\<close> 
                                          \<open>v'! x' = Max(set v')\<close>
                                          \<open> max_val_wrap v = Max(set v)\<close>
                                          \<open> max_val_wrap v' = Max(set v')\<close>
                                          \<open> max_val_wrap v \<noteq> max_val_wrap v'\<close> 
    by presburger    
  then have "x \<noteq> index parties party" using assms
    using \<open>x \<noteq> ip\<close>
  by metis
  then have "parties ! x \<noteq> party" 
    using assms max_val_helper_helper by presburger
  then have "x' \<noteq> index parties party" using assms
    using \<open>x' \<noteq> ip\<close> by blast
  then have "parties ! x' \<noteq> party" 
    using assms max_val_helper_helper by presburger
  then have "parties ! x = parties ! x'"
    using max_val_helper_helper by presburger
  then have "v ! x = v' ! x'" using assms
    by (metis max_val_helper_helper)
  then show ?thesis sorry
*)

lemma max_val_wrap:
  fixes
  v::"rat list" and
  v'::"rat list"
assumes "set v = set v'"
shows "max_val_wrap v = max_val_wrap v'"
  using assms by simp

lemma max_val_wrap_lemma:
  fixes fvv::"rat list" and fv1::"rat"
  assumes "fv1 = fvv ! i1" and "i1 < length fvv"
  shows "max_val_wrap fvv \<ge> fv1"
  by (simp add: assms)

fun max_p:: "rat \<Rightarrow> rat list \<Rightarrow> 'b Parties
                     \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
"max_p m v ps w = filter (\<lambda>x. v ! (index ps x) = m) ps" 

lemma max_p_ne:
  assumes "party \<in> set ps" and 
    "party \<notin> set (max_p m v ps w)" and 
    "m>0" and 
    "ps \<noteq> []"
  shows "v ! index ps party \<noteq> m"
  using assms by simp

lemma max_p_gt:
  assumes "party \<in> set ps" and 
    "party \<notin> set (max_p m v ps w)" and 
    "m>0" and 
    "ps \<noteq> []" and
    "m = max_val_wrap v" and
    "size v = size ps"
  shows "v ! index ps party < m"
proof - have "v ! index ps party \<noteq> m" using max_p_ne assms by simp
  then have "v ! index ps party \<noteq> Max(set v)" using assms by simp
  then show ?thesis using assms order_neq_le_trans
  by (metis index_less_size_conv max_val_wrap.elims max_val_wrap_lemma)
qed

(*
lemma max_p_no_empty:
  fixes m::"rat" and v::"rat list" and parties::"'b list" and il::"nat list"
  assumes "m = Max (set v)"
  assumes "m > 0"
  assumes "(set v) \<noteq> {}" and
  "finite (set v)"
  assumes "length v = length parties"
  assumes "parties \<noteq> []"
  assumes "\<forall>i j. i \<noteq> j \<Longrightarrow> parties ! i \<noteq> parties ! j"
  shows "max_p m v parties w \<noteq> []"
proof - 
  have "m = Max (set v)" 
    using assms by simp
  then have "Max(set v) \<in> (set v)" 
    using assms by simp
  then have "\<exists>y. y \<in> set parties \<Longrightarrow> Max(set v) = v ! index parties y \<Longrightarrow> filter (\<lambda>x. v ! (index parties x) = Max(set v)) parties \<noteq> []" 
    using assms by sledgehammer
  then show ?thesis
*)


lemma P_no:
  fixes m::"rat" and v::"rat list" and ps::"'b list"
  assumes 
    "x \<in> set xs" and  
    "\<not>(P x)"
  shows "x \<notin> set (filter(\<lambda>x. P x) xs)"
  using assms by simp

lemma filter_loss:
  fixes m::"rat" and v::"rat list" and ps::"'b list"
  assumes 
    "party \<in> set parties" and
    "m = Max(set v)" and
    "\<not> (v ! (index parties party) = m)"
  shows "party \<notin> set (filter (\<lambda>x. v ! (index parties x) = m) parties)"
  using assms by simp

lemma max_p_loss:
  fixes m::"rat" and v::"rat list" and ps::"'b list"
  assumes 
    "party \<in> set parties" and
    "m = Max(set v)" and
    "\<not> (v ! (index parties party) = m)"
  shows "party \<notin> set (max_p m v parties w)"
  using assms by simp

lemma max_p_in_win:
  fixes v::"rat list" and m::"rat"
  assumes "v ! (index ps px) = m" and "px \<in> set ps"
  shows "px \<in> set (max_p m v ps [])"
proof - have "max_p m v ps [] = filter (\<lambda>x. v ! (index ps x) = m) ps" using assms by simp
  then have "px \<in> set (filter (\<lambda>x. v ! (index ps x) = m) ps)"
    using assms by auto
then show ?thesis by simp
qed

fun empty_v :: "'b \<Rightarrow> rat" where
  "empty_v p = 0"

lemma max_parties_no_in:
  assumes "px \<notin> set sw"
  assumes "m > 0"
  assumes "v ! (index ps px) = 0"
  shows "px \<notin> set (max_p m v ps sw)"
  using assms by (induction ps sw rule: max_p.induct) auto

lemma max_parties_no_in_empty:
  assumes "m > 0"
  assumes "v ! (index ps px) = 0"
  shows "px \<notin> set (max_p m v ps [])"
  using assms max_parties_no_in by simp

fun get_winners :: "rat list \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
  "get_winners v p = (let m = max_val_wrap v in max_p m v p [])"

lemma get_winners_gt:
  assumes "party \<in> set ps" and 
    "party \<notin> set (get_winners v ps)" and 
    "ps \<noteq> []" and
    "size v = size ps"
  shows "v ! index ps party < max_val_wrap v"
proof - 
  have "party \<notin> set (max_p (max_val_wrap v) v ps [])" 
    using assms by simp
  then show ?thesis
    using assms index_less_size_conv max_p_in_win max_val_wrap_lemma order_le_imp_less_or_eq
    by metis
qed

lemma get_winners_no_empty:
  fixes m::"rat" and v::"rat list" and ps::"'b list"
  assumes "\<forall>i j. p ! i \<noteq> p ! j"
  shows "get_winners v ps \<noteq> []"
  using assms by blast

lemma get_winners_loss:
  fixes m::"rat" and v::"rat list" and ps::"'b list"
  assumes 
    "party \<in> set parties" and
    "(v ! (index parties party) \<noteq> Max(set v))"
  shows "party \<notin> set (get_winners v parties)"
  using assms by simp

theorem get_winners_in_win:
  fixes fv::"rat list" and m::"rat"
  assumes "fv ! (index ps px) = max_val_wrap fv"
  assumes "get_winners fv ps \<noteq> []" and "px \<in> set ps"
  shows "px \<in> set (get_winners fv ps)"
proof - have "get_winners fv ps = (let m = max_val_wrap fv in max_p m fv ps [])" 
    using get_winners.simps by blast
  then have "... = max_p (max_val_wrap fv) fv ps []" by simp
  then show ?thesis using assms by simp
qed

(*
lemma get_winners_perm:
  fixes 
  v::"rat list" and p::"'b list"
assumes "p \<noteq> []"
assumes "v \<noteq> []"
assumes "\<forall>x \<in> set p. (v ! index ps x = v' ! index ps' x)"
assumes "set (p') = set (p)"
assumes "set (v') = set (v)"
shows "set (get_winners v' p') = set (get_winners v p)"
proof - 
  have "get_winners v p = (let m = max_val_wrap v in max_p m v p [])" 
    using assms by simp
  then have " ... = max_p (max_val_wrap v) v p []" by simp
  then have "max_val_wrap v = max_val_wrap v'" using assms by simp
  then have "get_winners v' p' = (let m = max_val_wrap v' in max_p m v' p' [])" by simp
  then have " ... =  max_p (max_val_wrap v') v' p' []" using assms by simp
  then have " ... = max_p (max_val_wrap v) v' p' []" using assms by simp
  then show ?thesis by sledgehammer
*)

lemma get_winners_not_in_win:
  fixes fv::"rat list" and m::"rat"
  assumes "fv ! (index ps px) \<noteq> max_val_wrap fv"
  assumes "get_winners fv ps \<noteq> []"
  shows "px \<noteq> hd (get_winners fv ps)"
proof - 
  have "get_winners fv ps = (let m = max_val_wrap fv in max_p m fv ps [])" 
    using get_winners.simps by blast
  then have "px \<notin> set (max_p (max_val_wrap fv) fv ps [])" 
    using assms by simp
  then show ?thesis 
    using hd_in_set assms 
          \<open>get_winners fv ps = (let m = max_val_wrap fv in max_p m fv ps [])\<close> by metis
qed

lemma find_max_votes_not_empty:
  fixes
  v::"rat list" and
  p::"'b Parties"
  assumes "p \<noteq> []"
  shows "get_winners v p \<noteq> []"
  using assms
  sorry

fun update_seat :: "'a::linorder \<Rightarrow> 'b list \<Rightarrow> ('a::linorder, 'b) Seats 
                    \<Rightarrow> ('a::linorder, 'b) Seats" where
  "update_seat seat w seats = seats(seat := w)"

text \<open> This function counts seats of a given party. \<close>

fun cnt_seats :: "'b list \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "cnt_seats p s i = card {ix. ix \<in> i \<and> s ix = p}"

(*
lemma anonymous_total:
  fixes
parties::"'b Parties" and
parties'::"'b Parties" and
votes::"rat list" and
votes'::"rat list"
assumes "mset parties = mset parties'"
assumes "mset votes = mset votes'"
shows "get_winners votes parties = get_winners votes' parties'"
  sorry
*)

end