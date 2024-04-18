


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

text \<open> Auxiliary Code \<close> 

definition above_set :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "above_set r a \<equiv> above (set r) a"

lemmas [code] = above_set_def[symmetric]
lemma [code]:
  \<open>above_set [] a = {}\<close>
  \<open>above_set ((x,y)#xs) a = (if x=a then {y} else {}) \<union> above_set xs a\<close>
  by (auto simp: above_set_def above_def)

definition remove_some :: "'a multiset \<Rightarrow> 'a" where
"remove_some M = (SOME x. x \<in> set_mset M)"

fun empty_votes :: "char list \<Rightarrow> rat" where
  "empty_votes p = 0"

text \<open> This function returns the rank of one candidate over a ballot. \<close>
fun count_above :: "('a rel) \<Rightarrow> 'a \<Rightarrow> nat" where
  "count_above r a = card (above r a)"

fun count_above_mset :: "('a multiset rel) \<Rightarrow>'a multiset \<Rightarrow> nat" where
  "count_above_mset r a = card (above r a)"

subsection  \<open>Definition\<close>
text  \<open>Parties is the list of candidates that can be of any polymorphic type 'b. \<close>
type_synonym 'b Parties = "'b list"

text  \<open>Every seat is unique and has a set of parties to which it is assigned. 
       In the most common case, when it will be assigned to one party, it will be a 
       single element list. 
       In case of a tie, all the tied parties will be in the list, giving the chance in the 
       output to easily which parties contend for the seat. \<close>

type_synonym ('a, 'b) Seats = "'a \<Rightarrow> 'b list"

type_synonym Params = "nat list"

text \<open> This function retrieves the votes for the specified party. \<close>

fun get_votes :: "'b \<Rightarrow> 'b Parties \<Rightarrow> nat list \<Rightarrow> nat" where
"get_votes px ps v = v ! index ps px"

text \<open> This function counts votes for one party and add returns the number of votes. \<close>

fun cnt_votes :: "'a \<Rightarrow> 'a Profile \<Rightarrow> nat \<Rightarrow> nat" where
  "cnt_votes p [] n = n" |
  "cnt_votes p (px # pl) n = 
     (case (count_above px p) of
        0 \<Rightarrow> cnt_votes p pl (n + 1)
      | _ \<Rightarrow> cnt_votes p pl n)"

fun cnt_votes_mset :: "'a multiset \<Rightarrow> (('a multiset \<times> 'a multiset) set) list \<Rightarrow> nat \<Rightarrow> nat" 
  where
  "cnt_votes_mset p [] n = n" |
  "cnt_votes_mset p (px # profil) n = 
     (case (count_above_mset px p) of
        0 \<Rightarrow> cnt_votes_mset p profil (n + 1)
      | _ \<Rightarrow> cnt_votes_mset p profil n)"

text \<open> This function receives in input the list of parties and the list of preferation 
       relations. The output is a list in which every party has the 
       correspondent number of votes. \<close>

fun calc_votes :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a Profile \<Rightarrow> nat list \<Rightarrow> nat list" where
  "calc_votes [] fp pl votes = votes" |
  "calc_votes (px # ps) fp pl votes = 
      (let n = cnt_votes px pl 0;
       i = index fp px in
      calc_votes ps fp pl (list_update votes i n))"

text \<open> This function calculates the maximum number of votes. \<close>

fun max_v:: "'a::linorder list \<Rightarrow> 'a::linorder" where 
"max_v v = Max (set v)"

fun max_p:: "'a::linorder \<Rightarrow>'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" 
  where
"max_p m v ps = filter (\<lambda>x. v ! (index ps x) = m) ps" 

fun empty_v :: "'b \<Rightarrow> rat" where
  "empty_v p = 0"

text \<open> This function calculates the winners between candidates according to the votes. \<close>

fun get_winners :: "'a::linorder list \<Rightarrow> 'b Parties \<Rightarrow> 'b Parties" where
  "get_winners v p = (let m = max_v v in max_p m v p)"

text \<open> This function assigns the n-th seat to the winner. \<close>

fun update_seat :: "'a::linorder \<Rightarrow> 'b list \<Rightarrow> ('a::linorder, 'b) Seats 
                    \<Rightarrow> ('a::linorder, 'b) Seats" where
  "update_seat seat w seats = seats(seat := w)"

text \<open> This function counts seats of a given party. \<close>

fun cnt_seats :: "'b list \<Rightarrow> ('a::linorder, 'b) Seats \<Rightarrow> 
                    'a::linorder set => nat" where
  "cnt_seats p s i = card {ix. ix \<in> i \<and> s ix = p}"

text \<open> Auxiliary Lemmas \<close>

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


lemma minus_max:
 assumes "ip = index parties party"
  "size v = size parties" and
  "max_v v \<noteq> v ! ip" and
  "finite (set v)"
shows "Max(set v) = Max ((set v) - {v ! ip})" 
  by (metis Diff_empty Diff_insert0 Max.remove assms(3) assms(4) max_def max_v.simps)

lemma max_val_wrap:
  fixes
  v::"rat list" and
  v'::"rat list"
assumes "set v = set v'"
shows "max_v v = max_v v'"
  using assms by simp

lemma max_val_wrap_lemma:
  fixes fv::"rat list"
  assumes "fvx = fv ! i" and "i < length fv"
  shows "max_v fv \<ge> fvx"
  by (simp add: assms)

lemma max_p_ne:
  assumes "p \<in> set ps" and 
    "p \<notin> set (max_p m v ps)" and 
    "m>0" and 
    "ps \<noteq> []"
  shows "v ! index ps p \<noteq> m"
  using assms by simp


text \<open> This lemma shows that max_p output cannot be empty. \<close>
lemma max_p_no_empty:
  assumes "m = Max (set v)" and
  "(set v) \<noteq> {}" and
  "length v = length ps" and
  "\<And>i j. i \<noteq> j \<Longrightarrow> ps ! i \<noteq> ps ! j"
  shows "max_p m v ps \<noteq> []"
proof - 
  have "Max(set v) \<in> (set v)" 
    using assms(2) by auto
  then show ?thesis
    using \<open>Max (set v) \<in> set v\<close> assms empty_filter_conv in_set_conv_nth max_p.simps 
          nth_index nth_mem by (smt (verit))
qed

lemma P_no:
  assumes 
    "x \<in> set xs" and  
    "\<not>(P x)"
  shows "x \<notin> set (filter(\<lambda>x. P x) xs)"
  using assms by simp

lemma filter_loss:
  assumes 
    "p \<in> set ps" and
    "m = Max(set v)" and
    "\<not> (v ! (index ps p) = m)"
  shows "p \<notin> set (filter (\<lambda>x. v ! (index ps x) = m) ps)"
  using assms by simp

lemma max_p_loss:
  assumes 
    "p \<in> set ps" and
    "m = Max(set v)" and
    "\<not> (v ! (index ps p) = m)"
  shows "p \<notin> set (max_p m v ps)"
  using assms by simp

lemma max_p_in_win:
  assumes 
"v ! (index ps px) = m" and 
"px \<in> set ps"
  shows "px \<in> set (max_p m v ps)"
proof - 
  have "max_p m v ps = filter (\<lambda>x. v ! (index ps x) = m) ps" 
    using assms by simp
  then have "px \<in> set (filter (\<lambda>x. v ! (index ps x) = m) ps)"
    using assms by auto
  then show ?thesis 
    by simp
qed

lemma get_winners_no_empty:
  assumes "\<forall>i j. p ! i \<noteq> p ! j"
  shows "get_winners v ps \<noteq> []"
  using assms by blast

lemma get_winners_loss:
  assumes 
    "p \<in> set ps" and
    "(v ! (index ps p) \<noteq> Max(set v))"
  shows "p \<notin> set (get_winners v ps)"
  using assms by simp

text \<open> This theorem proves that if a party has the max votes, then it is in the list of 
        winners. \<close>

theorem get_winners_in_win:
  assumes 
    "fv ! index ps px = max_v fv" and 
    "px \<in> set ps"
  shows "px \<in> set (get_winners fv ps)"
proof - 
  have "get_winners fv ps = (let m = max_v fv in max_p m fv ps)" 
    using get_winners.simps by blast
  then have "... = max_p (max_v fv) fv ps" 
    by simp
  then show ?thesis 
    using assms max_p_in_win \<open>get_winners fv ps = (let m = max_v fv in max_p m fv ps)\<close> by metis
qed

lemma get_winners_not_in_win:
  assumes   
    "fv ! (index ps px) \<noteq> max_v fv" and 
    "get_winners fv ps \<noteq> []"
  shows "px \<noteq> hd (get_winners fv ps)"
proof - 
  have "get_winners fv ps = (let m = max_v fv in max_p m fv ps)" 
    using get_winners.simps by blast
  then have "px \<notin> set (max_p (max_v fv) fv ps)" 
    using assms by simp
  then show ?thesis 
    using \<open>get_winners fv ps = (let m = max_v fv in max_p m fv ps)\<close> 
          hd_in_set assms by metis
qed

lemma get_winners_only_winner:
  assumes "fv ! (index ps px) = max_v fv" and 
    "\<forall>x \<noteq> index ps px. fv ! (index ps x) < max_v fv" and 
    "get_winners fv ps \<noteq> []"
shows "px = hd (get_winners fv ps)"
  using get_winners_not_in_win verit_comp_simplify1(1) assms 
  by metis

lemma get_winners_weak_winner_implies_helper:
  assumes "x < size fv"
  shows "Max(set fv) \<ge> fv ! x" 
  using assms by simp

lemma max_val_wrap_eqI_helper:
  assumes 
"\<And>y. y \<in> (set fv) \<Longrightarrow> y \<le> fv ! x" and 
"fv ! x \<in> (set fv)"
  shows "Max(set fv) = fv ! x"
  using Max_eqI assms by blast

lemma max_eqI_helper:
  assumes 
"x < length l" and 
"length l = length l'" and
"l ! x = Max(set l)" and
"l' ! x > l ! x" and 
"\<And>y. y \<noteq> x \<Longrightarrow> y < length l \<Longrightarrow> l' ! y \<le> l ! y" 
shows "l' ! x = Max (set l')"
proof(rule ccontr)
  assume "l' ! x \<noteq> Max (set l')"
  then have "\<exists>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> Max(set l') = l' ! y" 
    by auto
  then have "\<And>y. y < length l \<Longrightarrow> l ! y \<le> Max(set l)" 
    by simp 
  then have "\<And>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> l' ! y \<le> Max(set l)"
    by (meson assms(5) dual_order.trans)
  then have "Max(set l') > Max(set l)"
    using assms dual_order.strict_trans1 
          get_winners_weak_winner_implies_helper by metis
  then have "\<And>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> l' ! y < Max(set l')"
    using \<open>\<And>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> l' ! y \<le> Max (set l)\<close> by fastforce
  then show False 
    using \<open>\<exists>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> Max(set l') = l' ! y\<close> 
          \<open>\<And>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> l' ! y < Max(set l')\<close> assms
          \<open>\<And>y. y \<noteq> x \<longrightarrow> y < length l \<longrightarrow> l' ! y \<le> Max (set l)\<close> 
          \<open>l' ! x \<noteq> Max (set l')\<close> in_set_conv_nth leD linorder_le_cases 
          max_val_wrap_eqI_helper order.strict_trans2
  by (metis (no_types, opaque_lifting))
qed

lemma max_eqI:
assumes
"index ps px < length fv" and
"length fv = length fv'" and
"fv ! index ps px = Max(set fv)" and
"fv' ! index ps px > fv ! index ps px" and
"\<And>y. y \<noteq> index ps px \<Longrightarrow> y < length fv \<Longrightarrow> fv' ! y \<le> fv ! y"
shows "Max(set fv') = fv' ! index ps px"
  using assms max_eqI_helper by metis

text \<open> This lemma proves that if a party wins, then if its votes increases, 
       it wins again. \<close>

lemma get_winners_weak_winner_implies:
assumes
"index ps px < length fv" and
"length fv = length fv'" and
"px \<in> set ps" and
"fv ! index ps px = Max(set fv)" and
"fv' ! index ps px > fv ! index ps px" and
"\<And>y. y \<noteq> index ps px \<Longrightarrow> y < length fv \<Longrightarrow> fv' ! y \<le> fv ! y"
shows "px \<in> set (get_winners fv' ps)"
  using assms get_winners_in_win max_eqI_helper max_v.simps by metis

lemma filter_size_is_one_helper:
  fixes
fv::"'a :: linorder list"
assumes
"x < length fv" and
"fv ! x = m" and
strict_le: "\<And>y. y \<noteq> x \<Longrightarrow> y < length fv \<Longrightarrow> fv ! y < m"
shows "length (filter (\<lambda>x. fv ! x =  m) [0..<length fv]) = 1"
proof -
  have le: \<open>[0..<length fv] = ([0..<x] @ [x] @ [Suc x ..< length fv])\<close>
    using \<open>fv ! x = m\<close> append_Cons assms(1) leI le_add_diff_inverse less_imp_le_nat 
        not_less_zero self_append_conv2 upt_add_eq_append upt_rec
    by metis
  show \<open>length (filter (\<lambda>x. fv ! x =  m) [0..<length fv]) = 1\<close>
    using strict_le assms unfolding le by (force simp: filter_empty_conv)
qed

lemma filter_size_is_one_helper_my_case:
  fixes
fv::"rat list"
assumes
"index ps x < length fv" and
"fv ! index ps x = m" and
strict_le: "\<And>y. y \<noteq> index ps x \<Longrightarrow> y < length fv \<Longrightarrow> fv ! y < m" and 
"length (filter (\<lambda>x. fv ! (index ps x) = m) ps) 
  = length (filter (\<lambda>x. fv ! x =  m) [0..<length fv])"
shows "length (filter (\<lambda>x. fv ! (index ps x) = m) ps) = 1"
  by (metis assms filter_size_is_one_helper)

lemma filter_size_is_one_helper_my_case_3:
  fixes
fv::"'a::linorder list"
assumes
"index ps x < length fv" and
"fv ! index ps x = m" and
strict_le: "\<And>y. y \<noteq> index ps x \<Longrightarrow> y < length fv \<Longrightarrow> fv ! y < m" and 
"length (get_winners fv ps) = length (filter (\<lambda>x. fv ! x =  m) [0..<length fv])"
shows "length (get_winners fv ps) = 1"
  using assms(1) assms(2) assms(4) filter_size_is_one_helper strict_le by auto

text \<open> This theorem states that if one the parties in the winners list gets its 
       votes increased, then it will become the only winner. \<close>
theorem  fixes
fv::"'a::linorder list"
assumes
"party \<in> set parties" and
"index parties party < length fv" and
"m = Max(set fv)" and
"fv ! index parties party = m" and
strict_le: "\<And>y. y \<noteq> index parties party \<Longrightarrow> y < length fv \<Longrightarrow> fv ! y < m" and 
"length (get_winners fv parties) = length (filter (\<lambda>x. fv ! x =  m) [0..<length fv])"
shows "party = hd (get_winners fv parties)"
proof - 
  have "length (get_winners fv parties) = 1" 
    using filter_size_is_one_helper_my_case_3
  by (metis assms(2) assms(4) assms(6) strict_le)
  then have "party \<in> set (get_winners fv parties)" 
    using assms(1) assms(3) assms(4) get_winners_in_win max_v.elims by metis
  then show ?thesis 
    using \<open>length (get_winners fv parties) = 1\<close> \<open>party \<in> set (get_winners fv parties)\<close> 
          hd_conv_nth in_set_conv_nth length_greater_0_conv less_one by metis
qed

text \<open> This lemma states that if a party is in the head of winners, then it has the maximum
       votes. \<close>

lemma get_winners_rev:
  assumes
    "party = hd (get_winners v ps)" and 
    "get_winners v ps \<noteq> []"
  shows "v ! index ps party = max_v v"
proof(rule ccontr)
  assume "v ! index ps party \<noteq> max_v v"
  then have "party \<notin> set (get_winners v ps)" 
    by simp
  then show False
    using assms list.set_sel(1) by blast
qed

end