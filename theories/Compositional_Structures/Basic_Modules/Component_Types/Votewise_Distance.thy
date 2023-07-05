(*  File:       Votewise_Distance.thy
    Copyright   2022  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Marion Steinriede, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Votewise Distance\<close>

theory Votewise_Distance
  imports "Norm"
          "Distance"
begin

text \<open>
  Votewise distances are a natural class of distances on elections distances
  which depend on the submitted votes in a simple and transparent manner.
  They are formed by using any distance d on individual orders and combining
  the components with a norm on R to n.
\<close>

subsection \<open>Definition\<close>

fun votewise_distance :: "'a Vote Distance \<Rightarrow> Norm \<Rightarrow> 'a Election Distance" where
  "votewise_distance d n (A, p) (A', p') =
    (if length p = length p' \<and> (0 < length p \<or> A = A')
    then n (map2 (\<lambda> q q'. d (A, q) (A', q')) p p')
    else \<infinity>)"

subsection \<open>Inference Rules\<close>

lemma symmetric_norm_imp_distance_anonymous:
  fixes
    d :: "'a Vote Distance" and
    n :: "Norm"
  assumes "symmetry n"
  shows "distance_anonymity (votewise_distance d n)"
proof (unfold distance_anonymity_def, safe)
  fix
    A  :: "'a set" and
    A' :: "'a set" and
    pi :: "nat \<Rightarrow> nat \<Rightarrow> nat" and
    p  :: "'a Profile" and
    p' :: "'a Profile"
  let ?z = "zip p p'" and
      ?lt_len = "\<lambda> i. {..< length i}" and
      ?pi_len = "\<lambda> i. pi (length i)" and
      ?c_prod = "case_prod (\<lambda> q q'. d (A, q) (A', q'))"
  let ?listpi = "\<lambda> q. permute_list (?pi_len q) q"
  let ?q = "?listpi p" and
      ?q' = "?listpi p'"
  assume perm: "\<forall> n. pi n permutes {..< n}"
  hence listpi_sym: "\<forall> l. ?listpi l <~~> l"
    using mset_permute_list
    by metis
  show "votewise_distance d n (A, p) (A', p') = votewise_distance d n (A, ?q) (A', ?q')"
  proof (cases "length p = length p' \<and> (0 < length p \<or> A = A')")
    case False
    thus ?thesis
      using perm
      by auto
  next
    case True
    hence "votewise_distance d n (A, p) (A', p') = n (map2 (\<lambda> x y. d (A, x) (A', y)) p p')"
      by auto
    also have "\<dots> = n (?listpi (map2 (\<lambda> x y. d (A, x) (A', y)) p p'))"
      using assms listpi_sym
      unfolding symmetry_def
      by (metis (no_types, lifting))
    also have "\<dots> = n (map (case_prod (\<lambda> x y. d (A, x) (A', y))) (?listpi (zip p p')))"
      using permute_list_map[of \<open>?pi_len p\<close> ?z ?c_prod] perm True
      by simp
    also have "\<dots> = n (map2 (\<lambda> x y. d (A, x) (A', y)) (?listpi p) (?listpi p'))"
      using permute_list_zip[of \<open>?pi_len p\<close> \<open>?lt_len p\<close> p p'] perm True
      by simp
    also have "\<dots> = votewise_distance d n (A, ?listpi p) (A', ?listpi p')"
      using True
      by auto
    finally show ?thesis
      by simp
  qed
qed

end
