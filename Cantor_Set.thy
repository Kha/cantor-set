theory Cantor_Set
imports Main Real Series
begin

subsection {* Definition of the Cantor Set *}

fun cantor_n where
  "cantor_n 0 = {0::real..1}"
| "cantor_n (Suc n) = (\<lambda>x. x/3) ` cantor_n n \<union> (\<lambda>x. 2/3 + x/3) ` cantor_n n"
definition "cantor \<equiv> \<Inter>range cantor_n"

subsection {* Representing reals from [0,1] to base n *}

definition n_ary :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "n_ary n f \<longleftrightarrow> n > 1 \<and> range f \<subseteq> {0..<n}"
lemmas n_aryI = n_ary_def[THEN iffD2]
lemma n_ary_n_gt_1[simp]: "n_ary n f \<Longrightarrow> n > 1"
  by (simp add:n_ary_def)
lemma le_diff_1[simp]: "(n::nat) < m \<Longrightarrow> n \<le> m - 1"
  by (metis Suc_diff_1 Suc_leI le_less_trans not_less zero_less_Suc)
lemma n_ary_le[simp]: "n_ary n f \<Longrightarrow> f i \<le> n - 1"
  by (rule le_diff_1, auto simp:n_ary_def image_def)

definition n_ary_series :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> real" where
  "n_ary_series n f = (\<lambda>k. f k * (1 / n) ^ Suc k)"
declare power_Suc[simp del]

lemma summable_geometric': "norm (c::real) < 1 \<Longrightarrow> summable (\<lambda>k. c ^ (Suc k))"
  apply (rule summable_ignore_initial_segment[of _ 1, simplified Suc_eq_plus1[symmetric]])
  apply (rule summable_geometric)
  by simp

lemma suminf_geometric': "norm (c::real) < 1 \<Longrightarrow> (\<Sum>n. c ^ Suc n) = c / (1 - c)"
  apply (subst suminf_minus_initial_segment[of _ 1, simplified Suc_eq_plus1[symmetric]])
  apply (erule summable_geometric)
  apply (subst suminf_geometric, simp, simp)
  apply (subst mult_right_cancel[of "1 - c", symmetric])
  by (auto simp:left_diff_distrib)

text {* The n-ary representation of 1. *}
definition "period_one n \<equiv> n_ary_series n (\<lambda>_. n - 1)"

lemma period_one_summable[simp]: "n > 1 \<Longrightarrow> summable (period_one n)"
  by (auto simp:n_ary_series_def period_one_def intro!:summable_geometric' summable_mult)

lemma[simp]: "n > 1 \<Longrightarrow> suminf (period_one n) = 1"
  unfolding period_one_def n_ary_series_def
  apply (subst suminf_mult)
  apply (rule summable_geometric')
  apply simp
  apply (subst suminf_geometric')
  by (auto simp:right_diff_distrib)

lemma period_one_skip_initial_segment[simp]:
  "n > 1 \<Longrightarrow> (\<Sum>k. period_one n (k + i)) = (1/n) ^ i * suminf (period_one n)"
  by (subst suminf_mult[symmetric], simp, rule arg_cong[where f=suminf], auto simp:period_one_def n_ary_series_def power_Suc power_add)

lemma n_ary_summable[simp]:
  assumes "n_ary n f"
  shows "summable (n_ary_series n f)"
proof (rule summableI_nonneg_bounded[where x="suminf (period_one n)"])
  fix k
  show "0 \<le> n_ary_series n f k" using assms by (auto simp:n_ary_def n_ary_series_def intro!:mult_nonneg_nonneg)
  have "setsum (n_ary_series n f) {..<k} \<le> setsum (period_one n) {..<k}"
    using assms n_ary_n_gt_1[OF assms]
    by (auto simp:n_ary_series_def n_ary_le[simplified One_nat_def] period_one_def intro!:setsum_mono)
  also have "... \<le> suminf (period_one n)" using assms
    by - (rule setsum_le_suminf, rule period_one_summable, rule n_ary_n_gt_1, auto simp:period_one_def n_ary_series_def)
  finally show "setsum (n_ary_series n f) {..<k} \<le> suminf (period_one n)" .
qed

lemma[simp]: "n_ary n f \<Longrightarrow> suminf (n_ary_series n f) \<ge> 0"
  by (rule suminf_nonneg, simp) (auto simp:n_ary_series_def)

subsection {* A bijection between the Cantor Set and a subset of ternary representations *}

abbreviation "cantor_ary f \<equiv> n_ary 3 f \<and> (\<forall>i. f i \<noteq> 1)"
 
lemma cantor_aryE:
  assumes "cantor_ary f"
  shows "f i \<in> {0,2}"
proof-
  from assms have "f i \<noteq> 1" "f i \<in> {0..<3}" by (auto simp only:n_ary_def)
  thus ?thesis by auto
qed

lemma cantor_ary_inj_aux:
  assumes a: "cantor_ary a"
  assumes b: "cantor_ary b"
  assumes ord: "a i < b i" "\<forall>j<i. a j = b j"
  assumes eq: "suminf (n_ary_series 3 a) = suminf (n_ary_series 3 b)"
  shows False
proof-
  have[simp]: "n_ary 3 a" "n_ary 3 b" using a b by simp_all
  have[simp]: "a i = 0" "b i = 2"
    using cantor_aryE[OF a, of i] cantor_aryE[OF b, of i] ord(1) by auto
  have[simp]: "n_ary_series 3 b i = 2 * (1/3) ^ Suc i" by (auto simp:n_ary_series_def)

  note summable_ignore_initial_segment[simp]
  note add_Suc_right[simp del]

  have "suminf (n_ary_series 3 a) = (\<Sum>n. n_ary_series 3 a (n + i)) + setsum (n_ary_series 3 a) {..<i}"
    by (rule suminf_split_initial_segment, simp)
  also have "(\<Sum>n. n_ary_series 3 a (n + i)) = (\<Sum>n. n_ary_series 3 a (n + Suc i))"
    by (subst suminf_split_initial_segment[where k=1]) (simp, simp add:n_ary_series_def add_Suc_right)
  also have "... \<le> (\<Sum>n. period_one 3 (n + Suc i))"
  proof-
    have "\<And>i. a i \<le> 2"
      using a by (metis One_nat_def diff_Suc_Suc diff_zero eval_nat_numeral(3) n_ary_le)
    hence "\<And>i. real (a i) \<le> 2"
      by (metis antisym_conv linear natceiling_le_eq natceiling_numeral_eq real_of_nat_numeral) (* ok... *)
    thus ?thesis by - (rule suminf_le, simp add:n_ary_series_def period_one_def, simp_all)
  qed
  also have "... = (1/3) ^ Suc i" by simp
  also have "... < 2 * (1/3) ^ Suc i" by simp
  also have "... \<le> (\<Sum>n. n_ary_series 3 b (n + i))"
  proof-
    have "0 \<le> (\<Sum>n. n_ary_series 3 b (n + Suc i))" by (rule suminf_nonneg, simp, simp add:n_ary_series_def)
    thus ?thesis by (subst suminf_split_initial_segment[where k=1]) (auto simp add:add_Suc_right)
  qed
  also have "... + setsum (n_ary_series 3 a) {..<i} = suminf (n_ary_series 3 b)"
  proof-
    have 1: "setsum (n_ary_series 3 a) {..<i} = setsum (n_ary_series 3 b) {..<i}" using ord(2) by (auto simp:n_ary_series_def)
    show ?thesis by (subst 1) (rule suminf_split_initial_segment[symmetric], simp)
  qed
  finally show False using eq by auto
qed

lemma ex_least: "P (n::nat) \<Longrightarrow> \<exists>m. P m \<and> (\<forall>i<m. \<not>P i)"
  by (metis ex_least_nat_le not_less0)

lemma cantor_ary_inj: "inj_on (suminf \<circ> n_ary_series 3) {f. cantor_ary f}"
proof (rule inj_onI, simp del:One_nat_def)
  fix a b
  assume asms: "cantor_ary a" "cantor_ary b" "suminf (n_ary_series 3 a) = suminf (n_ary_series 3 b)"

  show "a = b"
  proof (rule ccontr)
    assume "a \<noteq> b"
    then obtain i where "a i \<noteq> b i" by auto
    from ex_least[of "\<lambda>j. a j \<noteq> b j", OF this] obtain i where i: "a i \<noteq> b i" "\<forall>j<i. a j = b j" by auto
    show False
    proof (cases "a i < b i")
      case True
      thus ?thesis using asms i(2) by - (rule cantor_ary_inj_aux)
    next
      case False
      with i(1) have "b i < a i" by auto
      thus ?thesis using asms i(2) by - (rule cantor_ary_inj_aux[OF asms(2,1)], auto)
    qed
  qed
qed

definition "left_points n = {setsum (n_ary_series 3 f) {0..<n} |f. n_ary 3 f \<and> (\<forall>k \<in> {0..<n}. f k \<in> {0,2})}"
abbreviation "segment n l \<equiv> {l..l+(1/3)^n}"

lemma image_Union': "f ` \<Union>A = \<Union>((op ` f) ` A)" by auto

lemma "cantor_n n = \<Union>(segment n ` left_points n)"
proof (induct n)
  case 0
  have "n_ary 3 (\<lambda>_. 0)" by (auto simp:n_ary_def)
  hence "left_points 0 = {0}" by (auto simp:left_points_def)
  thus ?case by auto
next
  case (Suc n)
  have "\<And>(x::real) c A. x \<in> (\<lambda>x. c + x/3) ` A \<longleftrightarrow> x-c \<in> (\<lambda>x. x/3) ` A" by (auto intro!:image_eqI)
  hence 1: "\<And>c. op ` (\<lambda>(x::real). c + x / 3) \<circ> segment n = segment (Suc n) \<circ> (\<lambda>x. c + x / 3)" by - (rule ext, auto simp:power_Suc)
  have "(\<lambda>x. x/3) ` cantor_n n = \<Union>(segment (Suc n) ` (\<lambda>x. x/3) ` left_points n)"
   by (simp only:Suc.hyps image_Union') (rule arg_cong[where f=Union], simp add:image_comp 1[of 0, simplified])
  moreover have "(\<lambda>x. 2/3 + x/3) ` cantor_n n = \<Union>(segment (Suc n) ` (\<lambda>x. 2/3 + x/3) ` left_points n)"
    by (simp only:Suc.hyps image_Union') (rule arg_cong[where f=Union], simp add:image_comp 1)
  ultimately show ?case
    apply (simp add:Union_Un_distrib[symmetric] del:Sup_image_eq Union_Un_distrib)
    apply (rule arg_cong[where f=Union])
    apply auto
oops

lemma "cantor = (suminf \<circ> n_ary_series 3) ` {f. cantor_ary f}"
oops

theorem "bij_betw (suminf \<circ> n_ary_series 3) {f. cantor_ary f} cantor"
oops

end
