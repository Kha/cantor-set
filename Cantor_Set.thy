theory Cantor_Set
imports Main Real Series
begin

subsection {* Definition of the Cantor Set *}

definition go_left :: "real \<Rightarrow> real" where "go_left x = x/3"
definition go_right :: "real \<Rightarrow> real" where "go_right x = 2/3 + x/3"

fun cantor_n where
  "cantor_n 0 = {0::real..1}"
| "cantor_n (Suc n) = go_left ` cantor_n n \<union> go_right ` cantor_n n"
definition "cantor \<equiv> \<Inter>range cantor_n"

lemma cantor_bounds:
  assumes "x \<in> cantor"
  shows "0 \<le> x \<and> x \<le> 1"
proof-
  from assms have "x \<in> cantor_n 0" by (auto simp add: cantor_def simp del: cantor_n.simps)
  thus ?thesis by simp
qed

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
lemma n_ary_less[simp]: "n_ary n f \<Longrightarrow> f i < n"
  by (auto simp add: n_ary_def, metis UNIV_I atLeast0LessThan image_eqI lessThan_iff subsetCE)

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

lemma suminf_period_one_1[simp]: "n > 1 \<Longrightarrow> suminf (period_one n) = 1"
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

lemma nary_pos[simp]: "n_ary n f \<Longrightarrow> suminf (n_ary_series n f) \<ge> 0"
  by (rule suminf_nonneg, simp) (auto simp:n_ary_series_def)

lemma nary_le_1[simp]:
  assumes "n_ary n f"
  shows "suminf (n_ary_series n f) \<le> 1"
proof-
  have "suminf (n_ary_series n f) \<le> suminf (period_one n)"
  proof (rule suminf_le, rule)
    fix i
    from `n_ary n f` have "f i < n" by simp
    thus "n_ary_series n f i \<le> period_one n i" 
      unfolding n_ary_series_def period_one_def  by auto
  next
    show "summable (n_ary_series n f)" by (rule n_ary_summable[OF assms])
  next
    show "summable (period_one n)" by (rule period_one_summable[OF n_ary_n_gt_1[OF assms]])
  qed
  also have "\<dots> = 1" by (rule suminf_period_one_1[OF n_ary_n_gt_1[OF assms]])
  finally show ?thesis.
qed
subsection {* The n-arity expansion of a real *}

fun to_nary :: "nat \<Rightarrow>  real \<Rightarrow> (nat \<Rightarrow> nat)"
 where "to_nary n x i = (if x = 1 then n - 1 else natfloor (x * n^(Suc i)) mod n)"

lemma n_ary_to_nary[simp]: "n > 1 \<Longrightarrow> n_ary n (to_nary n x)"
  unfolding n_ary_def by auto

lemma summable_to_nary[simp]: "n > 1 \<Longrightarrow> summable (n_ary_series n (to_nary n x))"
  by (metis n_ary_summable n_ary_to_nary)

lemma natfloor_div_nat:
  assumes "y > 0"
  shows "natfloor (x / real y) = natfloor x div y"
proof-
  have "x \<le> 0 \<or> x \<ge> 0 \<and> x < 1 \<or> 1 \<le> x" by arith
  thus ?thesis
  proof(elim conjE disjE)
    assume *: "1 \<le> x"
    show ?thesis by (rule Real.natfloor_div_nat[OF * assms])
  next
    assume *: "x \<le> 0"
    moreover
    from * assms have "x / y \<le> 0" by (simp add: field_simps)
    ultimately
    show ?thesis by (simp add: natfloor_neg)
  next
    assume *: "x \<ge> 0" "x < 1"
    hence "natfloor x = 0" by (auto intro: natfloor_eq)
    moreover
    from * assms have "x / y \<ge> 0" and "x / y < 1" by (auto simp add: field_simps)
    hence "natfloor (x/y) = 0" by (auto intro: natfloor_eq)
    ultimately
    show ?thesis by simp
  qed
qed

lemma natfloor_mod:
  assumes "n > 1"
  shows "n * natfloor x + natfloor (n * x) mod n = natfloor (n * x)"
proof-
  have "natfloor (n * x) = n * (natfloor (n * x) div n) + natfloor (n * x) mod n"
    by (metis mod_div_equality2)
  also have "natfloor (n * x) div n = natfloor (n * x / n)"
    apply (rule natfloor_div_nat[symmetric])
    using assms by auto
  also have "n * x / n = x" using assms by simp
  finally show ?thesis..
qed


lemma partial_n_ary:
  assumes [simp]: "n > 1"
  assumes "0 \<le> x" "x < 1"
  shows "setsum (n_ary_series n (to_nary n x)) {..<i} = natfloor (x * n^i) / n^i"
proof (induction i)
  case 0
  from assms have "natfloor x = 0" by (auto intro: natfloor_eq)
  thus ?case by simp
next
  case (Suc i)
    have "setsum (n_ary_series n (to_nary n x)) {..<Suc i}
      =  setsum (n_ary_series n (to_nary n x)) {..<i} + n_ary_series n (to_nary n x) i"
     by simp
   also have "\<dots> = natfloor (x * real n ^ i) / real n ^ i + n_ary_series n (to_nary n x) i"
     unfolding Suc.IH..
   also have "\<dots> = natfloor (x * n ^ i) /  n ^ i + (natfloor (x * n ^ Suc i) mod n) / n ^ Suc i"
     using assms(3) by (simp add: n_ary_series_def field_simps)
   also have "\<dots> = (n * natfloor (x * n ^ i) + natfloor (n * (x * n ^ i)) mod n) / n ^ Suc i"
     using `n > 1` by (simp add: field_simps power_Suc)
   also have "\<dots> = natfloor (n * (x * n^i)) / n^Suc i"
     unfolding natfloor_mod[OF assms(1)] ..
   also have "\<dots> = natfloor (x * n^(Suc i)) / n^Suc i" by (simp add: power_Suc field_simps)
   finally
   show ?case by (metis power_real_of_nat)
qed

lemma bounded_0_inverse:
  fixes f :: "nat \<Rightarrow> real"
  assumes "x < 1"
  assumes "c > 0"
  assumes "\<And> i. 0 \<le> f i"
  assumes "\<And> i. f i \<le> c * x^i"
  shows "f ----> 0"
proof(rule tendsto_sandwich[OF eventually_sequentiallyI eventually_sequentiallyI])
  fix n show "0 \<le> f n" by fact
next
  fix n show "f n \<le> c*x^n" by fact
next
  show "(\<lambda>x. 0) ----> 0"  by (rule tendsto_const)
next
  have "0 \<le> x" by (metis assms(2-4) le_less_trans mult.commute mult_zero_left not_less power_one_right real_mult_le_cancel_iff1)
  hence "op ^ x ----> 0" 
    by (rule LIMSEQ_realpow_zero[OF _ assms(1)])
  thus "(\<lambda> i. c * x^i) ----> 0"
    by (rule tendsto_mult_right_zero)
qed

lemma suminf_n_ary_series_to_nary:
  assumes [simp]:"n > 1"
  assumes "0 \<le> x" "x \<le>1"
  shows "suminf (n_ary_series n (to_nary n x)) = x"
proof(cases "x = 1")
  case False with assms(3) have "x < 1" by simp

  have "suminf (n_ary_series n (to_nary n x)) = lim (\<lambda>i. setsum (n_ary_series n (to_nary n x)) {..<i})"
    by (rule suminf_eq_lim)
  also have "\<dots> = lim (\<lambda>i. natfloor (x * n^i) / n^i)"
    unfolding partial_n_ary[OF assms(1,2) `x < 1`] by simp
  also have "\<dots> = x"
  proof(rule limI)
    have "(\<lambda>i. x - (natfloor (x * (n ^ i))) / (n ^ i)) ----> 0"
    proof(rule bounded_0_inverse)
      fix i
      have "natfloor (x * (n^i)) \<le> x * (n^i)" 
          using assms by (simp add: real_natfloor_le field_simps)
      thus "0 \<le> x - natfloor (x * (n^i)) / (n^i)" 
          using assms(1) by (simp add: field_simps)
    next
      fix i 
      have "x * (n^i) - natfloor (x * (n^i)) \<le> 1"
         by (metis comm_monoid_diff_class.diff_cancel le_natfloor_eq_one less_eq_real_def natfloor_neg natfloor_one natfloor_subtract not_le power_0 power_eq_0_iff)
      from divide_right_mono[OF this, where c = "n^i"] assms(1)
      show "x - natfloor (x * (n ^ i)) / (n ^ i) \<le> 1 * (1/n)^i"
        using assms(1) by (simp add: field_simps )
    next
      show "1/n < 1" using assms(1) by auto
    next
      show "0 < (1::real)" by auto
    qed
    thus "(\<lambda>i. (natfloor (x * (n ^ i))) / (n ^ i)) ----> x"
      by (rule LIMSEQ_diff_approach_zero2[OF tendsto_const])
  qed
  finally show ?thesis.
next
  case True
  hence "to_nary n x = (\<lambda>i. n - 1)" by auto
  thus ?thesis
    using True suminf_period_one_1[OF assms(1), unfolded period_one_def]
    by simp
qed

subsection {* A cantor-like set on the representations *}

definition r_go_left :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
  where "r_go_left f = (\<lambda> i. if i = 0 then 0 else f (i - 1))" 
definition r_go_right :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
  where "r_go_right f= (\<lambda> i. if i = 0 then 2 else f (i - 1))" 

fun r_cantor_n where
  "r_cantor_n 0 = {f . n_ary 3 f}"
| "r_cantor_n (Suc n) = r_go_left ` r_cantor_n n \<union> r_go_right ` r_cantor_n n"
definition "r_cantor \<equiv> \<Inter>range r_cantor_n"

subsection {* A bijection between the Cantor Set and a subset of ternary representations *}

abbreviation "cantor_ary f \<equiv> n_ary 3 f \<and> (\<forall>i. f i \<noteq> 1)"

lemma cantor_aryI:
  assumes "\<And> i. f i \<in> {0,2}"
  shows "cantor_ary f"
  using assms
  apply (auto simp add: n_ary_def)
  apply (metis Suc_le_eq eval_nat_numeral(3) order_refl zero_less_numeral)
  apply (metis (no_types) Suc_1 n_not_Suc_n numeral_1_eq_Suc_0 numeral_One)
  done
 
lemma cantor_aryE:
  assumes "cantor_ary f"
  shows "f i \<in> {0,2}"
proof-
  from assms have "f i \<noteq> 1" "f i \<in> {0..<3}" by (auto simp only:n_ary_def)
  thus ?thesis by auto
qed

definition to_real :: "(nat \<Rightarrow> nat) \<Rightarrow> real"
  where "to_real = (\<lambda> f. suminf (n_ary_series 3 f))"


lemma to_real_inj_aux:
  assumes [simp]: "n_ary 3 a"
  assumes [simp]: "n_ary 3 b"
  assumes cantor_at_i: "a i \<in> {0,2}"  "b i \<in> {0,2}" 
  assumes ord: "a i < b i" "\<forall>j<i. a j = b j"
  assumes eq: "to_real a = to_real b"
  shows False
proof-
  have[simp]: "a i = 0" "b i = 2" using ord(1) cantor_at_i by auto
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
      using `n_ary 3 a` by (metis One_nat_def diff_Suc_Suc diff_zero eval_nat_numeral(3) n_ary_le)
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
  finally show False using eq  by (auto simp add: to_real_def)
qed

lemma to_real_inj_aux':
  assumes "n_ary 3 a"
  assumes "n_ary 3 b"
  assumes cantor_at_i: "a i \<in> {0,2}"  "b i \<in> {0,2}" 
  assumes ne: "a i \<noteq> b i" "\<forall>j<i. a j = b j"
  assumes eq: "to_real a = to_real b"
  shows False
proof-
  from ne
  have "a i < b i \<or> b i < a i" by auto
  thus ?thesis
  proof
    assume *: "a i < b i"
    show False by (rule to_real_inj_aux[OF assms(1,2,3,4) * assms(6,7)])
  next
    assume *: "b i < a i"
    moreover
    from ne(2) have "\<forall>j<i. b j = a j" by auto
    moreover
    note eq[symmetric]
    ultimately
    show False by (rule  to_real_inj_aux[OF assms(2,1,4,3)])
  qed
qed

lemma to_real_inj_next:
  assumes "n_ary 3 a" "n_ary 3 b"
  assumes cantor_at_i: "a i \<in> {0,2}"  "b i \<in> {0,2}" 
  assumes eq_so_far: "\<forall>j<i. a j = b j"
  assumes eq: "to_real a = to_real b"
  shows "a i = b i"
  using assms
  by (metis to_real_inj_aux')


lemma ex_least: "P (n::nat) \<Longrightarrow> \<exists>m. P m \<and> (\<forall>i<m. \<not>P i)"
  by (metis ex_least_nat_le not_less0)

lemma cantor_ary_inj: "inj_on to_real {f. cantor_ary f}"
proof (rule inj_onI, simp del:One_nat_def)
  fix a b
  assume asms: "cantor_ary a" "cantor_ary b" "to_real a = to_real b"

  show "a = b"
  proof (rule ccontr)
    assume "a \<noteq> b"
    then obtain i where "a i \<noteq> b i" by auto

    from ex_least[of "\<lambda>j. a j \<noteq> b j", OF this]
    obtain i where i: "a i \<noteq> b i" "\<forall>j<i. a j = b j" by auto

    from asms have "n_ary 3 a" "n_ary 3 b" by auto
    from this cantor_aryE[OF asms(1)] cantor_aryE[OF asms(2)] i asms(3)
    show False by (rule to_real_inj_aux')
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
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> cantor"

  have "cantor_ary (to_nary 3 x)" sorry
  moreover
  from `x \<in> cantor` have "1 < (3::nat)" and  "0 \<le> x" and "x \<le> 1"
    by (auto dest: cantor_bounds)
  hence "x = suminf (n_ary_series 3 (to_nary 3 x))" by (rule suminf_n_ary_series_to_nary[symmetric])
  ultimately
  show "x \<in> (suminf \<circ> n_ary_series 3) ` {f. cantor_ary f}" by auto
next
  fix x 
  assume "x \<in> (suminf \<circ> n_ary_series 3) ` {f. cantor_ary f}"
  then obtain f where "x = suminf (n_ary_series 3 f)" and "cantor_ary f" by auto
  {
  fix n
  have "x \<in> cantor_n n"

  
  
oops

theorem "bij_betw (suminf \<circ> n_ary_series 3) {f. cantor_ary f} cantor"
oops

subsection {* Alternative approach *}


lemma n_ary_go_left[simp]: "n_ary 3 f \<Longrightarrow> n_ary 3 (r_go_left f)"
  by (auto simp add: n_ary_def r_go_left_def)
lemma n_ary_go_right[simp]: "n_ary 3 f \<Longrightarrow> n_ary 3 (r_go_right f)"
  by (auto simp add: n_ary_def r_go_right_def)

lemma r_cantor_n_n_ary[simp]: "f \<in> r_cantor_n n \<Longrightarrow>  n_ary 3 f"
  by (induction n arbitrary: f) auto

lemma r_cantor_n_cantor_ary: "f \<in> r_cantor_n n \<longleftrightarrow> n_ary 3 f \<and> (\<forall>i<n. f i \<in> {0,2})"
proof(intro iffI conjI, erule_tac [3] conjE)
  fix n
  assume "f \<in> r_cantor_n n"
  thus "\<forall>i<n. f i \<in> {0,2}"
  proof(induction n arbitrary: f)
    case (Suc n)
    hence "f \<in> r_go_left ` r_cantor_n n \<or> f \<in> r_go_right ` r_cantor_n n" by simp
    then obtain f' where "f' \<in> r_cantor_n n" and "f = r_go_left f' \<or> f = r_go_right f'" by auto
    from Suc.IH[OF this(1)]
    have "\<forall>i<n. f' i \<in> {0, 2}".
    hence "\<forall>i<n. f (Suc i) \<in> {0, 2}"
      using `f = _ \<or> f = _`
      by (auto simp add:  r_go_left_def   r_go_right_def)
    moreover
    have "f 0 \<in> {0, 2}"
      using `f = _ \<or> f = _`
      by (auto simp add:  r_go_left_def   r_go_right_def)
    ultimately
    show ?case by (metis less_Suc_eq_0_disj)
  qed simp
next
  fix n
  assume "f \<in> r_cantor_n n"
  thus "n_ary 3 f" by (rule r_cantor_n_n_ary)
next
  fix n
  assume "n_ary 3 f" and  "\<forall>i<n. f i \<in> {0, 2}"
  thus "f \<in> r_cantor_n n"
  proof(induction n arbitrary: f)
    case 0 thus ?case by simp
  next
    case (Suc n)
    hence "f 0 = 0 \<or> f 0 = 2" by simp
    hence "f = r_go_left (\<lambda> i. f (Suc i)) \<or> f =  r_go_right (\<lambda> i. f (Suc i))"
      by (auto simp add:  r_go_left_def   r_go_right_def)
    moreover
    from Suc.prems
    have "(\<lambda> i. f (Suc i)) \<in> r_cantor_n n"
      by (auto intro!: Suc.IH simp add: n_ary_def)
    ultimately
    show "f \<in> r_cantor_n (Suc n)" by auto
  qed
qed
  

lemma r_cantor_cantor_ary:"f \<in> r_cantor \<longleftrightarrow> cantor_ary f"
proof-
  have "f \<in> r_cantor \<longleftrightarrow> (\<forall>n. f \<in> r_cantor_n n)" by (auto simp add: r_cantor_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>n. n_ary 3 f \<and> (\<forall>i<n. f i \<in> {0,2}))" unfolding r_cantor_n_cantor_ary..
  also have "\<dots> \<longleftrightarrow> n_ary 3 f \<and> (\<forall>n. f n \<in> {0,2})" by auto
  also have "\<dots> \<longleftrightarrow> cantor_ary f" by (metis cantor_aryE cantor_aryI)
  finally show ?thesis.
qed

lemma n_ary_series_div[simp]: "n_ary_series n f i / n = n_ary_series n (\<lambda> i. f (i - 1)) (Suc i)"
  unfolding n_ary_series_def
  by (simp add: power_Suc)

lemma suminf_split_first:
  assumes "summable (f :: nat \<Rightarrow> real)"
  shows "suminf f = (\<Sum>n. f (Suc n)) + f 0"
  using suminf_split_initial_segment[OF assms, of 1]
  by simp

lemma summable_changed:
  assumes "summable (f :: nat \<Rightarrow> real)"
  shows "summable (\<lambda>i. if i = 0 then x else f i)"
using assms summable_iff_shift[where k = 1 and f = f] summable_iff_shift[where k = 1 and f = " (\<lambda>i. if i = 0 then x else f i)"] 
by simp
  
lemma suminf_shift:
  assumes "summable (f :: nat \<Rightarrow> real)"
  shows "x + (\<Sum>i. f (Suc i)) = (\<Sum>i. if i = 0 then x else f i)"
  by (simp add: suminf_split_first[OF summable_changed[OF assms]])


lemma to_real_go_right[simp]:
  assumes "n_ary 3 f"
  shows "go_right (to_real f) = to_real (r_go_right f)"
proof-
  from assms
  have "summable (n_ary_series 3 f)" by (metis n_ary_summable)
  from assms
  have "n_ary 3 (\<lambda>i. f (i - 1))" by (auto simp add: n_ary_def)
  hence "summable (n_ary_series 3 (\<lambda>i. f (i - 1)))" by (metis n_ary_summable)

  have "go_right (to_real f) = 2/3 + to_real f / 3" by (simp add: go_right_def)
  also have "\<dots> = 2/3 + (\<Sum>i. n_ary_series 3 f i) / 3" by (simp add: to_real_def)
  also have "\<dots> = 2/3 + (\<Sum>i. n_ary_series 3 f i / 3)" by (rule arg_cong[OF suminf_divide[symmetric]]) fact
  also have "\<dots> = 2/3 + (\<Sum>i. n_ary_series 3 (\<lambda> i. f (i - 1)) (Suc i))"
    by (metis n_ary_series_div real_of_nat_numeral)
  also have "\<dots> = (\<Sum>i. if i = 0 then 2/3 else n_ary_series 3 (\<lambda> i. f (i - 1)) i)"
    by (rule suminf_shift) fact
  also have "\<dots> = (\<Sum>i. n_ary_series 3 (\<lambda> i. if i = 0 then 2 else f (i - 1)) i)"
    by (rule arg_cong[where f = suminf]) (auto simp add: n_ary_series_def power_Suc)
  also have "\<dots> = (\<Sum>i. n_ary_series 3 (r_go_right f) i)"
    by (simp add: r_go_right_def)
  also have "\<dots> = to_real (r_go_right f)"
    by (simp add: to_real_def)
  finally show ?thesis.
qed


lemma to_real_go_left[simp]:
  assumes "n_ary 3 f"
  shows "go_left (to_real f) = to_real (r_go_left f)"
proof-
  from assms
  have "summable (n_ary_series 3 f)" by (metis n_ary_summable)
  from assms
  have "n_ary 3 (\<lambda>i. f (i - 1))" by (auto simp add: n_ary_def)
  hence "summable (n_ary_series 3 (\<lambda>i. f (i - 1)))" by (metis n_ary_summable)

  have "go_left (to_real f) = to_real f / 3" by (simp add: go_left_def)
  also have "\<dots> = (\<Sum>i. n_ary_series 3 f i) / 3" by (simp add: to_real_def)
  also have "\<dots> = (\<Sum>i. n_ary_series 3 f i / 3)" by (rule suminf_divide[symmetric]) fact
  also have "\<dots> = (\<Sum>i. n_ary_series 3 (\<lambda> i. f (i - 1)) (Suc i))"
    by (metis n_ary_series_div real_of_nat_numeral)
  also have "\<dots> = 0 + (\<Sum>i. n_ary_series 3 (\<lambda> i. f (i - 1)) (Suc i))"
    by simp
  also have "\<dots> = (\<Sum>i. if i = 0 then 0 else n_ary_series 3 (\<lambda> i. f (i - 1)) i)"
    by (rule suminf_shift) fact
  also have "\<dots> = (\<Sum>i. n_ary_series 3 (\<lambda> i. if i = 0 then 0 else f (i - 1)) i)"
    by (rule arg_cong[where f = suminf])  (auto simp add: n_ary_series_def)
  also have "\<dots> = (\<Sum>i. n_ary_series 3 (r_go_left f) i)"
    by (simp add: r_go_left_def)
  also have "\<dots> = to_real (r_go_left f)"
    by (simp add: to_real_def)
  finally show ?thesis.
qed

(* This is basically the main theorem, for a simpler set :-) *)
lemma interval_covered:
  assumes "n > 1"
  shows "{0..1} = (\<lambda> f. suminf (n_ary_series n f)) ` {f. n_ary n f}"
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> (\<lambda> f. suminf (n_ary_series n f)) ` {f. n_ary n f}"
  then obtain f where "x = suminf (n_ary_series n f)" and "n_ary n f" by auto
  from nary_pos[OF `n_ary n f`] nary_le_1[OF `n_ary n f`]
  have "0 \<le> suminf (n_ary_series n f)" and "suminf (n_ary_series n f) \<le> 1" by (simp_all add: to_real_def)
  thus "x \<in> {0..1}" unfolding `x = suminf (n_ary_series n f)` by auto
next
  fix x :: real
  assume "x \<in> {0..1}" hence "0 \<le> x" and "x \<le> 1" by auto

  have "x = suminf (n_ary_series n (to_nary n x))"
    unfolding to_real_def
    by (rule suminf_n_ary_series_to_nary[OF assms `0 \<le> x` `x \<le> 1`, symmetric])
  moreover
  have "n_ary n (to_nary n x)" by (rule n_ary_to_nary[OF assms])
  ultimately
  show "x \<in>  (\<lambda> f. suminf (n_ary_series n f)) ` {f. n_ary n f}" by auto
qed

lemma cantor_n_eq:  "cantor_n n = to_real` r_cantor_n n"
proof(induction n)
  case 0 
  have "cantor_n 0  = {0..1}" by simp
  also have "\<dots> = to_real ` {f. n_ary 3 f}" 
    unfolding to_real_def by (rule interval_covered) simp
  also have "\<dots> = to_real ` r_cantor_n 0" by simp
  finally show ?case.
next
  case (Suc n)
  have "cantor_n (Suc n) = go_left ` cantor_n n \<union> go_right ` cantor_n n" by simp
  also have "\<dots> = go_left ` (to_real ` r_cantor_n n) \<union> go_right ` (to_real ` r_cantor_n n)"
    unfolding Suc.IH..
  also have "\<dots> = to_real ` r_go_left ` r_cantor_n n \<union> to_real ` r_go_right ` r_cantor_n n"
    by (simp add: image_image cong: image_cong)
  also have "\<dots> = to_real ` (r_go_left ` r_cantor_n n \<union> r_go_right ` r_cantor_n n)" by auto
  also have "\<dots> = to_real ` (r_cantor_n (Suc n))" by simp
  finally show ?case.
qed

lemma r_cantor_n_mono: "n \<le> m \<Longrightarrow> r_cantor_n m \<subseteq> r_cantor_n n"
  by (auto simp add: r_cantor_n_cantor_ary)

lemma r_cantor_n_same_prefix:
  assumes "a \<in> r_cantor_n n" "b \<in> r_cantor_n n"
  assumes eq: "to_real a = to_real b"
  shows "\<forall>j<n. a j = b j"
  using assms(1,2)
proof(induction n)
  case 0 show ?case by simp
next
  case (Suc n)
  from  `a \<in> r_cantor_n (Suc n)` `b \<in> r_cantor_n (Suc n)`
  have "n_ary 3 a" and "n_ary 3 b" by (metis r_cantor_n_n_ary)+
  moreover
  from `a \<in> r_cantor_n (Suc n)` `b \<in> r_cantor_n (Suc n)`
  have "a n \<in> {0,2}" and "b n \<in> {0,2}" unfolding r_cantor_n_cantor_ary by auto
  moreover
  from  `a \<in> r_cantor_n (Suc n)` `b \<in> r_cantor_n (Suc n)`
  have "a \<in> r_cantor_n n" and "b \<in> r_cantor_n n"
    using r_cantor_n_mono[where n = n and m = "Suc n"] by auto
  hence "\<forall>j<n. a j = b j" by (rule Suc.IH)
  moreover
  note eq
  ultimately
  have "a n = b n" by (rule to_real_inj_next)
  with `\<forall>j<n. a j = b j`
  show ?case by (metis less_antisym)
qed

lemma n_ary_series_diff:
  assumes "n_ary 3 a" and  "n_ary 3 b"
  shows "\<bar>n_ary_series 3 a n - n_ary_series 3 b n\<bar> \<le> (1/3)^n"
proof-
  have "\<bar>n_ary_series 3 a n - n_ary_series 3 b n\<bar> = \<bar>real (a n) - real(b n)\<bar> * (1 / 3) ^ Suc n"
    unfolding n_ary_series_def by (auto simp add: field_simps)
  also
  from assms have "\<bar>real (a n)\<bar> < 3" and  "\<bar>real (b n)\<bar> < 3" by auto
  hence "\<bar>real (a n) - real(b n)\<bar> \<le> 3" by auto
  also have "(3::real) * (1 / 3) ^ Suc n = (1/3)^n" by (simp add: power_Suc field_simps)
  finally show ?thesis by this auto
qed

lemma to_real_cont:
  assumes "n_ary 3 a" and  "n_ary 3 b"
  assumes "\<forall>j<n. a j = b j"
  shows "\<bar>to_real a - to_real b\<bar> \<le> 3 * (1 / 3) ^ n"
proof-
  note sm = n_ary_summable[OF assms(1)] n_ary_summable[OF assms(2)]
  note sm' = summable_diff[OF sm]
  have sm''': "summable (\<lambda>i. ((1 / 3)::real) ^ i)" by (rule summable_geometric) simp
  hence sm''': "summable (\<lambda>i.  (1/3 :: real) ^ (i + n))" by (metis summable_iff_shift[where k = n])
  hence sm'': "summable (\<lambda>i. \<bar>n_ary_series 3 a (i + n) - n_ary_series 3 b (i + n)\<bar>)"
    apply (rule summable_rabs_comparison_test[rotated])
    using n_ary_series_diff[OF assms(1,2)]
    apply auto
    done

  have "\<bar>to_real a - to_real b\<bar> = \<bar>(\<Sum>i. n_ary_series 3 a i - n_ary_series 3 b i)\<bar>"
    unfolding to_real_def by (rule arg_cong[OF suminf_diff[OF sm]])
  also have "\<dots> = \<bar>(\<Sum>i. n_ary_series 3 a (i + n) - n_ary_series 3 b (i + n)) + setsum (\<lambda> i. n_ary_series 3 a i - n_ary_series 3 b i) {..<n}\<bar>"
    by (rule arg_cong[OF suminf_split_initial_segment[OF sm']])
  also have "\<dots> = \<bar>(\<Sum>i. n_ary_series 3 a (i + n) - n_ary_series 3 b (i + n))\<bar>"
    using assms(3) by (auto simp add: n_ary_series_def)
  also have "\<dots> \<le> (\<Sum>i. \<bar>n_ary_series 3 a (i + n) - n_ary_series 3 b (i + n)\<bar>)"
    by (rule summable_rabs[OF sm''])
  also have "\<dots> \<le> (\<Sum>i. (1/3::real)^(i + n))"
    apply (rule suminf_le[OF _ sm'' sm'''])
    apply (rule)
    apply (rule n_ary_series_diff[OF assms(1,2)])
    done
  also have "\<dots> = (\<Sum>i. (1/3::real)^i * (1/3::real)^n)"
    by (simp add: field_simps add: power_add)
  also have "\<dots> = (\<Sum>i. (1/3::real)^i) * (1/3::real)^n"
    by (rule suminf_mult2[symmetric, OF summable_geometric]) simp
  also have "\<dots> = 1 / (1 - 1 / 3) * (1 / 3) ^ n"
    by (simp add: suminf_geometric) 
  also have "\<dots> \<le> 3 *  (1 / 3) ^ n" by (simp add: field_simps)
  finally show ?thesis.
qed

theorem "cantor = to_real ` r_cantor"
proof
  show "to_real` r_cantor \<subseteq> cantor"
  unfolding cantor_def r_cantor_def
  by (auto simp add: cantor_n_eq)
next
  show "cantor \<subseteq> to_real ` r_cantor"
  proof
    fix x
    assume "x \<in> cantor"
    hence "\<forall> n. \<exists> f. f \<in> r_cantor_n n \<and> x = to_real f"
      by (auto simp add: cantor_def cantor_n_eq)
    then obtain f where f: "\<And>n. f n \<in> r_cantor_n n" "\<And> n . x = to_real (f n)" by metis

    { fix n m :: nat
      note f(1)
      moreover
      assume "n \<le> m" with f(1)
      have "f m \<in> r_cantor_n n" by (metis r_cantor_n_mono subsetCE)
      moreover
      from f(2) have "to_real (f n) = to_real (f m)" by auto
      ultimately
      have "\<forall>j<n. f n j = f m j" by (rule r_cantor_n_same_prefix)
    }
    note * = this
    def f' == "\<lambda> n. f (Suc n) n"
    
    have "\<forall> n. f' n \<in> {0,2}" using f(1) by (metis f'_def lessI r_cantor_n_cantor_ary)
    hence "cantor_ary f'" using  cantor_aryI[where f = f'] by auto
    hence "f' \<in> r_cantor" unfolding r_cantor_cantor_ary.
    moreover
    have "(\<lambda> n. abs (to_real f' - to_real (f n))) ----> 0"
    proof(rule bounded_0_inverse)
      fix n
      show "0 \<le> \<bar>to_real f' - to_real (f n)\<bar>" by simp
    next
      fix n :: nat
      
      have "n_ary 3 f'" by (metis `cantor_ary f'`)
      moreover
      have "n_ary 3 (f n)" by (metis f(1) r_cantor_n_n_ary)
      moreover
      have "\<forall>j<n. f' j = f n j"  by (auto simp add: f'_def *)
      ultimately
      show "\<bar>to_real f' - to_real (f n)\<bar> \<le> 3* (1/3)^n" by (rule to_real_cont)
    next
      show "1/3 < (1::real)" by auto
    next
      show "0 < (3::real)" by auto
    qed
    hence "(\<lambda> n. to_real f' - to_real (f n)) ----> 0" by (rule tendsto_rabs_zero_cancel)
    hence "(\<lambda> n. to_real f' - x) ----> 0" unfolding f(2)[symmetric].
    hence "x = to_real f'" by (simp add: LIMSEQ_const_iff)
    ultimately
    show "x \<in> to_real ` r_cantor" by auto
  qed
qed

theorem "bij_betw to_real {f. cantor_ary f} cantor"
sledgehammer


end
