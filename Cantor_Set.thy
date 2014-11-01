theory Cantor_Set
imports Main Real Series "~~/src/HOL/Library/Product_Vector"
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

locale ary =
  fixes n :: nat
  assumes ng1: "n > 1"
begin 

text {*
The mod n is a trick to do something slightly more useful when the input has digits outside
the range.
*}
definition n_ary_series :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> real" where
  "n_ary_series f = (\<lambda>k. real (f k mod n) * (1 / n) ^ Suc k)"
declare power_Suc[simp del]

definition to_real :: "(nat \<Rightarrow> nat) \<Rightarrow> real"
  where "to_real = (\<lambda> f. suminf (n_ary_series f))"

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

lemma n_ary_series_div[simp]: "n_ary_series f i / n = n_ary_series (\<lambda> i. f (i - 1)) (Suc i)"
  unfolding n_ary_series_def
  by (simp add: power_Suc)

text {* The n-ary representation of 1. *}
definition "period_one \<equiv> n_ary_series (\<lambda>_. n - 1)"

lemma period_one_summable[simp]: "summable period_one"
  using ng1 by (auto simp:n_ary_series_def period_one_def intro!:summable_geometric' summable_mult)

lemma suminf_period_one_1[simp]: "suminf period_one = 1"
  using ng1
  unfolding period_one_def n_ary_series_def
  apply (subst suminf_mult)
  apply (rule summable_geometric')
  apply simp
  apply (subst suminf_geometric')
  by (auto simp:right_diff_distrib)

lemma period_one_skip_initial_segment[simp]:
  "(\<Sum>k. period_one (k + i)) = (1/n) ^ i * suminf period_one"
  by (subst suminf_mult[symmetric], simp, rule arg_cong[where f=suminf], auto simp:period_one_def n_ary_series_def power_Suc power_add)

lemma n_ary_summable[simp]:
  shows "summable (n_ary_series f)"
proof (rule summableI_nonneg_bounded[where x="suminf period_one"])
  fix k
  show "0 \<le> n_ary_series f k" using assms by (auto simp: n_ary_series_def intro!:mult_nonneg_nonneg)
  have "setsum (n_ary_series f) {..<k} \<le> setsum (period_one) {..<k}"
    using assms ng1
    by (auto simp:n_ary_series_def period_one_def intro!:setsum_mono)
       (metis Suc_pred mod_less_divisor neq0_conv not_less not_less_eq old.nat.distinct(2))
  also have "... \<le> suminf period_one" using assms
    by -(intro setsum_le_suminf period_one_summable,
         auto intro: simp:period_one_def n_ary_series_def)
  finally show "setsum (n_ary_series f) {..<k} \<le> suminf period_one" .
qed

lemma nary_pos[simp]: "to_real f \<ge> 0"
  unfolding to_real_def
  by (rule suminf_nonneg, simp) (auto simp:n_ary_series_def)

lemma nary_le_1[simp]:
  shows "to_real f \<le> 1"
proof-
  have "suminf (n_ary_series f) \<le> suminf period_one"
  proof (rule suminf_le, rule)
    fix i
    from ng1 have "f i mod n < n" by simp
    thus "n_ary_series f i \<le> period_one i" 
      unfolding n_ary_series_def period_one_def  by auto
  next
    show "summable (n_ary_series f)" by (rule n_ary_summable)
  next
    show "summable period_one" by (rule period_one_summable)
  qed
  also have "\<dots> = 1" by (rule suminf_period_one_1)
  finally show ?thesis unfolding to_real_def .
qed

subsection {* The n-arity expansion of a real *}

fun to_nary :: "real \<Rightarrow> (nat \<Rightarrow> nat)"
 where "to_nary x i = (if x = 1 then n - 1 else natfloor (x * n^(Suc i)) mod n)"

(* Generalized Real.natfloor_div_nat, included in the main library since Oct 2014. *)
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
  fixes x :: real
  shows "n * natfloor x + natfloor (n * x) mod n = natfloor (n * x)"
proof-
  have "natfloor (n * x) = n * (natfloor (n * x) div n) + natfloor (n * x) mod n"
    by (metis mod_div_equality2)
  also have "natfloor (n * x) div n = natfloor (n * x / n)"
    apply (rule natfloor_div_nat[symmetric])
    using ng1 by auto
  also have "n * x / n = x" using ng1 by simp
  finally show ?thesis..
qed

lemma partial_n_ary:
  fixes x :: real
  assumes "0 \<le> x" "x < 1"
  shows "setsum (n_ary_series (to_nary x)) {..<i} = natfloor (x * n^i) / n^i"
proof (induction i)
  case 0
  from assms have "natfloor x = 0" by (auto intro: natfloor_eq)
  thus ?case by simp
next
  case (Suc i)
    have "setsum (n_ary_series (to_nary x)) {..<Suc i}
      =  setsum (n_ary_series (to_nary x)) {..<i} + n_ary_series (to_nary x) i"
     by simp
   also have "\<dots> = natfloor (x * real (n ^ i)) / real (n ^ i) + n_ary_series (to_nary x) i"
     unfolding Suc.IH..
   also have "\<dots> = natfloor (x * n ^ i) /  n ^ i + (natfloor (x * n ^ Suc i) mod n) / n ^ Suc i"
     using assms(2) by (simp add: n_ary_series_def field_simps)
   also have "\<dots> = (n * natfloor (x * n ^ i) + natfloor (n * (x * n ^ i)) mod n) / n ^ Suc i"
     using ng1 by (simp add: field_simps power_Suc)
   also have "\<dots> = natfloor (n * (x * n^i)) / n^Suc i"
     unfolding natfloor_mod..
   also have "\<dots> = natfloor (x * n^(Suc i)) / n^Suc i" by (simp add: power_Suc field_simps)
   finally
   show ?case.
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
  fixes x :: real
  assumes "0 \<le> x" "x \<le>1"
  shows "to_real (to_nary x) = x"
proof(cases "x = 1")
  case False with assms(2) have "x < 1" by simp

  have "to_real (to_nary x) = lim (\<lambda>i. setsum (n_ary_series (to_nary x)) {..<i})"
    unfolding to_real_def by (rule suminf_eq_lim)
  also have "\<dots> = lim (\<lambda>i. natfloor (x * n^i) / n^i)"
    unfolding partial_n_ary[OF assms(1) `x < 1` ] by simp
  also have "\<dots> = x"
  proof(rule limI)
    have "(\<lambda>i. x - (natfloor (x * (n ^ i))) / (n ^ i)) ----> 0"
    proof(rule bounded_0_inverse)
      fix i
      have "natfloor (x * (n^i)) \<le> x * (n^i)" 
          using assms by (simp add: real_natfloor_le field_simps)
      thus "0 \<le> x - natfloor (x * (n^i)) / (n^i)" 
          using ng1 by (simp add: field_simps)
    next
      fix i 
      have "x * (n^i) - natfloor (x * (n^i)) \<le> 1"
         by (metis comm_monoid_diff_class.diff_cancel le_natfloor_eq_one less_eq_real_def natfloor_neg natfloor_one natfloor_subtract not_le power_0 power_eq_0_iff)
      from divide_right_mono[OF this, where c = "n^i"] assms(1)
      show "x - natfloor (x * (n ^ i)) / (n ^ i) \<le> 1 * (1/n)^i"
        using ng1 by (simp add: field_simps )
    next
      show "1/n < 1" using ng1 by auto
    next
      show "0 < (1::real)" by auto
    qed
    thus "(\<lambda>i. (natfloor (x * (n ^ i))) / (n ^ i)) ----> x"
      by (rule LIMSEQ_diff_approach_zero2[OF tendsto_const])
  qed
  finally show ?thesis.
next
  case True
  hence "to_nary x = (\<lambda>i. n - 1)" by auto
  thus ?thesis
    unfolding to_real_def using True suminf_period_one_1[unfolded period_one_def] by simp
qed
end

text {* We only really need this with @{term "n = 3"} there: *}
interpretation ary 3 by default auto

subsection {* A cantor-like set on the representations *}

definition r_go_left :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
  where "r_go_left f = (\<lambda> i. if i = 0 then 0 else f (i - 1))" 
definition r_go_right :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
  where "r_go_right f= (\<lambda> i. if i = 0 then 2 else f (i - 1))" 

fun r_cantor_n where
  "r_cantor_n 0 = UNIV"
| "r_cantor_n (Suc n) = r_go_left ` r_cantor_n n \<union> r_go_right ` r_cantor_n n"
definition "r_cantor \<equiv> \<Inter>range r_cantor_n"

subsection {* A bijection between the Cantor Set and a subset of ternary representations *}

subsubsection {* Recognizing the cantor sets via their digits *}

lemma r_cantor_n_cantor_ary: "f \<in> r_cantor_n n \<longleftrightarrow> (\<forall>i<n. f i \<in> {0,2})"
proof(intro iffI conjI)
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
  assume "\<forall>i<n. f i \<in> {0, 2}"
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
      by (auto intro!: Suc.IH)
    ultimately
    show "f \<in> r_cantor_n (Suc n)" by auto
  qed
qed

lemma r_cantor_zero_or_two: "f \<in> r_cantor \<longleftrightarrow> (\<forall> i. f i \<in> {0,2})"
proof-
  have "f \<in> r_cantor \<longleftrightarrow> (\<forall>n. f \<in> r_cantor_n n)" by (auto simp add: r_cantor_def)
  also have "\<dots> \<longleftrightarrow> (\<forall>n. (\<forall>i<n. f i \<in> {0,2}))" unfolding r_cantor_n_cantor_ary..
  also have "\<dots> \<longleftrightarrow> (\<forall>n. f n \<in> {0,2})" by auto
  finally show ?thesis.
qed

subsubsection {* Injectivity *}


lemma to_real_inj_aux:
  assumes cantor_at_i: "a i \<in> {0,2}"  "b i \<in> {0,2}" 
  assumes ord: "a i < b i" "\<forall>j<i. a j = b j"
  assumes eq: "to_real a = to_real b"
  shows False
proof-
  have[simp]: "a i = 0" "b i = 2" using ord(1) cantor_at_i by auto
  have[simp]: "n_ary_series b i = 2 * (1/3) ^ Suc i" by (auto simp:n_ary_series_def)

  note sm = summable_ignore_initial_segment[OF n_ary_summable]
            summable_ignore_initial_segment[OF period_one_summable]

  have "suminf (n_ary_series a) = (\<Sum>n. n_ary_series a (n + i)) + setsum (n_ary_series a) {..<i}"
    by (rule suminf_split_initial_segment[OF n_ary_summable])
  also have "(\<Sum>n. n_ary_series a (n + i)) = (\<Sum>n. n_ary_series a (n + Suc i))"
    by (subst suminf_split_initial_segment[OF sm(1), where k=1]) (simp add:n_ary_series_def)
  also have "... \<le> (\<Sum>n. period_one (n + Suc i))"
    by (rule suminf_le[OF _ sm]) (auto simp add: n_ary_series_def period_one_def)
  also have "... = (1/3) ^ Suc i" by (simp del: add_Suc_right)
  also have "... < 2 * (1/3) ^ Suc i" by simp
  also have "... \<le> (\<Sum>n. n_ary_series b (n + i))"
  proof-
    have "0 \<le> (\<Sum>n. n_ary_series b (n + Suc i))"
    by (rule suminf_nonneg[OF sm(1)]) (simp add:n_ary_series_def)
    thus ?thesis by (subst suminf_split_initial_segment[OF sm(1), where k=1]) auto
  qed
  also have "... + setsum (n_ary_series  a) {..<i} = suminf (n_ary_series b)"
  proof-
    have 1: "setsum (n_ary_series a) {..<i} = setsum (n_ary_series b) {..<i}" using ord(2) by (auto simp:n_ary_series_def)
    show ?thesis by (subst 1) (rule suminf_split_initial_segment[OF n_ary_summable, symmetric])
  qed
  finally show False using eq unfolding to_real_def by auto
qed

lemma to_real_inj_aux':
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
    show False by (rule to_real_inj_aux[OF assms(1,2) * assms(4,5)])
  next
    assume *: "b i < a i"
    note assms(2,1) *
    moreover
    from ne(2) have "\<forall>j<i. b j = a j" by auto
    moreover
    note eq[symmetric]
    ultimately
    show False by (rule to_real_inj_aux)
  qed
qed

lemma to_real_inj_next:
  assumes cantor_at_i: "a i \<in> {0,2}"  "b i \<in> {0,2}" 
  assumes eq_so_far: "\<forall>j<i. a j = b j"
  assumes eq: "to_real a = to_real b"
  shows "a i = b i"
  using assms
  by (metis to_real_inj_aux')


lemma ex_least: "P (n::nat) \<Longrightarrow> \<exists>m. P m \<and> (\<forall>i<m. \<not>P i)"
  by (metis ex_least_nat_le not_less0)



lemma to_real_inj: "inj_on to_real r_cantor"
proof (rule inj_onI)
  fix a b
  assume asms: "a \<in> r_cantor" "b \<in> r_cantor""to_real a = to_real b"

  show "a = b"
  proof (rule ccontr)
    assume "a \<noteq> b"
    then obtain i where "a i \<noteq> b i" by auto

    from ex_least[of "\<lambda>j. a j \<noteq> b j", OF this]
    obtain i where i: "a i \<noteq> b i" "\<forall>j<i. a j = b j" by auto
   
    from asms(1,2)
    have "a i \<in> {0,2}" and "b i \<in> {0,2}" unfolding r_cantor_zero_or_two by auto

    from this i asms(3)
    show False by (rule to_real_inj_aux')
  qed
qed

subsubsection {* Surjectivity *}

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
  shows "go_right (to_real f) = to_real (r_go_right f)"
proof-
  have "go_right (to_real f) = 2/3 + to_real f / 3" by (simp add: go_right_def)
  also have "\<dots> = 2/3 + (\<Sum>i. n_ary_series f i) / 3" by (simp add: to_real_def)
  also have "\<dots> = 2/3 + (\<Sum>i. n_ary_series f i / 3)" unfolding suminf_divide[OF n_ary_summable, symmetric]..
  also have "\<dots> = 2/3 + (\<Sum>i. n_ary_series (\<lambda> i. f (i - 1)) (Suc i))"
    by (metis n_ary_series_div real_of_nat_numeral)
  also have "\<dots> = (\<Sum>i. if i = 0 then 2/3 else n_ary_series (\<lambda> i. f (i - 1)) i)"
    by (rule suminf_shift[OF n_ary_summable])
  also have "\<dots> = (\<Sum>i. n_ary_series (\<lambda> i. if i = 0 then 2 else f (i - 1)) i)"
    by (rule arg_cong[where f = suminf]) (auto simp add: n_ary_series_def power_Suc)
  also have "\<dots> = (\<Sum>i. n_ary_series (r_go_right f) i)"
    by (simp add: r_go_right_def)
  also have "\<dots> = to_real (r_go_right f)"
    by (simp add: to_real_def)
  finally show ?thesis.
qed


lemma to_real_go_left[simp]:
  shows "go_left (to_real f) = to_real (r_go_left f)"
proof-
  have "go_left (to_real f) = to_real f / 3" by (simp add: go_left_def)
  also have "\<dots> = (\<Sum>i. n_ary_series f i) / 3" by (simp add: to_real_def)
  also have "\<dots> = (\<Sum>i. n_ary_series f i / 3)" by (rule suminf_divide[OF n_ary_summable, symmetric])
  also have "\<dots> = (\<Sum>i. n_ary_series (\<lambda> i. f (i - 1)) (Suc i))"
    by (metis n_ary_series_div real_of_nat_numeral)
  also have "\<dots> = 0 + (\<Sum>i. n_ary_series (\<lambda> i. f (i - 1)) (Suc i))"
    by simp
  also have "\<dots> = (\<Sum>i. if i = 0 then 0 else n_ary_series (\<lambda> i. f (i - 1)) i)"
    by (rule suminf_shift[OF n_ary_summable])
  also have "\<dots> = (\<Sum>i. n_ary_series (\<lambda> i. if i = 0 then 0 else f (i - 1)) i)"
    by (rule arg_cong[where f = suminf])  (auto simp add: n_ary_series_def)
  also have "\<dots> = (\<Sum>i. n_ary_series (r_go_left f) i)"
    by (simp add: r_go_left_def)
  also have "\<dots> = to_real (r_go_left f)"
    by (simp add: to_real_def)
  finally show ?thesis.
qed

(* This is basically the main theorem, for a simpler set :-) *)
lemma interval_covered:
  shows "{0..1} = range to_real"
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> range to_real"
  thus "x \<in> {0..1}" by auto
next
  fix x :: real
  assume "x \<in> {0..1}" hence "0 \<le> x" and "x \<le> 1" by auto

  have "x = to_real (to_nary x)"
    by (rule suminf_n_ary_series_to_nary[OF assms `0 \<le> x` `x \<le> 1`, symmetric])
  then
  show "x \<in> range to_real" by auto
qed

lemma cantor_n_eq:  "cantor_n n = to_real` r_cantor_n n"
proof(induction n)
  case 0 
  have "cantor_n 0  = {0..1}" by simp
  also have "\<dots> = range to_real" by (rule interval_covered)
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
  shows "\<bar>n_ary_series a k - n_ary_series b k\<bar> \<le> (1/3)^k"
proof-
  have "\<bar>n_ary_series a k - n_ary_series b k\<bar> = \<bar>real (a k mod 3) - real(b k mod 3)\<bar> * (1 / 3) ^ Suc k"
    unfolding n_ary_series_def by (auto simp add: field_simps)
  also
   have "\<bar>real (a k mod 3)\<bar> < 3" and  "\<bar>real (b k mod 3)\<bar> < 3" by auto
  hence "\<bar>real (a k mod 3) - real(b k mod 3)\<bar> \<le> 3" by auto
  also have "(3::real) * (1 / 3) ^ Suc k = (1/3)^k" by (simp add: power_Suc field_simps)
  finally show ?thesis by this auto
qed

lemma to_real_cont:
  assumes "\<forall>j<n. a j = b j"
  shows "\<bar>to_real a - to_real b\<bar> \<le> 3 * (1 / 3) ^ n"
proof-
  note sm' = summable_diff[OF n_ary_summable n_ary_summable]
  have sm''': "summable (\<lambda>i. ((1 / 3)::real) ^ i)" by (rule summable_geometric) simp
  hence sm''': "summable (\<lambda>i.  (1/3 :: real) ^ (i + n))" by (metis summable_iff_shift[where k = n])
  hence sm'': "summable (\<lambda>i. \<bar>n_ary_series a (i + n) - n_ary_series b (i + n)\<bar>)"
    apply (rule summable_rabs_comparison_test[rotated])
    using n_ary_series_diff
    apply auto
    done

  have "\<bar>to_real a - to_real b\<bar> = \<bar>(\<Sum>i. n_ary_series a i - n_ary_series b i)\<bar>"
    unfolding to_real_def by (rule arg_cong[OF suminf_diff[OF n_ary_summable n_ary_summable]])
  also have "\<dots> = \<bar>(\<Sum>i. n_ary_series a (i + n) - n_ary_series b (i + n)) + setsum (\<lambda> i. n_ary_series a i - n_ary_series b i) {..<n}\<bar>"
    by (rule arg_cong[OF suminf_split_initial_segment[OF sm']])
  also have "\<dots> = \<bar>(\<Sum>i. n_ary_series a (i + n) - n_ary_series b (i + n))\<bar>"
    using assms(1) by (auto simp add: n_ary_series_def)
  also have "\<dots> \<le> (\<Sum>i. \<bar>n_ary_series a (i + n) - n_ary_series b (i + n)\<bar>)"
    by (rule summable_rabs[OF sm''])
  also have "\<dots> \<le> (\<Sum>i. (1/3::real)^(i + n))"
    by (intro suminf_le[OF _ sm'' sm'''] allI n_ary_series_diff)
  also have "\<dots> = (\<Sum>i. (1/3::real)^i * (1/3::real)^n)"
    by (simp add: field_simps add: power_add)
  also have "\<dots> = (\<Sum>i. (1/3::real)^i) * (1/3::real)^n"
    by (rule suminf_mult2[symmetric, OF summable_geometric]) simp
  also have "\<dots> = 1 / (1 - 1 / 3) * (1 / 3) ^ n"
    by (simp add: suminf_geometric) 
  also have "\<dots> \<le> 3 *  (1 / 3) ^ n" by (simp add: field_simps)
  finally show ?thesis.
qed

theorem to_real_surj: "to_real ` r_cantor = cantor"
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
    hence "f' \<in> r_cantor" unfolding r_cantor_zero_or_two.
    moreover
    have "(\<lambda> n. abs (to_real f' - to_real (f n))) ----> 0"
    proof(rule bounded_0_inverse)
      fix n
      show "0 \<le> \<bar>to_real f' - to_real (f n)\<bar>" by simp
    next
      fix n :: nat
      
      have "\<forall>j<n. f' j = f n j"  by (auto simp add: f'_def *)
      then
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

subsubsection {* The bijection *}

theorem "bij_betw to_real r_cantor cantor"
  by (rule bij_betw_imageI[OF to_real_inj to_real_surj])

subsection {* A space-filling curve *}

definition "homeomorphism f A B \<equiv> bij_betw f A B \<and> continuous_on A f \<and> continuous_on B (the_inv_into A f)"

abbreviation "from_real \<equiv> the_inv_into r_cantor to_real"
definition "fill_1 f i \<equiv> f (2 * i)"
definition "fill_2 f i \<equiv> f (2 * i + 1)"

definition fill :: "real \<Rightarrow> real \<times> real" where
  "fill x \<equiv> (to_real (fill_1 (from_real x)), to_real (fill_2 (from_real x)))"

lemma[simp]: "f \<in> r_cantor \<Longrightarrow> fill_1 f \<in> r_cantor"
    unfolding r_cantor_zero_or_two by (auto simp add: fill_1_def)
lemma[simp]: "f \<in> r_cantor \<Longrightarrow> fill_2 f \<in> r_cantor"
    unfolding r_cantor_zero_or_two by (auto simp add: fill_2_def)

lemma fill_inj: "inj_on fill cantor"
proof (rule inj_onI)
  fix x y
  let ?a = "from_real x"
  let ?b = "from_real y"
  assume "x \<in> cantor" "y \<in> cantor" 
  hence[simp]: "?a \<in> r_cantor" "?b \<in> r_cantor" and xy: "x = to_real ?a" "y = to_real ?b"
    using the_inv_into_into[OF to_real_inj] f_the_inv_into_f[OF to_real_inj] to_real_surj by auto

  assume asm: "fill x = fill y"
  hence "to_real (fill_1 ?a) = to_real (fill_1 ?b)" by (simp add:fill_def)
  hence fill_1: "fill_1 ?a = fill_1 ?b" by (rule inj_onD[OF to_real_inj], simp_all)

  from asm have "to_real (fill_2 ?a) = to_real (fill_2 ?b)" by (simp add:fill_def)
  hence fill_2: "fill_2 ?a = fill_2 ?b"
    by (rule inj_onD[OF to_real_inj], auto)
  
  have "?a = ?b"
  proof
    fix i
    show "?a i = ?b i"
    proof (cases "i mod 2 = 0")
      case True
      hence "?a i = fill_1 ?a (i div 2)" by (auto simp:fill_1_def)
      moreover have "fill_1 ?b (i div 2) = ?b i" using True by (auto simp:fill_1_def)
      ultimately show ?thesis by (simp add:fill_1)
    next
      case False
      hence "i > 0" by simp
      with False have 1: "(i - 1) mod 2 = 0" by (metis `0 < i` even_def even_num_iff)
      hence "?a i = (fill_2 ?a) ((i - 1) div 2)" by (simp add:fill_2_def mult_div_cancel `i > 0`)
      moreover have "(fill_2 ?b) ((i - 1) div 2) = ?b i" using 1 by (simp add:fill_2_def mult_div_cancel `i > 0`)
      ultimately show ?thesis by (simp add:fill_2)
    qed
  qed
  thus "x = y" using xy by simp
qed

theorem "homeomorphism fill cantor (cantor \<times> cantor)"
  apply (simp add:homeomorphism_def bij_betw_def fill_inj)
  oops

end
