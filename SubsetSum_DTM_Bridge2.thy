theory SubsetSum_DTM_Bridge2
  imports "SubsetSum_DTM_Bridge"
begin

context Coverage_TM
begin

(* ========================================================================= *)
(* PART 1: Helper Lemmas (L2, R2)                                          *)
(* ========================================================================= *)

lemma enumL_length_geq_two:
  assumes n_def: "n = length as"
      and k_pos: "kk ≥ 1"
      and k_le: "kk ≤ n"
      and distinct: "distinct_subset_sums as"
  shows "2 ≤ length (enumL as s kk)"
proof -
  have card_eq: "card (LHS (e_k as s kk) n) = 2^kk"
    by (rule card_LHS_e_k[OF n_def k_le distinct])
  
  have pow_ge: "2 ≤ (2::nat)^kk"
  proof (cases kk)
    case 0
    with k_pos show ?thesis by simp
  next
    case (Suc k')
    show ?thesis by (simp add: Suc)
  qed
  
  have "length (enumL as s kk) = card (LHS (e_k as s kk) n)"
    using enumL_def distinct_card using n_def by auto
  
  with card_eq pow_ge show ?thesis by simp
qed

lemma enumR_length_geq_two:
  assumes n_def: "n = length as"
      and k_lt: "kk < n"
      and distinct: "distinct_subset_sums as"
  shows "2 ≤ length (enumR as s kk)"
proof -
  have k_le: "kk ≤ n" using k_lt by simp
  
  have card_eq: "card (RHS (e_k as s kk) n) = 2^(n - kk)"
    by (rule card_RHS_e_k[OF n_def k_le distinct])
  
  have pow_ge: "2 ≤ (2::nat)^(n - kk)"
  proof -
    have "n - kk ≥ 1" using k_lt by simp
    then obtain m where "n - kk = Suc m" by (cases "n - kk") simp_all
    thus ?thesis by simp
  qed
  
  have "length (enumR as s kk) = card (RHS (e_k as s kk) n)"
    using enumR_def distinct_card by (simp add: n_def)
  
  with card_eq pow_ge show ?thesis by simp
qed

(* ========================================================================= *)
(* PART 2: Hard Instance Construction for pow2_list                        *)
(* ========================================================================= *)

(* For the pow2_list family, we'll prove hit, miss, and baseline_only_j
   for a SPECIFIC choice of target s *)

definition pow2_target :: "nat ⇒ int" where
  "pow2_target n = (2::int)^(n-1) - 1"

(* LEMMA: hit holds for pow2_list with this target *)
lemma pow2_hit:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
  sorry

(* LEMMA: miss holds for pow2_list with this target *)
lemma pow2_miss:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
  sorry

(* LEMMA: baseline_only_j holds for pow2_list with this target *)
lemma pow2_baseline_only_j:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "∀j. good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
             (∀j'<length (enumL as s kk). j' ≠ j ⟶
                Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
  sorry

(* ========================================================================= *)
(* PART 3: Package Everything as a Hard Instance                           *)
(* ========================================================================= *)

lemma pow2_satisfies_all_coverage_conditions:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "length as = n"
    and "distinct_subset_sums as"
    and "2 ≤ length (enumL as s kk)"
    and "2 ≤ length (enumR as s kk)"
    and "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
    and "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
    and "∀j. good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
             (∀j'<length (enumL as s kk). j' ≠ j ⟶
                Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
proof -
  show "length as = n" by (simp add: as_def pow2_list_def)
  
  show "distinct_subset_sums as"
    by (simp add: as_def distinct_subset_sums_pow2_list)
  
  show "2 ≤ length (enumL as s kk)"
  proof -
    have "length as = n" by (simp add: as_def pow2_list_def)
    moreover have "kk ≥ 1" using kk_bounds by simp
    moreover have "kk ≤ n" using kk_bounds by simp
    moreover have "distinct_subset_sums as" by (simp add: as_def distinct_subset_sums_pow2_list)
    ultimately show ?thesis
      using enumL_length_geq_two by blast
  qed
  
  show "2 ≤ length (enumR as s kk)"
  proof -
    have "length as = n" by (simp add: as_def pow2_list_def)
    moreover have "kk < n" using kk_bounds by simp
    moreover have "distinct_subset_sums as" by (simp add: as_def distinct_subset_sums_pow2_list)
    ultimately show ?thesis
      using enumR_length_geq_two by blast
  qed
  
  show "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
    using pow2_hit[OF n_ge2 kk_bounds] by (simp add: as_def s_def)
  
  show "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
    using pow2_miss[OF n_ge2 kk_bounds] by (simp add: as_def s_def)
  
  show "∀j. good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
            (∀j'<length (enumL as s kk). j' ≠ j ⟶
               Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
    using pow2_baseline_only_j[OF n_ge2 kk_bounds] by (simp add: as_def s_def)
qed

end  (* context Coverage_TM *)

end  (* theory *)
