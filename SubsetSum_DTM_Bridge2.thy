theory SubsetSum_DTM_Bridge2
  imports "SubsetSum_DTM_Bridge"
begin

context Coverage_TM
begin

(* Add these helper lemmas at the top of SubsetSum_DTM_Bridge2: *)

lemma power_comparison_half:
  fixes n k :: nat
  assumes "2 * k ≤ n" "k ≥ 1"
  shows "(2::nat)^k ≤ 2^(n - k)"
proof -
  have "k ≤ n - k" using assms by simp
  thus ?thesis by (rule power_increasing) simp
qed

lemma power_comparison_half_strict:
  fixes n k :: nat  
  assumes "2 * k < n" "k ≥ 1"
  shows "(2::nat)^k < 2^(n - k)"
proof -
  have "k < n - k" using assms by simp
  thus ?thesis by (rule power_strict_increasing) simp
qed

(* ADD THIS HERE: *)
lemma LHS_larger_than_RHS_when_kk_large:
  assumes "n ≥ 2" "kk > n - kk" "kk < n"
      and "distinct_subset_sums as" "length as = n"
  shows "card (set (enumL as s kk)) > card (set (enumR as s kk))"
proof -
  have "card (set (enumL as s kk)) = 2^kk"
    using card_LHS_e_k assms by force
  moreover have "card (set (enumR as s kk)) = 2^(n - kk)"
    using card_RHS_e_k assms by force
  moreover have "kk > n - kk" using assms(2) .
  hence "(2::nat)^kk > 2^(n - kk)"
    by (rule power_strict_increasing) simp
  ultimately show ?thesis by simp
qed

(* Helper: Flipping one L-block doesn't affect other L-blocks (generic version) *)
lemma Lval_at_unchanged_other_blocks_generic:
  assumes jL_bound: "jL < length (enumL as s kk)"
      and jL'_bound: "jL' < length (enumL as s kk)"
      and jL'_diff: "jL' ≠ jL"
      and outside_same: "⋀i. i ∉ blockL_abs enc0 as s jL ⟹ oL' i = ((!) (enc as s kk)) i"
  shows "Lval_at as s oL' jL' = Lval_at as s ((!) (enc as s kk)) jL'"
  using Lval_at_unchanged_other_blocks[OF jL_bound jL'_bound jL'_diff outside_same] .

(* COROLLARY: Every L-block must be touched *)
lemma every_L_block_touched:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"  (* NEW *)
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"  (* NEW *)
  shows "∀jL < length (enumL as s kk). 
           Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {}"
  sorry

lemma every_L_block_touched_v2:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and kk_slack: "2 * kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
      and unread_R: "∀jR < length (enumR as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
  shows "∀jL < length (enumL as s kk). 
           Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {}"
  sorry

(* Symmetric: Every R-block must be touched (v2) *)
lemma every_R_block_touched_v2:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and kk_large: "kk > n - kk"  (* ADD THIS *)
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
      and unread_L: "∀jL < length (enumL as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
  shows "∀jR < length (enumR as s kk). 
           Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {}"
  sorry

lemma Rval_at_unchanged_other_blocks:
  assumes jR_bound: "jR < length (enumR as s kk)"
      and jR'_bound: "jR' < length (enumR as s kk)"
      and jR'_diff: "jR' ≠ jR"
      and outside_same: "⋀i. i ∉ blockR_abs enc0 as s kk jR ⟹ oR' i = ((!) (enc as s kk)) i"
  shows "Rval_at as s oR' jR' = Rval_at as s ((!) (enc as s kk)) jR'"
proof -
  define base_jR' where "base_jR' = length (enc0 as s) + offR as s kk jR'"
  
  have "Rval_at as s oR' jR' = from_bits (map oR' [base_jR' ..< base_jR' + W as s])"
    unfolding Rval_at_def base_jR'_def by simp
  
  also have "... = from_bits (map ((!) (enc as s kk)) [base_jR' ..< base_jR' + W as s])"
  proof -
    have "map oR' [base_jR' ..< base_jR' + W as s] = 
          map ((!) (enc as s kk)) [base_jR' ..< base_jR' + W as s]"
    proof (rule map_cong[OF refl])
      fix i assume i_in: "i ∈ set [base_jR' ..< base_jR' + W as s]"
      hence i_range: "base_jR' ≤ i" "i < base_jR' + W as s" by auto
      
      have i_in_block_jR': "i ∈ blockR_abs enc0 as s kk jR'"
        unfolding blockR_abs_def using i_range base_jR'_def by simp
      
      have "i ∉ blockR_abs enc0 as s kk jR"
      proof
        assume "i ∈ blockR_abs enc0 as s kk jR"
        hence "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' ≠ {}"
          using i_in_block_jR' by blast
        thus False using blockR_abs_disjoint[of jR jR' enc0 as s kk] jR'_diff by blast
      qed
      
      thus "oR' i = ((!) (enc as s kk)) i" using outside_same by blast
    qed
    thus ?thesis by presburger
  qed
  
  also have "... = Rval_at as s ((!) (enc as s kk)) jR'"
    unfolding Rval_at_def base_jR'_def by simp
  
  finally show ?thesis .
qed 

(* Symmetric for R-blocks *)
lemma every_R_block_touched:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"  (* Note: R then L *)
      and miss: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"  (* Note: R then L *)
  shows "∀jR < length (enumR as s kk). 
           Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {}"
  sorry

theorem coverage_blocks:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit_L: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss_L: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
      and hit_R: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)" 
      and miss_R: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
  shows "(∀j<length (enumL as s kk). 
            Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s j ≠ {}) ∧
         (∀j<length (enumR as s kk). 
            Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk j ≠ {})"
  using every_L_block_touched[OF n_ge2 kk_bounds distinct len hit_L miss_L]
        every_R_block_touched[OF n_ge2 kk_bounds distinct len hit_R miss_R]
  by blast

end  (* context Coverage_TM *)

end  (* theory *)
