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

(* Helper: Geometric sum for powers of 2 *)
lemma geometric_sum_pow2:
  shows "(∑i<n. (2::int)^i) = 2^n - 1"
proof (induction n)
  case 0
  show ?case by simp
next
  case (Suc n)
  have "(∑i<Suc n. (2::int)^i) = (∑i<n. 2^i) + 2^n"
    by simp
  also have "... = (2^n - 1) + 2^n"
    using Suc.IH by simp
  also have "... = 2^(Suc n) - 1"
    by simp
  finally show ?case .
qed

(* LEMMA: hit holds for pow2_list with this target *)
lemma pow2_hit:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
proof -
  (* Use v = 2^kk - 1 (sum of all first kk elements) *)
  define v where "v = (2::int)^kk - 1"
  
  have len_as: "length as = n"
    by (simp add: as_def pow2_list_def)
  
  (* Construct the bitvector that selects all first kk elements *)
  define xs where "xs = replicate kk (1::int) @ replicate (n - kk) (0::int)"
  
  have xs_in_bitvec: "xs ∈ bitvec n"
    unfolding bitvec_def using len_as xs_def assms(3) by auto
  
  (* v ∈ LHS: sum of first kk elements *)
  have v_in_LHS: "v ∈ LHS (e_k as s kk) n"
  proof -
    have "fst (e_k as s kk xs) = v"
    proof -
      have "fst (e_k as s kk xs) = lhs_of as kk xs"
        by (simp add: e_k_def)
      also have "... = sum_as_on as {0..<kk} xs"
        by (simp add: lhs_of_def)
      also have "... = (∑i∈{0..<kk}. as ! i * xs ! i)"
        by (simp add: sum_as_on_def)
      also have "... = (∑i∈{0..<kk}. as ! i * 1)"
      proof -
        have "as ! i * xs ! i = as ! i * 1" if "i ∈ {0..<kk}" for i
        proof -
          have "i < kk" using that by simp
          hence "xs ! i = 1"
            by (simp add: xs_def nth_append)
          thus ?thesis by simp
        qed
        thus ?thesis by (meson sum.cong)
      qed
      also have "... = (∑i∈{0..<kk}. as ! i)"
        by simp
      also have "... = (∑i∈{0..<kk}. (2::int)^i)"
      proof -
        have "as ! i = 2^i" if "i ∈ {0..<kk}" for i
        proof -
          have "i < kk" using that by simp
          hence "i < n" using assms(3) by simp
          thus ?thesis
            unfolding as_def pow2_list_def
            by simp
        qed
        thus ?thesis by auto
      qed
      also have "... = (∑i<kk. (2::int)^i)"
        by (simp add: lessThan_atLeast0)
      also have "... = 2^kk - 1"
        by (rule geometric_sum_pow2)
      finally show ?thesis by (simp add: v_def)
    qed
    
    thus ?thesis
      unfolding LHS_def using xs_in_bitvec by blast
  qed
  
  (* v ∈ RHS: need s - (sum of elements kk to n-2) = v *)
  have v_in_RHS: "v ∈ RHS (e_k as s kk) n"
  proof -
    (* Construct bitvector that selects positions kk to n-2, but NOT n-1 *)
    define ys where "ys = replicate kk (0::int) @ replicate (n - kk - 1) (1::int) @ [(0::int)]"
    
    have ys_len: "length ys = n"
      using ys_def assms(1,3) by auto
    
    have ys_in_bitvec: "ys ∈ bitvec n"
    proof -
      have "length ys = n" using ys_len .
      moreover have "∀x ∈ set ys. x = 0 ∨ x = 1"
      proof -
        have "set ys ⊆ {0, 1}"
          unfolding ys_def using set_append
        using Un_insert_right empty_set insert_absorb2 insert_commute by fastforce
        thus ?thesis by auto
      qed
      ultimately show ?thesis
        unfolding bitvec_def by auto
    qed
    
    have "snd (e_k as s kk ys) = v"
    proof -
      have "snd (e_k as s kk ys) = s - (∑i∈{kk..<n-1}. as ! i)"
      proof -
        have "snd (e_k as s kk ys) = rhs_of as kk s ys"
          by (simp add: e_k_def)
        also have "... = s - sum_as_on as {kk..<n} ys"
          by (simp add: rhs_of_def len_as)
        also have "... = s - (∑i∈{kk..<n}. as ! i * ys ! i)"
          by (simp add: sum_as_on_def)
        
        (* Simplify: ys ! (n-1) = 0, so drop that term *)
        also have "(∑i∈{kk..<n}. as ! i * ys ! i) = (∑i∈{kk..<n-1}. as ! i * ys ! i)"
        proof -
          have "ys ! (n-1) = 0"
            using ys_def assms(1,3) by (simp add: nth_append)
          
          have split: "{kk..<n} = {kk..<n-1} ∪ {n-1}"
            using assms(1,3) by auto
          
          have "(∑i∈{kk..<n}. as ! i * ys ! i) = 
                 (∑i∈{kk..<n-1} ∪ {n-1}. as ! i * ys ! i)"
            using split by simp
          also have "... = (∑i∈{kk..<n-1}. as ! i * ys ! i) + (∑i∈{n-1}. as ! i * ys ! i)"
          proof (rule sum.union_disjoint)
            show "finite {kk..<n-1}" by simp
            show "finite {n-1}" by simp
            show "{kk..<n-1} ∩ {n-1} = {}"
              using assms(1,3) by auto
          qed
          also have "(∑i∈{n-1}. as ! i * ys ! i) = as ! (n-1) * ys ! (n-1)"
            by simp
          also have "... = 0"
            using ‹ys ! (n-1) = 0› by simp
          finally show ?thesis by simp
        qed
        
        (* Simplify: ys ! i = 1 for i ∈ {kk..<n-1} *)
        also have "(∑i∈{kk..<n-1}. as ! i * ys ! i) = (∑i∈{kk..<n-1}. as ! i)"
        proof -
          have "ys ! i = 1" if "i ∈ {kk..<n-1}" for i
            using that ys_def assms(3) by (auto simp: nth_append)
          thus ?thesis by (auto intro: sum.cong)
        qed
        
        finally show ?thesis .
      qed
      
      (* Now show this equals v *)
      also have "... = v"
      proof -
        (* First rewrite as ! i = 2^i *)
        have as_rewrite: "(∑i∈{kk..<n-1}. as ! i) = (∑i∈{kk..<n-1}. (2::int)^i)"
        proof -
          have "as ! i = 2^i" if "i ∈ {kk..<n-1}" for i
          proof -
            have "i < n" using that assms(1) by auto
            thus ?thesis
              unfolding as_def pow2_list_def
              by simp
          qed
          thus ?thesis by (auto intro: sum.cong)
        qed
        
        (* Rewrite using geometric sums *)
        have sum_rewrite: "(∑i∈{kk..<n-1}. (2::int)^i) = (2^(n-1) - 1) - (2^kk - 1)"
        proof -
          have "(∑i∈{kk..<n-1}. (2::int)^i) = (∑i<n-1. 2^i) - (∑i<kk. 2^i)"
          proof -
            have "{..<n-1} = {..<kk} ∪ {kk..<n-1}"
              using assms(3) by auto
            hence "(∑i<n-1. (2::int)^i) = (∑i∈{..<kk} ∪ {kk..<n-1}. 2^i)"
              by simp
            also have "... = (∑i<kk. 2^i) + (∑i∈{kk..<n-1}. 2^i)"
            proof (rule sum.union_disjoint)
              show "finite {..<kk}" by simp
              show "finite {kk..<n-1}" by simp
              show "{..<kk} ∩ {kk..<n-1} = {}" by auto
            qed
            finally have "(∑i<n-1. (2::int)^i) = (∑i<kk. 2^i) + (∑i∈{kk..<n-1}. 2^i)" .
            thus ?thesis by simp
          qed
          also have "... = (2^(n-1) - 1) - (2^kk - 1)"
            by (simp add: geometric_sum_pow2)
          finally show ?thesis .
        qed
        
        (* Now put it all together *)
        show "s - (∑i∈{kk..<n-1}. as ! i) = v"
          using as_rewrite sum_rewrite
          by (simp add: s_def pow2_target_def v_def)
      qed
      
      finally show ?thesis .
    qed
    
    thus ?thesis
      unfolding RHS_def using ys_in_bitvec by blast
  qed
  
  (* Combine *)
  show ?thesis
    using v_in_LHS v_in_RHS
    by (auto simp: enumL_def enumR_def len_as)
qed

(* LEMMA: miss holds for pow2_list with this target *)
lemma pow2_miss:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
proof -
  (* Use v = 0 (taking no elements from first kk positions) *)
  define v where "v = (0::int)"
  
  have len_as: "length as = n"
    by (simp add: as_def pow2_list_def)
  
  (* v ∈ LHS: take no elements *)
  have v_in_LHS: "v ∈ LHS (e_k as s kk) n"
  proof -
    define xs where "xs = replicate n (0::int)"
    
    have xs_in_bitvec: "xs ∈ bitvec n"
      unfolding bitvec_def using len_as xs_def assms(3) by auto
    
    have "fst (e_k as s kk xs) = v"
    proof -
      have "fst (e_k as s kk xs) = sum_as_on as {0..<kk} xs"
        by (simp add: e_k_def lhs_of_def)
      also have "... = (∑i∈{0..<kk}. as ! i * xs ! i)"
        by (simp add: sum_as_on_def)
      also have "... = (∑i∈{0..<kk}. as ! i * 0)"
      proof -
        have "xs ! i = 0" if "i ∈ {0..<kk}" for i
          using that xs_def assms(2,3) by simp
        thus ?thesis by (auto intro: sum.cong)
      qed
      also have "... = 0"
        by simp
      finally show ?thesis by (simp add: v_def)
    qed
    
    thus ?thesis
      unfolding LHS_def using xs_in_bitvec by blast
  qed
  
  (* v ∉ RHS: 0 cannot be in RHS *)
  have v_not_in_RHS: "v ∉ RHS (e_k as s kk) n"
  proof
    assume "v ∈ RHS (e_k as s kk) n"
    then obtain ys where ys_bv: "ys ∈ bitvec n" 
      and ys_eq: "snd (e_k as s kk ys) = v"
      unfolding RHS_def by blast
    
    have sum_eq: "(∑i∈{kk..<n}. as ! i * ys ! i) = 2^(n-1) - 1"
      using ys_eq by (simp add: e_k_def rhs_of_def len_as v_def sum_as_on_def s_def pow2_target_def)
    
    (* Key lemma: any sum from positions kk..n-1 is divisible by 2^kk *)
        have dvd_sum: "(2::int)^kk dvd (∑i∈{kk..<n}. as ! i * ys ! i)"
    proof -
      have "∀i∈{kk..<n}. (2::int)^kk dvd (as ! i * ys ! i)"
      proof
        fix i assume "i ∈ {kk..<n}"
        hence i_bounds: "i < n" "kk ≤ i" by auto
        
        have as_i: "as ! i = (2::int)^i"
          using i_bounds by (simp add: as_def pow2_list_def)
        
        have dvd_power: "(2::int)^kk dvd (2::int)^i"
        proof -
          from ‹kk ≤ i› obtain d where "i = kk + d"
            using le_Suc_ex by blast
          hence "(2::int)^i = (2::int)^kk * (2::int)^d"
            by (auto simp: power_add)
          thus ?thesis by (metis dvd_triv_left)
        qed
        
        show "(2::int)^kk dvd (as ! i * ys ! i)"
          using as_i dvd_power by (simp add: dvd_mult_right)
      qed
      thus ?thesis by (meson dvd_sum)
    qed
    
    (* So 2^kk divides 2^(n-1) - 1 *)
    with sum_eq have dvd1: "(2::int)^kk dvd (2^(n-1) - 1)" 
      by simp
    
    (* Also 2^kk divides 2^(n-1) *)
    have dvd2: "(2::int)^kk dvd (2::int)^(n-1)"
    proof -
      have "kk ≤ n - 1" using assms(3) by simp
      from this obtain d where "n - 1 = kk + d"
        using le_Suc_ex by blast
      hence "(2::int)^(n-1) = (2::int)^(kk + d)" by simp
      also have "... = (2::int)^kk * (2::int)^d"
        by (simp add: power_add)
      finally show ?thesis by simp
    qed
    
    (* Therefore 2^kk divides their difference, which is 1 *)
    from dvd2 dvd1 
    have "(2::int)^kk dvd ((2::int)^(n-1) - ((2::int)^(n-1) - 1))"
      using dvd_diff by blast
    hence "(2::int)^kk dvd 1" by simp
    
    (* But 2^kk ≥ 2, contradiction *)
    moreover have "(2::int)^kk ≥ 2"
    proof -
      have "kk ≥ 1" using assms(2) by simp
      then obtain k where "kk = Suc k" by (cases kk) auto
      thus ?thesis by simp
    qed
    
    ultimately show False
      by simp
  qed
  
  show ?thesis
    using v_in_LHS v_not_in_RHS
    by (auto simp: enumL_def enumR_def len_as)
qed

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
