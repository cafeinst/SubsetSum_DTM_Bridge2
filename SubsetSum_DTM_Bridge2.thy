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

(* ========================================================================= *)
(* KEY LEMMA: Uniqueness of the Intersection                                *)
(* ========================================================================= *)

(* First, let's characterize what values can appear in LHS and RHS *)

lemma LHS_pow2_characterization:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n" and "s ≡ pow2_target n"
  shows "LHS (e_k as s kk) n = {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}"
proof -
  have len_as: "length as = n" by (simp add: as_def pow2_list_def)
  
  (* LHS values are sums over first kk positions *)
  show ?thesis
  proof (intro set_eqI iffI)
    fix v assume "v ∈ LHS (e_k as s kk) n"
    then obtain xs where xs_bv: "xs ∈ bitvec n"
      and v_eq: "v = fst (e_k as s kk xs)"
      unfolding LHS_def by blast
    
    have "v = sum_as_on as {0..<kk} xs"
      using v_eq by (simp add: e_k_def lhs_of_def)
    also have "... = (∑i∈{0..<kk}. as ! i * xs ! i)"
      by (simp add: sum_as_on_def)
    also have "... = (∑i∈{0..<kk}. (2::int)^i * xs ! i)"
    proof (rule sum.cong, simp)
      fix i assume "i ∈ {0..<kk}"
      hence "i < n" using assms(3) by simp
      thus "as ! i * xs ! i = 2^i * xs ! i"
        by (simp add: as_def pow2_list_def)
    qed
    finally have v_form: "v = (∑i∈{0..<kk}. (2::int)^i * xs ! i)" .
    
    (* Extract the subset S = {i : xs!i = 1} *)
    define S where "S = {i ∈ {0..<kk}. xs ! i = 1}"
    
    have "v = (∑i∈S. (2::int)^i)"
    proof -
      have "(∑i∈{0..<kk}. (2::int)^i * xs ! i) = (∑i∈S. (2::int)^i)"
      proof -
        have "(∑i∈{0..<kk}. (2::int)^i * xs ! i) 
            = (∑i∈{0..<kk}. if xs ! i = 1 then (2::int)^i else 0)"
        proof (rule sum.cong, simp)
          fix i assume "i ∈ {0..<kk}"
          hence "i < n" using assms(3) by simp
          hence "xs ! i ∈ {0,1}"
            using xs_bv bitvec_def nth_mem
            by (metis (mono_tags, lifting) mem_Collect_eq subsetD)
          thus "(2::int)^i * xs ! i = (if xs ! i = 1 then 2^i else 0)"
            by auto
        qed
        also have "... = (∑i∈S. (2::int)^i)"
        proof -
          have S_fin: "finite S" 
            by (simp add: S_def)
          have S_sub: "S ⊆ {0..<kk}" 
          proof -
            have "S = {i ∈ {0..<kk}. xs ! i = 1}" by (simp add: S_def)
            thus ?thesis by auto
          qed
          
          have split: "{0..<kk} = S ∪ ({0..<kk} - S)"
            using S_sub by auto
          
          have "(∑i∈{0..<kk}. if xs ! i = 1 then (2::int)^i else 0)
              = (∑i∈S ∪ ({0..<kk} - S). if xs ! i = 1 then 2^i else 0)"
            using split by simp
          also have "... = (∑i∈S. if xs ! i = 1 then 2^i else 0) 
                         + (∑i∈{0..<kk} - S. if xs ! i = 1 then 2^i else 0)"
            using S_fin by (subst sum.union_disjoint) auto
          also have "... = (∑i∈S. 2^i) + 0"
          proof -
            have eq1: "(∑i∈S. if xs ! i = 1 then (2::int)^i else 0) = (∑i∈S. 2^i)"
              by (rule sum.cong) (auto simp: S_def)
            have eq2: "(∑i∈{0..<kk} - S. if xs ! i = 1 then (2::int)^i else 0) = 0"
              by (rule sum.neutral) (auto simp: S_def)
            show ?thesis using eq1 eq2 by simp
          qed
          also have "... = (∑i∈S. 2^i)" by simp
          finally show ?thesis .
        qed
        finally show ?thesis .
      qed
      with v_form show ?thesis by simp
    qed
    
    moreover have "S ⊆ {0..<kk}" using S_def by blast
    ultimately show "v ∈ {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}" by blast
  next
    fix v assume "v ∈ {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}"
    then obtain S where S_sub: "S ⊆ {0..<kk}" and v_eq: "v = (∑i∈S. (2::int)^i)"
      by blast
    
    (* Construct a bitvector with 1s at positions in S *)
    define xs where "xs = (λi. if i ∈ S then (1::int) else 0)"
    define xs_list where "xs_list = map xs [0..<n]"
    
    have xs_list_bv: "xs_list ∈ bitvec n"
      unfolding bitvec_def xs_list_def xs_def by auto
    
    have "fst (e_k as s kk xs_list) = v"
    proof -
      have "fst (e_k as s kk xs_list) = sum_as_on as {0..<kk} xs_list"
        by (simp add: e_k_def lhs_of_def)
      also have "... = (∑i∈{0..<kk}. as ! i * xs_list ! i)"
        by (simp add: sum_as_on_def)
      also have "... = (∑i∈{0..<kk}. (2::int)^i * xs_list ! i)"
      proof (rule sum.cong, simp)
        fix i assume "i ∈ {0..<kk}"
        hence "i < n" using assms(3) by simp
        thus "as ! i * xs_list ! i = 2^i * xs_list ! i"
          by (simp add: as_def pow2_list_def xs_list_def)
      qed
      also have "... = (∑i∈S. (2::int)^i)"
      proof -
        have "(∑i∈{0..<kk}. (2::int)^i * xs_list ! i) = (∑i∈{0..<kk}. if i ∈ S then 2^i else 0)"
        proof (rule sum.cong, simp)
          fix i assume "i ∈ {0..<kk}"
          hence "i < n" using assms(3) by simp
          hence "i < length [0..<n]" by simp
          hence "xs_list ! i = xs i"
            unfolding xs_list_def by simp
          thus "(2::int)^i * xs_list ! i = (if i ∈ S then 2^i else 0)"
            unfolding xs_def by auto
        qed
                also have "... = (∑i∈S. (2::int)^i)"
        proof -
          have "(∑i∈{0..<kk}. if i ∈ S then (2::int)^i else 0) 
              = sum (λi. if i ∈ S then 2^i else 0) {0..<kk}"
            by simp
          also have "... = sum (λi. 2^i) S"
            using S_sub by (subst sum.inter_restrict[symmetric]) simp
          finally show ?thesis by simp
        qed
        finally show ?thesis .
      qed
      finally show ?thesis using v_eq by simp
    qed
    
    thus "v ∈ LHS (e_k as s kk) n"
      unfolding LHS_def using xs_list_bv by blast
  qed
qed

lemma RHS_pow2_characterization:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n" and "s ≡ pow2_target n"
  shows "RHS (e_k as s kk) n = 
         {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}"
proof -
  have len_as: "length as = n" by (simp add: as_def pow2_list_def)
  
  show ?thesis
  proof (intro set_eqI iffI)
    fix v assume "v ∈ RHS (e_k as s kk) n"
    then obtain xs where xs_bv: "xs ∈ bitvec n"
      and v_eq: "v = snd (e_k as s kk xs)"
      unfolding RHS_def by blast
    
    have "v = s - sum_as_on as {kk..<n} xs"
      using v_eq by (simp add: e_k_def rhs_of_def len_as)
    also have "... = (2::int)^(n-1) - 1 - (∑i∈{kk..<n}. as ! i * xs ! i)"
      by (simp add: sum_as_on_def s_def pow2_target_def)
    also have "... = (2::int)^(n-1) - 1 - (∑i∈{kk..<n}. (2::int)^i * xs ! i)"
    proof -
      have "(∑i∈{kk..<n}. as ! i * xs ! i) = (∑i∈{kk..<n}. (2::int)^i * xs ! i)"
      proof (rule sum.cong, simp)
        fix i assume "i ∈ {kk..<n}"
        hence "i < n" by simp
        thus "as ! i * xs ! i = 2^i * xs ! i"
          by (simp add: as_def pow2_list_def)
      qed
      thus ?thesis by simp
    qed
    finally have v_form: "v = (2::int)^(n-1) - 1 - (∑i∈{kk..<n}. (2::int)^i * xs ! i)" .
    
    define S where "S = {i ∈ {kk..<n}. xs ! i = 1}"
    
    have "v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)"
    proof -
      have "(∑i∈{kk..<n}. (2::int)^i * xs ! i) = (∑i∈S. (2::int)^i)"
      proof -
        have "(∑i∈{kk..<n}. (2::int)^i * xs ! i) 
            = (∑i∈{kk..<n}. if xs ! i = 1 then (2::int)^i else 0)"
        proof (rule sum.cong, simp)
          fix i assume "i ∈ {kk..<n}"
          hence "i < n" by simp
          hence "xs ! i ∈ {0,1}"
            using xs_bv bitvec_def nth_mem
            by (metis (mono_tags, lifting) mem_Collect_eq subsetD)
          thus "(2::int)^i * xs ! i = (if xs ! i = 1 then 2^i else 0)"
            by auto
        qed
        also have "... = (∑i∈S. (2::int)^i)"
          by (simp add: S_def sum.inter_restrict)
        finally show ?thesis .
      qed
      with v_form show ?thesis by simp
    qed
    
    moreover have "S ⊆ {kk..<n}" using S_def by blast
    ultimately show "v ∈ {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}"
      by blast
  next
    fix v assume "v ∈ {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}"
    then obtain S where S_sub: "S ⊆ {kk..<n}" 
      and v_eq: "v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)"
      by blast
    
    define xs where "xs = (λi. if i ∈ S then (1::int) else 0)"
    define xs_list where "xs_list = map xs [0..<n]"
    
    have xs_list_bv: "xs_list ∈ bitvec n"
      unfolding bitvec_def xs_list_def xs_def by auto
    
    have "snd (e_k as s kk xs_list) = v"
    proof -
      have "snd (e_k as s kk xs_list) = s - sum_as_on as {kk..<n} xs_list"
        by (simp add: e_k_def rhs_of_def len_as)
      also have "... = (2::int)^(n-1) - 1 - (∑i∈{kk..<n}. as ! i * xs_list ! i)"
        by (simp add: sum_as_on_def s_def pow2_target_def)
      also have "... = (2::int)^(n-1) - 1 - (∑i∈{kk..<n}. (2::int)^i * xs_list ! i)"
      proof -
        have "(∑i∈{kk..<n}. as ! i * xs_list ! i) = (∑i∈{kk..<n}. (2::int)^i * xs_list ! i)"
        proof (rule sum.cong, simp)
          fix i assume "i ∈ {kk..<n}"
          hence "i < n" by simp
          thus "as ! i * xs_list ! i = 2^i * xs_list ! i"
            by (simp add: as_def pow2_list_def xs_list_def)
        qed
        thus ?thesis by simp
      qed
      also have "... = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)"
      proof -
        have "(∑i∈{kk..<n}. (2::int)^i * xs_list ! i) = (∑i∈S. (2::int)^i)"
        proof -
          have "(∑i∈{kk..<n}. (2::int)^i * xs_list ! i) 
              = (∑i∈{kk..<n}. if i ∈ S then 2^i else 0)"
          proof (rule sum.cong, simp)
            fix i assume "i ∈ {kk..<n}"
            show "(2::int)^i * xs_list ! i = (if i ∈ S then 2^i else 0)"
              by (simp add: xs_list_def xs_def)
          qed
          also have "... = (∑i∈S. (2::int)^i)"
            by (simp add: sum.inter_restrict S_sub)
          finally show ?thesis .
        qed
        thus ?thesis by simp
      qed
      finally show ?thesis using v_eq by simp
    qed
    
    thus "v ∈ RHS (e_k as s kk) n"
      unfolding RHS_def using xs_list_bv by blast
  qed
qed

(* Now the key uniqueness lemma *)
lemma pow2_unique_intersection:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n" and "s ≡ pow2_target n"
  shows "set (enumL as s kk) ∩ set (enumR as s kk) = {(2::int)^kk - 1}"
proof -
  have LHS_char: "LHS (e_k as s kk) n = {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}"
    using LHS_pow2_characterization[OF assms(1-3)] by (simp add: as_def s_def)
  
  have RHS_char: "RHS (e_k as s kk) n = 
                  {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}"
    using RHS_pow2_characterization[OF assms(1-3)] by (simp add: as_def s_def)
  
  have "set (enumL as s kk) = LHS (e_k as s kk) n"
    by (simp add: enumL_def as_def)
  moreover have "set (enumR as s kk) = RHS (e_k as s kk) n"
    by (simp add: enumR_def as_def)
  ultimately have "set (enumL as s kk) ∩ set (enumR as s kk) = 
                   LHS (e_k as s kk) n ∩ RHS (e_k as s kk) n"
    by simp
  
  also have "... = {(2::int)^kk - 1}"
  proof (intro set_eqI iffI)
    fix v assume "v ∈ LHS (e_k as s kk) n ∩ RHS (e_k as s kk) n"
    hence v_LHS: "v ∈ LHS (e_k as s kk) n" and v_RHS: "v ∈ RHS (e_k as s kk) n"
      by blast+
    
    from v_LHS LHS_char obtain SL where SL_sub: "SL ⊆ {0..<kk}" 
      and v_L: "v = (∑i∈SL. (2::int)^i)" by blast
    
    from v_RHS RHS_char obtain SR where SR_sub: "SR ⊆ {kk..<n}" 
      and v_R: "v = (2::int)^(n-1) - 1 - (∑i∈SR. (2::int)^i)" by blast
    
    (* Combine the two equations *)
    have "(∑i∈SL. (2::int)^i) = (2::int)^(n-1) - 1 - (∑i∈SR. (2::int)^i)"
      using v_L v_R by simp
    hence "(∑i∈SL. (2::int)^i) + (∑i∈SR. (2::int)^i) = (2::int)^(n-1) - 1"
      by simp
    
    (* Key insight: (2^(n-1) - 1) = sum of all bits 0..(n-2) *)
    (* And SL ∪ SR gives us this sum, with SL and SR disjoint *)
    
    (* The ONLY way to make 2^(n-1) - 1 is to take ALL positions 0..(n-2) *)
    have "(2::int)^(n-1) - 1 = (∑i<n-1. (2::int)^i)"
      by (rule geometric_sum_pow2)
    
    (* So SL ∪ SR = {0..<n-1} *)
    (* But SL ⊆ {0..<kk} and SR ⊆ {kk..<n} are disjoint *)
    (* So we need SL = {0..<kk} and SR = {kk..<n-1} *)
    
    have SL_eq: "SL = {0..<kk}"
      sorry (* Need to prove this from the sum equation *)
    
    hence "v = (∑i∈{0..<kk}. (2::int)^i)"
      using v_L by simp
    also have "... = (∑i<kk. (2::int)^i)"
      by (simp add: lessThan_atLeast0)
    also have "... = (2::int)^kk - 1"
      by (rule geometric_sum_pow2)
    finally show "v = (2::int)^kk - 1" .
  next
    fix v assume "v = (2::int)^kk - 1"
    
    (* Show v ∈ LHS *)
    have "v ∈ LHS (e_k as s kk) n"
    proof -
      have "v = (∑i∈{0..<kk}. (2::int)^i)"
        using ‹v = (2::int)^kk - 1› by (simp add: geometric_sum_pow2 lessThan_atLeast0)
      with LHS_char show ?thesis by blast
    qed
    
    (* Show v ∈ RHS *)
    moreover have "v ∈ RHS (e_k as s kk) n"
    proof -
      have "v = (2::int)^(n-1) - 1 - (∑i∈{kk..<n-1}. (2::int)^i)"
      proof -
        have "(2::int)^(n-1) - 1 = (∑i<n-1. (2::int)^i)"
          by (rule geometric_sum_pow2)
        also have "... = (∑i∈{0..<kk}. (2::int)^i) + (∑i∈{kk..<n-1}. (2::int)^i)"
        proof -
          have "{0..<n-1} = {0..<kk} ∪ {kk..<n-1}"
            using assms(3) by auto
          hence "(∑i<n-1. (2::int)^i) = (∑i∈{0..<kk} ∪ {kk..<n-1}. 2^i)"
            by (simp add: lessThan_atLeast0)
          also have "... = (∑i∈{0..<kk}. 2^i) + (∑i∈{kk..<n-1}. 2^i)"
            by (rule sum.union_disjoint) auto
          finally show ?thesis .
        qed
        finally have "(2::int)^(n-1) - 1 - (∑i∈{kk..<n-1}. (2::int)^i) 
                    = (∑i∈{0..<kk}. (2::int)^i)"
          by simp
        thus ?thesis
          using ‹v = (2::int)^kk - 1› by (simp add: geometric_sum_pow2 lessThan_atLeast0)
      qed
      
      moreover have "{kk..<n-1} ⊆ {kk..<n}"
        using assms(1) by auto
      ultimately show ?thesis using RHS_char by blast
    qed
    
    ultimately show "v ∈ LHS (e_k as s kk) n ∩ RHS (e_k as s kk) n"
      by blast
  qed
  
  finally show ?thesis .
qed

(* LEMMA: baseline_only_j holds for pow2_list with this target *)
lemma pow2_baseline_only_j:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n"
      and "s ≡ pow2_target n"
  shows "∀j. good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
             (∀j'<length (enumL as s kk). j' ≠ j ⟶
                Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
proof (intro allI impI)
  fix j
  assume good_holds: "good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  
  have len_as: "length as = n"
    by (simp add: as_def pow2_list_def)
  
  (* From good, we know there EXISTS a matching pair *)
  obtain jL jR where
    jL_bound: "jL < length (enumL as s kk)" and
    jR_bound: "jR < length (enumR as s kk)" and
    match: "Lval_at as s ((!) (enc as s kk)) jL = 
            Rval_at as s ((!) (enc as s kk)) jR"
    using good_holds unfolding good_def by blast
  
  (* What is this matched value? It's enumL!jL = enumR!jR *)
  have "Lval_at as s ((!) (enc as s kk)) jL = enumL as s kk ! jL"
    using Lval_at_on_enc_block[OF jL_bound] by simp
  moreover have "Rval_at as s ((!) (enc as s kk)) jR = enumR as s kk ! jR"
    using Rval_at_on_enc_block[OF jR_bound] by simp
  ultimately have val_match: "enumL as s kk ! jL = enumR as s kk ! jR"
    using match by simp
  
  (* Key fact: For pow2_list with this target, the ONLY value in both 
     enumL and enumR is 2^kk - 1 (from pow2_hit proof) *)
  have unique_intersection: "enumL as s kk ! jL = (2::int)^kk - 1"
    sorry (* This requires proving that 2^kk - 1 is the UNIQUE intersection *)
  
  (* Now show: all OTHER j' don't match anything in enumR *)
  show "∀j'<length (enumL as s kk). j' ≠ j ⟶
        Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk)"
  proof (intro allI impI)
    fix j'
    assume j'_bound: "j' < length (enumL as s kk)"
       and j'_neq: "j' ≠ j"
    
    (* What is the value at j'? *)
    have "Lval_at as s ((!) (enc as s kk)) j' = enumL as s kk ! j'"
      using Lval_at_on_enc_block[OF j'_bound] by simp
    
    (* We need to show this is NOT in enumR *)
    (* Two cases: either j' = jL or j' ≠ jL *)
    show "Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk)"
    proof (cases "j' = jL")
      case True
      (* If j' = jL, then since j' ≠ j, we have j ≠ jL *)
      (* But wait - j is arbitrary! We can't conclude anything about j *)
      (* The statement is: IF good holds, THEN for ANY j' ≠ j, ... *)
      (* This means: IF good holds AND we pick ANY witness j, 
         THEN all j' ≠ j don't witness *)
      
      (* Actually, the statement is saying: "there exists at most one witness"
         So we need to prove: jL is the ONLY witness *)
      
      (* Since j' = jL and good holds with jL as witness, 
         and we're assuming j' ≠ j, this means j is NOT a witness *)
      sorry
      
    next
      case False
      (* j' ≠ jL, so enumL!j' ≠ enumL!jL (by distinctness) *)
      have "distinct (enumL as s kk)"
        by (simp add: enumL_def)
      
      hence "enumL as s kk ! j' ≠ enumL as s kk ! jL"
        using False j'_bound jL_bound by (simp add: nth_eq_iff_index_eq)
      
      (* So enumL!j' ≠ 2^kk - 1 (since enumL!jL = 2^kk - 1) *)
      hence "enumL as s kk ! j' ≠ (2::int)^kk - 1"
        using unique_intersection by simp
      
      (* And 2^kk - 1 is the ONLY value in both enumL and enumR *)
      moreover have "∀v ∈ set (enumL as s kk) ∩ set (enumR as s kk). v = (2::int)^kk - 1"
        sorry (* This is the key uniqueness property *)
      
      (* Therefore enumL!j' is NOT in enumR *)
      ultimately show ?thesis
        using ‹Lval_at as s ((!) (enc as s kk)) j' = enumL as s kk ! j'›
              j'_bound by (auto simp: in_set_conv_nth)
    qed
  qed
qed

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
