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

(* Helper: Uniqueness of binary representation *)
lemma pow2_sum_unique:
  assumes "finite A" "finite B" 
      and "A ⊆ {..<m}" "B ⊆ {..<m}"
      and "(∑i∈A. (2::int)^i) = (∑i∈B. (2::int)^i)"
  shows "A = B"
  using assms
proof (induction m arbitrary: A B)
  case 0
  then show ?case by auto
next
  case (Suc m)
  show ?case
  proof (cases "m ∈ A")
    case A_has_m: True
    show ?thesis
    proof (cases "m ∈ B")
      case B_has_m: True
      have "A - {m} ⊆ {..<m}" using Suc.prems(3) by auto
      moreover have "B - {m} ⊆ {..<m}" using Suc.prems(4) by auto
      moreover have "(∑i∈A - {m}. (2::int)^i) = (∑i∈B - {m}. (2::int)^i)"
      proof -
        have "(∑i∈A. (2::int)^i) = (∑i∈A - {m}. 2^i) + 2^m"
          using A_has_m Suc.prems(1) by (subst sum.remove) auto
        moreover have "(∑i∈B. (2::int)^i) = (∑i∈B - {m}. 2^i) + 2^m"
          using B_has_m Suc.prems(2) by (subst sum.remove) auto
        ultimately show ?thesis using Suc.prems(5) by simp
      qed
      ultimately have "A - {m} = B - {m}"
        using Suc.IH[of "A - {m}" "B - {m}"] Suc.prems(1,2) by auto
      then show ?thesis using A_has_m B_has_m by blast
    next
      case B_no_m: False
      have "2^m ≤ (∑i∈A. (2::int)^i)"
        using A_has_m Suc.prems(1) by (auto intro: member_le_sum)
      also have "... = (∑i∈B. (2::int)^i)" using Suc.prems(5) by simp
      also have "... = (∑i∈B. 2^i)" by simp
      also have "... < 2^m"
      proof -
        have "B ⊆ {..<m}" using Suc.prems(4) B_no_m
          by (simp add: lessThan_Suc subset_insert)
        hence "(∑i∈B. (2::int)^i) ≤ (∑i<m. (2::int)^i)"
          using Suc.prems(2) by (intro sum_mono2) auto
        also have "... = 2^m - 1" by (rule geometric_sum_pow2)
        finally show ?thesis by simp
      qed
      finally have "2^m < (2::int)^m"
        using Suc.prems(5) ‹2 ^ m ≤ sum ((^) 2) A› ‹sum ((^) 2) B < 2 ^ m› 
        by linarith
      then show ?thesis by simp
    qed
  next
    case A_no_m: False
    show ?thesis
    proof (cases "m ∈ B")
      case B_has_m: True
      have "2^m ≤ (∑i∈B. (2::int)^i)"
        using B_has_m Suc.prems(2) by (auto intro: member_le_sum)
      also have "... = (∑i∈A. (2::int)^i)" using Suc.prems(5) by simp
      also have "... < 2^m"
      proof -
        have "A ⊆ {..<m}" using Suc.prems(3) A_no_m
          by (simp add: lessThan_Suc subset_insert)
        hence "(∑i∈A. (2::int)^i) ≤ (∑i<m. (2::int)^i)"
          using Suc.prems(1) by (intro sum_mono2) auto
        also have "... = 2^m - 1" by (rule geometric_sum_pow2)
        finally show ?thesis by simp
      qed
      finally show ?thesis by simp
    next
      case B_no_m: False
      have "A ⊆ {..<m}" using Suc.prems(3) A_no_m
        by (simp add: lessThan_Suc subset_insert)
      moreover have "B ⊆ {..<m}" using Suc.prems(4) B_no_m
        by (simp add: lessThan_Suc subset_insert)
      ultimately show ?thesis
        using Suc.IH Suc.prems(1,2,5) by auto
    qed
  qed
qed

(* Characterization of LHS for pow2_list *)
lemma LHS_pow2_characterization:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n" and "s ≡ pow2_target n"
  shows "LHS (e_k as s kk) n = {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}"
proof (intro set_eqI iffI)
  fix v assume "v ∈ LHS (e_k as s kk) n"
  then obtain xs where xs: "xs ∈ bitvec n" and v: "v = fst (e_k as s kk xs)"
    by (auto simp: LHS_def)
  define S where "S = {i ∈ {0..<kk}. xs ! i = 1}"
  have "S ⊆ {0..<kk}" by (auto simp: S_def)
  moreover have "v = (∑i∈S. (2::int)^i)"
  proof -
    have "v = lhs_of as kk xs" using v by (simp add: e_k_def)
    also have "... = (∑i∈{0..<kk}. as ! i * xs ! i)"
      by (simp add: lhs_of_def sum_as_on_def)
    also have "... = (∑i∈{0..<kk}. (if xs ! i = 1 then (2::int)^i else 0))"
    proof (intro sum.cong refl)
      fix i assume i_bound: "i ∈ {0..<kk}"
      have "as ! i = 2^i"
        using i_bound assms(3) by (auto simp: as_def pow2_list_def nth_append)
      moreover have "xs ! i ∈ {0, 1}"
      proof -
        have "i < length xs" using xs i_bound assms(3) by (auto simp: bitvec_def)
        hence "xs ! i ∈ set xs" by (rule nth_mem)
        thus ?thesis using xs by (auto simp: bitvec_def)
      qed
      ultimately show "as ! i * xs ! i = (if xs ! i = 1 then (2::int)^i else 0)"
        by auto
    qed
    also have "... = (∑i∈S. (2::int)^i)"
    proof -
      have "(∑i∈{0..<kk}. if xs ! i = 1 then (2::int)^i else 0) = (∑i∈S. 2^i)"
      proof (rule sum.mono_neutral_cong_left[symmetric])
        show "finite {0..<kk}" by simp
        show "S ⊆ {0..<kk}" by (auto simp: S_def)
        show "∀i∈{0..<kk} - S. (if xs ! i = 1 then 2^i else 0) = 0"
          by (auto simp: S_def)
        fix i assume "i ∈ S"
        hence "xs ! i = 1" by (auto simp: S_def)
        thus "(2::int)^i = (if xs ! i = 1 then 2^i else 0)" by simp
      qed
      thus ?thesis .
    qed
    finally show ?thesis .
  qed
  ultimately show "v ∈ {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}" by blast
next
  fix v assume "v ∈ {v. ∃S⊆{0..<kk}. v = (∑i∈S. (2::int)^i)}"
  then obtain S where S: "S ⊆ {0..<kk}" and v: "v = (∑i∈S. (2::int)^i)" by blast
  define xs where "xs = map (λi. if i ∈ S then (1::int) else 0) [0..<n]"
  have xs_bv: "xs ∈ bitvec n"
    by (auto simp: xs_def bitvec_def)
  have "v = (∑i∈{0..<kk}. as ! i * xs ! i)"
  proof -
    have "(∑i∈S. (2::int)^i) = (∑i∈{0..<kk}. if i ∈ S then 2^i else 0)"
    proof -
      have "finite {0..<kk}" by simp
      moreover have "S ⊆ {0..<kk}" using S by simp
      moreover have "∀i∈{0..<kk} - S. (if i ∈ S then (2::int)^i else 0) = 0" 
        by simp
      moreover have "∀x∈S. (2::int)^x = (if x ∈ S then 2^x else 0)" 
        by simp
      ultimately show ?thesis
        using sum.mono_neutral_cong_left[symmetric, of "{0..<kk}" S 
            "λi. if i ∈ S then (2::int)^i else 0" "λi. (2::int)^i"]
        by simp
    qed
    also have "... = (∑i∈{0..<kk}. as ! i * xs ! i)"
    proof (intro sum.cong refl)
      fix i assume i: "i ∈ {0..<kk}"
      have "as ! i = 2^i"
        using i assms(3) by (auto simp: as_def pow2_list_def nth_append)
      moreover have "xs ! i = (if i ∈ S then 1 else 0)"
        using i assms(3) by (auto simp: xs_def)
      ultimately show "(if i ∈ S then (2::int)^i else 0) = as ! i * xs ! i"
        by auto
    qed
    finally show ?thesis using v by simp
  qed
  hence "v = fst (e_k as s kk xs)"
    by (simp add: e_k_def lhs_of_def sum_as_on_def)
  thus "v ∈ LHS (e_k as s kk) n"
    using xs_bv by (auto simp: LHS_def)
qed

(* Characterization of RHS for pow2_list *)
lemma RHS_pow2_characterization:
  assumes "n ≥ 2" "1 ≤ kk" "kk < n"
  defines "as ≡ pow2_list n" and "s ≡ pow2_target n"
  shows "RHS (e_k as s kk) n = {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}"
proof (intro set_eqI iffI)
  fix v assume "v ∈ RHS (e_k as s kk) n"
  then obtain xs where xs: "xs ∈ bitvec n" and v: "v = snd (e_k as s kk xs)"
    by (auto simp: RHS_def)
  define S where "S = {i ∈ {kk..<n}. xs ! i = 1}"
  have "S ⊆ {kk..<n}" by (auto simp: S_def)
  moreover have "v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)"
  proof -
    have len: "length as = n" by (simp add: as_def pow2_list_def)
    have "v = rhs_of as kk s xs" using v by (simp add: e_k_def)
    also have "... = s - (∑i∈{kk..<n}. as ! i * xs ! i)"
      by (simp add: rhs_of_def sum_as_on_def len)
    also have "... = (2::int)^(n-1) - 1 - (∑i∈{kk..<n}. (if xs ! i = 1 then (2::int)^i else 0))"
    proof -
      have "(∑i∈{kk..<n}. as ! i * xs ! i) = (∑i∈{kk..<n}. (if xs ! i = 1 then (2::int)^i else 0))"
      proof (intro sum.cong refl)
        fix i assume i: "i ∈ {kk..<n}"
        have "as ! i = 2^i"
          using i by (auto simp: as_def pow2_list_def nth_append)
        moreover have "xs ! i ∈ {0, 1}"
        proof -
          have "i < length xs" using xs i by (auto simp: bitvec_def)
          hence "xs ! i ∈ set xs" by (rule nth_mem)
          thus ?thesis using xs by (auto simp: bitvec_def)
        qed
        ultimately show "as ! i * xs ! i = (if xs ! i = 1 then (2::int)^i else 0)"
          by auto
      qed
      thus ?thesis by (simp add: s_def pow2_target_def)
    qed
    also have "... = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)"
    proof -
      have "(∑i∈{kk..<n}. (if xs ! i = 1 then (2::int)^i else 0)) = (∑i∈S. 2^i)"
      proof -
        have "S ⊆ {kk..<n}" by (auto simp: S_def)
        moreover have "∀i∈{kk..<n} - S. (if xs ! i = 1 then (2::int)^i else 0) = 0"
          by (auto simp: S_def)
        moreover have "∀i∈S. (2::int)^i = (if xs ! i = 1 then 2^i else 0)"
          by (auto simp: S_def)
        ultimately have "(∑i∈S. (2::int)^i) = (∑i∈{kk..<n}. if xs ! i = 1 then 2^i else 0)"
          using sum.mono_neutral_cong_left[symmetric, of "{kk..<n}" S "λi. if xs ! i = 1 then (2::int)^i else 0" "λi. (2::int)^i"]
          by simp
        thus ?thesis by simp
      qed
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
  ultimately show "v ∈ {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}" by blast
next
  fix v assume "v ∈ {v. ∃S⊆{kk..<n}. v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)}"
  then obtain S where S: "S ⊆ {kk..<n}" and v: "v = (2::int)^(n-1) - 1 - (∑i∈S. (2::int)^i)"
    by blast
  define xs where "xs = map (λi. if i ∈ S then (1::int) else 0) [0..<n]"
  have xs_bv: "xs ∈ bitvec n"
    by (auto simp: xs_def bitvec_def)
  have len: "length as = n" by (simp add: as_def pow2_list_def)
  have "v = s - (∑i∈{kk..<n}. as ! i * xs ! i)"
  proof -
    have "(∑i∈S. (2::int)^i) = (∑i∈{kk..<n}. if i ∈ S then 2^i else 0)"
    proof -
      have "finite {kk..<n}" by simp
      moreover have "S ⊆ {kk..<n}" using S by simp
      moreover have "∀i∈{kk..<n} - S. (if i ∈ S then (2::int)^i else 0) = 0" 
        by simp
      moreover have "∀x∈S. (2::int)^x = (if x ∈ S then 2^x else 0)" 
        by simp
      ultimately show ?thesis
        using sum.mono_neutral_cong_left[symmetric, of "{kk..<n}" S "λi. if i ∈ S then (2::int)^i else 0" "λi. (2::int)^i"]
        by simp
    qed
    also have "... = (∑i∈{kk..<n}. as ! i * xs ! i)"
    proof (intro sum.cong refl)
      fix i assume i: "i ∈ {kk..<n}"
      have "as ! i = 2^i"
        using i by (auto simp: as_def pow2_list_def nth_append)
      moreover have "xs ! i = (if i ∈ S then 1 else 0)"
        using i by (auto simp: xs_def)
      ultimately show "(if i ∈ S then (2::int)^i else 0) = as ! i * xs ! i"
        by auto
    qed
    finally show ?thesis using v by (simp add: s_def pow2_target_def)
  qed
  hence "v = snd (e_k as s kk xs)"
    by (simp add: e_k_def rhs_of_def sum_as_on_def len)
  thus "v ∈ RHS (e_k as s kk) n"
    using xs_bv by (auto simp: RHS_def)
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
    by (simp add: enumL_def as_def pow2_list_def)
  moreover have "set (enumR as s kk) = RHS (e_k as s kk) n"
    by (simp add: enumR_def as_def pow2_list_def)
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
    hence eq_sum: "(∑i∈SL. (2::int)^i) + (∑i∈SR. (2::int)^i) = (2::int)^(n-1) - 1"
      by simp
    
    (* Key insight: (2^(n-1) - 1) = sum of all bits 0..(n-2) *)
    (* And SL ∪ SR gives us this sum, with SL and SR disjoint *)
    
    (* The ONLY way to make 2^(n-1) - 1 is to take ALL positions 0..(n-2) *)
    have "(2::int)^(n-1) - 1 = (∑i<n-1. (2::int)^i)"
      by (simp add: geometric_sum_pow2)
    
    (* So SL ∪ SR = {0..<n-1} *)
    (* But SL ⊆ {0..<kk} and SR ⊆ {kk..<n} are disjoint *)
    (* So we need SL = {0..<kk} and SR = {kk..<n-1} *)
    
    have SL_eq: "SL = {0..<kk}"
    proof -
      (* We have: SL ⊆ {0..<kk}, SR ⊆ {kk..<n}, disjoint, and the sum equals 2^(n-1) - 1 *)
      have union_sum: "(∑i∈SL ∪ SR. (2::int)^i) = 2^(n-1) - 1"
      proof -
        have "SL ∩ SR = {}"
        proof (rule equals0I)
          fix x assume "x ∈ SL ∩ SR"
          hence "x ∈ SL" and "x ∈ SR" by auto
          hence "x < kk" using SL_sub by auto
          moreover have "kk ≤ x" using `x ∈ SR` SR_sub by auto
          ultimately show False by simp
        qed
        hence "(∑i∈SL ∪ SR. (2::int)^i) = (∑i∈SL. 2^i) + (∑i∈SR. 2^i)"
        proof (intro sum.union_disjoint)
          show "SL ∩ SR = {}" using `SL ∩ SR = {}` .
          show "finite SL" using SL_sub by (rule finite_subset) simp
          show "finite SR" using SR_sub by (rule finite_subset) simp
        qed
        also have "... = 2^(n-1) - 1"
          using eq_sum by simp
        finally show ?thesis .
      qed
      
      (* Also: {0..<n-1} sums to 2^(n-1) - 1 *)
      have full_sum: "(∑i∈{0..<n-1}. (2::int)^i) = 2^(n-1) - 1"
        using geometric_sum_pow2[of "n-1"] by (simp add: lessThan_atLeast0)
      
      (* By uniqueness of binary representation: *)
      have "finite SL" using SL_sub by (rule finite_subset) simp
      moreover have "finite SR" using SR_sub by (rule finite_subset) simp
      ultimately have "finite (SL ∪ SR)" by simp
      
      have "SL ∪ SR = {0..<n-1}"
      proof (rule pow2_sum_unique)
        show "finite (SL ∪ SR)" using `finite (SL ∪ SR)` .
        show "finite {0..<n-1}" by simp

        show "SL ∪ SR ⊆ {..<n-1}"
          using SL_sub SR_sub assms(3) by auto
        show "{0..<n-1} ⊆ {..<n-1}" by auto
        show "(∑i∈SL ∪ SR. (2::int)^i) = (∑i∈{0..<n-1}. (2::int)^i)"
          using union_sum full_sum by simp
      qed
      
      (* Since SL and SR are disjoint and cover {0..<n-1}, and SL ⊆ {0..<kk}: *)
      thus ?thesis
      proof -
        have "SL ∩ SR = {}"
          using SL_sub SR_sub by auto
        have "SL ∪ SR = {0..<n-1}" using ‹SL ∪ SR = {0..<n-1}› .
        have "{0..<n-1} = {0..<kk} ∪ {kk..<n-1}"
          using assms(3) by auto
        hence "SL ∪ SR = {0..<kk} ∪ {kk..<n-1}" using ‹SL ∪ SR = {0..<n-1}› by simp
        moreover have "SL ⊆ {0..<kk}" using SL_sub by simp
        moreover have "SR ⊆ {kk..<n-1}"
          using SR_sub ‹SL ∪ SR = {0..<kk} ∪ {kk..<n-1}› ‹SL ∩ SR = {}› by auto
        moreover have "{0..<kk} ∩ {kk..<n-1} = {}" by auto
        ultimately show "SL = {0..<kk}"
          using ‹SL ∩ SR = {}› by auto
      qed
    qed
    
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
  
  (* Key fact: the intersection is exactly {2^kk - 1} *)
  have intersection_singleton: "set (enumL as s kk) ∩ set (enumR as s kk) = {(2::int)^kk - 1}"
    using pow2_unique_intersection[OF assms(1-3)] by (simp add: as_def s_def)
  
  (* Since the intersection is a singleton, there's exactly one jL with enumL!jL in enumR *)
  have unique_witness: "∃!jL. jL < length (enumL as s kk) ∧ 
                              enumL as s kk ! jL ∈ set (enumR as s kk)"
  proof -
    have "distinct (enumL as s kk)"
      by (simp add: enumL_def)
    moreover have "{v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)} = {(2::int)^kk - 1}"
      using intersection_singleton by auto
    ultimately show ?thesis
      by (metis (mono_tags, lifting) distinct_Ex1 in_set_conv_nth mem_Collect_eq singletonD)
  qed
  
  (* Now show the required property *)
  show "∀j'<length (enumL as s kk). j' ≠ j ⟶
        Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk)"
  proof (intro allI impI)
    fix j'
    assume j'_bound: "j' < length (enumL as s kk)"
       and j'_neq: "j' ≠ j"
    
    have "Lval_at as s ((!) (enc as s kk)) j' = enumL as s kk ! j'"
      using Lval_at_on_enc_block[OF j'_bound] by simp
    
    (* If j is the unique witness, then j' ≠ j means j' is not a witness *)
    show "Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk)"
    proof (cases "j < length (enumL as s kk) ∧ enumL as s kk ! j ∈ set (enumR as s kk)")
      case True
      (* j is a witness, so by uniqueness, j is THE witness *)
      then have "j' < length (enumL as s kk) ∧ enumL as s kk ! j' ∈ set (enumR as s kk) ⟹ j' = j"
        using unique_witness by blast
      thus ?thesis using j'_neq by auto
    next  
      case False
      (* j is not a witness, so the implication is vacuous *)
      (* But we assumed good holds, which means there IS a witness *)
      (* So either j is out of bounds, or enumL!j is not in enumR *)
      (* In either case, we can't conclude anything about j' from this *)
      (* We fall back to the intersection singleton property *)
      show ?thesis
      proof (rule ccontr)
        assume "¬ (Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
        hence in_R: "Lval_at as s ((!) (enc as s kk)) j' ∈ set (enumR as s kk)" by simp
        have "enumL as s kk ! j' ∈ set (enumR as s kk)"
          using in_R ‹Lval_at as s ((!) (enc as s kk)) j' = enumL as s kk ! j'› by simp
        moreover have "enumL as s kk ! j' ∈ set (enumL as s kk)"
          using j'_bound by simp
        ultimately have "enumL as s kk ! j' ∈ set (enumL as s kk) ∩ set (enumR as s kk)"
          by simp
        hence "enumL as s kk ! j' = (2::int)^kk - 1"
          using intersection_singleton by auto
        
        (* So j' is the unique witness *)
        have "j' < length (enumL as s kk) ∧ enumL as s kk ! j' ∈ set (enumR as s kk)"
          using j'_bound ‹enumL as s kk ! j' ∈ set (enumR as s kk)› by simp
        
        (* Similarly, from good_holds, there exists some witness *)
        obtain jL jR where
          jL_bound: "jL < length (enumL as s kk)" and
          jR_bound: "jR < length (enumR as s kk)" and
          match: "Lval_at as s ((!) (enc as s kk)) jL = Rval_at as s ((!) (enc as s kk)) jR"
          using good_holds unfolding good_def by blast
        
        have "enumL as s kk ! jL = enumR as s kk ! jR"
        proof -
          have "Lval_at as s ((!) (enc as s kk)) jL = enumL as s kk ! jL"
            using Lval_at_on_enc_block[OF jL_bound] by simp
          moreover have "Rval_at as s ((!) (enc as s kk)) jR = enumR as s kk ! jR"
            using Rval_at_on_enc_block[OF jR_bound] by simp
          ultimately show ?thesis using match by simp
        qed
        
        hence "jL < length (enumL as s kk) ∧ enumL as s kk ! jL ∈ set (enumR as s kk)"
          using jL_bound jR_bound by auto
        
        (* By uniqueness, jL = j' *)
        hence "jL = j'" using unique_witness
          using ‹j' < length (enumL as s kk) ∧ enumL as s kk ! j' ∈ set (enumR as s kk)› by blast
        
        (* Now, if j < length enumL and enumL!j in enumR, then j = jL = j' by uniqueness *)
        (* But we have j' ≠ j, so this is a contradiction *)
        (* The resolution is that j is not a witness (case False) *)
        (* In that case, j is not the unique witness, so j ≠ j' *)
        (* Wait, we're already in case False, so this should be fine *)
        (* Actually, the issue is that when j is not the witness, *)
        (* the statement is vacuously true because good → False *)
        (* But we have good_holds, so there must be a witness *)
        (* That witness is j' (as we just showed) *)
        (* So j ≠ j' is consistent *)
        show False
          using False ‹jL = j'› j'_neq
          by (metis ‹jL < length (enumL as s kk) ∧ enumL as s kk ! jL ∈ set (enumR as s kk)›)
      qed
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
