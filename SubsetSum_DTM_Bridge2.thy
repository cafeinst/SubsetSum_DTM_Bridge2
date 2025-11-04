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

(* Step 3: Construct R-oracle avoiding forbidden L-values *)
lemma construct_avoiding_R_oracle:
  assumes unread_R: "∀jR < length (enumR as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
      and v_target: "v ∈ set (enumL as s kk)"
      and v_not_forbidden: "v ∉ F"
      and forbidden: "finite F" "F ⊆ set (enumL as s kk)"
      and slack: "card (set (enumR as s kk)) > card F + 1"
  shows "∃oR_has oR_no.
    (∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_has i = (enc as s kk) ! i) ∧
    (∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_no i = (enc as s kk) ! i) ∧
    (v ∈ set (enumR as s kk) ⟶ 
      (∃jR. jR < length (enumR as s kk) ∧ Rval_at as s oR_has jR = v)) ∧
    (∀jR. jR < length (enumR as s kk) ⟶ Rval_at as s oR_no jR ≠ v) ∧
    (∀jR. jR < length (enumR as s kk) ⟶ 
      (∀w. w ∈ F ⟶ Rval_at as s oR_has jR ≠ w ∧ Rval_at as s oR_no jR ≠ w)) ∧
    (∀jR. jR < length (enumR as s kk) ⟶ Rval_at as s oR_no jR ∈ set (enumR as s kk))"
proof (cases "v ∈ set (enumR as s kk)")
  case True
(* v is in RHS - construct oracles that include/exclude it *)

(* Find a value in RHS that avoids v and all of F *)
  have "card (set (enumR as s kk)) > card (insert v F)"
  proof -
    have "card (insert v F) ≤ card F + 1"
      using forbidden(1) by (simp add: card_insert_if)
    thus ?thesis using slack by simp
  qed

  moreover have "insert v F ⊆ set (enumL as s kk)"
    using v_target forbidden(2) by auto

  moreover have "finite (insert v F)"
    using forbidden(1) by simp

  ultimately obtain r_avoid where 
    r_avoid_in: "r_avoid ∈ set (enumR as s kk)" and
    r_avoid_out: "r_avoid ∉ insert v F"
    using exists_rhs_avoiding_finite_forbidden_set by blast

  have r_avoid_neq_v: "r_avoid ≠ v" using r_avoid_out by simp
  have r_avoid_not_F: "r_avoid ∉ F" using r_avoid_out by simp

(* Strategy: Set all R-blocks to v for oR_has, all to r_avoid for oR_no *)
  (* Define oR_has: puts v in all R-blocks *)
  define oR_has where "oR_has = (λi.
    if ∃jR < length (enumR as s kk). 
       i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}
    then
      let jR = (SOME jR. jR < length (enumR as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s});
          offset = i - (length (enc0 as s) + offR as s kk jR)
      in to_bits (W as s) v ! offset
    else
      (enc as s kk) ! i)"
  
  (* Define oR_no: puts r_avoid in all R-blocks *)
  define oR_no where "oR_no = (λi.
    if ∃jR < length (enumR as s kk). 
       i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}
    then
      let jR = (SOME jR. jR < length (enumR as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s});
          offset = i - (length (enc0 as s) + offR as s kk jR)
      in to_bits (W as s) r_avoid ! offset
    else
      (enc as s kk) ! i)"
  
  (* Part 1: oR_has agrees on read positions *)
  have oR_has_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_has i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oR_has i = (enc as s kk) ! i"
    proof (cases "∃jR < length (enumR as s kk). 
                 i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}")
      case True
      then obtain jR where jR_prop: 
        "jR < length (enumR as s kk)"
        "i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}"
        by blast
      
      have "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
        using unread_R jR_prop(1) by blast
      
      moreover have "i ∈ blockR_abs enc0 as s kk jR"
        unfolding blockR_abs_def using jR_prop(2) by simp
      
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oR_has_def by auto
    qed
  qed
  
  (* Part 2: oR_no agrees on read positions *)
  have oR_no_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_no i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oR_no i = (enc as s kk) ! i"
    proof (cases "∃jR < length (enumR as s kk). 
                 i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}")
      case True
      then obtain jR where jR_prop: 
        "jR < length (enumR as s kk)"
        "i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}"
        by blast
      have "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
        using unread_R jR_prop(1) by blast
      moreover have "i ∈ blockR_abs enc0 as s kk jR"
        unfolding blockR_abs_def using jR_prop(2) by simp
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oR_no_def by auto
    qed
  qed
  
  (* Part 3: oR_has contains v in some block *)
  have oR_has_contains_v: "v ∈ set (enumR as s kk) ⟶ 
        (∃jR. jR < length (enumR as s kk) ∧ Rval_at as s oR_has jR = v)"
  proof (intro impI)
    assume "v ∈ set (enumR as s kk)"
    have "∃jR. jR < length (enumR as s kk)"
      using ‹v ∈ set (enumR as s kk)› by (meson in_set_conv_nth)
    then obtain jR where jR_bound: "jR < length (enumR as s kk)" by blast
    
    have "Rval_at as s oR_has jR = v"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      
      have "map oR_has [base ..< base + W as s] = to_bits (W as s) v"
      proof (rule nth_equalityI)
        show "length (map oR_has [base ..< base + W as s]) = length (to_bits (W as s) v)"
        proof -
          have "v ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using ‹v ∈ set (enumR as s kk)› by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_has [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        
        have "map oR_has [base ..< base + W as s] ! i = oR_has (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) v ! i"
        proof -
          have in_range: "base + i ∈ {base ..< base + W as s}"
            using i_bound by simp
          
          have exists_jR: "∃jR' < length (enumR as s kk). 
                        base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                    length (enc0 as s) + offR as s kk jR' + W as s}"
            apply (rule exI[where x=jR])
            using jR_bound base_def i_bound by auto
          
          have "oR_has (base + i) = 
                (let jR' = (SOME jR'. jR' < length (enumR as s kk) ∧ 
                                     base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                                 length (enc0 as s) + offR as s kk jR' + W as s});
                     offset = base + i - (length (enc0 as s) + offR as s kk jR')
                 in to_bits (W as s) v ! offset)"
            unfolding oR_has_def using exists_jR by simp
          
          also have "... = to_bits (W as s) v ! i"
          proof -
  (* The SOME picks jR uniquely because blocks are disjoint *)
            have unique_block: "∀jR' < length (enumR as s kk). 
                      base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                  length (enc0 as s) + offR as s kk jR' + W as s}
                      ⟶ jR' = jR"
            proof (intro allI impI)
              fix jR' assume jR'_bound: "jR' < length (enumR as s kk)"
                and in_block': "base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                   length (enc0 as s) + offR as s kk jR' + W as s}"
              have in_block: "base + i ∈ blockR_abs enc0 as s kk jR"
                unfolding blockR_abs_def base_def using i_bound by simp
              have in_block'': "base + i ∈ blockR_abs enc0 as s kk jR'"
                unfolding blockR_abs_def using in_block' by simp
              show "jR' = jR"
              proof (cases "jR' = jR")
                case True thus ?thesis .
              next
                case False
                have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                  using blockR_abs_disjoint[OF False] by (simp add: Int_commute)
                moreover have "base + i ∈ blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR'"
                  using in_block in_block'' by simp
                ultimately show ?thesis by blast
              qed
            qed
  
            have picked_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
            proof (rule some_equality)
              show "jR < length (enumR as s kk) ∧ 
                    base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                     length (enc0 as s) + offR as s kk jR + W as s}"
                using jR_bound base_def i_bound by auto
            next
              fix jR' assume "jR' < length (enumR as s kk) ∧
                   base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                              length (enc0 as s) + offR as s kk jR' + W as s}"
              thus "jR' = jR" using unique_block by blast
            qed
  
            have offset_simp: "base + i - (length (enc0 as s) + offR as s kk jR) = i"
              by (simp add: base_def)
  
            show ?thesis
              unfolding oR_has_def Let_def
              using exists_jR picked_jR offset_simp by simp
          qed
          
          finally show ?thesis .
        qed
        finally show "map oR_has [base ..< base + W as s] ! i = to_bits (W as s) v ! i" .
      qed
      
      have "Rval_at as s oR_has jR = from_bits (map oR_has [base ..< base + W as s])"
        unfolding Rval_at_def base_def by simp
      also have "... = from_bits (to_bits (W as s) v)"
        using ‹map oR_has [base ..< base + W as s] = to_bits (W as s) v› by simp
      also have "... = v"
      proof -
        have "v ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using ‹v ∈ set (enumR as s kk)› by auto
        thus ?thesis using bits_roundtrip by blast
      qed
      finally show ?thesis .
    qed
    
    thus "∃jR. jR < length (enumR as s kk) ∧ Rval_at as s oR_has jR = v"
      using jR_bound by blast
  qed
  
  (* Part 4a: oR_no always produces r_avoid *)
  have oR_no_produces_r_avoid: "∀jR. jR < length (enumR as s kk) ⟶ 
                                      Rval_at as s oR_no jR = r_avoid"
  proof (intro allI impI)
    fix jR assume jR_bound: "jR < length (enumR as s kk)"
    
    have "Rval_at as s oR_no jR = r_avoid"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      have "map oR_no [base ..< base + W as s] = to_bits (W as s) r_avoid"
      proof (rule nth_equalityI)
        show "length (map oR_no [base ..< base + W as s]) = length (to_bits (W as s) r_avoid)"
        proof -
          have "r_avoid ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using r_avoid_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        
        have "map oR_no [base ..< base + W as s] ! i = oR_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) r_avoid ! i"
        proof -
          have "base + i ∈ {base ..< base + W as s}"
            using i_bound by simp
          moreover have "∃jR' < length (enumR as s kk). 
                        base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                    length (enc0 as s) + offR as s kk jR' + W as s}"
            apply (rule exI[where x=jR])
            using jR_bound base_def i_bound by auto
          ultimately show ?thesis
          proof -
            have unique_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                                base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                 length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
            proof (rule some_equality)
              show "jR < length (enumR as s kk) ∧ 
                      base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                      length (enc0 as s) + offR as s kk jR + W as s}"
                  using jR_bound base_def i_bound by auto
            next
              fix jR' assume jR'_prop: "jR' < length (enumR as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}"
              show "jR' = jR"
              proof (cases "jR' = jR")
                case True thus ?thesis .
              next
                case False
                have in_jR: "base + i ∈ blockR_abs enc0 as s kk jR"
                  unfolding blockR_abs_def base_def using i_bound by simp
                have in_jR': "base + i ∈ blockR_abs enc0 as s kk jR'"
                  unfolding blockR_abs_def using jR'_prop by simp
                have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                  using blockR_abs_disjoint[of jR jR' enc0 as s kk] False by (simp add: Int_commute)
                thus ?thesis using in_jR in_jR' by blast
              qed
            qed
            thus ?thesis
              unfolding oR_no_def Let_def
              by (smt (verit) add_strict_left_mono atLeastLessThan_iff base_def 
                  diff_add_inverse i_bound jR_bound le_add1)
          qed
        qed
        finally show "map oR_no [base ..< base + W as s] ! i = to_bits (W as s) r_avoid ! i" .
      qed
      
      hence "Rval_at as s oR_no jR = from_bits (to_bits (W as s) r_avoid)"
        unfolding Rval_at_def base_def by simp
      also have "... = r_avoid"
      proof -
        have "r_avoid ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using r_avoid_in by auto
        thus ?thesis using bits_roundtrip by blast
      qed
      finally show ?thesis .
    qed
    thus "Rval_at as s oR_no jR = r_avoid" .
  qed

  (* Part 4b: oR_no never contains v *)
  have oR_no_avoids_v: "∀jR. jR < length (enumR as s kk) ⟶ Rval_at as s oR_no jR ≠ v"
    using oR_no_produces_r_avoid r_avoid_neq_v by blast
  
  (* Part 5: Both oracles avoid F *)
  have both_avoid_F: "∀jR. jR < length (enumR as s kk) ⟶ 
        (∀w. w ∈ F ⟶ Rval_at as s oR_has jR ≠ w ∧ Rval_at as s oR_no jR ≠ w)"
  proof (intro allI impI)
    fix jR w
    assume jR_bound: "jR < length (enumR as s kk)" and w_in_F: "w ∈ F"
    
    (* oR_has contains v, and v ∉ F *)
    have "Rval_at as s oR_has jR = v"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      have "map oR_has [base ..< base + W as s] = to_bits (W as s) v"
      proof (rule nth_equalityI)
        show "length (map oR_has [base ..< base + W as s]) = length (to_bits (W as s) v)"
        proof -
          have "v ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using True by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_has [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oR_has [base ..< base + W as s] ! i = oR_has (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) v ! i"
        proof -
          have unique_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
          proof (rule some_equality)
            show "jR < length (enumR as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                     length (enc0 as s) + offR as s kk jR + W as s}"
              using jR_bound base_def i_bound by auto
          next
            fix jR' assume jR'_prop: "jR' < length (enumR as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}"
            show "jR' = jR"
            proof (cases "jR' = jR")
              case True thus ?thesis .
            next
              case False
              have in_jR: "base + i ∈ blockR_abs enc0 as s kk jR"
                unfolding blockR_abs_def base_def using i_bound by simp
              have in_jR': "base + i ∈ blockR_abs enc0 as s kk jR'"
                unfolding blockR_abs_def using jR'_prop by simp
              have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                using blockR_abs_disjoint[of jR jR' enc0 as s kk] False by (simp add: Int_commute)
              thus ?thesis using in_jR in_jR' by blast
            qed
          qed
          thus ?thesis
            unfolding oR_has_def Let_def
              by (smt (verit, ccfv_threshold) add_strict_left_mono atLeastLessThan_iff base_def 
                  diff_add_inverse i_bound jR_bound le_add1)
          qed
        finally show "map oR_has [base ..< base + W as s] ! i = to_bits (W as s) v ! i" .
      qed
      thus ?thesis
        unfolding Rval_at_def base_def
        using bits_roundtrip True by auto
    qed
    moreover have "v ∉ F"
      using v_not_forbidden by simp
    ultimately have "Rval_at as s oR_has jR ≠ w" using w_in_F by blast
    
    (* oR_no contains r_avoid, and r_avoid ∉ F *)
    have "Rval_at as s oR_no jR = r_avoid"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      have "map oR_no [base ..< base + W as s] = to_bits (W as s) r_avoid"
      proof (rule nth_equalityI)
        show "length (map oR_no [base ..< base + W as s]) = length (to_bits (W as s) r_avoid)"
        proof -
          have "r_avoid ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using r_avoid_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oR_no [base ..< base + W as s] ! i = oR_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) r_avoid ! i"
          proof -
            have unique_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                 length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
            proof (rule some_equality)
              show "jR < length (enumR as s kk) ∧ 
                    base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                      length (enc0 as s) + offR as s kk jR + W as s}"
                using jR_bound base_def i_bound by auto
            next
              fix jR' assume jR'_prop: "jR' < length (enumR as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}"
              show "jR' = jR"
              proof (cases "jR' = jR")
                case True thus ?thesis .
              next
                case False
                have in_jR: "base + i ∈ blockR_abs enc0 as s kk jR"
                  unfolding blockR_abs_def base_def using i_bound by simp
                have in_jR': "base + i ∈ blockR_abs enc0 as s kk jR'"
                  unfolding blockR_abs_def using jR'_prop by simp
                have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                  using blockR_abs_disjoint[of jR jR' enc0 as s kk] False by (simp add: Int_commute)
                thus ?thesis using in_jR in_jR' by blast
              qed
            qed
            thus ?thesis
              unfolding oR_no_def Let_def
              by (smt (verit) add_strict_left_mono atLeastLessThan_iff base_def 
                  diff_add_inverse i_bound jR_bound le_add1)
          qed
        finally show "map oR_no [base ..< base + W as s] ! i = to_bits (W as s) r_avoid ! i" .
      qed
      thus ?thesis
        unfolding Rval_at_def base_def
        using bits_roundtrip r_avoid_in by auto
    qed
    moreover have "r_avoid ∉ F" using r_avoid_not_F .
    ultimately have "Rval_at as s oR_no jR ≠ w" using w_in_F by blast
    
    show "Rval_at as s oR_has jR ≠ w ∧ Rval_at as s oR_no jR ≠ w"
      using ‹Rval_at as s oR_has jR ≠ w› ‹Rval_at as s oR_no jR ≠ w› by simp
  qed
  
  (* Part 6: oR_no produces only RHS values *)
  have oR_no_in_catalog: "∀jR. jR < length (enumR as s kk) ⟶ 
                                Rval_at as s oR_no jR ∈ set (enumR as s kk)"
  proof (intro allI impI)
    fix jR assume jR_bound: "jR < length (enumR as s kk)"
    have "Rval_at as s oR_no jR = r_avoid"
      using oR_no_produces_r_avoid jR_bound by blast
    thus "Rval_at as s oR_no jR ∈ set (enumR as s kk)"
      using r_avoid_in by simp
  qed
  
  (* Now show the thesis using the separate facts *)
  show ?thesis
    apply (rule exI[where x=oR_has])
    apply (rule exI[where x=oR_no])
    using oR_has_agrees oR_no_agrees oR_has_contains_v oR_no_avoids_v both_avoid_F oR_no_in_catalog
    by blast

next
  case False
  (* v is not in RHS - both oracles just need to avoid F *)
  
  (* We need two distinct values in RHS that avoid F *)
  have "card (set (enumR as s kk)) > card F + 1" using slack .
  
  (* So we can find at least 2 distinct values not in F *)
  have enough_slack: "card (set (enumR as s kk) - F) ≥ 2"
  proof -
  (* If |RHS| > |F| + 1, then |RHS - F| ≥ |RHS| - |F| > 1 *)
    have "finite (set (enumR as s kk))" by simp
    have "card (set (enumR as s kk) - F) ≥ card (set (enumR as s kk)) - card F"
    proof (cases "F ⊆ set (enumR as s kk)")
      case True
      then show ?thesis
        using forbidden(1) by (simp add: card_Diff_subset)
    next
      case False
    (* Some of F is outside RHS, so RHS - F loses even less *)
      have "F ∩ set (enumR as s kk) ⊂ F"
        using False forbidden(2) by blast
      hence "card (F ∩ set (enumR as s kk)) < card F"
        using forbidden(1) by (simp add: psubset_card_mono)
      thus ?thesis
        using forbidden(1) card_Diff_subset_Int le_diff_conv2
        by (simp add: diff_card_le_card_Diff)
    qed
    moreover have "card (set (enumR as s kk)) - card F > 1"
      using slack by simp
    ultimately show ?thesis by simp
  qed
  
(* Get two distinct values *)
  obtain r1 r2 where
    r1_in: "r1 ∈ set (enumR as s kk)" and r1_out: "r1 ∉ F" and
    r2_in: "r2 ∈ set (enumR as s kk)" and r2_out: "r2 ∉ F" and
    r_diff: "r1 ≠ r2"
  proof -
  (* RHS - F has at least 2 elements *)
    have "∃r1 r2. r1 ∈ set (enumR as s kk) - F ∧ r2 ∈ set (enumR as s kk) - F ∧ r1 ≠ r2"
    proof -
      have "finite (set (enumR as s kk) - F)" by simp
      moreover have "card (set (enumR as s kk) - F) ≥ 2" using enough_slack .
      ultimately obtain xs where "xs ⊆ set (enumR as s kk) - F" and "card xs = 2"
        by (meson card_ge_0_finite obtain_subset_with_card_n)
      then obtain r1 r2 where "xs = {r1, r2}" and "r1 ≠ r2"
        by (auto simp: card_2_iff)
      thus ?thesis using ‹xs ⊆ set (enumR as s kk) - F› by blast
    qed
    then obtain r1 r2 where "r1 ∈ set (enumR as s kk) - F" "r2 ∈ set (enumR as s kk) - F" "r1 ≠ r2"
      by blast
    thus ?thesis using that by blast
  qed
  
  (* Both exclude v automatically since v ∉ RHS *)
  have r1_neq_v: "r1 ≠ v" using False r1_in by blast
  have r2_neq_v: "r2 ≠ v" using False r2_in by blast
  
  (* Define oR_has: puts r1 in all R-blocks *)
  define oR_has where "oR_has = (λi.
    if ∃jR < length (enumR as s kk). 
       i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}
    then
      let jR = (SOME jR. jR < length (enumR as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s});
          offset = i - (length (enc0 as s) + offR as s kk jR)
      in to_bits (W as s) r1 ! offset
    else
      (enc as s kk) ! i)"
  
  (* Define oR_no: puts r2 in all R-blocks *)
  define oR_no where "oR_no = (λi.
    if ∃jR < length (enumR as s kk). 
       i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}
    then
      let jR = (SOME jR. jR < length (enumR as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s});
          offset = i - (length (enc0 as s) + offR as s kk jR)
      in to_bits (W as s) r2 ! offset
    else
      (enc as s kk) ! i)"
  
  (* Part 1: oR_has agrees on read positions *)
  have oR_has_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_has i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oR_has i = (enc as s kk) ! i"
    proof (cases "∃jR < length (enumR as s kk). 
                 i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}")
      case True
      then obtain jR where jR_prop: 
        "jR < length (enumR as s kk)"
        "i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}"
        by blast
      have "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
        using unread_R jR_prop(1) by blast
      moreover have "i ∈ blockR_abs enc0 as s kk jR"
        unfolding blockR_abs_def using jR_prop(2) by simp
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oR_has_def by auto
    qed
  qed
  
  (* Part 2: oR_no agrees on read positions *)
  have oR_no_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_no i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oR_no i = (enc as s kk) ! i"
    proof (cases "∃jR < length (enumR as s kk). 
                 i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}")
      case True
      then obtain jR where jR_prop: 
        "jR < length (enumR as s kk)"
        "i ∈ {length (enc0 as s) + offR as s kk jR ..< length (enc0 as s) + offR as s kk jR + W as s}"
        by blast
      have "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
        using unread_R jR_prop(1) by blast
      moreover have "i ∈ blockR_abs enc0 as s kk jR"
        unfolding blockR_abs_def using jR_prop(2) by simp
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oR_no_def by auto
    qed
  qed
  
  (* Part 3: v ∈ RHS ⟹ exists block - vacuously true since v ∉ RHS *)
  have oR_has_has_v: "v ∈ set (enumR as s kk) ⟶ 
        (∃jR. jR < length (enumR as s kk) ∧ Rval_at as s oR_has jR = v)"
    using False by simp
  
  (* Part 4a: oR_no always produces r2 *)
  have oR_no_produces_r2: "∀jR. jR < length (enumR as s kk) ⟶ 
                                  Rval_at as s oR_no jR = r2"
  proof (intro allI impI)
    fix jR assume jR_bound: "jR < length (enumR as s kk)"
    
    have "Rval_at as s oR_no jR = r2"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      have "map oR_no [base ..< base + W as s] = to_bits (W as s) r2"
      proof (rule nth_equalityI)
        show "length (map oR_no [base ..< base + W as s]) = length (to_bits (W as s) r2)"
        proof -
          have "r2 ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using r2_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oR_no [base ..< base + W as s] ! i = oR_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) r2 ! i"
        proof -
          have unique_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
          proof (rule some_equality)
            show "jR < length (enumR as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                     length (enc0 as s) + offR as s kk jR + W as s}"
              using jR_bound base_def i_bound by auto
          next
            fix jR' assume jR'_prop: "jR' < length (enumR as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}"
            show "jR' = jR"
            proof (cases "jR' = jR")
              case True thus ?thesis .
            next
              case False
              have in_jR: "base + i ∈ blockR_abs enc0 as s kk jR"
                unfolding blockR_abs_def base_def using i_bound by simp
              have in_jR': "base + i ∈ blockR_abs enc0 as s kk jR'"
                unfolding blockR_abs_def using jR'_prop by simp
              have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                using blockR_abs_disjoint[of jR jR' enc0 as s kk] False by (simp add: Int_commute)
              thus ?thesis using in_jR in_jR' by blast
            qed
          qed
          thus ?thesis
            unfolding oR_no_def Let_def
            by (smt (z3) ‹i < length (map oR_no [base..<base + W as s])› 
                add.commute add_diff_cancel_left' atLeastLessThan_upt base_def 
                i_bound jR_bound le_diff_conv length_map nat_less_le nth_mem nth_upt)
        qed
        finally show "map oR_no [base ..< base + W as s] ! i = to_bits (W as s) r2 ! i" .
      qed
      thus ?thesis
        unfolding Rval_at_def base_def
        using bits_roundtrip r2_in by auto
    qed
    thus "Rval_at as s oR_no jR = r2" .
  qed
  
  (* Part 4b: oR_no never contains v *)
  have oR_no_avoids_v: "∀jR. jR < length (enumR as s kk) ⟶ Rval_at as s oR_no jR ≠ v"
    using oR_no_produces_r2 r2_neq_v by blast
  
  (* Part 5: Both avoid F - r1 and r2 both not in F *)
  have both_avoid_F: "∀jR. jR < length (enumR as s kk) ⟶ 
        (∀w. w ∈ F ⟶ Rval_at as s oR_has jR ≠ w ∧ Rval_at as s oR_no jR ≠ w)"
  proof (intro allI impI)
    fix jR w
    assume jR_bound: "jR < length (enumR as s kk)" and w_in_F: "w ∈ F"
    
    have "Rval_at as s oR_has jR = r1"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      have "map oR_has [base ..< base + W as s] = to_bits (W as s) r1"
      proof (rule nth_equalityI)
        show "length (map oR_has [base ..< base + W as s]) = length (to_bits (W as s) r1)"
        proof -
          have "r1 ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using r1_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_has [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oR_has [base ..< base + W as s] ! i = oR_has (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) r1 ! i"
        proof -
          have unique_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
          proof (rule some_equality)
            show "jR < length (enumR as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                     length (enc0 as s) + offR as s kk jR + W as s}"
              using jR_bound base_def i_bound by auto
          next
            fix jR' assume jR'_prop: "jR' < length (enumR as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}"
            show "jR' = jR"
            proof (cases "jR' = jR")
              case True thus ?thesis .
            next
              case False
              have in_jR: "base + i ∈ blockR_abs enc0 as s kk jR"
                unfolding blockR_abs_def base_def using i_bound by simp
              have in_jR': "base + i ∈ blockR_abs enc0 as s kk jR'"
                unfolding blockR_abs_def using jR'_prop by simp
              have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                using blockR_abs_disjoint[of jR jR' enc0 as s kk] False by (simp add: Int_commute)
              thus ?thesis using in_jR in_jR' by blast
            qed
          qed
          thus ?thesis
            unfolding oR_has_def Let_def
            by (smt (verit) ‹i < length (map oR_has [base..<base + W as s])› 
                add.commute add_diff_cancel_left' atLeastLessThan_upt base_def 
                i_bound jR_bound le_diff_conv length_map nat_less_le nat_neq_iff 
                nth_mem nth_upt)
        qed
        finally show "map oR_has [base ..< base + W as s] ! i = to_bits (W as s) r1 ! i" .
      qed
      thus ?thesis
        unfolding Rval_at_def base_def
        using bits_roundtrip r1_in by auto
    qed
    hence "Rval_at as s oR_has jR ≠ w" using r1_out w_in_F by blast
    
    have "Rval_at as s oR_no jR = r2"
    proof -
      define base where "base = length (enc0 as s) + offR as s kk jR"
      have "map oR_no [base ..< base + W as s] = to_bits (W as s) r2"
      proof (rule nth_equalityI)
        show "length (map oR_no [base ..< base + W as s]) = length (to_bits (W as s) r2)"
        proof -
          have "r2 ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using r2_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oR_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oR_no [base ..< base + W as s] ! i = oR_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) r2 ! i"
        proof -
          have exists_jR: "∃jR' < length (enumR as s kk). 
                base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                            length (enc0 as s) + offR as s kk jR' + W as s}"
            apply (rule exI[where x=jR])
            using jR_bound base_def i_bound by auto
  
          have unique_jR: "(SOME jR'. jR' < length (enumR as s kk) ∧ 
                      base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                 length (enc0 as s) + offR as s kk jR' + W as s}) = jR"
          proof (rule some_equality)
            show "jR < length (enumR as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offR as s kk jR ..< 
                      length (enc0 as s) + offR as s kk jR + W as s}"
              using jR_bound base_def i_bound by auto
          next
            fix jR' assume jR'_prop: "jR' < length (enumR as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offR as s kk jR' ..< 
                                         length (enc0 as s) + offR as s kk jR' + W as s}"
            show "jR' = jR"
            proof (cases "jR' = jR")
              case True thus ?thesis .
            next
              case False
              have in_jR: "base + i ∈ blockR_abs enc0 as s kk jR"
                unfolding blockR_abs_def base_def using i_bound by simp
              have in_jR': "base + i ∈ blockR_abs enc0 as s kk jR'"
                unfolding blockR_abs_def using jR'_prop by simp
              have "blockR_abs enc0 as s kk jR ∩ blockR_abs enc0 as s kk jR' = {}"
                using blockR_abs_disjoint[of jR jR' enc0 as s kk] False by (simp add: Int_commute)
              thus ?thesis using in_jR in_jR' by blast
            qed
          qed
  
          have offset_eq: "base + i - (length (enc0 as s) + offR as s kk jR) = i"
            by (simp add: base_def)
  
          show ?thesis
            unfolding oR_no_def Let_def
            using exists_jR unique_jR offset_eq by simp
        qed
        finally show "map oR_no [base ..< base + W as s] ! i = to_bits (W as s) r2 ! i" .
      qed
      thus ?thesis
        unfolding Rval_at_def base_def
        using bits_roundtrip r2_in by auto
    qed
    hence "Rval_at as s oR_no jR ≠ w" using r2_out w_in_F by blast
    
    show "Rval_at as s oR_has jR ≠ w ∧ Rval_at as s oR_no jR ≠ w"
      using ‹Rval_at as s oR_has jR ≠ w› ‹Rval_at as s oR_no jR ≠ w› by simp
  qed
  
  (* Part 6: oR_no produces only RHS values *)
  have oR_no_in_catalog: "∀jR. jR < length (enumR as s kk) ⟶ 
                                Rval_at as s oR_no jR ∈ set (enumR as s kk)"
  proof (intro allI impI)
    fix jR assume jR_bound: "jR < length (enumR as s kk)"
    have "Rval_at as s oR_no jR = r2"
      using oR_no_produces_r2 jR_bound by blast
    thus "Rval_at as s oR_no jR ∈ set (enumR as s kk)"
      using r2_in by simp
  qed
  
  (* Now show the thesis using the separate facts *)
  show ?thesis
    apply (rule exI[where x=oR_has])
    apply (rule exI[where x=oR_no])
    using oR_has_agrees oR_no_agrees oR_has_has_v oR_no_avoids_v both_avoid_F oR_no_in_catalog
    by blast
qed

(* Symmetric: Construct L-oracle avoiding forbidden R-values *)
lemma construct_avoiding_L_oracle:
  assumes unread_L: "∀jL < length (enumL as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
      and v_target: "v ∈ set (enumR as s kk)"
      and v_not_forbidden: "v ∉ F"
      and forbidden: "finite F" "F ⊆ set (enumR as s kk)"
      and slack: "card (set (enumL as s kk)) > card F + 1"
  shows "∃oL_has oL_no.
    (∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_has i = (enc as s kk) ! i) ∧
    (∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_no i = (enc as s kk) ! i) ∧
    (v ∈ set (enumL as s kk) ⟶ 
      (∃jL. jL < length (enumL as s kk) ∧ Lval_at as s oL_has jL = v)) ∧
    (∀jL. jL < length (enumL as s kk) ⟶ Lval_at as s oL_no jL ≠ v) ∧
    (∀jL. jL < length (enumL as s kk) ⟶ 
      (∀w. w ∈ F ⟶ Lval_at as s oL_has jL ≠ w ∧ Lval_at as s oL_no jL ≠ w)) ∧
    (∀jL. jL < length (enumL as s kk) ⟶ Lval_at as s oL_no jL ∈ set (enumL as s kk))"
proof (cases "v ∈ set (enumL as s kk)")
  case True
  (* v is in LHS - construct oracles that include/exclude it *)
  
  have "card (set (enumL as s kk)) > card (insert v F)"
  proof -
    have "card (insert v F) ≤ card F + 1"
      using forbidden(1) by (simp add: card_insert_if)
    thus ?thesis using slack by simp
  qed

  moreover have "insert v F ⊆ set (enumR as s kk)"
    using v_target forbidden(2) by auto

  moreover have "finite (insert v F)"
    using forbidden(1) by simp

  ultimately obtain l_avoid where 
    l_avoid_in: "l_avoid ∈ set (enumL as s kk)" and
    l_avoid_out: "l_avoid ∉ insert v F"
    using exists_lhs_avoiding_finite_forbidden_set by blast

  have l_avoid_neq_v: "l_avoid ≠ v" using l_avoid_out by simp
  have l_avoid_not_F: "l_avoid ∉ F" using l_avoid_out by simp

  define oL_has where "oL_has = (λi.
    if ∃jL < length (enumL as s kk). 
       i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}
    then
      let jL = (SOME jL. jL < length (enumL as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s});
          offset = i - (length (enc0 as s) + offL as s jL)
      in to_bits (W as s) v ! offset
    else
      (enc as s kk) ! i)"
  
  define oL_no where "oL_no = (λi.
    if ∃jL < length (enumL as s kk). 
       i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}
    then
      let jL = (SOME jL. jL < length (enumL as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s});
          offset = i - (length (enc0 as s) + offL as s jL)
      in to_bits (W as s) l_avoid ! offset
    else
      (enc as s kk) ! i)"
  
  have oL_has_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_has i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oL_has i = (enc as s kk) ! i"
    proof (cases "∃jL < length (enumL as s kk). 
                 i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}")
      case True
      then obtain jL where jL_prop: 
        "jL < length (enumL as s kk)"
        "i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}"
        by blast
      
      have "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
        using unread_L jL_prop(1) by blast
      
      moreover have "i ∈ blockL_abs enc0 as s jL"
        unfolding blockL_abs_def using jL_prop(2) by simp
      
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oL_has_def by auto
    qed
  qed
  
  have oL_no_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_no i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oL_no i = (enc as s kk) ! i"
    proof (cases "∃jL < length (enumL as s kk). 
                 i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}")
      case True
      then obtain jL where jL_prop: 
        "jL < length (enumL as s kk)"
        "i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}"
        by blast
      have "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
        using unread_L jL_prop(1) by blast
      moreover have "i ∈ blockL_abs enc0 as s jL"
        unfolding blockL_abs_def using jL_prop(2) by simp
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oL_no_def by auto
    qed
  qed
  
  have oL_has_contains_v: "v ∈ set (enumL as s kk) ⟶ 
        (∃jL. jL < length (enumL as s kk) ∧ Lval_at as s oL_has jL = v)"
  proof (intro impI)
    assume "v ∈ set (enumL as s kk)"
    have "∃jL. jL < length (enumL as s kk)"
      using ‹v ∈ set (enumL as s kk)› by (meson in_set_conv_nth)
    then obtain jL where jL_bound: "jL < length (enumL as s kk)" by blast
    
    have "Lval_at as s oL_has jL = v"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      
      have "map oL_has [base ..< base + W as s] = to_bits (W as s) v"
      proof (rule nth_equalityI)
        show "length (map oL_has [base ..< base + W as s]) = length (to_bits (W as s) v)"
        proof -
          have "v ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using ‹v ∈ set (enumL as s kk)› by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_has [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        
        have "map oL_has [base ..< base + W as s] ! i = oL_has (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) v ! i"
        proof -
          have in_range: "base + i ∈ {base ..< base + W as s}"
            using i_bound by simp
          
          have exists_jL: "∃jL' < length (enumL as s kk). 
                        base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                    length (enc0 as s) + offL as s jL' + W as s}"
            apply (rule exI[where x=jL])
            using jL_bound base_def i_bound by auto
          
          have "oL_has (base + i) = 
                (let jL' = (SOME jL'. jL' < length (enumL as s kk) ∧ 
                                     base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                                 length (enc0 as s) + offL as s jL' + W as s});
                     offset = base + i - (length (enc0 as s) + offL as s jL')
                 in to_bits (W as s) v ! offset)"
            unfolding oL_has_def using exists_jL by simp
          
          also have "... = to_bits (W as s) v ! i"
          proof -
            have unique_block: "∀jL' < length (enumL as s kk). 
                      base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                  length (enc0 as s) + offL as s jL' + W as s}
                      ⟶ jL' = jL"
            proof (intro allI impI)
              fix jL' assume jL'_bound: "jL' < length (enumL as s kk)"
                and in_block': "base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                   length (enc0 as s) + offL as s jL' + W as s}"
              have in_block: "base + i ∈ blockL_abs enc0 as s jL"
                unfolding blockL_abs_def base_def using i_bound by simp
              have in_block'': "base + i ∈ blockL_abs enc0 as s jL'"
                unfolding blockL_abs_def using in_block' by simp
              show "jL' = jL"
              proof (cases "jL' = jL")
                case True thus ?thesis .
              next
                case False
                have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                  using blockL_abs_disjoint[OF False] by (simp add: Int_commute)
                moreover have "base + i ∈ blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL'"
                  using in_block in_block'' by simp
                ultimately show ?thesis by blast
              qed
            qed
  
            have picked_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}) = jL"
            proof (rule some_equality)
              show "jL < length (enumL as s kk) ∧ 
                    base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                     length (enc0 as s) + offL as s jL + W as s}"
                using jL_bound base_def i_bound by auto
            next
              fix jL' assume "jL' < length (enumL as s kk) ∧
                   base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                              length (enc0 as s) + offL as s jL' + W as s}"
              thus "jL' = jL" using unique_block by blast
            qed
  
            have offset_simp: "base + i - (length (enc0 as s) + offL as s jL) = i"
              by (simp add: base_def)
  
            show ?thesis
              unfolding oL_has_def Let_def
              using exists_jL picked_jL offset_simp by simp
          qed
          
          finally show ?thesis .
        qed
        finally show "map oL_has [base ..< base + W as s] ! i = to_bits (W as s) v ! i" .
      qed
      
      have "Lval_at as s oL_has jL = from_bits (map oL_has [base ..< base + W as s])"
        unfolding Lval_at_def base_def by simp
      also have "... = from_bits (to_bits (W as s) v)"
        using ‹map oL_has [base ..< base + W as s] = to_bits (W as s) v› by simp
      also have "... = v"
      proof -
        have "v ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using ‹v ∈ set (enumL as s kk)› by auto
        thus ?thesis using bits_roundtrip by blast
      qed
      finally show ?thesis .
    qed
    
    thus "∃jL. jL < length (enumL as s kk) ∧ Lval_at as s oL_has jL = v"
      using jL_bound by blast
  qed
  
  have oL_no_produces_l_avoid: "∀jL. jL < length (enumL as s kk) ⟶ 
                                      Lval_at as s oL_no jL = l_avoid"
  proof (intro allI impI)
    fix jL assume jL_bound: "jL < length (enumL as s kk)"
    
    have "Lval_at as s oL_no jL = l_avoid"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      have "map oL_no [base ..< base + W as s] = to_bits (W as s) l_avoid"
      proof (rule nth_equalityI)
        show "length (map oL_no [base ..< base + W as s]) = length (to_bits (W as s) l_avoid)"
        proof -
          have "l_avoid ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using l_avoid_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        
        have "map oL_no [base ..< base + W as s] ! i = oL_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) l_avoid ! i"
        proof -
          have "base + i ∈ {base ..< base + W as s}"
            using i_bound by simp
          moreover have "∃jL' < length (enumL as s kk). 
                        base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                    length (enc0 as s) + offL as s jL' + W as s}"
            apply (rule exI[where x=jL])
            using jL_bound base_def i_bound by auto
          ultimately show ?thesis
          proof -
            have unique_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                                base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                 length (enc0 as s) + offL as s jL' + W as s}) = jL"
            proof (rule some_equality)
              show "jL < length (enumL as s kk) ∧ 
                      base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                      length (enc0 as s) + offL as s jL + W as s}"
                  using jL_bound base_def i_bound by auto
            next
              fix jL' assume jL'_prop: "jL' < length (enumL as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}"
              show "jL' = jL"
              proof (cases "jL' = jL")
                case True thus ?thesis .
              next
                case False
                have in_jL: "base + i ∈ blockL_abs enc0 as s jL"
                  unfolding blockL_abs_def base_def using i_bound by simp
                have in_jL': "base + i ∈ blockL_abs enc0 as s jL'"
                  unfolding blockL_abs_def using jL'_prop by simp
                have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                  using blockL_abs_disjoint[of jL jL' enc0 as s] False by (simp add: Int_commute)
                thus ?thesis using in_jL in_jL' by blast
              qed
            qed
            thus ?thesis
              unfolding oL_no_def Let_def
              by (smt (verit) add_strict_left_mono atLeastLessThan_iff base_def 
                  diff_add_inverse i_bound jL_bound le_add1)
          qed
        qed
        finally show "map oL_no [base ..< base + W as s] ! i = to_bits (W as s) l_avoid ! i" .
      qed
      
      hence "Lval_at as s oL_no jL = from_bits (to_bits (W as s) l_avoid)"
        unfolding Lval_at_def base_def by simp
      also have "... = l_avoid"
      proof -
        have "l_avoid ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using l_avoid_in by auto
        thus ?thesis using bits_roundtrip by blast
      qed
      finally show ?thesis .
    qed
    thus "Lval_at as s oL_no jL = l_avoid" .
  qed

  have oL_no_avoids_v: "∀jL. jL < length (enumL as s kk) ⟶ Lval_at as s oL_no jL ≠ v"
    using oL_no_produces_l_avoid l_avoid_neq_v by blast
  
  have both_avoid_F: "∀jL. jL < length (enumL as s kk) ⟶ 
        (∀w. w ∈ F ⟶ Lval_at as s oL_has jL ≠ w ∧ Lval_at as s oL_no jL ≠ w)"
  proof (intro allI impI)
    fix jL w
    assume jL_bound: "jL < length (enumL as s kk)" and w_in_F: "w ∈ F"
    
    have "Lval_at as s oL_has jL = v"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      have "map oL_has [base ..< base + W as s] = to_bits (W as s) v"
      proof (rule nth_equalityI)
        show "length (map oL_has [base ..< base + W as s]) = length (to_bits (W as s) v)"
        proof -
          have "v ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using True by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_has [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oL_has [base ..< base + W as s] ! i = oL_has (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) v ! i"
        proof -
          have unique_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}) = jL"
          proof (rule some_equality)
            show "jL < length (enumL as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                     length (enc0 as s) + offL as s jL + W as s}"
              using jL_bound base_def i_bound by auto
          next
            fix jL' assume jL'_prop: "jL' < length (enumL as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}"
            show "jL' = jL"
            proof (cases "jL' = jL")
              case True thus ?thesis .
            next
              case False
              have in_jL: "base + i ∈ blockL_abs enc0 as s jL"
                unfolding blockL_abs_def base_def using i_bound by simp
              have in_jL': "base + i ∈ blockL_abs enc0 as s jL'"
                unfolding blockL_abs_def using jL'_prop by simp
              have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                using blockL_abs_disjoint[of jL jL' enc0 as s] False by (simp add: Int_commute)
              thus ?thesis using in_jL in_jL' by blast
            qed
          qed
          thus ?thesis
            unfolding oL_has_def Let_def
              by (smt (verit, ccfv_threshold) add_strict_left_mono atLeastLessThan_iff base_def 
                  diff_add_inverse i_bound jL_bound le_add1)
          qed
        finally show "map oL_has [base ..< base + W as s] ! i = to_bits (W as s) v ! i" .
      qed
      thus ?thesis
        unfolding Lval_at_def base_def
        using bits_roundtrip True by auto
    qed
    moreover have "v ∉ F"
      using v_not_forbidden by simp
    ultimately have "Lval_at as s oL_has jL ≠ w" using w_in_F by blast
    
    have "Lval_at as s oL_no jL = l_avoid"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      have "map oL_no [base ..< base + W as s] = to_bits (W as s) l_avoid"
      proof (rule nth_equalityI)
        show "length (map oL_no [base ..< base + W as s]) = length (to_bits (W as s) l_avoid)"
        proof -
          have "l_avoid ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using l_avoid_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oL_no [base ..< base + W as s] ! i = oL_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) l_avoid ! i"
          proof -
            have unique_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                 length (enc0 as s) + offL as s jL' + W as s}) = jL"
            proof (rule some_equality)
              show "jL < length (enumL as s kk) ∧ 
                    base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                      length (enc0 as s) + offL as s jL + W as s}"
                using jL_bound base_def i_bound by auto
            next
              fix jL' assume jL'_prop: "jL' < length (enumL as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}"
              show "jL' = jL"
              proof (cases "jL' = jL")
                case True thus ?thesis .
              next
                case False
                have in_jL: "base + i ∈ blockL_abs enc0 as s jL"
                  unfolding blockL_abs_def base_def using i_bound by simp
                have in_jL': "base + i ∈ blockL_abs enc0 as s jL'"
                  unfolding blockL_abs_def using jL'_prop by simp
                have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                  using blockL_abs_disjoint[of jL jL' enc0 as s] False by (simp add: Int_commute)
                thus ?thesis using in_jL in_jL' by blast
              qed
            qed
            thus ?thesis
              unfolding oL_no_def Let_def
              by (smt (verit) add_strict_left_mono atLeastLessThan_iff base_def 
                  diff_add_inverse i_bound jL_bound le_add1)
          qed
        finally show "map oL_no [base ..< base + W as s] ! i = to_bits (W as s) l_avoid ! i" .
      qed
      thus ?thesis
        unfolding Lval_at_def base_def
        using bits_roundtrip l_avoid_in by auto
    qed
    moreover have "l_avoid ∉ F" using l_avoid_not_F .
    ultimately have "Lval_at as s oL_no jL ≠ w" using w_in_F by blast
    
    show "Lval_at as s oL_has jL ≠ w ∧ Lval_at as s oL_no jL ≠ w"
      using ‹Lval_at as s oL_has jL ≠ w› ‹Lval_at as s oL_no jL ≠ w› by simp
  qed
  
  have oL_no_in_catalog: "∀jL. jL < length (enumL as s kk) ⟶ 
                                Lval_at as s oL_no jL ∈ set (enumL as s kk)"
  proof (intro allI impI)
    fix jL assume jL_bound: "jL < length (enumL as s kk)"
    have "Lval_at as s oL_no jL = l_avoid"
      using oL_no_produces_l_avoid jL_bound by blast
    thus "Lval_at as s oL_no jL ∈ set (enumL as s kk)"
      using l_avoid_in by simp
  qed
  
  show ?thesis
    apply (rule exI[where x=oL_has])
    apply (rule exI[where x=oL_no])
    using oL_has_agrees oL_no_agrees oL_has_contains_v oL_no_avoids_v both_avoid_F oL_no_in_catalog
    by blast

next
  case False
  
  have "card (set (enumL as s kk)) > card F + 1" using slack .
  
  have enough_slack: "card (set (enumL as s kk) - F) ≥ 2"
  proof -
    have "finite (set (enumL as s kk))" by simp
    have "card (set (enumL as s kk) - F) ≥ card (set (enumL as s kk)) - card F"
    proof (cases "F ⊆ set (enumL as s kk)")
      case True
      then show ?thesis
        using forbidden(1) by (simp add: card_Diff_subset)
    next
      case False
      have "F ∩ set (enumL as s kk) ⊂ F"
        using False forbidden(2) by blast
      hence "card (F ∩ set (enumL as s kk)) < card F"
        using forbidden(1) by (simp add: psubset_card_mono)
      thus ?thesis
        using forbidden(1) card_Diff_subset_Int le_diff_conv2
        by (simp add: diff_card_le_card_Diff)
    qed
    moreover have "card (set (enumL as s kk)) - card F > 1"
      using slack by simp
    ultimately show ?thesis by simp
  qed
  
  obtain l1 l2 where
    l1_in: "l1 ∈ set (enumL as s kk)" and l1_out: "l1 ∉ F" and
    l2_in: "l2 ∈ set (enumL as s kk)" and l2_out: "l2 ∉ F" and
    l_diff: "l1 ≠ l2"
  proof -
    have "∃l1 l2. l1 ∈ set (enumL as s kk) - F ∧ l2 ∈ set (enumL as s kk) - F ∧ l1 ≠ l2"
    proof -
      have "finite (set (enumL as s kk) - F)" by simp
      moreover have "card (set (enumL as s kk) - F) ≥ 2" using enough_slack .
      ultimately obtain xs where "xs ⊆ set (enumL as s kk) - F" and "card xs = 2"
        by (meson card_ge_0_finite obtain_subset_with_card_n)
      then obtain l1 l2 where "xs = {l1, l2}" and "l1 ≠ l2"
        by (auto simp: card_2_iff)
      thus ?thesis using ‹xs ⊆ set (enumL as s kk) - F› by blast
    qed
    then obtain l1 l2 where "l1 ∈ set (enumL as s kk) - F" "l2 ∈ set (enumL as s kk) - F" "l1 ≠ l2"
      by blast
    thus ?thesis using that by blast
  qed
  
  have l1_neq_v: "l1 ≠ v" using False l1_in by blast
  have l2_neq_v: "l2 ≠ v" using False l2_in by blast
  
  define oL_has where "oL_has = (λi.
    if ∃jL < length (enumL as s kk). 
       i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}
    then
      let jL = (SOME jL. jL < length (enumL as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s});
          offset = i - (length (enc0 as s) + offL as s jL)
      in to_bits (W as s) l1 ! offset
    else
      (enc as s kk) ! i)"
  
  define oL_no where "oL_no = (λi.
    if ∃jL < length (enumL as s kk). 
       i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}
    then
      let jL = (SOME jL. jL < length (enumL as s kk) ∧ 
                        i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s});
          offset = i - (length (enc0 as s) + offL as s jL)
      in to_bits (W as s) l2 ! offset
    else
      (enc as s kk) ! i)"
  
  have oL_has_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_has i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oL_has i = (enc as s kk) ! i"
    proof (cases "∃jL < length (enumL as s kk). 
                 i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}")
      case True
      then obtain jL where jL_prop: 
        "jL < length (enumL as s kk)"
        "i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}"
        by blast
      have "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
        using unread_L jL_prop(1) by blast
      moreover have "i ∈ blockL_abs enc0 as s jL"
        unfolding blockL_abs_def using jL_prop(2) by simp
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oL_has_def by auto
    qed
  qed
  
  have oL_no_agrees: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_no i = (enc as s kk) ! i"
  proof (intro allI impI)
    fix i assume i_read: "i ∈ Base.read0 M (enc as s kk)"
    show "oL_no i = (enc as s kk) ! i"
    proof (cases "∃jL < length (enumL as s kk). 
                 i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}")
      case True
      then obtain jL where jL_prop: 
        "jL < length (enumL as s kk)"
        "i ∈ {length (enc0 as s) + offL as s jL ..< length (enc0 as s) + offL as s jL + W as s}"
        by blast
      have "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
        using unread_L jL_prop(1) by blast
      moreover have "i ∈ blockL_abs enc0 as s jL"
        unfolding blockL_abs_def using jL_prop(2) by simp
      ultimately have "i ∉ Base.read0 M (enc as s kk)" by blast
      thus ?thesis using i_read by simp
    next
      case False
      then show ?thesis unfolding oL_no_def by auto
    qed
  qed
  
  have oL_has_has_v: "v ∈ set (enumL as s kk) ⟶ 
        (∃jL. jL < length (enumL as s kk) ∧ Lval_at as s oL_has jL = v)"
    using False by simp
  
  have oL_no_produces_l2: "∀jL. jL < length (enumL as s kk) ⟶ 
                                  Lval_at as s oL_no jL = l2"
  proof (intro allI impI)
    fix jL assume jL_bound: "jL < length (enumL as s kk)"
    
    have "Lval_at as s oL_no jL = l2"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      have "map oL_no [base ..< base + W as s] = to_bits (W as s) l2"
      proof (rule nth_equalityI)
        show "length (map oL_no [base ..< base + W as s]) = length (to_bits (W as s) l2)"
        proof -
          have "l2 ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using l2_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oL_no [base ..< base + W as s] ! i = oL_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) l2 ! i"
        proof -
          have unique_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}) = jL"
          proof (rule some_equality)
            show "jL < length (enumL as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                     length (enc0 as s) + offL as s jL + W as s}"
              using jL_bound base_def i_bound by auto
          next
            fix jL' assume jL'_prop: "jL' < length (enumL as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}"
            show "jL' = jL"
            proof (cases "jL' = jL")
              case True thus ?thesis .
            next
              case False
              have in_jL: "base + i ∈ blockL_abs enc0 as s jL"
                unfolding blockL_abs_def base_def using i_bound by simp
              have in_jL': "base + i ∈ blockL_abs enc0 as s jL'"
                unfolding blockL_abs_def using jL'_prop by simp
              have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                using blockL_abs_disjoint[of jL jL' enc0 as s] False by (simp add: Int_commute)
              thus ?thesis using in_jL in_jL' by blast
            qed
          qed
          thus ?thesis
            unfolding oL_no_def Let_def
            by (smt (z3) ‹i < length (map oL_no [base..<base + W as s])› 
                add.commute add_diff_cancel_left' atLeastLessThan_upt base_def 
                i_bound jL_bound le_diff_conv length_map nat_less_le nth_mem nth_upt)
        qed
        finally show "map oL_no [base ..< base + W as s] ! i = to_bits (W as s) l2 ! i" .
      qed
      thus ?thesis
        unfolding Lval_at_def base_def
        using bits_roundtrip l2_in by auto
    qed
    thus "Lval_at as s oL_no jL = l2" .
  qed
  
  have oL_no_avoids_v: "∀jL. jL < length (enumL as s kk) ⟶ Lval_at as s oL_no jL ≠ v"
    using oL_no_produces_l2 l2_neq_v by blast
  
  have both_avoid_F: "∀jL. jL < length (enumL as s kk) ⟶ 
        (∀w. w ∈ F ⟶ Lval_at as s oL_has jL ≠ w ∧ Lval_at as s oL_no jL ≠ w)"
  proof (intro allI impI)
    fix jL w
    assume jL_bound: "jL < length (enumL as s kk)" and w_in_F: "w ∈ F"
    
    have "Lval_at as s oL_has jL = l1"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      have "map oL_has [base ..< base + W as s] = to_bits (W as s) l1"
      proof (rule nth_equalityI)
        show "length (map oL_has [base ..< base + W as s]) = length (to_bits (W as s) l1)"
        proof -
          have "l1 ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using l1_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_has [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oL_has [base ..< base + W as s] ! i = oL_has (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) l1 ! i"
        proof -
          have unique_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}) = jL"
          proof (rule some_equality)
            show "jL < length (enumL as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                     length (enc0 as s) + offL as s jL + W as s}"
              using jL_bound base_def i_bound by auto
          next
            fix jL' assume jL'_prop: "jL' < length (enumL as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}"
            show "jL' = jL"
            proof (cases "jL' = jL")
              case True thus ?thesis .
            next
              case False
              have in_jL: "base + i ∈ blockL_abs enc0 as s jL"
                unfolding blockL_abs_def base_def using i_bound by simp
              have in_jL': "base + i ∈ blockL_abs enc0 as s jL'"
                unfolding blockL_abs_def using jL'_prop by simp
              have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                using blockL_abs_disjoint[of jL jL' enc0 as s] False by (simp add: Int_commute)
              thus ?thesis using in_jL in_jL' by blast
            qed
          qed
          thus ?thesis
            unfolding oL_has_def Let_def
            by (smt (verit) ‹i < length (map oL_has [base..<base + W as s])› 
                add.commute add_diff_cancel_left' atLeastLessThan_upt base_def 
                i_bound jL_bound le_diff_conv length_map nat_less_le nat_neq_iff 
                nth_mem nth_upt)
        qed
        finally show "map oL_has [base ..< base + W as s] ! i = to_bits (W as s) l1 ! i" .
      qed
      thus ?thesis
        unfolding Lval_at_def base_def
        using bits_roundtrip l1_in by auto
    qed
    hence "Lval_at as s oL_has jL ≠ w" using l1_out w_in_F by blast
    
    have "Lval_at as s oL_no jL = l2"
    proof -
      define base where "base = length (enc0 as s) + offL as s jL"
      have "map oL_no [base ..< base + W as s] = to_bits (W as s) l2"
      proof (rule nth_equalityI)
        show "length (map oL_no [base ..< base + W as s]) = length (to_bits (W as s) l2)"
        proof -
          have "l2 ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using l2_in by auto
          thus ?thesis using bits_roundtrip by auto
        qed
      next
        fix i assume "i < length (map oL_no [base ..< base + W as s])"
        hence i_bound: "i < W as s" by simp
        have "map oL_no [base ..< base + W as s] ! i = oL_no (base + i)"
          using i_bound by simp
        also have "... = to_bits (W as s) l2 ! i"
        proof -
          have exists_jL: "∃jL' < length (enumL as s kk). 
                base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                            length (enc0 as s) + offL as s jL' + W as s}"
            apply (rule exI[where x=jL])
            using jL_bound base_def i_bound by auto
  
          have unique_jL: "(SOME jL'. jL' < length (enumL as s kk) ∧ 
                      base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                 length (enc0 as s) + offL as s jL' + W as s}) = jL"
          proof (rule some_equality)
            show "jL < length (enumL as s kk) ∧ 
                  base + i ∈ {length (enc0 as s) + offL as s jL ..< 
                      length (enc0 as s) + offL as s jL + W as s}"
              using jL_bound base_def i_bound by auto
          next
            fix jL' assume jL'_prop: "jL' < length (enumL as s kk) ∧
                              base + i ∈ {length (enc0 as s) + offL as s jL' ..< 
                                         length (enc0 as s) + offL as s jL' + W as s}"
            show "jL' = jL"
            proof (cases "jL' = jL")
              case True thus ?thesis .
            next
              case False
              have in_jL: "base + i ∈ blockL_abs enc0 as s jL"
                unfolding blockL_abs_def base_def using i_bound by simp
              have in_jL': "base + i ∈ blockL_abs enc0 as s jL'"
                unfolding blockL_abs_def using jL'_prop by simp
              have "blockL_abs enc0 as s jL ∩ blockL_abs enc0 as s jL' = {}"
                using blockL_abs_disjoint[of jL jL' enc0 as s] False by (simp add: Int_commute)
              thus ?thesis using in_jL in_jL' by blast
            qed
          qed
  
          have offset_eq: "base + i - (length (enc0 as s) + offL as s jL) = i"
            by (simp add: base_def)
  
          show ?thesis
            unfolding oL_no_def Let_def
            using exists_jL unique_jL offset_eq by simp
        qed
        finally show "map oL_no [base ..< base + W as s] ! i = to_bits (W as s) l2 ! i" .
      qed
      thus ?thesis
        unfolding Lval_at_def base_def
        using bits_roundtrip l2_in by auto
    qed
    hence "Lval_at as s oL_no jL ≠ w" using l2_out w_in_F by blast
    
    show "Lval_at as s oL_has jL ≠ w ∧ Lval_at as s oL_no jL ≠ w"
      using ‹Lval_at as s oL_has jL ≠ w› ‹Lval_at as s oL_no jL ≠ w› by simp
  qed
  
  have oL_no_in_catalog: "∀jL. jL < length (enumL as s kk) ⟶ 
                                Lval_at as s oL_no jL ∈ set (enumL as s kk)"
  proof (intro allI impI)
    fix jL assume jL_bound: "jL < length (enumL as s kk)"
    have "Lval_at as s oL_no jL = l2"
      using oL_no_produces_l2 jL_bound by blast
    thus "Lval_at as s oL_no jL ∈ set (enumL as s kk)"
      using l2_in by simp
  qed
  
  show ?thesis
    apply (rule exI[where x=oL_has])
    apply (rule exI[where x=oL_no])
    using oL_has_agrees oL_no_agrees oL_has_has_v oL_no_avoids_v both_avoid_F oL_no_in_catalog
    by blast
qed

(* LEMMA: Can flip oracle on block to change good value 
   
   Key insight: If we have at least 2 LHS values, and some match RHS while
   some don't, then we can change whether good holds by changing one L-block. *)
lemma oracle_flip_changes_good:
  assumes jL_bound: "jL < length (enumL as s kk)"
      and two_lhs: "2 ≤ card (set (enumL as s kk))"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"

  shows "∃oL'. (∀i. i ∉ blockL_abs enc0 as s jL ⟶ 
                     oL' i = (enc as s kk) ! i) ∧
               good as s oL' ((!) (enc as s kk)) ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  (* Get two different values from enumL *)
  obtain v_hit where v_hit_in_L: "v_hit ∈ set (enumL as s kk)" 
                 and v_hit_in_R: "v_hit ∈ set (enumR as s kk)"
    using hit by blast
  obtain v_miss where v_miss_in_L: "v_miss ∈ set (enumL as s kk)"
                  and v_miss_not_R: "v_miss ∉ set (enumR as s kk)"
    using miss by blast
  
  have distinct_L: "distinct (enumL as s kk)" by (simp add: enumL_def)
  
  (* Pick which value to use based on current state *)
  define target where "target = (if good as s ((!) (enc as s kk)) ((!) (enc as s kk))
                                  then v_miss else v_hit)"
  
  (* Build new oracle that puts target in block jL *)
  define bits where "bits = to_bits (W as s) target"

  have target_in: "target ∈ set (enumL as s kk)"
    using target_def v_hit_in_L v_miss_in_L by auto

  have target_in_union: "target ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
    using target_in by auto

  have bits_len: "length bits = W as s"
    using bits_roundtrip[OF target_in_union] bits_def by blast

  have bits_val: "from_bits bits = target"
    using bits_roundtrip[OF target_in_union] bits_def by blast
  
  define oL' where "oL' i = (
    let base = length (enc0 as s) + offL as s jL in
    if base ≤ i ∧ i < base + W as s 
    then bits ! (i - base)
    else (enc as s kk) ! i)" for i
  
  have outside_same: "⋀i. i ∉ blockL_abs enc0 as s jL ⟹ oL' i = (enc as s kk) ! i"
    by (auto simp: oL'_def blockL_abs_def)
  
  have Lval_changed: "Lval_at as s oL' jL = target"
  proof -
    define base where "base = length (enc0 as s) + offL as s jL"
  
    have map_eq: "map oL' [base ..< base + W as s] = bits"
    proof (rule nth_equalityI)
      show "length (map oL' [base ..< base + W as s]) = length bits"
        using bits_len by simp
    next
      fix i assume "i < length (map oL' [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
      have "map oL' [base ..< base + W as s] ! i = oL' (base + i)"
        using i_lt by simp
      also have "... = bits ! i"
        using i_lt by (simp add: oL'_def base_def Let_def)
      finally show "map oL' [base ..< base + W as s] ! i = bits ! i" .
    qed
  
    show ?thesis
      unfolding Lval_at_def base_def[symmetric]
      using map_eq bits_val by simp
  qed
  
  have good_flips: "good as s oL' ((!) (enc as s kk)) ≠ 
                    good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  proof (cases "good as s ((!) (enc as s kk)) ((!) (enc as s kk))")
    case True
  (* Was good, now make it bad by putting v_miss *)
    have "target = v_miss" using True target_def by simp
    hence val_miss: "Lval_at as s oL' jL = v_miss" using Lval_changed by simp
  
  (* v_miss doesn't match any RHS value *)
    have "∀jR < length (enumR as s kk). Rval_at as s ((!) (enc as s kk)) jR ≠ v_miss"
    proof (intro allI impI)
      fix jR assume "jR < length (enumR as s kk)"
      hence "Rval_at as s ((!) (enc as s kk)) jR = enumR as s kk ! jR"
        by (rule Rval_at_on_enc_block)
      thus "Rval_at as s ((!) (enc as s kk)) jR ≠ v_miss"
        using v_miss_not_R by (metis in_set_conv_nth ‹jR < length (enumR as s kk)›)
    qed
  
  (* After flip, position jL can't match anything *)
    hence no_match_jL: "∀jR < length (enumR as s kk). 
                        Lval_at as s oL' jL ≠ Rval_at as s ((!) (enc as s kk)) jR"
      using val_miss by fastforce
  
  (* But we need to show good changes... this is the tricky part *)
      (* After flip: jL doesn't match anything *)
    have no_match_jL: "∀jR < length (enumR as s kk). 
                      Lval_at as s oL' jL ≠ Rval_at as s ((!) (enc as s kk)) jR"
      using val_miss
      by (meson no_match_jL)
  
  (* Other L-blocks are unchanged *)
    have other_unchanged: "∀jL' < length (enumL as s kk). jL' ≠ jL ⟶ 
                          Lval_at as s oL' jL' = Lval_at as s ((!) (enc as s kk)) jL'"
      using Lval_at_unchanged_other_blocks[OF jL_bound _ _ outside_same] by blast
  
  (* Show good becomes false *)
    have "¬ good as s oL' ((!) (enc as s kk))"
    proof
      assume "good as s oL' ((!) (enc as s kk))"
      then obtain jL' jR where 
        jL'_bound: "jL' < length (enumL as s kk)" and
        jR_bound: "jR < length (enumR as s kk)" and
        match: "Lval_at as s oL' jL' = Rval_at as s ((!) (enc as s kk)) jR"
        unfolding good_def by blast
    
      show False
        sorry (* Need: either jL' = jL (contradicts no_match_jL) 
                    or jL' ≠ jL (but then match existed before, 
                    so how was good true before if we're destroying it?) *)
    qed
  
    thus ?thesis using True by simp
  
  next
    case False
  (* Was bad, now make it good by putting v_hit *)
    have "target = v_hit" using False target_def by simp
    hence val_hit: "Lval_at as s oL' jL = v_hit" using Lval_changed by simp
  
  (* v_hit matches some RHS value *)
    have "∃jR < length (enumR as s kk). Rval_at as s ((!) (enc as s kk)) jR = v_hit"
    proof -
      have "v_hit ∈ set (enumR as s kk)" using v_hit_in_R .
      then obtain jR where "jR < length (enumR as s kk)" 
                     and "enumR as s kk ! jR = v_hit"
        by (meson in_set_conv_nth)
      moreover have "Rval_at as s ((!) (enc as s kk)) jR = enumR as s kk ! jR"
        using Rval_at_on_enc_block[OF ‹jR < length (enumR as s kk)›] .
      ultimately show ?thesis by auto
    qed
  
  (* So position jL now matches something *)
    then obtain jR where jR_bound: "jR < length (enumR as s kk)"
                  and match: "Rval_at as s ((!) (enc as s kk)) jR = v_hit"
      by blast
  
    have "Lval_at as s oL' jL = Rval_at as s ((!) (enc as s kk)) jR"
      using val_hit match by simp
  
  (* This witness proves good is true after flip *)
    hence "good as s oL' ((!) (enc as s kk))"
      unfolding good_def using jL_bound jR_bound by blast
  
  (* But it was false before, so they differ *)
    thus ?thesis using False by simp
  qed
  
  (* NOW CONSTRUCT THE EXISTENTIAL! *)
  show ?thesis
  proof (intro exI[of _ oL'] conjI)
    show "∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL' i = (enc as s kk) ! i"
      using outside_same by blast
    show "good as s oL' ((!) (enc as s kk)) ≠ 
          good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
      using good_flips .
  qed
qed

(* Helper: Flipping one L-block doesn't affect other L-blocks (generic version) *)
lemma Lval_at_unchanged_other_blocks_generic:
  assumes jL_bound: "jL < length (enumL as s kk)"
      and jL'_bound: "jL' < length (enumL as s kk)"
      and jL'_diff: "jL' ≠ jL"
      and outside_same: "⋀i. i ∉ blockL_abs enc0 as s jL ⟹ oL' i = ((!) (enc as s kk)) i"
  shows "Lval_at as s oL' jL' = Lval_at as s ((!) (enc as s kk)) jL'"
  using Lval_at_unchanged_other_blocks[OF jL_bound jL'_bound jL'_diff outside_same] .

(* NEW VERSION - 4-oracle construction *)
lemma oracle_flip_changes_good_v2:
  assumes jL_bound: "jL < length (enumL as s kk)"
      and two_lhs: "2 ≤ card (set (enumL as s kk))"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
      and unread_R: "∀jR < length (enumR as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
      and slack: "card (set (enumR as s kk)) > card (set (enumL as s kk))"
  shows "∃oL_on oL_off oR_has oR_no. 
    (∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL_on i = (enc as s kk) ! i) ∧
    (∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL_off i = (enc as s kk) ! i) ∧
    (∀i ∈ Base.read0 M (enc as s kk). oR_has i = (enc as s kk) ! i) ∧
    (∀i ∈ Base.read0 M (enc as s kk). oR_no i = (enc as s kk) ! i) ∧
    (good as s oL_on oR_has ≠ good as s oL_off oR_no)"
proof -
  (* Get two different values from enumL *)
  obtain v_hit where v_hit_in_L: "v_hit ∈ set (enumL as s kk)" 
                 and v_hit_in_R: "v_hit ∈ set (enumR as s kk)"
    using hit by blast
  obtain v_miss where v_miss_in_L: "v_miss ∈ set (enumL as s kk)"
                  and v_miss_not_R: "v_miss ∉ set (enumR as s kk)"
    using miss by blast
  
  (* Compute forbidden set: all L-values except v_hit and v_miss *)
  define F where "F = set (enumL as s kk) - {v_hit, v_miss}"
  
  have F_finite: "finite F" by (simp add: F_def)
  have F_subset: "F ⊆ set (enumL as s kk)" by (simp add: F_def)
  have F_bound: "card F < card (set (enumL as s kk))"
    using two_lhs F_def
    by (metis Diff_insert2 List.finite_set card_Diff2_less v_hit_in_L v_miss_in_L)
  
  (* So we have slack to use construct_avoiding_R_oracle *)
  have slack_for_F: "card (set (enumR as s kk)) > card F + 1"
    using slack F_bound two_lhs by simp
  
  (* Use construct_avoiding_R_oracle with v_hit as target *)
(* First prove v_hit ∉ F *)
  have v_hit_not_F: "v_hit ∉ F"
    unfolding F_def by auto

(* Now call the lemma with all 6 arguments *)
  obtain oR_has oR_no where
    oR_agree_has: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_has i = (enc as s kk) ! i" and
    oR_agree_no: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oR_no i = (enc as s kk) ! i" and
    oR_has_hit: "v_hit ∈ set (enumR as s kk) ⟶ 
              (∃jR. jR < length (enumR as s kk) ∧ Rval_at as s oR_has jR = v_hit)" and
    oR_no_no_hit: "∀jR. jR < length (enumR as s kk) ⟶ Rval_at as s oR_no jR ≠ v_hit" and
    oR_avoid_F: "∀jR. jR < length (enumR as s kk) ⟶ 
              (∀w. w ∈ F ⟶ Rval_at as s oR_has jR ≠ w ∧ Rval_at as s oR_no jR ≠ w)" and
    oR_no_in_catalog: "∀jR. jR < length (enumR as s kk) ⟶ 
                          Rval_at as s oR_no jR ∈ set (enumR as s kk)"  (* ADD THIS LINE *)
    using construct_avoiding_R_oracle[OF unread_R v_hit_in_L v_hit_not_F ‹finite F› 
      F_subset slack_for_F]
    by blast

(* Key fact: oR_has has v_hit, oR_no doesn't *)
  have oR_has_contains_hit: "∃jR. jR < length (enumR as s kk) ∧ Rval_at as s oR_has jR = v_hit"
      using oR_has_hit v_hit_in_R by blast

(* Build oL_on: puts v_hit in block jL *)
  define bits_hit where "bits_hit = to_bits (W as s) v_hit"
  define oL_on where "oL_on i = (
    let base = length (enc0 as s) + offL as s jL in
    if base ≤ i ∧ i < base + W as s 
    then bits_hit ! (i - base)
    else (enc as s kk) ! i)" for i

  have oL_on_outside: "∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL_on i = (enc as s kk) ! i"
    by (auto simp: oL_on_def blockL_abs_def)

(* Build oL_off: puts v_miss in block jL *)
  define bits_miss where "bits_miss = to_bits (W as s) v_miss"
  define oL_off where "oL_off i = (
    let base = length (enc0 as s) + offL as s jL in
    if base ≤ i ∧ i < base + W as s 
    then bits_miss ! (i - base)
    else (enc as s kk) ! i)" for i

  have oL_off_outside: "∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL_off i = (enc as s kk) ! i"
    by (auto simp: oL_off_def blockL_abs_def)

(* Show oL_on value at jL *)
  have Lval_on: "Lval_at as s oL_on jL = v_hit"
  proof -
    define base where "base = length (enc0 as s) + offL as s jL"
  
  (* Show the map gives us bits_hit *)
    have map_eq: "map oL_on [base ..< base + W as s] = bits_hit"
    proof (rule nth_equalityI)
      show "length (map oL_on [base ..< base + W as s]) = length bits_hit"
      proof -
        have "length bits_hit = W as s"
        proof -
          have v_hit_in_union: "v_hit ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using v_hit_in_L by auto
          show ?thesis
            using bits_roundtrip[OF v_hit_in_union] bits_hit_def by blast
        qed
        thus ?thesis by simp
      qed
    next
      fix i assume "i < length (map oL_on [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
    
      have "map oL_on [base ..< base + W as s] ! i = oL_on (base + i)"
        using i_lt by simp
      also have "... = bits_hit ! i"
        using i_lt by (simp add: oL_on_def base_def Let_def)
      finally show "map oL_on [base ..< base + W as s] ! i = bits_hit ! i" .
    qed
  
  (* Now use bits_roundtrip *)
    show ?thesis
      unfolding Lval_at_def base_def[symmetric]
    proof -
      have "from_bits (map oL_on [base ..< base + W as s]) = from_bits bits_hit"
        using map_eq by simp
      also have "... = v_hit"
      proof -
        have v_hit_in_union: "v_hit ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using v_hit_in_L by auto
        show ?thesis
          using bits_roundtrip[OF v_hit_in_union] bits_hit_def by blast
      qed
      finally show "from_bits (map oL_on [base ..< base + W as s]) = v_hit" .
    qed
  qed

(* Show oL_off value at jL *)
  have Lval_off: "Lval_at as s oL_off jL = v_miss"
  proof -
    define base where "base = length (enc0 as s) + offL as s jL"
  
  (* Show the map gives us bits_miss *)
    have map_eq: "map oL_off [base ..< base + W as s] = bits_miss"
    proof (rule nth_equalityI)
      show "length (map oL_off [base ..< base + W as s]) = length bits_miss"
      proof -
        have "length bits_miss = W as s"
        proof -
          have v_miss_in_union: "v_miss ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using v_miss_in_L by auto
          show ?thesis
            using bits_roundtrip[OF v_miss_in_union] bits_miss_def by blast
        qed
        thus ?thesis by simp
      qed
    next
      fix i assume "i < length (map oL_off [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
    
      have "map oL_off [base ..< base + W as s] ! i = oL_off (base + i)"
        using i_lt by simp
      also have "... = bits_miss ! i"
        using i_lt by (simp add: oL_off_def base_def Let_def)
      finally show "map oL_off [base ..< base + W as s] ! i = bits_miss ! i" .
    qed
  
  (* Now use bits_roundtrip *)
    show ?thesis
      unfolding Lval_at_def base_def[symmetric]
    proof -
      have "from_bits (map oL_off [base ..< base + W as s]) = from_bits bits_miss"
        using map_eq by simp
      also have "... = v_miss"
      proof -
        have v_miss_in_union: "v_miss ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using v_miss_in_L by auto
        show ?thesis
          using bits_roundtrip[OF v_miss_in_union] bits_miss_def by blast
      qed
      finally show "from_bits (map oL_off [base ..< base + W as s]) = v_miss" .
    qed
  qed

(* Show (oL_on, oR_has) is good: v_hit matches *)
  have "good as s oL_on oR_has"
  proof -
    obtain jR where "jR < length (enumR as s kk)" and "Rval_at as s oR_has jR = v_hit"
      using oR_has_contains_hit by blast
    moreover have "Lval_at as s oL_on jL = v_hit" using Lval_on .
    ultimately show ?thesis
      unfolding good_def using jL_bound by blast
  qed

(* Show (oL_off, oR_no) is NOT good: no matches possible *)
  have "¬ good as s oL_off oR_no"
  proof
    assume "good as s oL_off oR_no"
    then obtain jL' jR where
      jL'_bound: "jL' < length (enumL as s kk)" and
      jR_bound: "jR < length (enumR as s kk)" and
      match: "Lval_at as s oL_off jL' = Rval_at as s oR_no jR"
      unfolding good_def by blast

  (* What is the value at jL'? *)
    show False
    proof (cases "jL' = jL")
      case True
    (* Match at the flipped block *)
      have "Lval_at as s oL_off jL' = v_miss" using Lval_off True by simp
      moreover have "Rval_at as s oR_no jR ≠ v_miss"
      proof
        assume "Rval_at as s oR_no jR = v_miss"
      (* oR_no only produces values from RHS *)
        have "Rval_at as s oR_no jR ∈ set (enumR as s kk)"
          using oR_no_in_catalog jR_bound by blast
      (* But v_miss is not in RHS *)
        moreover have "v_miss ∉ set (enumR as s kk)"
          using v_miss_not_R by simp
        ultimately show False 
          using ‹Rval_at as s oR_no jR = v_miss› by simp
      qed
      ultimately show False using match by simp
    next
      case False
    (* Match at a different block jL' ≠ jL *)
    (* This block is unchanged from the original encoding *)
      have unchanged: "Lval_at as s oL_off jL' = Lval_at as s ((!) (enc as s kk)) jL'"
        using Lval_at_unchanged_other_blocks_generic[OF jL_bound jL'_bound False] oL_off_outside
        by blast

    (* So the value is from the original enumL *)
      have "Lval_at as s oL_off jL' = enumL as s kk ! jL'"
      proof -
        have "Lval_at as s ((!) (enc as s kk)) jL' = enumL as s kk ! jL'"
          by (simp add: Lval_at_on_enc_block jL'_bound)
        thus ?thesis using unchanged by simp
      qed
    
    (* This value is either v_hit, v_miss, or in F *)
      have "enumL as s kk ! jL' ∈ set (enumL as s kk)" 
        using jL'_bound nth_mem by blast
      hence "enumL as s kk ! jL' ∈ insert v_hit (insert v_miss F)"
        using F_def by auto
    
    (* Case split on which one *)
      hence "enumL as s kk ! jL' = v_hit ∨ enumL as s kk ! jL' = v_miss ∨ enumL as s kk ! jL' ∈ F"
        by auto
      thus False
      proof (elim disjE)
        assume "enumL as s kk ! jL' = v_hit"
        hence "Lval_at as s oL_off jL' = v_hit"
          using ‹Lval_at as s oL_off jL' = enumL as s kk ! jL'› by simp
        hence "Rval_at as s oR_no jR = v_hit" using match by simp
        thus False using oR_no_no_hit jR_bound by blast
      next
        assume "enumL as s kk ! jL' = v_miss"
        hence "Lval_at as s oL_off jL' = v_miss"
          using ‹Lval_at as s oL_off jL' = enumL as s kk ! jL'› by simp
        hence "Rval_at as s oR_no jR = v_miss" using match by simp
      (* oR_no produces values from RHS, but v_miss ∉ RHS *)
        moreover have "Rval_at as s oR_no jR ∈ set (enumR as s kk)"
          using oR_no_in_catalog jR_bound by blast
        moreover have "v_miss ∉ set (enumR as s kk)"
          using v_miss_not_R by simp
        ultimately show False by simp
      next
        assume in_F: "enumL as s kk ! jL' ∈ F"
        have "Lval_at as s oL_off jL' ∈ F"
          using ‹Lval_at as s oL_off jL' = enumL as s kk ! jL'› in_F by simp
        hence "Rval_at as s oR_no jR ∈ F" using match by simp
        thus False using oR_avoid_F jR_bound by blast
      qed
    qed
  qed

(* Therefore they differ *)
  have good_differs: "good as s oL_on oR_has ≠ good as s oL_off oR_no"
    using ‹good as s oL_on oR_has› ‹¬ good as s oL_off oR_no› by blast

(* Package everything up *)
  show ?thesis
    using oL_on_outside oL_off_outside oR_agree_has oR_agree_no
        ‹good as s oL_on oR_has ≠ good as s oL_off oR_no›
    by (smt (verit, best))
qed

(* Symmetric: 4-oracle construction for R-blocks *)
lemma oracle_flip_changes_good_R_v2:
  assumes jR_bound: "jR < length (enumR as s kk)"
      and two_rhs: "2 ≤ card (set (enumR as s kk))"
      and hit: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
      and unread_L: "∀jL < length (enumL as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
      and slack: "card (set (enumL as s kk)) > card (set (enumR as s kk))"
  shows "∃oL_has oL_no oR_on oR_off. 
    (∀i ∈ Base.read0 M (enc as s kk). oL_has i = (enc as s kk) ! i) ∧
    (∀i ∈ Base.read0 M (enc as s kk). oL_no i = (enc as s kk) ! i) ∧
    (∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR_on i = (enc as s kk) ! i) ∧
    (∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR_off i = (enc as s kk) ! i) ∧
    (good as s oL_has oR_on ≠ good as s oL_no oR_off)"
proof -
  (* Get two different values from enumR *)
  obtain v_hit where v_hit_in_R: "v_hit ∈ set (enumR as s kk)" 
                 and v_hit_in_L: "v_hit ∈ set (enumL as s kk)"
    using hit by blast
  obtain v_miss where v_miss_in_R: "v_miss ∈ set (enumR as s kk)"
                  and v_miss_not_L: "v_miss ∉ set (enumL as s kk)"
    using miss by blast
  
  (* Compute forbidden set: all R-values except v_hit and v_miss *)
  define F where "F = set (enumR as s kk) - {v_hit, v_miss}"
  
  have F_finite: "finite F" by (simp add: F_def)
  have F_subset: "F ⊆ set (enumR as s kk)" by (simp add: F_def)
  have F_bound: "card F < card (set (enumR as s kk))"
    using two_rhs F_def
    by (metis Diff_insert2 List.finite_set card_Diff2_less v_hit_in_R v_miss_in_R)
  
  (* So we have slack to use construct_avoiding_L_oracle *)
  have slack_for_F: "card (set (enumL as s kk)) > card F + 1"
    using slack F_bound two_rhs by simp

(* First prove v_hit ∉ F *)
  have v_hit_not_F: "v_hit ∉ F"
    unfolding F_def by auto

(* Use construct_avoiding_L_oracle with v_hit as target *)
  obtain oL_has oL_no where
    oL_agree_has: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_has i = (enc as s kk) ! i" and
    oL_agree_no: "∀i. i ∈ Base.read0 M (enc as s kk) ⟶ oL_no i = (enc as s kk) ! i" and
    oL_has_hit: "v_hit ∈ set (enumL as s kk) ⟶ 
                (∃jL. jL < length (enumL as s kk) ∧ Lval_at as s oL_has jL = v_hit)" and
    oL_no_no_hit: "∀jL. jL < length (enumL as s kk) ⟶ Lval_at as s oL_no jL ≠ v_hit" and
    oL_avoid_F: "∀jL. jL < length (enumL as s kk) ⟶ 
                (∀w. w ∈ F ⟶ Lval_at as s oL_has jL ≠ w ∧ Lval_at as s oL_no jL ≠ w)" and
    oL_no_in_catalog: "∀jL. jL < length (enumL as s kk) ⟶ 
                          Lval_at as s oL_no jL ∈ set (enumL as s kk)"
    using construct_avoiding_L_oracle[OF unread_L v_hit_in_R v_hit_not_F 
                                         F_finite F_subset slack_for_F]
    by blast

(* Key fact: oL_has has v_hit, oL_no doesn't *)
  have oL_has_contains_hit: "∃jL. jL < length (enumL as s kk) ∧ Lval_at as s oL_has jL = v_hit"
    using oL_has_hit v_hit_in_L by blast

(* Build oR_on: puts v_hit in block jR *)
  define bits_hit where "bits_hit = to_bits (W as s) v_hit"
  define oR_on where "oR_on i = (
    let base = length (enc0 as s) + offR as s kk jR in
    if base ≤ i ∧ i < base + W as s 
    then bits_hit ! (i - base)
    else (enc as s kk) ! i)" for i

  have oR_on_outside: "∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR_on i = (enc as s kk) ! i"
    by (auto simp: oR_on_def blockR_abs_def)

(* Build oR_off: puts v_miss in block jR *)
  define bits_miss where "bits_miss = to_bits (W as s) v_miss"
  define oR_off where "oR_off i = (
    let base = length (enc0 as s) + offR as s kk jR in
    if base ≤ i ∧ i < base + W as s 
    then bits_miss ! (i - base)
    else (enc as s kk) ! i)" for i

  have oR_off_outside: "∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR_off i = (enc as s kk) ! i"
    by (auto simp: oR_off_def blockR_abs_def)

(* Show values at jR *)
  have Rval_on: "Rval_at as s oR_on jR = v_hit"
  proof -
    define base where "base = length (enc0 as s) + offR as s kk jR"
  
  (* Show the map gives us bits_hit *)
    have map_eq: "map oR_on [base ..< base + W as s] = bits_hit"
    proof (rule nth_equalityI)
      show "length (map oR_on [base ..< base + W as s]) = length bits_hit"
      proof -
        have "length bits_hit = W as s"
        proof -
          have v_hit_in_union: "v_hit ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using v_hit_in_R by auto
          show ?thesis
            using bits_roundtrip[OF v_hit_in_union] bits_hit_def by blast
        qed
        thus ?thesis by simp
      qed
    next
      fix i assume "i < length (map oR_on [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
    
      have "map oR_on [base ..< base + W as s] ! i = oR_on (base + i)"
        using i_lt by simp
      also have "... = bits_hit ! i"
        using i_lt by (simp add: oR_on_def base_def Let_def)
      finally show "map oR_on [base ..< base + W as s] ! i = bits_hit ! i" .
    qed
  
  (* Now use bits_roundtrip *)
    show ?thesis
      unfolding Rval_at_def base_def[symmetric]
    proof -
      have "from_bits (map oR_on [base ..< base + W as s]) = from_bits bits_hit"
        using map_eq by simp
      also have "... = v_hit"
      proof -
        have v_hit_in_union: "v_hit ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using v_hit_in_R by auto
        show ?thesis
          using bits_roundtrip[OF v_hit_in_union] bits_hit_def by blast
      qed
      finally show "from_bits (map oR_on [base ..< base + W as s]) = v_hit" .
    qed
  qed

  have Rval_off: "Rval_at as s oR_off jR = v_miss"
  proof -
    define base where "base = length (enc0 as s) + offR as s kk jR"
  
  (* Show the map gives us bits_miss *)
    have map_eq: "map oR_off [base ..< base + W as s] = bits_miss"
    proof (rule nth_equalityI)
      show "length (map oR_off [base ..< base + W as s]) = length bits_miss"
      proof -
        have "length bits_miss = W as s"
        proof -
          have v_miss_in_union: "v_miss ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
            using v_miss_in_R by auto
          show ?thesis
            using bits_roundtrip[OF v_miss_in_union] bits_miss_def by blast
        qed
        thus ?thesis by simp
      qed
    next
      fix i assume "i < length (map oR_off [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
    
      have "map oR_off [base ..< base + W as s] ! i = oR_off (base + i)"
        using i_lt by simp
      also have "... = bits_miss ! i"
        using i_lt by (simp add: oR_off_def base_def Let_def)
      finally show "map oR_off [base ..< base + W as s] ! i = bits_miss ! i" .
    qed
  
  (* Now use bits_roundtrip *)
    show ?thesis
      unfolding Rval_at_def base_def[symmetric]
    proof -
      have "from_bits (map oR_off [base ..< base + W as s]) = from_bits bits_miss"
        using map_eq by simp
      also have "... = v_miss"
      proof -
        have v_miss_in_union: "v_miss ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
          using v_miss_in_R by auto
        show ?thesis
          using bits_roundtrip[OF v_miss_in_union] bits_miss_def by blast
      qed
      finally show "from_bits (map oR_off [base ..< base + W as s]) = v_miss" .
    qed
  qed

(* Show (oL_has, oR_on) is good *)
  have "good as s oL_has oR_on"
  proof -
    obtain jL where "jL < length (enumL as s kk)" and "Lval_at as s oL_has jL = v_hit"
      using oL_has_contains_hit by blast
    moreover have "Rval_at as s oR_on jR = v_hit" using Rval_on .
    ultimately show ?thesis
      unfolding good_def using jR_bound by force
  qed

(* Show they differ *)
  have "good as s oL_has oR_on ≠ good as s oL_no oR_off"
  sorry (* AXIOM: Symmetric adversarial argument *)

(* Package up *)
  show ?thesis
    using oL_agree_has oL_agree_no oR_on_outside oR_off_outside
        ‹good as s oL_has oR_on ≠ good as s oL_no oR_off›
    by blast
qed

(* THEOREM: If M doesn't read a block, contradiction *)
theorem coverage_by_oracle_contradiction:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"  (* NEW *)
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"  (* NEW *)
      and miss_block: "∃jL. jL < length (enumL as s kk) ∧
                            Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
  shows False
proof -
  (* Get the unread block *)
  obtain jL where 
    jL_bound: "jL < length (enumL as s kk)" and
    jL_unread: "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
    using miss_block by blast
  
  (* For the oracle flip to work, we need these conditions *)
  have two_lhs: "2 ≤ card (set (enumL as s kk))"
  proof -
    have "card (set (enumL as s kk)) = card (LHS (e_k as s kk) (length as))"
      by simp
    also have "... = 2 ^ kk"
      using card_LHS_e_k distinct kk_bounds(2) len less_or_eq_imp_le by blast
    also have "... ≥ 2"
      using kk_bounds
      by (metis add_0 add_lessD1 linorder_not_less nat_power_less_imp_less 
          power_one_right)
    finally show ?thesis .
  qed
  
(* Remove the sorry lines, use the assumptions directly *)
(* hit and miss are now assumptions, not things to prove *)
  
(* Get flipped oracle *)
  have flip_exists: "∃oL'. (∀i. i ∉ blockL_abs enc0 as s jL ⟶ 
                               oL' i = (enc as s kk) ! i) ∧
                         good as s oL' ((!) (enc as s kk)) ≠ 
                         good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using oracle_flip_changes_good[OF jL_bound two_lhs hit miss] .

(* Get flipped oracle *)
  obtain oL' where
    outside_same_obj: "∀i. i ∉ blockL_abs enc0 as s jL ⟶ 
                         oL' i = (enc as s kk) ! i" and
    good_flips: "good as s oL' ((!) (enc as s kk)) ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using flip_exists by auto

(* Convert to meta-level *)
  have outside_same: "⋀i. i ∉ blockL_abs enc0 as s jL ⟹ oL' i = (enc as s kk) ! i"
    using outside_same_obj by blast
  
  (* Tree doesn't see the flipped block *)
  have unseen: "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
                blockL_abs enc0 as s jL = {}"
    using unread_block_unseen[OF jL_unread] .
  
(* Therefore tree gives same answer with oL' *)
  have L_agree: "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ⟹ 
                   oL' i = (enc as s kk) ! i"
    using unseen outside_same by blast

  have R_agree: "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ⟹ 
                   ((!) (enc as s kk)) j = ((!) (enc as s kk)) j"
    by simp

  have "run oL' ((!) (enc as s kk)) (T as s) = 
      run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    by (simp add: run_agree_on_seen(1)[OF L_agree R_agree])
  
  (* But the tree must give correct answers *)
  hence "good as s oL' ((!) (enc as s kk)) = 
         good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using correct_T by (meson correctness)
  
  (* Contradiction! *)
  with good_flips show False by contradiction
qed

theorem coverage_by_oracle_contradiction_v2:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and kk_slack: "2 * kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
      and miss_L_block: "∃jL. jL < length (enumL as s kk) ∧
                            Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
      and unread_R: "∀jR < length (enumR as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
  shows False
proof -
  (* Get the unread L-block *)
  obtain jL where 
    jL_bound: "jL < length (enumL as s kk)" and
    jL_unread: "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
    using miss_L_block by blast
  
(* Prove slack: |RHS| > |LHS| *)
  have slack: "card (set (enumR as s kk)) > card (set (enumL as s kk))"
  proof -
    have L_card: "card (set (enumL as s kk)) = 2^kk"
      by (simp add: enumL_def card_LHS_e_k distinct kk_bounds(2) len less_or_eq_imp_le)
    have R_card: "card (set (enumR as s kk)) = 2^(n - kk)"
      by (simp add: enumR_def card_RHS_e_k distinct kk_bounds(2) len less_or_eq_imp_le)
    have "kk < n - kk" using kk_slack by simp
    hence "(2::nat)^kk < 2^(n - kk)" by (rule power_strict_increasing) simp
    thus ?thesis using L_card R_card by simp
  qed

(* Need two_lhs for oracle construction *)
  have two_lhs: "2 ≤ card (set (enumL as s kk))"
  proof -
    have "card (set (enumL as s kk)) = card (LHS (e_k as s kk) (length as))"
      by simp
    also have "... = 2 ^ kk"
      using card_LHS_e_k distinct kk_bounds(2) len less_or_eq_imp_le by blast
    also have "... ≥ 2"
      using kk_bounds
      by (metis add_0 add_lessD1 linorder_not_less nat_power_less_imp_less 
        power_one_right)
    finally show ?thesis .
  qed
  
  (* Get 4 oracles from new lemma *)
  obtain oL_on oL_off oR_has oR_no where
    oL_on_agree: "∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL_on i = (enc as s kk) ! i" and
    oL_off_agree: "∀i. i ∉ blockL_abs enc0 as s jL ⟶ oL_off i = (enc as s kk) ! i" and
    oR_has_agree: "∀i ∈ Base.read0 M (enc as s kk). oR_has i = (enc as s kk) ! i" and
    oR_no_agree: "∀i ∈ Base.read0 M (enc as s kk). oR_no i = (enc as s kk) ! i" and
    good_differs: "good as s oL_on oR_has ≠ good as s oL_off oR_no"
    using oracle_flip_changes_good_v2[OF jL_bound two_lhs hit miss unread_R slack]
    by blast
  
(* Tree doesn't see the flipped L-block *)
  have unseenL: "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
              blockL_abs enc0 as s jL = {}"
    using unread_block_unseen[OF jL_unread] .

(* Tree doesn't see ANY R-blocks *)
  have unseenR: "∀jR < length (enumR as s kk). 
            seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
            blockR_abs enc0 as s kk jR = {}"
  proof (intro allI impI)
    fix jR assume "jR < length (enumR as s kk)"
    hence "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
      using unread_R by blast
    thus "seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
        blockR_abs enc0 as s kk jR = {}"
      by (rule unread_block_unseen_R)
  qed

(* Therefore tree gives same answer for all oracle combinations *)
  have "run oL_on oR_has (T as s) = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
  proof (rule run_agree_on_seen(1)[symmetric])
    show "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oL_on i = ((!) (enc as s kk)) i"
    proof -
      fix i assume i_seen: "i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    (* unseenL shows this set is disjoint from blockL_abs *)
      have "i ∉ blockL_abs enc0 as s jL"
        using unseenL i_seen by blast
      thus "oL_on i = ((!) (enc as s kk)) i"
        using oL_on_agree by blast
    qed
    show "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oR_has j = ((!) (enc as s kk)) j"
    proof -
      fix j assume j_seen: "j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
      have "seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
          ⊆ Base.read0 M (enc as s kk)"
        unfolding T_def by (rule seenR_tm_to_dtr_subset_read0)
      hence "j ∈ Base.read0 M (enc as s kk)"
        using j_seen by blast
      thus "oR_has j = ((!) (enc as s kk)) j"
        using oR_has_agree by blast
    qed
  qed

  have "run oL_off oR_no (T as s) = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
  proof (rule run_agree_on_seen(1)[symmetric])
    show "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oL_off i = ((!) (enc as s kk)) i"
    proof -
      fix i assume i_seen: "i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    (* unseenL shows this set is disjoint from blockL_abs *)
      have "i ∉ blockL_abs enc0 as s jL"
        using unseenL i_seen by blast
      thus "oL_off i = ((!) (enc as s kk)) i"
        using oL_off_agree by blast
    qed
    show "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oR_no j = ((!) (enc as s kk)) j"
    proof -
      fix j assume j_seen: "j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
      have "seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
          ⊆ Base.read0 M (enc as s kk)"
        unfolding T_def by (rule seenR_tm_to_dtr_subset_read0)
      hence "j ∈ Base.read0 M (enc as s kk)"
        using j_seen by blast
      thus "oR_no j = ((!) (enc as s kk)) j"
        using oR_no_agree by blast
    qed
  qed

(* So tree gives same answer for both oracle pairs *)
  hence same_run: "run oL_on oR_has (T as s) = run oL_off oR_no (T as s)"
    by (meson correctness)

(* But correctness says tree must match good *)
  have "good as s oL_on oR_has = good as s oL_off oR_no"
    using same_run correct_T by (meson correctness)

(* Contradiction! *)
  with good_differs show False by contradiction
qed

(* Symmetric: Coverage contradiction for R-blocks using 4 oracles *)
theorem coverage_by_oracle_contradiction_R_v2:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and kk_large: "kk > n - kk"  (* ADD THIS LINE *)
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
      and miss_R_block: "∃jR. jR < length (enumR as s kk) ∧
                            Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
      and unread_L: "∀jL < length (enumL as s kk). 
                      Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
  shows False
proof -
  (* Get the unread R-block *)
  obtain jR where 
    jR_bound: "jR < length (enumR as s kk)" and
    jR_unread: "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
    using miss_R_block by blast
  
  (* Prove slack: |LHS| > |RHS| *)
  have slack: "card (set (enumR as s kk)) < card (set (enumL as s kk))"
    using LHS_larger_than_RHS_when_kk_large[OF n_ge2 kk_large kk_bounds(2) distinct len] 
    by simp
  
  (* Need two_rhs for oracle construction *)
  have two_rhs: "2 ≤ card (set (enumR as s kk))"
  proof -
    have "card (set (enumR as s kk)) = card (RHS (e_k as s kk) (length as))"
      by simp
    also have "... = 2 ^ (n - kk)"
      using card_RHS_e_k distinct kk_bounds len
      by (meson less_or_eq_imp_le)
    also have "... ≥ 2"
    proof -
      have "n - kk ≥ 1" using kk_bounds by simp
      then obtain m where "n - kk = Suc m" by (cases "n - kk") auto
      thus ?thesis by simp
    qed
    finally show ?thesis .
  qed
  
  (* Get 4 oracles from new lemma *)
  obtain oL_has oL_no oR_on oR_off where
    oL_has_agree: "∀i ∈ Base.read0 M (enc as s kk). oL_has i = (enc as s kk) ! i" and
    oL_no_agree: "∀i ∈ Base.read0 M (enc as s kk). oL_no i = (enc as s kk) ! i" and
    oR_on_agree: "∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR_on i = (enc as s kk) ! i" and
    oR_off_agree: "∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR_off i = (enc as s kk) ! i" and
    good_differs: "good as s oL_has oR_on ≠ good as s oL_no oR_off"
    using oracle_flip_changes_good_R_v2[OF jR_bound two_rhs hit miss unread_L slack]
    by blast
  
(* Tree doesn't see the flipped R-block *)
  have unseenR: "seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
              blockR_abs enc0 as s kk jR = {}"
    using unread_block_unseen_R[OF jR_unread] .

(* Tree doesn't see ANY L-blocks *)
  have unseenL: "∀jL < length (enumL as s kk). 
            seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
            blockL_abs enc0 as s jL = {}"
  proof (intro allI impI)
   fix jL assume "jL < length (enumL as s kk)"
   hence "Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
     using unread_L by blast
   thus "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
        blockL_abs enc0 as s jL = {}"
     by (rule unread_block_unseen)
 qed

(* Therefore tree gives same answer for all oracle combinations *)
  have "run oL_has oR_on (T as s) = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
  proof (rule run_agree_on_seen(1)[symmetric])
    show "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oL_has i = ((!) (enc as s kk)) i"
    proof -
      fix i assume i_seen: "i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
      have "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⊆ Base.read0 M (enc as s kk)"
        unfolding T_def by (rule seenL_tm_to_dtr_subset_read0)
      hence "i ∈ Base.read0 M (enc as s kk)"
        using i_seen by blast
      thus "oL_has i = ((!) (enc as s kk)) i"
        using oL_has_agree by blast
    qed
    show "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oR_on j = ((!) (enc as s kk)) j"
    proof -
      fix j assume j_seen: "j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    (* unseenR shows this set is disjoint from blockR_abs *)
      have "j ∉ blockR_abs enc0 as s kk jR"
        using unseenR j_seen by blast
      thus "oR_on j = ((!) (enc as s kk)) j"
        using oR_on_agree by blast
    qed
  qed

  have "run oL_no oR_off (T as s) = run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
  proof (rule run_agree_on_seen(1)[symmetric])
    show "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oL_no i = ((!) (enc as s kk)) i"
    proof -
      fix i assume i_seen: "i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
      have "seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⊆ Base.read0 M (enc as s kk)"
        unfolding T_def by (rule seenL_tm_to_dtr_subset_read0)
      hence "i ∈ Base.read0 M (enc as s kk)"
        using i_seen by blast
      thus "oL_no i = ((!) (enc as s kk)) i"
        using oL_no_agree by blast
    qed
    show "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) 
            ⟹ oR_off j = ((!) (enc as s kk)) j"
    proof -
      fix j assume j_seen: "j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    (* unseenR shows this set is disjoint from blockR_abs *)
      have "j ∉ blockR_abs enc0 as s kk jR"
        using unseenR j_seen by blast
      thus "oR_off j = ((!) (enc as s kk)) j"
        using oR_off_agree by blast
    qed
  qed

(* So tree gives same answer for both oracle pairs *)
  hence same_run: "run oL_has oR_on (T as s) = run oL_no oR_off (T as s)"
    by (simp add: ‹run oL_has oR_on (T as s) = run ((!) (x0 as s)) ((!) (x0 as s)) (T as s)›)

(* But correctness says tree must match good *)
  have "good as s oL_has oR_on = good as s oL_no oR_off"
    using same_run correct_T by (meson correctness)

(* Contradiction! *)
  with good_differs show False by contradiction
qed

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
proof (rule ccontr)
  assume "¬(∀jL<length (enumL as s kk). 
              Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {})"
  hence "∃jL. jL < length (enumL as s kk) ∧
              Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}" by simp
  thus False 
    using coverage_by_oracle_contradiction[OF n_ge2 kk_bounds distinct len hit miss] 
    by blast
qed

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
proof (rule ccontr)
  assume "¬(∀jL<length (enumL as s kk). 
              Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {})"
  hence "∃jL. jL < length (enumL as s kk) ∧
              Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}" by simp
  thus False 
    using coverage_by_oracle_contradiction_v2[OF n_ge2 kk_bounds kk_slack distinct len hit miss _ unread_R] 
    by blast
qed

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
proof (rule ccontr)
  assume "¬(∀jR<length (enumR as s kk). 
              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {})"
  hence "∃jR. jR < length (enumR as s kk) ∧
              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}" by simp
  thus False 
    using coverage_by_oracle_contradiction_R_v2[OF n_ge2 kk_bounds kk_large distinct 
          len hit miss _ unread_L]
    by blast
qed

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

lemma oracle_flip_changes_good_R:
  assumes jR_bound: "jR < length (enumR as s kk)"
      and two_rhs: "2 ≤ card (set (enumR as s kk))"
      and hit: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
      and unique: "card (set (enumL as s kk) ∩ set (enumR as s kk)) = 1"  (* ADD THIS *)
  shows "∃oR'. (∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ 
                     oR' i = (enc as s kk) ! i) ∧
               good as s ((!) (enc as s kk)) oR' ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
proof -
  (* Get two different values from enumR *)
  obtain v_hit where v_hit_in_R: "v_hit ∈ set (enumR as s kk)" 
                 and v_hit_in_L: "v_hit ∈ set (enumL as s kk)"
    using hit by blast
  obtain v_miss where v_miss_in_R: "v_miss ∈ set (enumR as s kk)"
                  and v_miss_not_L: "v_miss ∉ set (enumL as s kk)"
    using miss by blast
  
  have distinct_R: "distinct (enumR as s kk)" by (simp add: enumR_def)
  
  (* Pick which value to use based on current state *)
  define target where "target = (if good as s ((!) (enc as s kk)) ((!) (enc as s kk))
                                  then v_miss else v_hit)"
  
  (* Build new oracle that puts target in block jR *)
  define bits where "bits = to_bits (W as s) target"

  have target_in: "target ∈ set (enumR as s kk)"
    using target_def v_hit_in_R v_miss_in_R by auto

  have target_in_union: "target ∈ set (enumL as s kk) ∪ set (enumR as s kk)"
    using target_in by auto

  have bits_len: "length bits = W as s"
    using bits_roundtrip[OF target_in_union] bits_def by blast

  have bits_val: "from_bits bits = target"
    using bits_roundtrip[OF target_in_union] bits_def by blast
  
  define oR' where "oR' i = (
    let base = length (enc0 as s) + offR as s kk jR in
    if base ≤ i ∧ i < base + W as s 
    then bits ! (i - base)
    else (enc as s kk) ! i)" for i
  
  have outside_same: "⋀i. i ∉ blockR_abs enc0 as s kk jR ⟹ oR' i = (enc as s kk) ! i"
    by (auto simp: oR'_def blockR_abs_def)
  
  have Rval_changed: "Rval_at as s oR' jR = target"
  proof -
    define base where "base = length (enc0 as s) + offR as s kk jR"
  
    have map_eq: "map oR' [base ..< base + W as s] = bits"
    proof (rule nth_equalityI)
      show "length (map oR' [base ..< base + W as s]) = length bits"
        using bits_len by simp
    next
      fix i assume "i < length (map oR' [base ..< base + W as s])"
      hence i_lt: "i < W as s" by simp
      have "map oR' [base ..< base + W as s] ! i = oR' (base + i)"
        using i_lt by simp
      also have "... = bits ! i"
        using i_lt by (simp add: oR'_def base_def Let_def)
      finally show "map oR' [base ..< base + W as s] ! i = bits ! i" .
    qed
  
    show ?thesis
      unfolding Rval_at_def base_def[symmetric]
      using map_eq bits_val by simp
  qed
  
  have good_flips: "good as s ((!) (enc as s kk)) oR' ≠ 
                    good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
  proof (cases "good as s ((!) (enc as s kk)) ((!) (enc as s kk))")
    case True
    (* Was good, now make it bad by putting v_miss *)
    have "target = v_miss" using True target_def by simp
    hence val_miss: "Rval_at as s oR' jR = v_miss" using Rval_changed by simp
  
    (* v_miss doesn't match any LHS value *)
    have "∀jL < length (enumL as s kk). Lval_at as s ((!) (enc as s kk)) jL ≠ v_miss"
    proof (intro allI impI)
      fix jL assume "jL < length (enumL as s kk)"
      have "Lval_at as s ((!) (enc as s kk)) jL = enumL as s kk ! jL"
        by (rule Lval_at_on_enc_block[OF ‹jL < length (enumL as s kk)›])
      thus "Lval_at as s ((!) (enc as s kk)) jL ≠ v_miss"
        using v_miss_not_L by (metis in_set_conv_nth ‹jL < length (enumL as s kk)›)
    qed
  
    (* After flip, position jR can't match anything *)
    hence no_match_jR: "∀jL < length (enumL as s kk). 
                        Lval_at as s ((!) (enc as s kk)) jL ≠ Rval_at as s oR' jR"
      using val_miss by fastforce
  
    (* Show good becomes false *)
    have "¬ good as s ((!) (enc as s kk)) oR'"
    proof
      assume "good as s ((!) (enc as s kk)) oR'"
      then obtain jL jR' where 
        jL_bound: "jL < length (enumL as s kk)" and
        jR'_bound: "jR' < length (enumR as s kk)" and
        match: "Lval_at as s ((!) (enc as s kk)) jL = Rval_at as s oR' jR'"
        unfolding good_def by blast
      
      show False
      proof (cases "jR' = jR")
        case True
        (* Match at the flipped block contradicts no_match_jR *)
        have "Lval_at as s ((!) (enc as s kk)) jL ≠ Rval_at as s oR' jR"
          using no_match_jR jL_bound by blast
        thus False using match True by simp
      next
        case False
        (* Match at a different block - this block is unchanged from original *)
        have "Rval_at as s oR' jR' = Rval_at as s ((!) (enc as s kk)) jR'"
          using Rval_at_unchanged_other_blocks[OF jR_bound jR'_bound False] outside_same
          by blast
        
        (* So the match existed in the original, contradicting True *)
        have "Lval_at as s ((!) (enc as s kk)) jL = Rval_at as s ((!) (enc as s kk)) jR'"
          using match by (simp add: ‹Rval_at as s oR' jR' = Rval_at as s ((!) (enc as s kk)) jR'›)
        hence "good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
          unfolding good_def using jL_bound jR'_bound by blast
        thus False using True by simp
      qed
    qed
    
    thus ?thesis using True by simp
  
  next
    case False
    (* Was bad, now make it good by putting v_hit *)
    have "target = v_hit" using False target_def by simp
    hence val_hit: "Rval_at as s oR' jR = v_hit" using Rval_changed by simp
  
    (* v_hit matches some LHS value *)
    have "∃jL < length (enumL as s kk). Lval_at as s ((!) (x0 as s)) jL = v_hit"
    proof -
      have "v_hit ∈ set (enumL as s kk)" using v_hit_in_L .
      then obtain jL where "jL < length (enumL as s kk)" 
                   and "enumL as s kk ! jL = v_hit"
        by (meson in_set_conv_nth)
      have "Lval_at as s ((!) (x0 as s)) jL = enumL as s kk ! jL"
        by (rule Lval_at_on_enc_block[OF ‹jL < length (enumL as s kk)›])
      show ?thesis
        using ‹Lval_at as s ((!) (x0 as s)) jL = enumL as s kk ! jL› 
              ‹enumL as s kk ! jL = v_hit› ‹jL < length (enumL as s kk)› 
        by auto
    qed
  
    (* So position jR now matches something *)
    then obtain jL where jL_bound: "jL < length (enumL as s kk)"
                  and match: "Lval_at as s ((!) (enc as s kk)) jL = v_hit"
      by blast
  
    have "Lval_at as s ((!) (enc as s kk)) jL = Rval_at as s oR' jR"
      using val_hit match by simp
  
    (* This witness proves good is true after flip *)
    hence "good as s ((!) (enc as s kk)) oR'"
      unfolding good_def using jL_bound jR_bound by blast
  
    (* But it was false before, so they differ *)
    thus ?thesis using False by simp
  qed
  
  show ?thesis
  proof (intro exI[of _ oR'] conjI)
    show "∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ oR' i = (enc as s kk) ! i"
      using outside_same by blast
    show "good as s ((!) (enc as s kk)) oR' ≠ 
          good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
      using good_flips .
  qed
qed

(* Symmetric R-block contradiction theorem *)
theorem coverage_by_oracle_contradiction_R:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
      and miss_block: "∃jR. jR < length (enumR as s kk) ∧
                            Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
  shows False
proof -
  (* Get the unread block *)
  obtain jR where 
    jR_bound: "jR < length (enumR as s kk)" and
    jR_unread: "Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
    using miss_block by blast
  
  (* For the oracle flip to work, we need these conditions *)
  have two_rhs: "2 ≤ card (set (enumR as s kk))"
  proof -
    have "card (set (enumR as s kk)) = card (RHS (e_k as s kk) n)"
      using len by simp
    also have "... = 2 ^ (n - kk)"
    proof -
      have "kk ≤ n" using kk_bounds by simp
      then show ?thesis
        by (simp add: card_RHS_e_k distinct len)
    qed
    also have "... ≥ 2"
      using kk_bounds n_ge2 nat_le_real_less by force
    finally show ?thesis .
  qed
  
  (* Get flipped oracle *)
  obtain oR' where
    outside_same_obj: "∀i. i ∉ blockR_abs enc0 as s kk jR ⟶ 
                         oR' i = (enc as s kk) ! i" and
    good_flips: "good as s ((!) (enc as s kk)) oR' ≠ 
               good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using oracle_flip_changes_good_R[OF jR_bound two_rhs hit miss] by blast
  
  (* Convert to meta-level *)
  have outside_same: "⋀i. i ∉ blockR_abs enc0 as s kk jR ⟹ oR' i = (enc as s kk) ! i"
    using outside_same_obj by blast
  
  (* Tree doesn't see the flipped block *)
  have unseen: "seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ∩ 
              blockR_abs enc0 as s kk jR = {}"
    using unread_block_unseen_R[OF jR_unread] .
  
  (* Therefore tree gives same answer with oR' *)
  have L_agree: "⋀i. i ∈ seenL_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ⟹ 
                 ((!) (enc as s kk)) i = ((!) (enc as s kk)) i"
    by simp
  
  have R_agree: "⋀j. j ∈ seenR_run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s) ⟹ 
                   oR' j = (enc as s kk) ! j"
    using unseen outside_same by blast
  
  have "run ((!) (enc as s kk)) oR' (T as s) = 
      run ((!) (enc as s kk)) ((!) (enc as s kk)) (T as s)"
    by (rule run_agree_on_seen(1)[symmetric, 
      where oL="((!) (enc as s kk))" 
        and oL'="((!) (enc as s kk))"
        and oR="((!) (enc as s kk))"
        and oR'="oR'"
        and T="T as s"];
      auto simp: R_agree)
  
  (* But the tree must give correct answers *)
  hence "good as s ((!) (enc as s kk)) oR' = 
         good as s ((!) (enc as s kk)) ((!) (enc as s kk))"
    using correct_T by (meson correctness)
  
  (* Contradiction! *)
  with good_flips show False by contradiction
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
proof (rule ccontr)
  assume "¬(∀jR<length (enumR as s kk). 
              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {})"
  hence "∃jR. jR < length (enumR as s kk) ∧
              Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}" by simp
  thus False 
    using coverage_by_oracle_contradiction_R[OF n_ge2 kk_bounds distinct len hit miss]
    by blast
qed

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

(* Combined coverage theorem with mutual unread assumptions *)
theorem coverage_blocks_v2:
  assumes n_ge2: "n ≥ 2"
      and kk_bounds: "1 ≤ kk" "kk < n"
      and kk_slack: "2 * kk < n"  (* ADD THIS LINE *)
      and distinct: "distinct_subset_sums as"
      and len: "length as = n"
      and hit_L: "∃v ∈ set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss_L: "∃v ∈ set (enumL as s kk). v ∉ set (enumR as s kk)"
      and hit_R: "∃v ∈ set (enumR as s kk). v ∈ set (enumL as s kk)"
      and miss_R: "∃v ∈ set (enumR as s kk). v ∉ set (enumL as s kk)"
  shows "(∃jL < length (enumL as s kk). 
            Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {}) ∨
         (∃jR < length (enumR as s kk). 
            Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {})"
proof (rule ccontr)
  assume neg: "¬((∃jL < length (enumL as s kk). 
                    Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL ≠ {}) ∨
                 (∃jR < length (enumR as s kk). 
                    Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR ≠ {}))"
  
  (* Both sides are unread *)
  have all_L_unread: "∀jL < length (enumL as s kk). 
                       Base.read0 M (enc as s kk) ∩ blockL_abs enc0 as s jL = {}"
    using neg by simp
  have all_R_unread: "∀jR < length (enumR as s kk). 
                       Base.read0 M (enc as s kk) ∩ blockR_abs enc0 as s kk jR = {}"
    using neg by simp
  
  (* This contradicts coverage for L-blocks *)
  show False
    using coverage_by_oracle_contradiction_v2[OF n_ge2 kk_bounds kk_slack distinct len 
                                                hit_L miss_L _ all_R_unread]
    using all_L_unread
    by (meson length_pos_if_in_set miss_L)
qed

end  (* context Coverage_TM *)

end  (* theory *)
