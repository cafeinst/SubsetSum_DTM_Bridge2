theory SubsetSum_DTM_Bridge2
  imports "SubsetSum_DecisionTree" "SubsetSum_DTM_Bridge"
begin

context Coverage_TM
begin

lemma run_drive_T0:
  "run oL oR (T0 as s)
   = final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) oL)"
  by (simp add: run_tm_to_dtr' T0_def)

lemma Run_unread_R:
  fixes x y :: "bool list"
  assumes DISJ:  "Base.read0 M x ∩ blockR_abs enc0 as s kk j = {}"
  assumes AGREE: "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = x ! i"
  assumes X:     "x = enc as s kk"
  shows "run ((!) x) ((!) y) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
proof -
  have SRsub: "seenR_run ((!) x) ((!) y) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenR_T0_subset_read0[OF X])
  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) x) ((!) y) (T0 as s) ⟹ (!) y i = (!) x i"
  proof -
    fix i assume "i ∈ seenR_run ((!) x) ((!) y) (T0 as s)"
    with SRsub have "i ∈ Base.read0 M x" by blast
    with DISJ have "i ∉ blockR_abs enc0 as s kk j" by auto
    with AGREE show "(!) y i = (!) x i" by simp
  qed
  show ?thesis
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) x) ((!) y) (T0 as s) ⟹ (!) x i = (!) x i" by simp
  next
    show "⋀i. i ∈ seenR_run ((!) x) ((!) y) (T0 as s) ⟹ (!) y i = (!) x i"
      by (rule agree_on_seenR)
  qed
qed

lemma blockR_pairwise_disjoint:
  assumes jR:  "j  < length (enumR as s kk)"
      and j'R: "j' < length (enumR as s kk)"
      and ne:  "j ≠ j'"
  shows "blockR_abs enc0 as s kk j ∩ blockR_abs enc0 as s kk j' = {}"
  using ne
  by (rule blockR_abs_disjoint)

lemma coverage_for_enc_blocks_L:
  assumes hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
      and miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
      and baseline_only_j:
        "⋀j. Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟹
             (∀j'<length (enumL as s kk). j' ≠ j ⟶
                Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
  shows "∀j<length (enumL as s kk). touches (x0 as s) (blockL_abs enc0 as s j)"
proof (intro allI impI)
  fix j assume jL: "j < length (enumL as s kk)"
  let ?x = "x0 as s"
  show "touches ?x (blockL_abs enc0 as s j)"
  proof (rule ccontr)
    assume NT: "¬ touches ?x (blockL_abs enc0 as s j)"
    then have not_touch:
      "Base.read0 M ?x ∩ blockL_abs enc0 as s j = {}"
      by (simp add: touches_def)

    define a where "a = length (enc0 as s) + offL as s j"
    define w where "w = W as s"
    have blk_repr: "blockL_abs enc0 as s j = {a ..< a + w}"
      by (simp add: a_def w_def blockL_abs_def offL_def)

    have X0: "?x = x0 as s" by simp

    consider (G) "Good as s ((!) ?x) ((!) ?x)"
           | (NG) "¬ Good as s ((!) ?x) ((!) ?x)" by blast
    then show False
    proof cases
      case G
      from miss obtain v_out where
        vL:  "v_out ∈ set (enumL as s kk)" and
        vNR: "v_out ∉ set (enumR as s kk)"
        by blast

      obtain pat where
        pat_len: "length pat = w" and
        pat_val: "from_bits pat = v_out"
        using vL bits_roundtrip w_def by blast

      define oL' where
        "oL' i = (if i ∈ {a ..< a + w} then pat ! (i - a) else ?x ! i)" for i
      define y where "y = splice a w ?x (map oL' [a ..< a + w])"

      have LEN: "length (map oL' [a ..< a + w]) = w" by simp
      have AL: "a ≤ length ?x"
        using offL_window_in_enc[OF jL] by (simp add: a_def w_def)

      have outside_y:
        "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockL_abs enc0 as s j"
        from nin blk_repr have nin': "i < a ∨ ¬ i < a + w" by auto
        show "y ! i = ?x ! i"
        proof (cases "i < a")
          case True
          with AL show ?thesis by (simp add: y_def splice_nth_left)
        next
          case False
          with nin' have "¬ i < a + w" by simp
          with AL LEN show ?thesis
            using y_def splice_nth_right
            by (simp add: a_def jL offL_window_in_enc w_def)
        qed
      qed

      have slice_pat: "map oL' [a ..< a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oL' [a ..< a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oL' [a ..< a + w])"
        hence tw: "t < w" by simp
        have idx: "[a ..< a + w] ! t = a + t" using tw by simp
        show "map oL' [a ..< a + w] ! t = pat ! t"
          by (simp add: oL'_def idx tw)
      qed

      (* compute the left value at block j directly from the slice *)
      have Lj_y: "Lval_at as s ((!) y) j = v_out"
        unfolding Lval_at_def a_def w_def
        using slice_pat pat_val G Good_char_encR 
          baseline_only_j nat_neq_iff by blast

      (* show y's other L-blocks match x0's *)
      have Good_y: "¬ Good as s ((!) y) ((!) ?x)"
      proof -
        have "Lval_at as s ((!) y) j ∉ set (enumR as s kk)"
          using Lj_y vNR by simp
        moreover have
          "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j ⟹
             Lval_at as s ((!) y) j' ∉ set (enumR as s kk)"
        proof -
          fix j' assume j'lt: "j' < length (enumL as s kk)" and ne: "j' ≠ j"

          define a' where "a' = length (enc0 as s) + offL as s j'"
          define w' where "w' = W as s"
          have blk': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
            by (simp add: a'_def w'_def blockL_abs_def offL_def)

          have disj:
            "blockL_abs enc0 as s j ∩ blockL_abs enc0 as s j' = {}"
            using blockL_abs_disjoint[OF ne] by blast

          have eq_on:
            "⋀i. i ∈ blockL_abs enc0 as s j' ⟹ y ! i = ?x ! i"
            using outside_y disj by blast

          have slices_eq:
            "map ((!) y) [a' ..< a' + w'] = map ((!) (x0 as s)) [a' ..< a' + w']"
          proof (rule nth_equalityI)
            show "length (map ((!) y) [a' ..< a' + w']) =
                  length (map ((!) (x0 as s)) [a' ..< a' + w'])" by simp
          next
            fix t assume "t < length (map ((!) y) [a' ..< a' + w'])"
            hence tw': "t < w'" by simp
            have idx': "[a' ..< a' + w'] ! t = a' + t" using tw' by simp
            have mem: "a' + t ∈ blockL_abs enc0 as s j'"
              by (simp add: blk' tw')
            show "map ((!) y) [a' ..< a' + w'] ! t =
                  map ((!) (x0 as s)) [a' ..< a' + w'] ! t"
              by (simp add: idx' tw' eq_on[OF mem])
          qed

          have eq_other:
            "Lval_at as s ((!) y) j' = Lval_at as s ((!) (x0 as s)) j'"
            using Lval_at_def a'_def w'_def slices_eq
            by presburger

          from baseline_only_j[OF G, of j'] j'lt ne
          show "Lval_at as s ((!) y) j' ∉ set (enumR as s kk)"
            using eq_other G baseline_only_j by presburger
        qed
        ultimately show ?thesis
          using Good_char_encR by blast
      qed

      have unread_eq:
        "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
        using G Good_char_encR baseline_only_j linorder_neq_iff by blast
      from unread_eq G Good_y show False by simp

    next
      case NG
      from hit obtain v_in where
        vL: "v_in ∈ set (enumL as s kk)" and vR: "v_in ∈ set (enumR as s kk)"
        by blast

      obtain pat where
        pat_len: "length pat = w" and
        pat_val: "from_bits pat = v_in"
        using vL bits_roundtrip w_def by blast

      define oL' where
        "oL' i = (if i ∈ {a ..< a + w} then pat ! (i - a) else ?x ! i)" for i
      define y where "y = splice a w ?x (map oL' [a ..< a + w])"

      have LEN: "length (map oL' [a ..< a + w]) = w" by simp
      have AL: "a ≤ length ?x"
        using offL_window_in_enc[OF jL] by (simp add: a_def w_def)

      have outside_y:
        "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockL_abs enc0 as s j"
        from nin blk_repr have nin': "i < a ∨ ¬ i < a + w" by auto
        show "y ! i = ?x ! i"
        proof (cases "i < a")
          case True
          with AL show ?thesis by (simp add: y_def splice_nth_left)
        next
          case False
          with nin' have "¬ i < a + w" by simp
          with AL LEN show ?thesis
            using y_def splice_nth_right
            by (simp add: a_def jL offL_window_in_enc w_def)
        qed
      qed

      have slice_pat: "map oL' [a ..< a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oL' [a ..< a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oL' [a ..< a + w])"
        hence tw: "t < w" by simp
        have idx: "[a ..< a + w] ! t = a + t" using tw by simp
        show "map oL' [a ..< a + w] ! t = pat ! t"
          by (simp add: oL'_def idx tw)
      qed

      have Lj_y: "Lval_at as s ((!) y) j = v_in"
        unfolding Lval_at_def a_def w_def
        using slice_pat pat_val
        by (smt (verit) ‹oL' ≡ λi. if i ∈ {a..<a + w} 
        then pat ! (i - a) else x0 as s ! i› a_def add_less_cancel_left 
            blk_repr jL length_map map_equality_iff nat_le_linear nth_upt 
            offL_window_in_enc outside_y pat_len splice_nth_inside 
            trans_le_add1 w_def x0_is_enc y_def)

      have Good_y: "Good as s ((!) y) ((!) ?x)"
      proof -
        have "Lval_at as s ((!) y) j ∈ set (enumR as s kk)"
          using Lj_y vR by simp
        hence "∃jL<length (enumL as s kk).
                 Lval_at as s ((!) y) jL ∈ set (enumR as s kk)"
          using jL by blast
        thus ?thesis using Good_char_encR by simp
      qed

      have unread_eq:
        "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
        using Good_def Lval_at_on_enc_block NG Rval_at_on_enc_block 
              good_def in_set_conv_nth vL vR by metis
      from unread_eq Good_y NG show False by simp
    qed
  qed
qed

(* sums over subsets, as in your development *)
definition sum_over :: "int list ⇒ nat set ⇒ int" where
  "sum_over as S = (∑ i∈S. as ! i)"

(* 1) The 0/1 mask built from a set S is a bitvector *)
lemma mask_is_bitvec:
  fixes S :: "nat set" and n :: nat
  defines "xs ≡ map (λi. if i ∈ S then (1::int) else 0) [0..<n]"
  shows   "xs ∈ bitvec n"
  unfolding bitvec_def xs_def by auto

(* 2) Masked prefix-sum equals the set-sum over S, provided S ⊆ {..<n} *)
lemma masked_sum_eq_sum_over:
  fixes as :: "int list" and n :: nat and S :: "nat set"
  defines "xs ≡ map (λi. if i ∈ S then (1::int) else 0) [0..<n]"
  assumes Ssub: "S ⊆ {..<n}"
  shows "(∑ i < n. as ! i * xs ! i) = sum_over as S"
proof -
  have "(∑ i < n. as ! i * xs ! i)
        = (∑ i < n. as ! i * (if i ∈ S then 1 else 0))"
    by (simp add: xs_def)
  also have "... = (∑ i < n. if i ∈ S then as ! i else 0)"
    by (metis (mono_tags, opaque_lifting) mult_cancel_left1 mult_zero_right)
  also have "... = (∑ i∈S ∩ {0..<n}. as ! i)"
    by (simp add: sum.If_cases Int_commute atLeast0LessThan)
  also from Ssub have "... = (∑ i∈S. as ! i)"
    using Int_absorb2 by (metis lessThan_atLeast0)
  finally show ?thesis
    by (simp add: sum_over_def)
qed

(* 3) Two sets version, convenient when you define both masks at once *)
lemma masked_sums_eq_sum_over_both:
  fixes as :: "int list" and n :: nat and S T :: "nat set"
  defines "xs ≡ map (λi. if i ∈ S then (1::int) else 0) [0..<n]"
      and "ys ≡ map (λi. if i ∈ T then (1::int) else 0) [0..<n]"
  assumes Ssub: "S ⊆ {..<n}" and Tsub: "T ⊆ {..<n}"
  shows "(∑ i < n. as ! i * xs ! i) = sum_over as S"
    and "(∑ i < n. as ! i * ys ! i) = sum_over as T"
proof-
  show "(∑ i < n. as ! i * xs ! i) = sum_over as S"
  proof -
    have "(∑ i < n. as ! i * (map (λi. if i ∈ S then (1::int) else 0) [0..<n]) ! i)
          = sum_over as S"
      by (rule masked_sum_eq_sum_over[OF Ssub])
    thus ?thesis by (simp add: xs_def)
  qed
next
  show "(∑ i < n. as ! i * ys ! i) = sum_over as T"
  proof -
    have "(∑ i < n. as ! i * (map (λi. if i ∈ T then (1::int) else 0) [0..<n]) ! i)
          = sum_over as T"
      by (rule masked_sum_eq_sum_over[OF Tsub])
    thus ?thesis by (simp add: ys_def)
  qed
qed

lemma distinct_subset_sums_inj:
  fixes as :: "int list" and n :: nat
  assumes sep:
    "⋀xs ys. xs ∈ bitvec n ⟹ ys ∈ bitvec n ⟹ xs ≠ ys
             ⟹ (∑ i<n. as ! i * xs ! i) ≠ (∑ i<n. as ! i * ys ! i)"
  shows "inj_on (sum_over as) {U. U ⊆ {..<n}}"
proof (rule inj_onI)
  fix S T
  assume Sin: "S ∈ {U. U ⊆ {..<n}}"
  assume Tin: "T ∈ {U. U ⊆ {..<n}}"
  assume eqS: "sum_over as S = sum_over as T"

  from Sin have Ssub: "S ⊆ {..<n}" by simp
  from Tin have Tsub: "T ⊆ {..<n}" by simp

  define xs where "xs = map (λi. if i ∈ S then (1::int) else 0) [0..<n]"
  define ys where "ys = map (λi. if i ∈ T then (1::int) else 0) [0..<n]"

  have xs_bv: "xs ∈ bitvec n" and ys_bv: "ys ∈ bitvec n"
    by (simp_all add: mask_is_bitvec xs_def ys_def)

  have sums_eq:
    "(∑ i < n. as ! i * xs ! i) = (∑ i < n. as ! i * ys ! i)"
  proof -
    have L: "(∑ i < n. as ! i * xs ! i) = sum_over as S"
      unfolding xs_def by (rule masked_sum_eq_sum_over[OF Ssub])
    have R: "(∑ i < n. as ! i * ys ! i) = sum_over as T"
      unfolding ys_def by (rule masked_sum_eq_sum_over[OF Tsub])
    from L R eqS show ?thesis by simp
  qed

  have xs_eq_ys: "xs = ys"
  proof (rule ccontr)
    assume "xs ≠ ys"
    from sep xs_bv ys_bv
      have "xs ≠ ys ⟶ (∑ i < n. as ! i * xs ! i) ≠ (∑ i < n. as ! i * ys ! i)" by blast
    hence "(∑ i < n. as ! i * xs ! i) ≠ (∑ i < n. as ! i * ys ! i)"
      using ‹xs ≠ ys› by blast
    thus False using sums_eq by contradiction
  qed

  have mem_eq: "⋀i. i < n ⟹ (i ∈ S) = (i ∈ T)"
  proof -
    fix i assume iLt: "i < n"
    have "xs ! i = ys ! i" using xs_eq_ys by simp
    hence "(if i ∈ S then (1::int) else 0) = (if i ∈ T then 1 else 0)"
      using xs_def ys_def nth_upt iLt by simp
    thus "(i ∈ S) = (i ∈ T)" by (cases "i ∈ S"; cases "i ∈ T"; simp)
  qed

  have ST: "S ⊆ T"
  proof
    fix i assume "i ∈ S"
    from Ssub ‹i ∈ S› have "i < n" by auto
    with mem_eq[OF this] ‹i ∈ S› show "i ∈ T" by simp
  qed
  have TS: "T ⊆ S"
  proof
    fix i assume "i ∈ T"
    from Tsub ‹i ∈ T› have "i < n" by auto
    with mem_eq[OF this] ‹i ∈ T› show "i ∈ S" by simp
  qed

  show "S = T" by (rule subset_antisym[OF ST TS])
qed

(*
  Guarded definition: NEVER expose xs ! i when i ≥ length xs.
  If you already have sum_as_on, replace its body with this guarded one.
*)
definition sum_as_on :: "int list ⇒ nat set ⇒ int list ⇒ int" where
  "sum_as_on as S xs = (∑ i∈S. as ! i * (if i < length xs then xs ! i else 0))"

definition sum_as_on_local where
  "sum_as_on_local as I xs ≡ sum_as_on as I xs"

definition LHS_local where
  "LHS_local E n ≡ SubsetSum_DecisionTree.LHS E n"

definition RHS_local where
  "RHS_local E n ≡ SubsetSum_DecisionTree.RHS E n"

lemma bitvec_length[simp]:
  assumes "xs ∈ bitvec n"
  shows "length xs = n"
  using assms by (auto simp: bitvec_def)

lemma sum_as_on_guarded_set:
  assumes "xs ∈ bitvec n"
  shows
    "sum_as_on_local as {0..<kk} xs
     = (∑ i∈{0..<kk}. as ! i * (if i < n then xs ! i else 0))"
  unfolding sum_as_on_local_def sum_as_on_def
  using assms by simp

lemma set_to_bounded_sum:
  "(∑ i∈{0..<kk}. f i) = (∑ i = 0..<kk. f i)"
  by (simp add: atLeast0LessThan)

lemma sum_as_on_guarded:
  assumes "xs ∈ bitvec n"
  shows
    "sum_as_on_local as {0..<kk} xs
     = (∑ i = 0..<kk. as ! i * (if i < n then xs ! i else 0))"
  using sum_as_on_guarded_set[OF assms]
  by (simp add: atLeast0LessThan)

lemma sum_as_on_guarded_DT:
  assumes "xs ∈ bitvec n" and "kk ≤ n"
  shows
    "SubsetSum_DecisionTree.sum_as_on as {0..<kk} xs
     = (∑ i∈{0..<kk}. as ! i * (if i < n then xs ! i else 0))"
  using assms
  unfolding SubsetSum_DecisionTree.sum_as_on_def
  by (simp)   (* now i<kk implies i<n, so the guard is redundant *)

lemma sum_as_on_guarded_bounded:
  assumes xs: "xs ∈ bitvec n"
  shows "sum_as_on_local as {0..<kk} xs
       = (∑ i = 0..<kk. as ! i * (if i < n then xs ! i else 0))"
  using sum_as_on_guarded[OF xs] by (simp add: atLeast0LessThan)

lemma sum_guarded_I:
  assumes "xs ∈ bitvec n" "kk ≤ n"
  shows "(∑ i = 0..<kk. as ! i * xs ! i)
       = (∑ i = 0..<kk. as ! i * (if i < n then xs ! i else 0))"
  using assms
  by (intro sum.cong) (auto dest: less_le_trans)

lemma sum_as_on_guarded_DT_prefix_bounded:
  fixes n :: nat
  assumes xs: "xs ∈ bitvec n" and le: "kk ≤ n"
  shows
    "SubsetSum_DecisionTree.sum_as_on as {0..<kk} xs
     = (∑ i = 0..<kk. as ! i * xs ! i)"
  unfolding SubsetSum_DecisionTree.sum_as_on_def
  by (simp add: bitvec_length[OF xs] atLeast0LessThan le)

lemma sum_as_on_guarded_DT_prefix:
  fixes n :: nat
  assumes xs: "xs ∈ bitvec n" and le: "kk ≤ n"
  shows "SubsetSum_DecisionTree.sum_as_on as {0..<kk} xs
       = (∑ i∈{0..<kk}. as ! i * (if i < n then xs ! i else 0))"
  using assms
  unfolding SubsetSum_DecisionTree.sum_as_on_def
  by (simp add: bitvec_length[OF xs])

lemma LHS_char_bounded:
  assumes le: "kk ≤ length as"
  shows "v ∈ LHS (e_k as s kk) (length as)
         ⟷ (∃L ⊆ {..<kk}. sum_over as L = v)"
proof -
  let ?n = "length as"

  have LHS_exp:
    "v ∈ LHS (e_k as s kk) ?n
     ⟷ (∃xs∈bitvec ?n. v = (∑ i = 0..<kk. as ! i * xs ! i))"
    unfolding SubsetSum_DecisionTree.LHS_def
              SubsetSum_DecisionTree.e_k_def
              SubsetSum_DecisionTree.lhs_of_def
              SubsetSum_DecisionTree.sum_as_on_def
    by (simp add: Bex_def conj_commute)

  show ?thesis
  proof
    assume "v ∈ LHS (e_k as s kk) ?n"
    then obtain xs where xs: "xs ∈ bitvec ?n"
      and vdef: "v = (∑ i = 0..<kk. as ! i * xs ! i)"
      using LHS_exp by blast

    from xs have len:  "length xs = ?n"            using bitvec_def by blast
    from xs have xs01: "set xs ⊆ ({0,1}::int set)" using bitvec_def by blast

    have "(∑ i = 0..<kk. as ! i * xs ! i)
          = (∑ i∈{0..<kk}. as ! i * (if i < ?n then xs ! i else 0))"
      using xs le by (simp add: atLeast0LessThan sum_guarded_I)
    also have "... = (∑ i∈{0..<kk}. as ! i * xs ! i)"
      using le by (intro sum.cong[OF refl]) auto
    finally have v': "v = (∑ i∈{0..<kk}. as ! i * xs ! i)"
      using vdef by simp

    define L where "L = {i∈{0..<kk}. xs ! i = 1}"
    have Lsub: "L ⊆ {..<kk}" using L_def by auto

    have "(∑ i∈{0..<kk}. as ! i * xs ! i)
      = (∑ i∈{0..<kk}. if i∈L then as ! i else 0)"
    proof (rule sum.cong[OF refl])
      fix i assume iin: "i ∈ {0..<kk}"
      have i_lt: "i < kk" using iin by simp
      have i_lt_n: "i < ?n" using le i_lt by (meson less_le_trans)
      have xi_in01: "xs ! i ∈ ({0,1}::int set)"
        using xs01 len i_lt_n nth_mem
        by (metis in_mono)

      have i_in_L_eq: "(i∈L) ⟷ xs ! i = 1"
        using i_lt by (simp add: L_def)

      show "as ! i * xs ! i = (if i∈L then as ! i else 0)"
      proof (cases "xs ! i = 1")
        case True
        with i_in_L_eq show ?thesis by simp
      next
        case False
        from xi_in01 False have "xs ! i = 0" by auto
        with i_in_L_eq False show ?thesis by simp
      qed
    qed
    also have "... = (∑ i∈{0..<kk} ∩ L. as ! i)"
      by (simp add: sum.If_cases)
    also from Lsub have "... = (∑ i∈L. as ! i)"
      by (simp add: inf.absorb_iff2 lessThan_atLeast0)
    also have "... = sum_over as L"
      by (simp add: sum_over_def)
    finally have "sum_over as L = v"
    using v' ‹(∑i = 0..<kk. as ! i * xs ! i) = (∑i = 0..<kk. if i ∈ L then as ! i else 0)› 
      ‹(∑i = 0..<kk. if i ∈ L then as ! i else 0) = sum ((!) as) ({0..<kk} ∩ L)› 
      ‹sum ((!) as) ({0..<kk} ∩ L) = sum ((!) as) L› ‹sum ((!) as) L = sum_over as L› 
    by argo
    thus "∃L ⊆ {..<kk}. sum_over as L = v" using Lsub by blast
  next
    assume "∃L ⊆ {..<kk}. sum_over as L = v"
    then obtain L where Lsub: "L ⊆ {..<kk}" and vdef: "sum_over as L = v" by blast

    define xs where "xs = map (λi. if i∈L then (1::int) else 0) [0..<?n]"
    have xs_bv: "xs ∈ bitvec ?n" by (simp add: xs_def mask_is_bitvec)

    have "(∑ i = 0..<kk. as ! i * xs ! i)
          = (∑ i∈{0..<kk}. as ! i * xs ! i)"
      by (simp add: atLeast0LessThan)
    also have "... = (∑ i∈{0..<kk}. as ! i * (if i ∈ L then 1 else 0))"
    proof (rule sum.cong[OF refl])
      fix i assume i: "i ∈ {0..<kk}"
      from i have iK: "i < kk" by simp
      from iK le have iN: "i < ?n" by (meson less_le_trans)
      have xs_i: "xs ! i = (if i ∈ L then 1 else 0)"
        by (simp add: xs_def iN)
      show "as ! i * xs ! i = as ! i * (if i ∈ L then 1 else 0)"
        by (simp add: xs_i)
    qed
    also have "... = (∑ i∈{0..<kk} ∩ L. as ! i)"
    proof -
      have "(∑ i∈{0..<kk}. as ! i * (if i ∈ L then 1 else 0))
        = (∑ i∈{0..<kk}. (if i ∈ L then as ! i else 0))"
        by (metis (mono_tags, opaque_lifting) mult.comm_neutral times_int_code(1))
      also have "... = (∑ i∈{0..<kk} ∩ L. as ! i)"
        by (simp add: sum.If_cases)
      finally show ?thesis .
    qed
    also have "... = (∑ i∈L. as ! i)"
    proof -
      have "{0..<kk} ∩ L = L" using Lsub by auto
      thus ?thesis by simp
    qed
    also have "... = sum_over as L"
      by (simp add: sum_over_def)
    finally have "(∑ i = 0..<kk. as ! i * xs ! i) = v"
      using vdef ‹(∑i = 0..<kk. as ! i * (if i ∈ L then 1 else 0)) = 
        sum ((!) as) ({0..<kk} ∩ L)› ‹(∑i = 0..<kk. as ! i * xs ! i) = 
        (∑i = 0..<kk. as ! i * (if i ∈ L then 1 else 0))› 
        ‹sum ((!) as) ({0..<kk} ∩ L) = sum ((!) as) L› 
        ‹sum ((!) as) L = sum_over as L› by presburger
    hence "∃xs∈bitvec ?n. v = (∑ i = 0..<kk. as ! i * xs ! i)"
      using xs_bv by blast
    thus "v ∈ LHS (e_k as s kk) ?n"
      unfolding SubsetSum_DecisionTree.LHS_def
                SubsetSum_DecisionTree.e_k_def
                SubsetSum_DecisionTree.lhs_of_def
                SubsetSum_DecisionTree.sum_as_on_def
      by (simp add: Bex_def conj_commute)
  qed
qed

lemma LHS_char:
  assumes "kk ≤ length as"
  shows   "v ∈ LHS (e_k as s kk) (length as) ⟷ (∃L ⊆ {..<kk}. sum_over as L = v)"
  using LHS_char_bounded[OF assms] .

lemma RHS_char_bounded:
  assumes le: "kk ≤ length as"
  shows
    "v ∈ RHS (e_k as s kk) (length as)
     ⟷ (∃T ⊆ {kk..<length as}. sum_over as T = s - v)"
proof -
  let ?n = "length as"

  have RHS_exp:
    "v ∈ RHS (e_k as s kk) ?n
     ⟷ (∃xs∈bitvec ?n. v = s - (∑ i=kk..<?n. as ! i * xs ! i))"
    unfolding SubsetSum_DecisionTree.RHS_def
              SubsetSum_DecisionTree.e_k_def
              SubsetSum_DecisionTree.rhs_of_def
              SubsetSum_DecisionTree.sum_as_on_def
    by (simp add: Bex_def conj_commute atLeastLessThan_def)

  show ?thesis
  proof
    (* ⇒ : read off T from the 0/1 vector on the suffix kk..<n *)
    assume "v ∈ RHS (e_k as s kk) ?n"
    then obtain xs where xs_bv: "xs ∈ bitvec ?n"
      and vdef: "v = s - (∑ i=kk..<?n. as ! i * xs ! i)"
      using RHS_exp by blast
    define T where "T = {i∈{kk..<?n}. xs ! i = 1}"

    have len:  "length xs = ?n"
      using xs_bv using bitvec_def by blast

    have xs01: "set xs ⊆ ({0,1}::int set)"
      using xs_bv using bitvec_def by blast

    have "(∑ i=kk..<?n. as ! i * xs ! i)
          = (∑ i=kk..<?n. (if i∈T then as ! i else 0))"
    proof (rule sum.cong[OF refl], goal_cases)
      case (1 i)
      hence iN: "i < ?n" by auto
      (* derive xs ! i ∈ {0,1} via nth_mem, not by simp *)
      have "xs ! i ∈ set xs" using iN len by simp
      then have xi01: "xs ! i = 0 ∨ xs ! i = 1" using xs01 by auto
      have "(i∈T) ⟷ xs ! i = 1" using 1 by (simp add: T_def)
      with xi01 show ?case by auto
    qed
    also have "... = (∑ i∈{kk..<?n} ∩ T. as ! i)"
      by (simp add: sum.If_cases)
    also have "... = (∑ i∈T. as ! i)"
      using T_def
      by (smt (verit, best) Collect_cong Int_iff inf_commute inf_set_def mem_Collect_eq)
    also have "... = sum_over as T"
      by (simp add: sum_over_def)
    finally have "(∑ i=kk..<?n. as ! i * xs ! i) = sum_over as T" .

    with vdef have "sum_over as T = s - v" by simp
    moreover have "T ⊆ {kk..<?n}" using T_def by blast
    ultimately show "∃T ⊆ {kk..<length as}. sum_over as T = s - v" by blast
  next
    (* ⇐ : build a 0/1 mask from T and fold the sum back *)
    assume "∃T ⊆ {kk..<?n}. sum_over as T = s - v"
    then obtain T where Tsub: "T ⊆ {kk..<?n}" and Tv: "sum_over as T = s - v"
      by blast
    define xs where "xs = map (λi. if i∈T then (1::int) else 0) [0..<?n]"
    have xs_bv: "xs ∈ bitvec ?n"
      by (simp add: xs_def mask_is_bitvec)

    have "(∑ i=kk..< ?n. as ! i * xs ! i)
        = (∑ i=kk..< ?n. as ! i * (if i ∈ T then 1 else 0))"
      by (intro sum.cong[OF refl]) (simp add: xs_def)
    also have "... = (∑ i=kk..< ?n. (if i ∈ T then as ! i else 0))"
      by (intro sum.cong[OF refl]) simp
    also have "... = (∑ i∈{kk..< ?n} ∩ T. as ! i)"
      by (simp add: sum.If_cases)
    (* absorb the intersection using T ⊆ {kk..< ?n} *)
    have inter_absorb2: "{kk..< ?n} ∩ T = T"
      using Tsub by auto
    have "(∑ i∈{kk..< ?n} ∩ T. as ! i) = (∑ i∈T. as ! i)"
      by (simp only: inter_absorb2)
    have "... = sum_over as T"
      using sum_over_def by auto
    then have sum_eq_T: "(∑ i=kk..< ?n. as ! i * xs ! i) = sum_over as T" 
      by (simp add: ‹(∑i = kk..<length as. if i ∈ T then as ! i else 0) = 
        sum ((!) as) ({kk..<length as} ∩ T)› calculation inter_absorb2)
    have "v = s - (∑ i=kk..< ?n. as ! i * xs ! i)"
      using Tv sum_eq_T by simp
    hence "∃xs∈bitvec ?n. v = s - (∑ i=kk..< ?n. as ! i * xs ! i)"
      using xs_bv by blast
    thus "v ∈ RHS (e_k as s kk) ?n"
      using RHS_exp by simp
  qed
qed

lemma RHS_char:
  assumes "kk ≤ length as"
  shows   "v ∈ RHS (e_k as s kk) (length as)
           ⟷ (∃T ⊆ {kk..<length as}. sum_over as T = s - v)"
  using RHS_char_bounded[OF assms] .

(* disjoint-union splitting for your sum_over *)
lemma sum_over_union_disjoint:
  assumes "finite A" "finite B" "A ∩ B = {}"
  shows   "sum_over as (A ∪ B) = sum_over as A + sum_over as B"
  using assms by (simp add: sum_over_def sum.union_disjoint)

lemma distinct_subset_sums_inj_len:
  assumes dss: "distinct_subset_sums as"
  shows "inj_on (sum_over as) {U. U ⊆ {..<length as}}"
proof -
  let ?n = "length as"
  have sep:
    "⋀xs ys. xs ∈ bitvec ?n ⟹ ys ∈ bitvec ?n ⟹ xs ≠ ys
             ⟹ (∑ i<?n. as ! i * xs ! i) ≠ (∑ i<?n. as ! i * ys ! i)"
    using dss by (simp add: distinct_subset_sums_def)
  from distinct_subset_sums_inj[OF sep]
  show ?thesis by simp
qed

lemma DSS_intersection_at_most_one:
  assumes le:  "kk ≤ length as"
      and dss: "distinct_subset_sums as"
  shows
    "⋀v w.
       v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as) ⟹
       w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as) ⟹
       v = w"
proof -
  fix v w
  assume v_in: "v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  assume w_in: "w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as)"

  obtain L where Lsub: "L ⊆ {..<kk}" and Lv: "sum_over as L = v"
    using v_in by (auto simp: LHS_char[OF le])
  obtain R where Rsub: "R ⊆ {kk..<length as}" and Rv: "sum_over as R = s - v"
    using v_in by (auto simp: RHS_char[OF le])

  obtain L' where L'sub: "L' ⊆ {..<kk}" and Lw: "sum_over as L' = w"
    using w_in by (auto simp: LHS_char[OF le])
  obtain R' where R'sub: "R' ⊆ {kk..<length as}" and Rw: "sum_over as R' = s - w"
    using w_in by (auto simp: RHS_char[OF le])

  have LR_disj:   "L ∩ R = {}"   using Lsub Rsub
    by (metis Int_mono bot.extremum_uniqueI ivl_disj_int_one(2))
  have L'R'_disj: "L' ∩ R' = {}" using L'sub R'sub 
    by (metis Int_mono bot.extremum_uniqueI ivl_disj_int_one(2))
  have finL:  "finite L"   using Lsub  by (meson finite_subset finite_lessThan)
  have finR:  "finite R"   using Rsub  by (meson finite_subset finite_atLeastLessThan)
  have finL': "finite L'"  using L'sub by (meson finite_subset finite_lessThan)
  have finR': "finite R'"  using R'sub by (meson finite_subset finite_atLeastLessThan)

  define S  where "S  = L ∪ R"
  define S' where "S' = L' ∪ R'"

  have sumS:  "sum_over as S = s"
    using finL finR LR_disj by (simp add: S_def sum_over_union_disjoint Lv Rv)
  have sumS': "sum_over as S' = s"
    using finL' finR' L'R'_disj by (simp add: S'_def sum_over_union_disjoint Lw Rw)

  have Ssub:  "S  ⊆ {..<length as}" using S_def Lsub Rsub
    by (metis Un_mono ivl_disj_un_one(2) le)
  have S'sub: "S' ⊆ {..<length as}" using S'_def L'sub R'sub 
    by (metis Un_mono ivl_disj_un_one(2) le)

  have inj: "inj_on (sum_over as) {U. U ⊆ {..<length as}}"
    by (rule distinct_subset_sums_inj_len[OF dss])

  have eqSums: "sum_over as S = sum_over as S'"
    using sumS sumS' by simp

  have SS': "S = S'"
  proof (rule inj_onD[OF inj])
    show "S ∈ {U. U ⊆ {..<length as}}"  using Ssub  by simp
    show "S' ∈ {U. U ⊆ {..<length as}}" using S'sub by simp
    show "sum_over as S = sum_over as S'"  by (rule eqSums)
  qed

  have "L = S ∩ {..<kk}"  and "L' = S' ∩ {..<kk}"
    using Lsub Rsub L'sub R'sub by (auto simp: S_def S'_def)
  hence "L = L'" using SS' by simp

  thus "v = w" using Lv Lw by simp
qed

lemma DSS_unique_value_param:
  assumes dss: "distinct_subset_sums as"
      and ex:  "∃v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  shows "∃!v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
proof -
  obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
              and vR: "v ∈ RHS (e_k as s kk) (length as)"
    using ex by blast
  have uniq:
    "⋀w. w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as) ⟹ w = v"
    using DSS_intersection_at_most_one[OF dss] vL vR by blast
  show ?thesis using vL vR uniq by auto
qed

lemma DSS_hit:
  assumes le:  "kk ≤ length as"
      and dss: "distinct_subset_sums as"
      and SOL: "∃S⊆{..<length as}. sum_over as S = s"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∈ RHS (e_k as s kk) (length as)"
proof -
  obtain S where Ssub: "S ⊆ {..<length as}" and SS: "sum_over as S = s" using SOL by blast
  define L where "L = S ∩ {..<kk}"
  define R where "R = S ∩ {kk..<length as}"

  have S_eq: "S = L ∪ R"  unfolding L_def R_def using Ssub by auto
  have LR_disj: "L ∩ R = {}" unfolding L_def R_def by auto
  have finL: "finite L" by (simp add: L_def)
  have finR: "finite R" by (simp add: R_def)

  have splitS: "sum_over as S = sum_over as L + sum_over as R"
    using finL finR LR_disj by (simp add: S_eq sum_over_union_disjoint)

  define v where "v = sum_over as L"
  have Lsub: "L ⊆ {..<kk}" unfolding L_def by auto
  have Rsub: "R ⊆ {kk..<length as}" unfolding R_def by auto

  have v_in_LHS: "v ∈ LHS (e_k as s kk) (length as)"
    using Lsub by (auto simp: LHS_char[OF le] v_def)

  have "v + sum_over as R = s" using SS splitS v_def by simp
  hence R_sum: "sum_over as R = s - v" by simp

  have v_in_RHS: "v ∈ RHS (e_k as s kk) (length as)"
    using Rsub R_sum by (auto simp: RHS_char[OF le])

  show ?thesis using v_in_LHS v_in_RHS by blast
qed

lemma DSS_unique_value:
  assumes le:  "kk ≤ length as"
      and dss: "distinct_subset_sums as"
  shows "∃!v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  using DSS_unique_value_param[OF le dss] DSS_hit[OF le dss] by auto

(* there exists also an L value not in the R set *)
lemma DSS_miss:
  assumes dss: "distinct_subset_sums as"
      and twoL: "∃u v. u ∈ LHS (e_k as s kk) (length as) ∧ v ∈ LHS (e_k as s kk) (length as) ∧ u ≠ v"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∉ RHS (e_k as s kk) (length as)"
proof -
  obtain v where v_in:
    "v ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as)"
    and uniq:  "⋀w. w ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as) ⟹ w = v"
    using DSS_unique_value[OF dss] by (metis IntD1 IntD2 IntI)
  obtain u w where uL: "u ∈ LHS (e_k as s kk) (length as)"
                 and wL: "w ∈ LHS (e_k as s kk) (length as)"
                 and uneq: "u ≠ w"
    using twoL by blast
  have "u ≠ v ∨ w ≠ v" using uneq by auto
  then obtain t where tL: "t ∈ LHS (e_k as s kk) (length as)" and tne: "t ≠ v" by (cases "u = v") (use wL uL in auto)
  have "t ∉ RHS (e_k as s kk) (length as)"
    using uniq tL tne by auto
  thus ?thesis using tL by blast
qed

lemma DSS_missR:
  assumes dss: "distinct_subset_sums as"
      and twoR: "∃u v. u ∈ RHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as) ∧ u ≠ v"
  shows "∃v ∈ RHS (e_k as s kk) (length as). v ∉ LHS (e_k as s kk) (length as)"
proof -
  obtain v where v_in:
    "v ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as)"
    and uniq:  "⋀w. w ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as) ⟹ w = v"
    using DSS_unique_value[OF dss] by simp
  obtain u w where uR: "u ∈ RHS (e_k as s kk) (length as)"
                 and wR: "w ∈ RHS (e_k as s kk) (length as)"
                 and uneq: "u ≠ w"
    using twoR by blast
  have "u ≠ v ∨ w ≠ v" using uneq by auto
  then obtain t where tR: "t ∈ RHS (e_k as s kk) (length as)" and tne: "t ≠ v" by (cases "u = v") (use wR uR in auto)
  have "t ∉ LHS (e_k as s kk) (length as)"
    using uniq tR tne by auto
  thus ?thesis using tR by blast
qed

(* uniqueness-of-witness for the baseline; adjust statement to what you need *)
lemma DSS_baseline_only_j:
  assumes dss: "distinct_subset_sums as" and jL: "j < length (enumL as s kk)"
  shows "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
         (∀j'<length (enumL as s kk). j' ≠ j ⟶
            Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
proof
  assume BASE: "Good as s ((!) (x0 as s)) ((!) (x0 as s))"
  (* good ⇔ some equal-value exists *)
  obtain jR where jR: "jR < length (enumR as s kk)"
    and EQ: "Lval_at as s ((!) (x0 as s)) j = Rval_at as s ((!) (x0 as s)) jR"
    using BASE Good_char_encR[of as s "(!) (x0 as s)"] jL by auto
  (* decode to values on the catalogs *)
  have Vj: "Lval_at as s ((!) (x0 as s)) j = enumL as s kk ! j"
    using Lval_at_on_enc_block jL by simp
  have WjR: "Rval_at as s ((!) (x0 as s)) jR = enumR as s kk ! jR"
    using Rval_at_on_enc_block jR by simp
  have meet_val:
    "enumL as s kk ! j ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as)"
    using enumL_set enumR_set jL jR Vj WjR EQ by auto
  (* uniqueness of intersection value *)
  have uniq_val: "⋀w. w ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as)
                  ⟹ w = enumL as s kk ! j"
    using DSS_unique_value[OF dss] meet_val by simp
  (* now forbid any other L-index j' to hit RHS *)
  fix j' assume j'L: "j' < length (enumL as s kk)" and ne: "j' ≠ j"
  have distinctL: "distinct (enumL as s kk)" by (simp add: enumL_def)
  from distinct_conv_nth[THEN iffD1, OF distinctL jL j'L] ne
  have neq_vals: "enumL as s kk ! j' ≠ enumL as s kk ! j" by blast
  show "Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
  proof
    assume inR: "Lval_at as s ((!) (x0 as s)) j' ∈ set (enumR as s kk)"
    then obtain jR' where jR': "jR' < length (enumR as s kk)"
      and EQ': "Rval_at as s ((!) (x0 as s)) jR' = Lval_at as s ((!) (x0 as s)) j'"
      by (meson in_set_conv_nth)
    have Vj': "Lval_at as s ((!) (x0 as s)) j' = enumL as s kk ! j'" using Lval_at_on_enc_block j'L by simp
    have WjR': "Rval_at as s ((!) (x0 as s)) jR' = enumR as s kk ! jR'" using Rval_at_on_enc_block jR' by simp
    have "enumL as s kk ! j' ∈ LHS … ∩ RHS …"
      using enumL_set enumR_set j'L jR' Vj' WjR' EQ' by auto
    hence "enumL as s kk ! j' = enumL as s kk ! j" using uniq_val by blast
    thus False using neq_vals by contradiction
  qed
qed

lemma DSS_baseline_only_jR:
  assumes dss: "distinct_subset_sums as" and jR: "j < length (enumR as s kk)"
  shows "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
         (∀j'<length (enumR as s kk). j' ≠ j ⟶
            Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
proof
  assume BASE: "Good as s ((!) (x0 as s)) ((!) (x0 as s))"
  (* good ⇔ some equal-value exists, now from the R side *)
  obtain jL where jL: "jL < length (enumL as s kk)"
    and EQ: "Rval_at as s ((!) (x0 as s)) j = Lval_at as s ((!) (x0 as s)) jL"
    using BASE Good_char_encL[of as s "(!) (x0 as s)"] jR by auto

  have Vj:   "Rval_at as s ((!) (x0 as s)) j   = enumR as s kk ! j"
    using Rval_at_on_enc_block jR by simp
  have WjL:  "Lval_at as s ((!) (x0 as s)) jL  = enumL as s kk ! jL"
    using Lval_at_on_enc_block jL by simp

  have meet_val:
    "enumR as s kk ! j ∈ RHS (e_k as s kk) (length as) ∩ LHS (e_k as s kk) (length as)"
    using enumL_set enumR_set jL jR Vj WjL EQ by auto

  have uniq_val:
    "⋀w. w ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as)
         ⟹ w = enumR as s kk ! j"
    using DSS_unique_value[OF dss] meet_val by simp

  fix j' assume j'R: "j' < length (enumR as s kk)" and ne: "j' ≠ j"
  have distinctR: "distinct (enumR as s kk)" by (simp add: enumR_def)
  from distinct_conv_nth[THEN iffD1, OF distinctR jR j'R] ne
  have neq_vals: "enumR as s kk ! j' ≠ enumR as s kk ! j" by blast

  show "Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk)"
  proof
    assume inL: "Rval_at as s ((!) (x0 as s)) j' ∈ set (enumL as s kk)"
    then obtain jL' where jL': "jL' < length (enumL as s kk)"
      and EQ': "Lval_at as s ((!) (x0 as s)) jL' = Rval_at as s ((!) (x0 as s)) j'"
      by (meson in_set_conv_nth)

    have Vj':  "Rval_at as s ((!) (x0 as s)) j'  = enumR as s kk ! j'"
      using Rval_at_on_enc_block j'R by simp
    have WjL': "Lval_at as s ((!) (x0 as s)) jL' = enumL as s kk ! jL'"
      using Lval_at_on_enc_block jL' by simp

    have "enumR as s kk ! j' ∈ RHS … ∩ LHS …"
      using enumL_set enumR_set j'R jL' Vj' WjL' EQ' by auto
    hence "enumR as s kk ! j' = enumR as s kk ! j" using uniq_val by blast
    thus False using neq_vals by contradiction
  qed
qed

lemma read0_hits_L:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
      and jL: "j < length (enumL as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockL_abs enc0 as s j)"
  hence DISJ: "Base.read0 M ?x ∩ blockL_abs enc0 as s j = {}" by auto

  (* 1) From DSS, get one hit and one miss between L and R, and deduce |enumL| ≥ 2 *)
  have hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
  proof -
    obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
               and vR: "v ∈ RHS (e_k as s kk) (length as)"
      using DSS_hit[OF dss] by blast
    thus ?thesis using enumL_set enumR_set by auto
  qed
  have miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
  proof -
    obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
               and vNR: "v ∉ RHS (e_k as s kk) (length as)"
      using DSS_miss[OF dss] by blast
    thus ?thesis using enumL_set enumR_set by auto
  qed
  have L2: "2 ≤ length (enumL as s kk)"
  proof -
    obtain vH where vH_L: "vH ∈ set (enumL as s kk)"
                 and vH_R: "vH ∈ set (enumR as s kk)" using hit by blast
    obtain vM where vM_L: "vM ∈ set (enumL as s kk)"
                 and vM_notR: "vM ∉ set (enumR as s kk)" using miss by blast
    have "vH ≠ vM" using vH_R vM_notR by auto
    have fin: "finite (set (enumL as s kk))" by simp
    have subs: "{vH, vM} ⊆ set (enumL as s kk)" using vH_L vM_L by auto
    have "card {vH, vM} = 2" using ‹vH ≠ vM› by simp
    hence "2 ≤ card (set (enumL as s kk))"
      using card_mono[OF fin subs] by simp
    also have "… ≤ length (enumL as s kk)" by (rule card_length)
    finally show ?thesis .
  qed

  (* 2) The “baseline-unique j” condition *)
  have baseline_only_j:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumL as s kk). j' ≠ j ⟶
        Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
    by (rule DSS_baseline_only_j[OF dss jL])

  (* 3) Flip only this L block while leaving others identical *)
  obtain oL' where
    OUT: "∀i. i ∉ blockL_abs enc0 as s j ⟶ oL' i = ((!) ?x) i" and
    FLP: "Good as s oL' ((!) ?x) ≠ Good as s ((!) ?x) ((!) ?x)"
    using flipL0[OF jL L2 hit miss baseline_only_j] by blast

  (* Build y by splicing the j-th L-block with the oL' bits *)
  define a where "a = length (enc0 as s) + offL as s j"
  define w where "w = W as s"
  have blk_repr: "blockL_abs enc0 as s j = {a ..< a + w}"
    by (simp add: a_def w_def blockL_abs_def offL_def)
  have BND: "a + w ≤ length ?x"
    using offL_window_in_enc[OF jL] by (simp add: a_def w_def)
  define y where
    "y = splice a w ?x (map oL' [a ..< a + w])"

  (* Outside the j-block, y agrees with x *)
  have outside_y:
    "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = ?x ! i"
  proof -
    fix i assume nin: "i ∉ blockL_abs enc0 as s j"
    from nin blk_repr have nin': "i < a ∨ ¬ i < a + w" by auto
    show "y ! i = ?x ! i"
    proof (cases "i < a")
      case True
      thus ?thesis using y_def splice_nth_left BND by simp
    next
      case False
      with nin' have "¬ i < a + w" by simp
      thus ?thesis
        using y_def splice_nth_right w_def BND by simp
    qed
  qed

  (* On the j-block, y’s slice is exactly the oL' slice *)
  have slice_j:
    "map ((!) y) [a ..< a + w] = map oL' [a ..< a + w]"
  proof (rule nth_equalityI)
    show "length (map ((!) y) [a ..< a + w]) =
          length (map oL'      [a ..< a + w])" by simp
  next
    fix t assume tlt: "t < length (map ((!) y) [a ..< a + w])"
    hence tw: "t < w" by simp
    have idx: "[a ..< a + w] ! t = a + t" using tw by simp
    have inblk: "a ≤ a + t ∧ a + t < a + w" using tw by simp
    have yn: "y ! (a + t) = (map oL' [a ..< a + w]) ! t"
      using y_def splice_nth_inside inblk by (simp add: BND)
    show "map ((!) y) [a ..< a + w] ! t =
          map oL' [a ..< a + w] ! t"
      by (simp add: idx yn tw)
  qed

  (* Therefore Lval_at on j matches oL' on j *)
  have Lval_y_j: "Lval_at as s ((!) y) j = Lval_at as s oL' j"
    using Lval_at_def a_def w_def slice_j by presburger

  (* For any other j', both y and oL' coincide with x on that block *)
  have Lval_eq_all:
    "⋀j'. j' < length (enumL as s kk) ⟹
          Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
  proof -
    fix j' assume j'L: "j' < length (enumL as s kk)"
    consider (eq) "j' = j" | (ne) "j' ≠ j" by blast
    then show "Lval_at as s ((!) y) j' = Lval_at as s oL' j'"
    proof cases
      case eq
      thus ?thesis by (simp add: Lval_y_j)
    next
      case ne
      define a' where "a' = length (enc0 as s) + offL as s j'"
      define w' where "w' = W as s"
      have blk': "blockL_abs enc0 as s j' = {a' ..< a' + w'}"
        by (simp add: a'_def w'_def blockL_abs_def offL_def)
      have agree_y_x:
        "map ((!) y)  [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [a' ..< a' + w']) =
              length (map ((!) ?x) [a' ..< a' + w'])" by simp
      next
        fix t assume "t < length (map ((!) y) [a' ..< a' + w'])"
        hence tw: "t < w'" by (simp add: w'_def)
        have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
        have mem: "a' + t ∈ blockL_abs enc0 as s j'" by (simp add: blk' tw)
        have nin: "a' + t ∉ blockL_abs enc0 as s j"
          using blockL_abs_disjoint[OF ne] mem by auto
        have "map ((!) y) [a' ..< a' + w'] ! t = (!) y (a' + t)"
          by (simp add: idx tw)
        also have "... = ?x ! (a' + t)" using outside_y nin by simp
        also have "... = map ((!) ?x) [a' ..< a' + w'] ! t"
          by (simp add: idx tw)
        finally show "map ((!) y) [a' ..< a' + w'] ! t
                      = map ((!) ?x) [a' ..< a' + w'] ! t" .
      qed
      have agree_oL_x:
        "map oL' [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule nth_equalityI)
        show "length (map oL' [a' ..< a' + w']) =
              length (map ((!) ?x) [a' ..< a' + w'])" by simp
      next
        fix t assume "t < length (map oL' [a' ..< a' + w'])"
        hence tw: "t < w'" by (simp add: w'_def)
        have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
        have mem: "a' + t ∈ blockL_abs enc0 as s j'" by (simp add: blk' tw)
        have nin: "a' + t ∉ blockL_abs enc0 as s j"
          using blockL_abs_disjoint[OF ne] mem by auto
        have "map oL' [a' ..< a' + w'] ! t = oL' (a' + t)"
          by (simp add: idx tw)
        also have "... = ?x ! (a' + t)" using OUT nin by simp
        also have "... = map ((!) ?x) [a' ..< a' + w'] ! t"
          by (simp add: idx tw)
        finally show "map oL' [a' ..< a' + w'] ! t
                      = map ((!) ?x) [a' ..< a' + w'] ! t" .
      qed
      have "Lval_at as s ((!) y) j'
            = from_bits (map ((!) y) [a' ..< a' + w'])"
        by (simp add: Lval_at_def a'_def w'_def)
      also have "... = from_bits (map ((!) ?x) [a' ..< a' + w'])"
        by (simp add: agree_y_x)
      also have "... = from_bits (map oL' [a' ..< a' + w'])"
        by (simp add: agree_oL_x)
      also have "... = Lval_at as s oL' j'"
        by (simp add: Lval_at_def a'_def w'_def)
      finally show ?thesis .
    qed
  qed

  (* With R fixed to enc, Good(y,enc) = Good(oL',enc) *)
  have Good_y_oL'_eq:
    "Good as s ((!) y) ((!) ?x) = Good as s oL' ((!) ?x)"
  proof -
    have "Good as s ((!) y) ((!) ?x)
          ⟷ (∃j'<length (enumL as s kk). Lval_at as s ((!) y) j' ∈ set (enumR as s kk))"
      using Good_char_encR by simp
    also have "... ⟷ (∃j'<length (enumL as s kk). Lval_at as s oL' j' ∈ set (enumR as s kk))"
      by (metis Lval_eq_all)
    also have "... ⟷ Good as s oL' ((!) ?x)"
      using Good_char_encR[symmetric] by simp
    finally show ?thesis .
  qed

  from Good_y_oL'_eq FLP have
    "Good as s ((!) y) ((!) ?x) ≠ Good as s ((!) ?x) ((!) ?x)"
    by simp

 (* Show that changing only inside the L-block j cannot change the run of T0 *)
  have seenL_sub:
    "seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenL_T0_subset_read0[OF refl])
  have seenR_sub:
    "seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenR_T0_subset_read0[OF refl])

  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) y i"
  proof -
    fix i assume "i ∈ seenL_run ((!) ?x) ((!) ?x) (T0 as s)"
    hence "i ∈ Base.read0 M ?x" using seenL_sub by blast
    with DISJ have "i ∉ blockL_abs enc0 as s j" by auto
    thus "(!) ?x i = (!) y i" using outside_y by simp
  qed

  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) ?x i"
    by simp

  have RUN_EQ:
  "run ((!) ?x) ((!) ?x) (T0 as s) = run ((!) y) ((!) ?x) (T0 as s)"
  by (rule run_agrees_on_seen[OF agree_on_seenL agree_on_seenR])

  (* Tie run to Good via correctness of T0 *)
  have Good_eq_baseline:
    "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
  proof -
  (* no use of correct_T0 on the LHS! *)
    have "run ((!) y) ((!) ?x) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
      using RUN_EQ[symmetric] by simp
    moreover have "run ((!) ?x) ((!) ?x) (T0 as s)
                 = Good as s ((!) ?x) ((!) ?x)"
      by (simp add: correct_T0)
    ultimately show ?thesis
      using Good_char_encR Lval_eq_all
      by (metis DSS_baseline_only_j Lval_at_on_enc_block dss hit in_set_conv_nth miss)
  qed

  (* Contradiction to FLP *)
  from Good_y_oL'_eq Good_eq_baseline have
    "Good as s oL' ((!) ?x) = Good as s ((!) ?x) ((!) ?x)" by simp
  with FLP show False by simp
qed

lemma DSS_unique_L_witness:
  assumes dss:  "distinct_subset_sums as"
      and j'L:  "j' < length (enumL as s kk)"
      and j''L: "j'' < length (enumL as s kk)"
      and inR':  "enumL as s kk ! j'  ∈ RHS (e_k as s kk) (length as)"
      and inR'': "enumL as s kk ! j'' ∈ RHS (e_k as s kk) (length as)"
  shows "j' = j''"
proof -
  (* Both enumL!j' and enumL!j'' are in LHS, because enumL enumerates LHS *)
  have inL':  "enumL as s kk ! j'  ∈ LHS (e_k as s kk) (length as)"
    using j'L enumL_set nth_mem by blast
  have inL'': "enumL as s kk ! j'' ∈ LHS (e_k as s kk) (length as)"
    using j''L enumL_set nth_mem by blast

  (* Uniqueness of the intersection gives equality of the values *)
  obtain v where v_def:
      "v = enumL as s kk ! j'"
    and v_unique:
      "∀w. (w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as)) ⟶ w = v"
    using DSS_unique_value[OF dss] inL' inR'
    by (metis (mono_tags, lifting))

  have eq_vals:
    "enumL as s kk ! j' = enumL as s kk ! j''"
    using v_unique inL'' inR'' v_def by auto

  (* enumL is a sorted_list_of_set, hence distinct *)
  have distinctL: "distinct (enumL as s kk)"
    by (simp add: enumL_def)

  (* In a distinct list, equal nth values imply equal indices *)
  from distinct_conv_nth[THEN iffD1, OF distinctL] j'L j''L
  have "j' ≠ j'' ⟹ enumL as s kk ! j' ≠ enumL as s kk ! j''" by blast
  with eq_vals show "j' = j''" by auto
qed

lemma Run_unread_L:
  fixes x y :: "bool list"
  assumes DISJ:  "Base.read0 M x ∩ blockL_abs enc0 as s j = {}"
  assumes AGREE: "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = x ! i"
  assumes X:     "x = enc as s kk"
  shows "run ((!) y) ((!) x) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
proof -
  (* bound the seen-sets using the pair (x,x) so they sit inside read0 M x *)
  have SLsub: "seenL_run ((!) x) ((!) x) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenL_T0_subset_read0[OF X])
  have SRsub: "seenR_run ((!) x) ((!) x) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenR_T0_subset_read0[OF X])

  (* agree with y on everything seen on the left; right oracles are identical anyway *)
  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) x) ((!) x) (T0 as s) ⟹ (!) x i = (!) y i"
  proof -
    fix i assume "i ∈ seenL_run ((!) x) ((!) x) (T0 as s)"
    with SLsub have "i ∈ Base.read0 M x" by blast
    with DISJ have "i ∉ blockL_abs enc0 as s j" by auto
    with AGREE show "(!) x i = (!) y i" by simp
  qed
  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) x) ((!) x) (T0 as s) ⟹ (!) x i = (!) x i"
    by simp

  (* apply run_agrees_on_seen with (oL,oR)=((!) x, (! ) x) and (oL',oR')=((!) y, (! ) x) *)
  have "run ((!) x) ((!) x) (T0 as s) = run ((!) y) ((!) x) (T0 as s)"
    by (rule run_agrees_on_seen[OF agree_on_seenL agree_on_seenR])
  thus ?thesis by simp
qed

(* -- R blocks are touched --------------------------------------------------- *)
lemma read0_hits_R:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
      and jR:    "j < length (enumR as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockR_abs enc0 as s kk j)"
  hence DISJ: "Base.read0 M ?x ∩ blockR_abs enc0 as s kk j = {}" by auto

  (* 1) From DSS, get one hit and one miss between R and L, and deduce |enumR| ≥ 2 *)
  have hitR: "∃v∈set (enumR as s kk). v ∈ set (enumL as s kk)"
  proof -
    obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
               and vR: "v ∈ RHS (e_k as s kk) (length as)"
      using DSS_hit[OF dss] by blast
    thus ?thesis using enumL_set enumR_set by blast
  qed

  have missR: "∃v∈set (enumR as s kk). v ∉ set (enumL as s kk)"
  proof -
    obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
               and vNR: "v ∉ RHS (e_k as s kk) (length as)"
      using DSS_miss[OF dss] by blast
    (* flip the roles via enum-sets *)
    from vNR have "v ∉ set (enumR as s kk)" using enumR_set by blast
    moreover from vL have "v ∈ set (enumL as s kk)" using enumL_set by blast
    ultimately show ?thesis by (simp add: DSS_missR dss)
  qed

  have R2: "2 ≤ length (enumR as s kk)"
  proof -
    obtain vH where vH_R: "vH ∈ set (enumR as s kk)"
                 and vH_L: "vH ∈ set (enumL as s kk)" using hitR by blast
    obtain vM where vM_R: "vM ∈ set (enumR as s kk)"
                 and vM_notL: "vM ∉ set (enumL as s kk)" using missR by blast
    have "vH ≠ vM" using vH_L vM_notL by auto
    have fin: "finite (set (enumR as s kk))" by simp
    have subs: "{vH, vM} ⊆ set (enumR as s kk)" using vH_R vM_R by auto
    have "card {vH, vM} = 2" using ‹vH ≠ vM› by simp
    hence "2 ≤ card (set (enumR as s kk))" using card_mono[OF fin subs] by simp
    also have "… ≤ length (enumR as s kk)" by (rule card_length)
    finally show ?thesis .
  qed

  (* 2) The “baseline-unique j” condition on the R side *)
  have baseline_only_jR:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumR as s kk). j' ≠ j ⟶
        Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
    by (rule DSS_baseline_only_jR[OF dss jR])

  (* 3) Flip only this R block while leaving others identical *)
  obtain oR' where
    OUT: "∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = ((!) ?x) i" and
    FLP: "Good as s ((!) ?x) oR' ≠ Good as s ((!) ?x) ((!) ?x)"
    using DSS_baseline_only_jR Good_char_encR Lval_at_on_enc_block 
        Rval_at_on_enc_block dss hitR in_set_conv_nth missR by metis

  (* Build y by splicing the j-th R-block with the oR' bits *)
  define a where "a = offR as s kk j"
  define w where "w = W as s"
  have blk_repr: "blockR_abs enc0 as s kk j = {a ..< a + w}"
    using a_def w_def blockR_abs_def offR_def DSS_baseline_only_jR Good_char_encR 
     Lval_at_on_enc_block Rval_at_on_enc_block dss hitR in_set_conv_nth missR
     by metis
  have BND: "a + w ≤ length ?x"
    using offR_window_in_enc[OF jR] by (simp add: a_def w_def)
  define y where
    "y = splice a w ?x (map oR' [a ..< a + w])"

  (* Outside the j-block, y agrees with x *)
  have outside_y:
    "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = ?x ! i"
  proof -
    fix i assume nin: "i ∉ blockR_abs enc0 as s kk j"
    from nin blk_repr have nin': "i < a ∨ ¬ i < a + w" by auto
    show "y ! i = ?x ! i"
    proof (cases "i < a")
      case True
      thus ?thesis using y_def splice_nth_left BND by simp
    next
      case False
      with nin' have "¬ i < a + w" by simp
      thus ?thesis using y_def splice_nth_right w_def BND by simp
    qed
  qed

  (* On the j-block, y’s slice is exactly the oR' slice *)
  have slice_j:
    "map ((!) y) [a ..< a + w] = map oR' [a ..< a + w]"
  proof (rule nth_equalityI)
    show "length (map ((!) y) [a ..< a + w]) =
          length (map oR'      [a ..< a + w])" by simp
  next
    fix t assume tlt: "t < length (map ((!) y) [a ..< a + w])"
    hence tw: "t < w" by simp
    have idx: "[a ..< a + w] ! t = a + t" using tw by simp
    have inblk: "a ≤ a + t ∧ a + t < a + w" using tw by simp
    have yn: "y ! (a + t) = (map oR' [a ..< a + w]) ! t"
      using y_def splice_nth_inside inblk by (simp add: BND)
    show "map ((!) y) [a ..< a + w] ! t =
          map oR' [a ..< a + w] ! t"
      by (simp add: idx yn tw)
  qed

  (* Therefore Rval_at on j matches oR' on j *)
  have Rval_y_j: "Rval_at as s ((!) y) j = Rval_at as s oR' j"
    using Rval_at_def a_def w_def slice_j DSS_baseline_only_jR 
          Good_char_encL Rval_at_on_enc_block dss hitR in_set_conv_nth missR
    by metis

  (* For any other j', both y and oR' coincide with x on that block *)
  have Rval_eq_all:
    "⋀j'. j' < length (enumR as s kk) ⟹
          Rval_at as s ((!) y) j' = Rval_at as s oR' j'"
  proof -
    fix j' assume j'R: "j' < length (enumR as s kk)"
    consider (eq) "j' = j" | (ne) "j' ≠ j" by blast
    then show "Rval_at as s ((!) y) j' = Rval_at as s oR' j'"
    proof cases
      case eq
      thus ?thesis by (simp add: Rval_y_j)
    next
      case ne
      define a' where "a' = offR as s kk j'"
      define w' where "w' = W as s"
      have blk': "blockR_abs enc0 as s kk j' = {a' ..< a' + w'}"
        using a'_def w'_def blockR_abs_def offR_def DSS_baseline_only_jR 
          Good_char_encL Rval_at_on_enc_block dss hitR in_set_conv_nth j'R jR ne
        by (metis)
      have agree_y_x:
        "map ((!) y)  [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [a' ..< a' + w']) =
              length (map ((!) ?x) [a' ..< a' + w'])" by simp
      next
        fix t assume "t < length (map ((!) y) [a' ..< a' + w'])"
        hence tw: "t < w'" by (simp add: w'_def)
        have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
        have mem: "a' + t ∈ blockR_abs enc0 as s kk j'" by (simp add: blk' tw)
        have nin: "a' + t ∉ blockR_abs enc0 as s kk j"
          using blockR_abs_disjoint[OF ne] mem by blast
        have "map ((!) y) [a' ..< a' + w'] ! t = (!) y (a' + t)"
          by (simp add: idx tw)
        also have "... = ?x ! (a' + t)" using outside_y nin by simp
        also have "... = map ((!) ?x) [a' ..< a' + w'] ! t"
          by (simp add: idx tw)
        finally show "map ((!) y) [a' ..< a' + w'] ! t
                      = map ((!) ?x) [a' ..< a' + w'] ! t" .
      qed
      have agree_oR_x:
        "map oR' [a' ..< a' + w'] = map ((!) ?x) [a' ..< a' + w']"
      proof (rule nth_equalityI)
        show "length (map oR' [a' ..< a' + w']) =
              length (map ((!) ?x) [a' ..< a' + w'])" by simp
      next
        fix t assume "t < length (map oR' [a' ..< a' + w'])"
        hence tw: "t < w'" by (simp add: w'_def)
        have idx: "[a' ..< a' + w'] ! t = a' + t" using tw by simp
        have mem: "a' + t ∈ blockR_abs enc0 as s kk j'" by (simp add: blk' tw)
        have nin: "a' + t ∉ blockR_abs enc0 as s kk j"
          using blockR_abs_disjoint[OF ne] mem by blast
        have "map oR' [a' ..< a' + w'] ! t = oR' (a' + t)"
          by (simp add: idx tw)
        also have "... = ?x ! (a' + t)" using OUT nin by simp
        also have "... = map ((!) ?x) [a' ..< a' + w'] ! t"
          by (simp add: idx tw)
        finally show "map oR' [a' ..< a' + w'] ! t
                      = map ((!) ?x) [a' ..< a' + w'] ! t" .
      qed
      have "Rval_at as s ((!) y) j'
            = from_bits (map ((!) y) [a' ..< a' + w'])"
        using Rval_at_def a'_def w'_def DSS_baseline_only_jR Good_char_encL 
              Rval_at_on_enc_block dss hitR in_set_conv_nth j'R jR ne
        by metis
      also have "... = from_bits (map ((!) ?x) [a' ..< a' + w'])"
        by (simp add: agree_y_x)
      also have "... = from_bits (map oR' [a' ..< a' + w'])"
        by (simp add: agree_oR_x)
      also have "... = Rval_at as s oR' j'"
        using Rval_at_def a'_def w'_def DSS_baseline_only_jR Good_char_encL 
              Rval_at_on_enc_block dss hitR in_set_conv_nth j'R jR ne
        by metis 
      finally show ?thesis .
    qed
  qed

  (* With L fixed to enc, Good(enc,y) = Good(enc,oR') *)
  have Good_y_oR'_eq:
    "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) oR'"
  proof -
    have "Good as s ((!) ?x) ((!) y)
          ⟷ (∃j'<length (enumR as s kk). Rval_at as s ((!) y) j' ∈ set (enumL as s kk))"
      using Good_char_encL by simp
    also have "... ⟷ (∃j'<length (enumR as s kk). Rval_at as s oR' j' ∈ set (enumL as s kk))"
      by (metis Rval_eq_all)
    also have "... ⟷ Good as s ((!) ?x) oR'"
      using Good_char_encL[symmetric] by simp
    finally show ?thesis .
  qed

  from Good_y_oR'_eq FLP have
    "Good as s ((!) ?x) ((!) y) ≠ Good as s ((!) ?x) ((!) ?x)" by simp

  (* Changing only inside the R-block j cannot change the run of T0 *)
  have seenL_sub:
    "seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenL_T0_subset_read0[OF refl])
  have seenR_sub:
    "seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⊆ Base.read0 M ?x"
    by (rule seenR_T0_subset_read0[OF refl])

  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) y i"
  proof -
    fix i assume "i ∈ seenR_run ((!) ?x) ((!) ?x) (T0 as s)"
    hence "i ∈ Base.read0 M ?x" using seenR_sub by blast
    with DISJ have "i ∉ blockR_abs enc0 as s kk j" by auto
    thus "(!) ?x i = (!) y i" using outside_y by simp
  qed

  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) ?x) ((!) ?x) (T0 as s) ⟹ (!) ?x i = (!) ?x i" by simp

  have RUN_EQ:
    "run ((!) ?x) ((!) ?x) (T0 as s) = run ((!) ?x) ((!) y) (T0 as s)"
    by (rule run_agrees_on_seen[OF agree_on_seenL agree_on_seenR])

  (* Tie run to Good via correctness of T0 only on the baseline side *)
  have Good_eq_baseline:
    "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
  proof -
    have "run ((!) ?x) ((!) y) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
      using RUN_EQ[symmetric] by simp
    moreover have "run ((!) ?x) ((!) ?x) (T0 as s)
                 = Good as s ((!) ?x) ((!) ?x)"
      by (simp add: correct_T0)
    ultimately show ?thesis
      using Good_char_encL Rval_eq_all
      by (metis DSS_baseline_only_jR Rval_at_on_enc_block dss hitR in_set_conv_nth missR)
  qed

  (* Contradiction to FLP *)
  from Good_y_oR'_eq Good_eq_baseline have
    "Good as s ((!) ?x) oR' = Good as s ((!) ?x) ((!) ?x)" by simp
  with FLP show False by simp
qed

(* 9) The coverage result you wanted, phrased on block families *)
lemma coverage_blocks:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
  shows
   "(∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
    (∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof (intro conjI allI impI)
  fix j assume jL: "j < length (enumL as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
    by (rule read0_hits_L[OF n_def dss jL])
  thus "touches (enc as s kk) (blockL_abs enc0 as s j)"
    using touches_def by auto
next
  fix j assume jR: "j < length (enumR as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
    by (rule read0_hits_R[OF n_def dss jR])
  thus "touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using touches_def by auto
qed

lemma steps_lower_bound:
  assumes n_def: "n = length as" and distinct: "distinct_subset_sums as"
  shows "steps M (enc as s kk) ≥
           card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
  from coverage_blocks[OF n_def distinct] obtain
    Lcov_ALL: "∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)" and
    Rcov_ALL: "∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    by blast

  have Lcov:
    "⋀j. j < length (enumL as s kk) ⟹ touches (enc as s kk) (blockL_abs enc0 as s j)"
    using Lcov_ALL by blast
  have Rcov:
    "⋀j. j < length (enumR as s kk) ⟹ touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using Rcov_ALL by blast

  define x0 where "x0 = enc as s kk"
  define R0 :: "nat set" where "R0 = Base.read0 M x0"

  define IL where "IL = {0..<length (enumL as s kk)}"
  define IR where "IR = {0..<length (enumR as s kk)}"

  (* pick one read index from each touched absolute block *)
  define pickL where "pickL j = (SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j)" for j
  define pickR where "pickR j = (SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j)" for j

  (* existence: each touched block contributes one read index *)
  have exL:
    "⋀j. j ∈ IL ⟹ ∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    hence jlt: "j < length (enumL as s kk)" by (simp add: IL_def)
    from Lcov[OF jlt] obtain i where
      "i ∈ Base.read0 M (enc as s kk)" "i ∈ blockL_abs enc0 as s j"
      by (auto simp: touches_def)
    hence "i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
      by (simp add: R0_def x0_def)
    thus "∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j" ..
  qed

  have exR:
    "⋀j. j ∈ IR ⟹ ∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    hence jlt: "j < length (enumR as s kk)" by (simp add: IR_def)
    from Rcov[OF jlt] obtain i where
      "i ∈ Base.read0 M (enc as s kk)" "i ∈ blockR_abs enc0 as s kk j"
      by (auto simp: touches_def)
    hence "i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
      by (simp add: R0_def x0_def)
    thus "∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j" ..
  qed

  have pickL_in:
    "⋀j. j ∈ IL ⟹ pickL j ∈ R0"
    "⋀j. j ∈ IL ⟹ pickL j ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    have conj: "pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
      using exL[OF jIL] unfolding pickL_def by (rule someI_ex)
    thus "pickL j ∈ R0" by (rule conjunct1)
  next
    fix j assume jIL: "j ∈ IL"
    have conj: "pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
      using exL[OF jIL] unfolding pickL_def by (rule someI_ex)
    thus "pickL j ∈ blockL_abs enc0 as s j" by (rule conjunct2)
  qed

  have pickR_in:
    "⋀j. j ∈ IR ⟹ pickR j ∈ R0"
    "⋀j. j ∈ IR ⟹ pickR j ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    have conj: "pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
      using exR[OF jIR] unfolding pickR_def by (rule someI_ex)
    thus "pickR j ∈ R0" by (rule conjunct1)
  next
    fix j assume jIR: "j ∈ IR"
    have conj: "pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
      using exR[OF jIR] unfolding pickR_def by (rule someI_ex)
    thus "pickR j ∈ blockR_abs enc0 as s kk j" by (rule conjunct2)
  qed

  have subL: "pickL ` IL ⊆ R0"
    by (auto dest: pickL_in)

  have subR: "pickR ` IR ⊆ R0"
    by (auto dest: pickR_in)

  have union_sub: "pickL ` IL ∪ pickR ` IR ⊆ R0"
    using subL subR by auto

  have injL: "inj_on pickL IL"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IL" and j2: "j2 ∈ IL" and eq: "pickL j1 = pickL j2"
    have in1: "pickL j1 ∈ blockL_abs enc0 as s j1" using pickL_in[OF j1] by blast
    have in2: "pickL j2 ∈ blockL_abs enc0 as s j2" using pickL_in[OF j2] by blast
    have "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 ≠ {}"
      using eq in1 in2 by auto
    then show "j1 = j2"
      using Int_emptyI blockL_abs_disjoint j1 j2 subsetI
      by meson
  qed

  have injR: "inj_on pickR IR"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IR" and j2: "j2 ∈ IR" and eq: "pickR j1 = pickR j2"
    have in1: "pickR j1 ∈ blockR_abs enc0 as s kk j1" using pickR_in[OF j1] by blast
    have in2: "pickR j2 ∈ blockR_abs enc0 as s kk j2" using pickR_in[OF j2] by blast
    have "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 ≠ {}"
      using eq in1 in2 by auto
    then show "j1 = j2"
      using Int_emptyI blockR_abs_disjoint j1 j2 subsetI 
      by meson
  qed

  have fin_R0:   "finite R0"             by (simp add: R0_def)
  have fin_imgL: "finite (pickL ` IL)"   by (intro finite_imageI) (simp add: IL_def)
  have fin_imgR: "finite (pickR ` IR)"   by (intro finite_imageI) (simp add: IR_def)

  have card_lower: "card (pickL ` IL ∪ pickR ` IR) ≤ card R0"
    by (rule card_mono[OF fin_R0 union_sub])

  have disj_images: "(pickL ` IL) ∩ (pickR ` IR) = {}"
  proof
    show "(pickL ` IL) ∩ (pickR ` IR) ⊆ {}"
    proof
      fix i assume "i ∈ (pickL ` IL) ∩ (pickR ` IR)"
      then obtain jL jR where jL: "jL ∈ IL" "i = pickL jL"
                          and jR: "jR ∈ IR" "i = pickR jR" by blast
      have iL: "i ∈ blockL_abs enc0 as s jL" using jL pickL_in by auto
      have iR: "i ∈ blockR_abs enc0 as s kk jR" using jR pickR_in by auto
      have "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        using blockL_abs_blockR_abs_disjoint[OF _] IL_def jL(1) 
        by simp
      thus "i ∈ {}" using iL iR by auto
    qed
  qed simp

  have card_union:
    "card (pickL ` IL ∪ pickR ` IR) = card (pickL ` IL) + card (pickR ` IR)"
    by (subst card_Un_disjoint) (use disj_images fin_imgL fin_imgR in auto)

  have inj_cardL: "card (pickL ` IL) = card IL" by (rule card_image[OF injL])
  have inj_cardR: "card (pickR ` IR) = card IR" by (rule card_image[OF injR])

  from card_lower card_union inj_cardL inj_cardR
  have A: "card IL + card IR ≤ card R0" by simp

  have card_IL: "card IL = card (LHS (e_k as s kk) n)"
  proof -
    have "card IL = length (enumL as s kk)" by (simp add: IL_def)
    also have "... = card (LHS (e_k as s kk) n)"
      by (simp add: enumL_def n_def)      (* whichever equation you have for enumL *)
    finally show ?thesis .
  qed
  have card_IR: "card IR = card (RHS (e_k as s kk) n)"
  proof -
    have "card IR = length (enumR as s kk)" by (simp add: IR_def)
    also have "... = card (RHS (e_k as s kk) n)"
      by (simp add: enumR_def n_def)      (* likewise for enumR *)
    finally show ?thesis .
  qed

  have B:
   "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ card R0"
    using A by (simp add: card_IL card_IR)

  have "card R0 ≤ steps M x0"
    by (simp add: R0_def Base.card_read0_le_steps)
  from B this have "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ steps M x0"
    by (rule le_trans)
  thus ?thesis
    by (simp add: x0_def)
qed

end  (* context Coverage_TM *)

end  (* theory *)
