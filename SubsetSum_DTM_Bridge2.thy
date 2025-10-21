theory SubsetSum_DTM_Bridge2
  imports "SubsetSum_DTM_Bridge"
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
  assumes le:  "kk ≤ length as"
      and dss: "distinct_subset_sums as"
      and ex:  "∃v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  shows "∃!v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
proof -
  obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
              and vR: "v ∈ RHS (e_k as s kk) (length as)"
    using ex by blast

  have uniq:
    "⋀w. w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as) ⟹ w = v"
  proof -
    fix w assume hw: "w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as)"
    from DSS_intersection_at_most_one[OF le dss, of v w]
    show "w = v" using vL vR hw DSS_intersection_at_most_one dss le 
      by presburger
  qed

  show ?thesis
  proof (rule ex1I[of _ v])
    show "v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
      using vL vR by simp
  next
    show "⋀w. w ∈ LHS (e_k as s kk) (length as) ∧ w ∈ RHS (e_k as s kk) (length as) ⟹ w = v"
      by (rule uniq)
  qed
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
      and SOL: "∃S⊆{..<length as}. sum_over as S = s"
  shows "∃!v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  using DSS_unique_value_param[OF le dss]
        DSS_hit[OF le dss SOL]
  by auto

(* there exists also an L value not in the R set *)
lemma DSS_miss:
  assumes le:  "kk ≤ length as"
      and dss: "distinct_subset_sums as"
      and twoL: "∃u v. u ∈ LHS (e_k as s kk) (length as)
                     ∧ v ∈ LHS (e_k as s kk) (length as) ∧ u ≠ v"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∉ RHS (e_k as s kk) (length as)"
proof -
  obtain u z where uL: "u ∈ LHS (e_k as s kk) (length as)"
               and zL: "z ∈ LHS (e_k as s kk) (length as)"
               and uneq: "u ≠ z"
    using twoL by blast

  have disj:
  "u ∉ RHS (e_k as s kk) (length as) ∨ z ∉ RHS (e_k as s kk) (length as)"
    using DSS_unique_value_param dss le uL uneq zL by blast

  from disj show ?thesis
  proof
    assume "u ∉ RHS (e_k as s kk) (length as)"
    thus ?thesis using uL by blast
  next
    assume "z ∉ RHS (e_k as s kk) (length as)"
    thus ?thesis using zL by blast
  qed
qed

lemma DSS_missR:
  assumes le:  "kk ≤ length as"
      and dss: "distinct_subset_sums as"
      and twoR: "∃u v. u ∈ RHS (e_k as s kk) (length as)
                     ∧ v ∈ RHS (e_k as s kk) (length as) ∧ u ≠ v"
  shows "∃v ∈ RHS (e_k as s kk) (length as). v ∉ LHS (e_k as s kk) (length as)"
proof -
  obtain u z where uR: "u ∈ RHS (e_k as s kk) (length as)"
               and zR: "z ∈ RHS (e_k as s kk) (length as)"
               and uneq: "u ≠ z"
    using twoR by blast
  have disj: "u ∉ LHS (e_k as s kk) (length as) ∨ z ∉ LHS (e_k as s kk) (length as)"
    using DSS_unique_value_param dss le uR uneq zR by blast
  thus ?thesis
  proof
    assume "u ∉ LHS (e_k as s kk) (length as)"
    thus ?thesis using uR by blast
  next
    assume "z ∉ LHS (e_k as s kk) (length as)"
    thus ?thesis using zR by blast
  qed
qed

lemma DSS_baseline_only_j_ex:
  assumes le:   "kk ≤ length as"
      and dss:  "distinct_subset_sums as"
      and BASE: "Good as s ((!) (x0 as s)) ((!) (x0 as s))"
      and SOL:  "∃S ⊆ {..<length as}. sum_over as S = s"
  shows "∃j<length (enumL as s kk).
           (∀j'<length (enumL as s kk). j' ≠ j ⟶
              Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
proof -
  (* From Good we get at least one L-index whose value lands in the R-catalog *)
  obtain j where jL: "j < length (enumL as s kk)"
    and inRj: "Lval_at as s ((!) (x0 as s)) j ∈ set (enumR as s kk)"
    using BASE Good_char_encR[of as s "(!) (x0 as s)"] by blast

  (* Uniqueness of the intersection value *)
  have ex1:
    "∃!v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
    using DSS_unique_value[OF le dss SOL] .

  (* That unique value is precisely enumL!j *)
  have Vj: "Lval_at as s ((!) (x0 as s)) j = enumL as s kk ! j"
    using Lval_at_on_enc_block jL by simp
  have meet_j:
    "enumL as s kk ! j ∈ LHS (e_k as s kk) (length as) ∧
     enumL as s kk ! j ∈ RHS (e_k as s kk) (length as)"
    using enumL_set enumR_set jL Vj inRj nth_mem by force

  (* Any other j' hitting RHS would force equal enumL-values; but enumL is distinct *)
  have distinctL: "distinct (enumL as s kk)" by (simp add: enumL_def)
  have no_other:
    "∀j'<length (enumL as s kk). j' ≠ j ⟶
       Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
  proof (intro allI impI)
    fix j' assume j'L: "j' < length (enumL as s kk)" and ne: "j' ≠ j"
    have Vj': "Lval_at as s ((!) (x0 as s)) j' = enumL as s kk ! j'"
      using Lval_at_on_enc_block j'L by simp
    show "Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
    proof
      assume "Lval_at as s ((!) (x0 as s)) j' ∈ set (enumR as s kk)"
      then obtain jR' where jR': "jR' < length (enumR as s kk)"
        and EQ': "Rval_at as s ((!) (x0 as s)) jR' = Lval_at as s ((!) (x0 as s)) j'"
        by (metis Rval_at_on_enc_block in_set_conv_nth)
      hence meet_j':
        "enumL as s kk ! j' ∈ LHS (e_k as s kk) (length as) ∧
         enumL as s kk ! j' ∈ RHS (e_k as s kk) (length as)"
        using enumL_set enumR_set j'L Vj'
        by (metis ‹Lval_at as s ((!) (x0 as s)) j' ∈ set (enumR as s kk)› nth_mem)
      from ex1 meet_j meet_j'
      have "enumL as s kk ! j = enumL as s kk ! j'" by auto
      have eq: "enumL as s kk ! j = enumL as s kk ! j'" by fact
      have j_eq: "j = j'"
        using distinctL eq j'L jL nth_eq_iff_index_eq by blast
      from ne and j_eq show False by simp
    qed
  qed
  show ?thesis using jL no_other by blast
qed

lemma DSS_baseline_only_jR_ex:
  assumes le:   "kk ≤ length as"
      and dss:  "distinct_subset_sums as"
      and BASE: "Good as s ((!) (x0 as s)) ((!) (x0 as s))"
      and SOL:  "∃S ⊆ {..<length as}. sum_over as S = s"
  shows "∃j<length (enumR as s kk).
           (∀j'<length (enumR as s kk). j' ≠ j ⟶
              Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
proof -
  (* From Good we get at least one R-index whose value lands in the L-catalog *)
  obtain j where jR: "j < length (enumR as s kk)"
    and inLj: "Rval_at as s ((!) (x0 as s)) j ∈ set (enumL as s kk)"
    using BASE Good_char_encL[of as s "(!) (x0 as s)"] by blast

  (* Uniqueness of the intersection value *)
  have ex1:
    "∃!v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
    using DSS_unique_value[OF le dss SOL] .

  (* That unique value is precisely enumR!j *)
  have Vj: "Rval_at as s ((!) (x0 as s)) j = enumR as s kk ! j"
    using Rval_at_on_enc_block jR by simp
  have meet_j:
    "enumR as s kk ! j ∈ RHS (e_k as s kk) (length as) ∧
     enumR as s kk ! j ∈ LHS (e_k as s kk) (length as)"
    using enumL_set enumR_set jR Vj inLj by (metis nth_mem)

  (* Any other j' hitting L would force equal enumR-values; but enumR is distinct *)
  have distinctR: "distinct (enumR as s kk)" by (simp add: enumR_def)
  have no_other:
    "∀j'<length (enumR as s kk). j' ≠ j ⟶
       Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk)"
  proof (intro allI impI)
    fix j' assume j'R: "j' < length (enumR as s kk)" and ne: "j' ≠ j"
    have Vj': "Rval_at as s ((!) (x0 as s)) j' = enumR as s kk ! j'"
      using Rval_at_on_enc_block j'R by simp
    show "Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk)"
    proof
      assume "Rval_at as s ((!) (x0 as s)) j' ∈ set (enumL as s kk)"
      then obtain jL' where jL': "jL' < length (enumL as s kk)"
        and EQ': "Lval_at as s ((!) (x0 as s)) jL' = Rval_at as s ((!) (x0 as s)) j'"
        by (metis Lval_at_on_enc_block in_set_conv_nth)
      hence meet_j':
        "enumR as s kk ! j' ∈ RHS (e_k as s kk) (length as) ∧
         enumR as s kk ! j' ∈ LHS (e_k as s kk) (length as)"
        using enumL_set enumR_set j'R Vj'
        by (metis ‹Rval_at as s ((!) (x0 as s)) j' ∈ set (enumL as s kk)› nth_mem)
      from ex1 meet_j meet_j'
      have "enumR as s kk ! j = enumR as s kk ! j'" by auto
      have eq: "enumL as s kk ! j = enumL as s kk ! j'"
        using ‹enumR as s kk ! j = enumR as s kk ! j'› distinctR j'R jR nth_eq_iff_index_eq by blast
      have neq: "enumL as s kk ! j ≠ enumL as s kk ! j'"
        using ‹enumR as s kk ! j = enumR as s kk ! j'› distinctR j'R jR ne nth_eq_iff_index_eq by blast
      from eq and neq show False by contradiction
    qed
  qed
  show ?thesis using jR no_other by blast
qed

lemma twoL_witness:
  assumes le: "kk ≤ length as"
      and dss: "distinct_subset_sums as"
      and kkpos: "kk > 0"
  shows "∃u v. u ∈ LHS (e_k as s kk) (length as)
           ∧ v ∈ LHS (e_k as s kk) (length as) ∧ u ≠ v"
proof -
  have inj: "inj_on (sum_over as) {U. U ⊆ {..<length as}}"
    by (rule distinct_subset_sums_inj_len[OF dss])

  have "{} ⊆ {..<kk}" by simp
  with le have "{0} ⊆ {..<kk}" using kkpos by auto

  have u_in: "sum_over as {} ∈ LHS (e_k as s kk) (length as)"
    using LHS_char[OF le] by blast
  have v_in: "sum_over as {0} ∈ LHS (e_k as s kk) (length as)"
    using LHS_char[OF le] kkpos by blast

  have "sum_over as {} ≠ sum_over as {0}"
  proof
    assume eq: "sum_over as {} = sum_over as {0}"
    have A0: "{} ∈ {U. U ⊆ {..<length as}}" by simp
    have A1: "{0} ⊆ {..<length as}" using le kkpos by auto
    hence A1': "{0} ∈ {U. U ⊆ {..<length as}}" by simp
    from inj eq A0 A1' have "{} = {0}" 
      using inj_onD by (metis insert_not_empty)
    thus False by simp
  qed

  then show ?thesis using u_in v_in by blast
qed

lemma twoR_witness:
  assumes le:   "kk ≤ length as"
      and dss:  "distinct_subset_sums as"
      and kklt: "kk < length as"
  shows "∃u v.
           u ∈ RHS (e_k as s kk) (length as)
         ∧ v ∈ RHS (e_k as s kk) (length as) ∧ u ≠ v"
proof -
  have inj: "inj_on (sum_over as) {U. U ⊆ {..<length as}}"
    by (rule distinct_subset_sums_inj_len[OF dss])

  have emp_sub: "{} ⊆ {kk..<length as}" by simp
  have kk_sub:  "{kk} ⊆ {kk..<length as}" using kklt by auto

  let ?u = "s - sum_over as {}"
  let ?v = "s - sum_over as {kk}"

  have u_in: "?u ∈ RHS (e_k as s kk) (length as)"
  proof -
    have "sum_over as {} = s - ?u" by simp
    with emp_sub show ?thesis
      using RHS_char[OF le] by blast
  qed

  have v_in: "?v ∈ RHS (e_k as s kk) (length as)"
  proof -
    have "sum_over as {kk} = s - ?v" by simp
    with kk_sub show ?thesis
      using RHS_char[OF le] by blast
  qed

  have "?u ≠ ?v"
  proof
    assume eq: "?u = ?v"
    hence eqSums: "sum_over as {} = sum_over as {kk}" by simp
    have A0: "{} ∈ {U. U ⊆ {..<length as}}" by simp
    have A1': "{kk} ∈ {U. U ⊆ {..<length as}}" using kklt by simp
    from inj_onD[OF inj eqSums A0 A1'] have "{} = {kk}" .
    thus False by simp
  qed

  thus ?thesis using u_in v_in by blast
qed

(* If two bit-slices are equal on the j-window, the corresponding Lval_at are equal. *)
lemma Lval_eq_of_slice_eq:
  fixes f g :: "nat ⇒ bool"
  assumes A: "map f [a ..< a + w] = map g [a ..< a + w]"
  assumes a_def: "a = length (enc0 as s) + offL as s j"
  assumes w_def: "w = W as s"
  shows "Lval_at as s f j = Lval_at as s g j"
proof -
  have "from_bits (map f [a ..< a + w]) = from_bits (map g [a ..< a + w])"
    using A by presburger
  thus ?thesis
    unfolding Lval_at_def a_def w_def by simp
qed

(* If a function equals x at every index of a block, the slice equals x’s slice. *)
lemma slice_eq_of_pointwise_outside:
  fixes f :: "nat ⇒ bool"
  assumes OUT: "⋀i. i ∈ {a ..< a + w} ⟹ f i = x i"
  shows "map f [a ..< a + w] = map x [a ..< a + w]"
proof (rule nth_equalityI)
  show "length (map f [a ..< a + w]) = length (map x [a ..< a + w])" by simp
next
  fix t assume "t < length (map f [a ..< a + w])"
  hence "t < w" by simp
  then have idx: "[a ..< a + w] ! t = a + t" by simp
  with OUT[of "a+t"] ‹t < w› show "map f [a ..< a + w] ! t = map x [a ..< a + w] ! t"
    by (simp add: idx)
qed

(* Peel away a single candidate j from Good when it is known to miss. *)
lemma Good_drop_witness_encR:
  assumes miss: "Lval_at as s f j ∉ RHS (e_k as s kk) (length as)"
  assumes le:   "kk ≤ length as"
  shows "Good as s f ((!) (enc as s kk)) ⟷
         (∃j'<length (enumL as s kk). j' ≠ j ∧
            Lval_at as s f j' ∈ RHS (e_k as s kk) (length as))"
proof -
  (* Characterize Good with enc on the right, then switch set(enumR) ↔ RHS *)
  have Gdef_set:
    "Good as s f ((!) (enc as s kk)) ⟷
     (∃j'<length (enumL as s kk).
        Lval_at as s f j' ∈ set (enumR as s kk))"
    using le Good_char_encR by simp
  have Gdef:
    "Good as s f ((!) (enc as s kk)) ⟷
     (∃j'<length (enumL as s kk).
        Lval_at as s f j' ∈ RHS (e_k as s kk) (length as))"
    using Gdef_set by simp

  (* Remove the bad candidate j from the existential using miss *)
  have Ex_remove_j:
    "(∃j'<length (enumL as s kk).
        Lval_at as s f j' ∈ RHS (e_k as s kk) (length as))
     ⟷ (∃j'<length (enumL as s kk). j' ≠ j ∧
        Lval_at as s f j' ∈ RHS (e_k as s kk) (length as))"
  proof
    assume ex1:
      "∃j'<length (enumL as s kk).
         Lval_at as s f j' ∈ RHS (e_k as s kk) (length as)"
    then obtain j' where j'L:
      "j' < length (enumL as s kk)" and Hin:
      "Lval_at as s f j' ∈ RHS (e_k as s kk) (length as)" by blast
    have "j' ≠ j" using miss Hin by auto
    thus "∃j'<length (enumL as s kk). j' ≠ j ∧
             Lval_at as s f j' ∈ RHS (e_k as s kk) (length as)"
      using j'L Hin by blast
  next
    assume ex2:
      "∃j'<length (enumL as s kk). j' ≠ j ∧
         Lval_at as s f j' ∈ RHS (e_k as s kk) (length as)"
    then show
      "∃j'<length (enumL as s kk).
         Lval_at as s f j' ∈ RHS (e_k as s kk) (length as)"
      by blast
  qed

  from Gdef Ex_remove_j show ?thesis by blast
qed

end  (* context Coverage_TM *)

end  (* theory *)
