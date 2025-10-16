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

(* intersection non-empty: there exists a value in both LHS and RHS *)
lemma DSS_hit:
  assumes dss: "distinct_subset_sums as"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∈ RHS (e_k as s kk) (length as)"
proof -
  have "∃v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  by (meson DSS_unique_value[OF dss] ex1_implies_ex)
  then show "∃v∈LHS (e_k as s kk) (length as). v ∈ RHS (e_k as s kk) (length as)"
    by (simp add: Bex_def)
qed

(* there exists also an L value not in the R set *)
lemma DSS_miss:
  assumes dss: "distinct_subset_sums as"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∉ RHS (e_k as s kk) (length as)"
proof -
  obtain v where v_unique:
    "v ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as)"
    and uniq:  "⋀w. w ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as) ⟹ w = v"
    using DSS_unique_value[OF dss] by (metis ex1E)
  (* pick any u ∈ LHS differing from v; existence follows since LHS has ≥ 2
     values in your meet-in-the-middle catalogue (or at least one other value such as non-empty subset sum) *)
  have "finite (LHS (e_k as s kk) (length as))" by simp
  moreover have "LHS (e_k as s kk) (length as) ≠ {v}"
    (* justify here: e.g. show LHS has at least two elements in your instance,
       or argue via your earlier “hit+miss” assumptions if you prefer to import them *)
    sorry
  ultimately obtain u where uL: "u ∈ LHS (e_k as s kk) (length as)" and "u ≠ v"
    by (metis finite_singleton insertE insert_not_empty not_ex)
  hence "u ∉ RHS (e_k as s kk) (length as)"
    using uniq v_unique by auto
  thus ?thesis using uL by blast
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
    using DSS_unique_value[OF dss] meet_val by (metis ex1E)
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

lemma DSS_unique_value:
  assumes dss: "distinct_subset_sums as"
  shows "∃! v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
proof -
  obtain v where vL: "v ∈ LHS (e_k as s kk) (length as)"
             and vR: "v ∈ RHS (e_k as s kk) (length as)"
    using DSS_hit[OF dss] by blast
  have at_most_one:
    "⋀w. w ∈ LHS (e_k as s kk) (length as) ∩ RHS (e_k as s kk) (length as) ⟹ w = v"
  proof -
    fix w assume wL: "w ∈ LHS …" and wR: "w ∈ RHS …"
    (* here call your “uniqueness of meet” fact derived from dss,
       or argue via subsets decoding to conclude w = v *)
    (* … *)
  qed
  show ?thesis by (intro ex1I[of _ v]) (use vL vR at_most_one in blast)+
qed

(* >>> Add this new symmetric one right here <<< *)
lemma DSS_missR:
  assumes "distinct_subset_sums as"
  shows "∃v∈RHS (e_k as s kk) (length as). v ∉ LHS (e_k as s kk) (length as)"
  sorry

lemma DSS_baseline_only_jR:
  assumes dss: "distinct_subset_sums as"
      and jR:  "j < length (enumR as s kk)"
  shows
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumR as s kk). j' ≠ j ⟶
        Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
  sorry

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
