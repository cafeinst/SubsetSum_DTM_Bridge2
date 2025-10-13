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
  assumes "distinct_subset_sums as"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∈ RHS (e_k as s kk) (length as)"
  sorry

(* there exists also an L value not in the R set *)
lemma DSS_miss:
  assumes "distinct_subset_sums as"
  shows "∃v ∈ LHS (e_k as s kk) (length as). v ∉ RHS (e_k as s kk) (length as)"
  sorry

(* uniqueness-of-witness for the baseline; adjust statement to what you need *)
lemma DSS_baseline_only_j:
  assumes dss: "distinct_subset_sums as"
      and jL:  "j < length (enumL as s kk)"
  shows "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
         (∀j'<length (enumL as s kk). j' ≠ j ⟶
            Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
  sorry

lemma DSS_unique_value:
  assumes "distinct_subset_sums as"
  shows "∃! v. v ∈ LHS (e_k as s kk) (length as) ∧ v ∈ RHS (e_k as s kk) (length as)"
  sorry

lemma read0_hits_L_min:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
      and jL: "j < length (enumL as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
proof -
  have L2:   "2 ≤ length (enumL as s kk)"
    by (rule enumL_len_ge_2[OF n_def dss])
  have hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
    by simp (rule DSS_hit[OF dss])
  have miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
    by simp (rule DSS_miss[OF dss])
  have baseline_only_j:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumL as s kk). j' ≠ j ⟶
        Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"
    by (rule DSS_baseline_only_j[OF dss jL])
  show ?thesis
    by (rule read0_hits_L[OF n_def dss jL L2 hit miss baseline_only_j])
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

(* -- L blocks are touched --------------------------------------------------- *)

lemma read0_hits_L:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
      and jL: "j < length (enumL as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockL_abs enc0 as s j)"
  hence DISJ: "Base.read0 M ?x ∩ blockL_abs enc0 as s j = {}" by auto

  (* From DSS we get a hit and a miss on catalogs, and uniqueness of baseline witness *)
  have hit: "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
  proof -
    have "∃v∈LHS (e_k as s kk) (length as).
           v ∈ RHS (e_k as s kk) (length as)"
      using DSS_hit[OF ‹distinct_subset_sums as›] .
    then show ?thesis
      using enumL_set enumR_set by simp
  qed

  have miss: "∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
  proof -
    have "∃v∈LHS (e_k as s kk) (length as).
           v ∉ RHS (e_k as s kk) (length as)"
      using DSS_miss[OF ‹distinct_subset_sums as›] .
    then show ?thesis
      using enumL_set enumR_set by simp
  qed

  have baseline_only_j:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
     (∀j'<length (enumL as s kk). j' ≠ j ⟶
        Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk))"  (* from dss *)
  proof
    assume G: "Good as s ((!) (x0 as s)) ((!) (x0 as s))"
    (* DSS_unique_L_witness should say: among the L-values, at most one
       equals some R-value for this instance (when Good holds). *)
    have uniq:
      "⋀j' j''. j' < length (enumL as s kk) ⟹ j'' < length (enumL as s kk) ⟹
        Lval_at as s ((!) (x0 as s)) j' ∈ set (enumR as s kk) ⟹
        Lval_at as s ((!) (x0 as s)) j'' ∈ set (enumR as s kk) ⟹
        j' = j''"
    proof -
      fix j' j'' assume j'L: "j' < length (enumL as s kk)" and j''L: "j'' < length (enumL as s kk)"
      assume inR':  "Lval_at as s ((!) (x0 as s)) j'  ∈ set (enumR as s kk)"
      assume inR'': "Lval_at as s ((!) (x0 as s)) j'' ∈ set (enumR as s kk)"
      (* Turn Lval_at on enc back into the catalog values via your proved lemma *)
      have E':  "Lval_at as s ((!) (x0 as s)) j'  = enumL as s kk ! j'"
        using Lval_at_on_enc_block j'L by simp
      have E'': "Lval_at as s ((!) (x0 as s)) j'' = enumL as s kk ! j''"
        using Lval_at_on_enc_block j''L by simp
      (* Rewrite membership with sets of enumL/enumR *)
      have "enumL as s kk ! j'  ∈ RHS (e_k as s kk) (length as)"
        using inR' E' enumR_set by simp
      moreover
      have "enumL as s kk ! j'' ∈ RHS (e_k as s kk) (length as)"
        using inR'' E'' enumR_set by simp
      ultimately show "j' = j''"
        using DSS_unique_L_witness[OF ‹distinct_subset_sums as› j'L j''L]
        by blast
    qed
    (* Now the requested “only j” statement *)
    show "∀j'<length (enumL as s kk). j' ≠ j ⟶
            Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
    proof (intro allI impI)
      fix j' assume j'L: "j' < length (enumL as s kk)" and neq: "j' ≠ j"
      (* If some j'≠j also hit RHS, uniqueness would be violated *)
      show "Lval_at as s ((!) (x0 as s)) j' ∉ set (enumR as s kk)"
      proof
        assume contra: "Lval_at as s ((!) (x0 as s)) j' ∈ set (enumR as s kk)"
        (* Since Good holds, there exists at least one j0 that hits RHS.
           Pick ours to be the given j, then apply uniqueness. *)
        have jL: "j < length (enumL as s kk)" using G Good_char_encR exE
          by (simp add: jL)
        have inRj: "Lval_at as s ((!) (x0 as s)) j ∈ set (enumR as s kk)"
          using G Good_char_encR jL DSS_unique dss by blast
        from uniq[OF j'L jL contra inRj] show False using neq by simp
      qed
    qed
  qed

  (* Use flipL0 to obtain an oracle that flips Good by changing only block j *)
  obtain oL' where
    OUT: "∀i. i ∉ blockL_abs enc0 as s j ⟹ oL' i = ((!) ?x) i" and
    FLP: "Good as s oL' ((!) ?x) ≠ Good as s ((!) ?x) ((!) ?x)"
    using flipL0[OF jL _ hit miss baseline_only_j] by (cases "2 ≤ length (enumL as s kk)") auto
    (* If you have a lemma ensuring length ≥ 2 from dss, you can discharge the length premise here. *)

  define y where "y i = (if i ∈ blockL_abs enc0 as s j then oL' i else ?x ! i)" for i

  have AGREE: "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y i = ?x ! i"
    by (simp add: y_def)

  (* If block j is unread, changing it cannot change the run *)
  have RUN_EQ:
    "run ((!) y) ((!) ?x) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
    by (rule Run_unread_L[OF DISJ AGREE refl])

  (* But correctness of T0 ties run to Good, giving a contradiction *)
  have "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
    using RUN_EQ correct_T0 by simp
  moreover have "Good as s ((!) y) ((!) ?x) = Good as s oL' ((!) ?x)"
    by (simp add: y_def)
  ultimately show False using FLP by simp
qed

(* -- R blocks are touched --------------------------------------------------- *)
lemma read0_hits_R_min:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
      and jR:    "j < length (enumR as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockR_abs enc0 as s kk j)"
  hence DISJ: "Base.read0 M ?x ∩ blockR_abs enc0 as s kk j = {}" by auto

  (* pick patterns for an 'in L' and an 'out of L' R-value *)
  obtain v_in where vinR: "v_in ∈ RHS (e_k as s kk) (length as)"
                 and vinL: "v_in ∈ LHS (e_k as s kk) (length as)"
    using DSS_hit_R[OF dss] by blast
  obtain v_out where voutR: "v_out ∈ RHS (e_k as s kk) (length as)"
                  and voutNL: "v_out ∉ LHS (e_k as s kk) (length as)"
    using DSS_miss_R[OF dss] by blast

  let ?a = "length (enc0 as s) + offR as s kk j"
  let ?w = "W as s"

  obtain b_in where bin_len: "length b_in = ?w" and bin_val: "from_bits b_in = v_in"
    using vinR bits_roundtrip by (auto simp: enumR_set)
  obtain b_out where bout_len: "length b_out = ?w" and bout_val: "from_bits b_out = v_out"
    using voutR bits_roundtrip by (auto simp: enumR_set)

  (* define y^in / y^out by overwriting exactly the j-th R block *)
  define y_in  where "y_in  i = (if i ∈ blockR_abs enc0 as s kk j then b_in  ! (i - ?a) else ?x ! i)"
  define y_out where "y_out i = (if i ∈ blockR_abs enc0 as s kk j then b_out ! (i - ?a) else ?x ! i)"

  have AGREE_in:  "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y_in  i = ?x ! i"  by (simp add: y_in_def)
  have AGREE_out: "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y_out i = ?x ! i" by (simp add: y_out_def)

  (* evaluate the j-th R value after overwrite *)
  have Rj_in:  "Rval_at as s ((!) y_in)  j = v_in"
    by (simp add: Rval_at_def y_in_def blockR_abs_def offR_def bin_len bin_val)
  have Rj_out: "Rval_at as s ((!) y_out) j = v_out"
    by (simp add: Rval_at_def y_out_def blockR_abs_def offR_def bout_len bout_val)

  (* unread ⇒ run is unchanged *)
  have RUN_in:
    "run ((!) ?x) ((!) y_in) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
    by (rule Run_unread_R[OF DISJ AGREE_in refl])
  have RUN_out:
    "run ((!) ?x) ((!) y_out) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
    by (rule Run_unread_R[OF DISJ AGREE_out refl])

  (* tie run to Good *)
  have G_in_eq:  "Good as s ((!) ?x) ((!) y_in)  = Good as s ((!) ?x) ((!) ?x)" by (simp add: RUN_in  correct_T0)
  have G_out_eq: "Good as s ((!) ?x) ((!) y_out) = Good as s ((!) ?x) ((!) ?x)" by (simp add: RUN_out correct_T0)

  (* but Good_char_encL lets us flip Good by choosing v_in (∈ enumL) vs v_out (∉ enumL) *)
  have inL:  "v_in  ∈ set (enumL as s kk)"  using vinL  by (simp add: enumL_set)
  have outL: "v_out ∉ set (enumL as s kk)"  using voutNL by (simp add: enumL_set)

  have G_in_true:  "Good as s ((!) ?x) ((!) y_in)"
    using Good_char_encL[of as s "((!) ?x)" "((!) y_in)"] jR Rj_in inL by blast
  have G_out_false: "¬ Good as s ((!) ?x) ((!) y_out)"
    using Good_char_encL[of as s "((!) ?x)" "((!) y_out)"] jR Rj_out outL by blast

  from G_in_eq G_in_true G_out_eq G_out_false show False by simp
qed

lemma read0_hits_R:
  assumes n_def: "n = length as" and dss: "distinct_subset_sums as"
      and jR: "j < length (enumR as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
proof (rule ccontr)
  let ?x = "enc as s kk"
  assume H: "¬ (∃i∈Base.read0 M ?x. i ∈ blockR_abs enc0 as s kk j)"
  hence DISJ: "Base.read0 M ?x ∩ blockR_abs enc0 as s kk j = {}" by auto

  (* From DSS, ensure the R catalog has at least two elements *)
  have R2: "2 ≤ length (enumR as s kk)"  (* derivable from dss; insert your lemma *)
    sorry

  (* Flip just the j-th R block while leaving the rest identical *)
  obtain oR' where
    OUT: "∀i. i ∉ blockR_abs enc0 as s kk j ⟹ oR' i = ((!) ?x) i" and
    DIFF: "Rval_at as s oR' j ≠ Rval_at as s ((!) ?x) j"
    using flipR_pointwise_block[OF jR R2, of "((!) ?x)"] by blast

  define y where "y i = (if i ∈ blockR_abs enc0 as s kk j then oR' i else ?x ! i)" for i

  have AGREE: "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y i = ?x ! i"
    by (simp add: y_def)

  (* If block j is unread, changing it cannot change the run *)
  have RUN_EQ:
    "run ((!) ?x) ((!) y) (T0 as s) = run ((!) ?x) ((!) ?x) (T0 as s)"
    by (rule Run_unread_R[OF DISJ AGREE refl])

  (* Correctness of T0: run equals Good *)
  have "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
    using RUN_EQ correct_T0 by simp

  (* But changing only this R block can be arranged to flip Good (by Good_char_encL);
     if you have a direct lemma from DSS that guarantees such a flip exists for some
     choice inside the block, apply it here. Otherwise, argue by cases on baseline
     Good/¬Good and pick a value accordingly, as in coverage_for_enc_blocks_L. *)
  have CONTRA: "Good as s ((!) ?x) ((!) y) ≠ Good as s ((!) ?x) ((!) ?x)"
    (* insert your short case-split on Good using Good_char_encL and the fact DIFF *)
    sorry

  show False using ‹Good as s ((!) ?x) ((!) y) = _› CONTRA by simp
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
    by (rule read0_hits_L_min[OF n_def dss jL])
  thus "touches (enc as s kk) (blockL_abs enc0 as s j)"
    using touches_def by auto
next
  fix j assume jR: "j < length (enumR as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
    by (rule read0_hits_R_min[OF n_def dss jR])
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
