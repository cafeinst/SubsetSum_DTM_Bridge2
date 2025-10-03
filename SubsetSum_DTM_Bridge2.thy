theory SubsetSum_DTM_Bridge2
  imports "SubsetSum_DecisionTree" "SubsetSum_DTM_Bridge"
begin

context Coverage_TM
begin

lemma run_drive_T0:
  "run oL oR (T0 as s)
   = final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) oL)"
  by (simp add: run_tm_to_dtr' T0_def)

lemma drive_char_RHS_core:
  "final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) oL)
   = Good as s oL ((!) (x0 as s))"
proof -
  define x where [simp]: "x = x0 as s"
  define T where [simp]: "T = T0 as s"

  (* x is the canonical encoding, so the “T0 subset read0” lemmas apply *)
  have x_enc[simp]: "x = enc as s kk" by simp

  (* run/drive bridge *)
  have RUN0:
    "final_acc (drive (steps M x) (conf M x 0) oL) = run oL ((!) x) T"
    by (simp add: run_drive_T0)

  (* What may be read *)
  define may_read :: "nat set"
    where "may_read ≡ Lset as s ∪ Rset as s"

  (* Build y from oL but keep x outside may_read *)
  define Y :: "nat ⇒ bool"
    where "Y i = (if i ∈ may_read then oL i else x ! i)"
  define y where "y = map Y [0..<length x]"

  (* (x,y) orientation *)
  have SL_sub_read0_xy:
    "seenL_run ((!) x) ((!) y) T ⊆ Base.read0 M x"
    by (simp add: seenL_T0_subset_read0)

  (* (y,x) orientation — this one is used later *)
have SL_sub_read0_yx:
  "seenL_run ((!) y) ((!) x) T ⊆ Base.read0 M x"
  unfolding x_def T_def
  by (simp add: x0_is_enc seenL_T0_subset_read0)

have SL_sub_read0_yx:
  "seenL_run ((!) y) ((!) x) T ⊆ Base.read0 M x"
  by (simp add: x_def T_def SL_sub_read0_yx0)

  (* size facts for windows *)
  have len_x[simp]:
    "length x = length (enc0 as s) + length (padL as s kk) + length (padR as s kk)"
    by (simp add: enc_def)

  (* any read0 lies in may_read *)
  have read0_sub_may: "Base.read0 M x ⊆ may_read"
    unfolding may_read_def
    by (simp add: read0_subset_blocks_abs)

  (* indices in may_read are within bounds of x *)
  have may_read_lt_len:
    "⋀i. i ∈ may_read ⟹ i < length x"
  proof -
    fix i assume "i ∈ may_read"
    hence "i ∈ Lset as s ∨ i ∈ Rset as s" by (simp add: may_read_def)
    then consider
      (L) j where "j < length (enumL as s kk)" and "i ∈ blockL_abs enc0 as s j"
    | (R) j where "j < length (enumR as s kk)" and "i ∈ blockR_abs enc0 as s kk j"
      unfolding Lset_def Rset_def by auto
    thus "i < length x"
    proof cases
      case (L j)
      let ?a = "length (enc0 as s) + offL as s j"
      let ?w = "W as s"
      have blk: "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
        by (simp add: blockL_abs_def offL_def)
      have top: "?a + ?w ≤ length x"
        using offL_window_in_enc[OF L(1)] by simp
      from L(2) have "i ∈ {?a ..< ?a + ?w}" by (simp add: blk)
      then have "i < ?a + ?w" by simp
      with top show ?thesis by linarith
    next
      case (R j)
      let ?a = "length (enc0 as s) + offR as s kk j"
      let ?w = "W as s"
      have blk: "blockR_abs enc0 as s kk j = {?a ..< ?a + ?w}"
        by (simp add: blockR_abs_def)
      have top: "?a + ?w ≤ length x"
        using offR_window_in_enc[OF R(1)] length_padL by simp
      from R(2) have "i ∈ {?a ..< ?a + ?w}" by (simp add: blk)
      then have "i < ?a + ?w" by simp
      with top show ?thesis by linarith
    qed
  qed

  (* agree on what the left side actually sees *)
  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) x) ((!) y) T ⟹ y ! i = oL i"
  proof -
    fix i assume iSL: "i ∈ seenL_run ((!) x) ((!) y) T"
    from SL_sub_read0_xy iSL have iR0: "i ∈ Base.read0 M x" by blast
    from read0_sub_may iR0 have iMay: "i ∈ may_read" by blast
    from may_read_lt_len iMay have iLt: "i < length x" .
    have "y ! i = (map Y [0..<length x]) ! i" by (simp add: y_def)
    also from iLt have "... = Y i" by simp
    also from iMay have "... = oL i" by (simp add: Y_def)
    finally show "y ! i = oL i" .
  qed

  (* normalize Good on the left windows *)
  have Good_normalize:
    "Good as s ((!) y) ((!) x) = Good as s oL ((!) x)"
  proof -
    have Lwin_eq:
      "⋀j. j < length (enumL as s kk) ⟹
         Lval_at as s ((!) y) j = Lval_at as s oL j"
    proof -
      fix j assume jL: "j < length (enumL as s kk)"
      let ?a = "length (enc0 as s) + offL as s j"
      let ?w = "W as s"
      have blk: "blockL_abs enc0 as s j = {?a ..< ?a + ?w}"
        by (simp add: blockL_abs_def offL_def)
      have ALe: "?a + ?w ≤ length x"
        using offL_window_in_enc[OF jL] by simp
      have slice_eq:
        "map ((!) y) [?a ..< ?a + ?w] = map oL [?a ..< ?a + ?w]"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [?a..< ?a+?w]) =
              length (map oL       [?a..< ?a+?w])" by simp
      next
        fix t assume "t < length (map ((!) y) [?a..< ?a+?w])"
        then have tw: "t < ?w" by simp
        have idx: "[?a..< ?a+?w] ! t = ?a + t" using tw by simp
        have AT: "?a + t < length x" using ALe tw by linarith
        have in_may: "?a + t ∈ may_read"
        proof -
          have mem: "?a + t ∈ blockL_abs enc0 as s j" by (simp add: blk tw)
          have fam: "blockL_abs enc0 as s j
                       ∈ (blockL_abs enc0 as s ` {..<length (enumL as s kk)})"
            using jL by (intro imageI) simp
          show ?thesis
            unfolding may_read_def Lset_def by (intro UnI1 UnionI[OF fam mem])
        qed
        show "map ((!) y) [?a..< ?a+?w] ! t = map oL [?a..< ?a+?w] ! t"
          by (simp add: idx y_def Y_def AT in_may)
      qed
      show "Lval_at as s ((!) y) j = Lval_at as s oL j"
        by (simp add: Lval_at_def slice_eq)
    qed
    show ?thesis by (simp add: Good_def good_def Lwin_eq)
  qed

  (* agree-on-seen for (y,x) to switch run to oL *)
  have agree_on_seenL_for_pair:
    "⋀i. i ∈ seenL_run ((!) y) ((!) x) T ⟹ (!) y i = oL i"
  proof -
    fix i assume iSL: "i ∈ seenL_run ((!) y) ((!) x) T"
    from SL_sub_read0_yx iSL have iR0: "i ∈ Base.read0 M x" by blast
    from read0_sub_may iR0 have iMay: "i ∈ may_read" by blast
    have iLt: "i < length x" by (rule may_read_lt_len[OF iMay])
    have "(!) y i = y ! i" by simp
    also have "... = (map Y [0..<length x]) ! i" by (simp add: y_def)
    also from iLt have "... = Y i" by simp
    also from iMay have "... = oL i" by (simp add: Y_def)
    finally show "(!) y i = oL i" .
  qed

  have run_yx_eq_olx:
    "run ((!) y) ((!) x) T = run oL ((!) x) T"
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) y) ((!) x) T ⟹ (!) y i = oL i"
      by (rule agree_on_seenL_for_pair)
  next
    show "⋀i. i ∈ seenR_run ((!) y) ((!) x) T ⟹ (!) x i = (!) x i" by simp
  qed

  have run_xx_eq_Good_xx:
    "run ((!) x) ((!) x) T = Good as s ((!) x) ((!) x)"
    by (rule correct_T0)

  have SL_sub_read0_x:
    "seenL_run ((!) x) ((!) x) T ⊆ Base.read0 M x"
    by (rule seenL_T0_subset_read0) simp

  have run_yx_eq_xx:
    "run ((!) y) ((!) x) T = run ((!) x) ((!) x) T"
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) y) ((!) x) T ⟹ (!) y i = (!) x i"
    proof -
      fix i assume iSL: "i ∈ seenL_run ((!) y) ((!) x) T"
      from SL_sub_read0_x iSL have "i ∈ Base.read0 M x" by blast
      with read0_sub_may have "i ∈ may_read" by blast
      thus "(!) y i = (!) x i" by (simp add: y_def Y_def)
    qed
  next
    show "⋀i. i ∈ seenR_run ((!) y) ((!) x) T ⟹ (!) x i = (!) x i" by simp
  qed

  have "run oL ((!) x) T = run ((!) y) ((!) x) T"
    by (simp add: run_yx_eq_olx[symmetric])
  also have "... = run ((!) x) ((!) x) T" by (rule run_yx_eq_xx)
  also have "... = Good as s ((!) x) ((!) x)" by (rule run_xx_eq_Good_xx)
  also have "... = Good as s ((!) y) ((!) x)"
    by (simp add: Good_normalize[symmetric])
  finally show ?thesis by (simp add: RUN0)
qed

lemma drive_char_LHS_core:
   "final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) ((!) (x0 as s)))
   = Good as s ((!) (x0 as s)) oR"
proof -
  let ?x = "x0 as s"
  let ?T = "T0 as s"

  have RUN0:
    "final_acc (drive (steps M ?x) (conf M ?x 0) ((!) ?x)) = run ((!) ?x) oR ?T"
    by (simp add: run_drive_T0)

  define may_read where "may_read ≡ Lset as s ∪ Rset as s"
  define Z where "Z i = (if i ∈ may_read then oR i else ?x ! i)" for i
  define z where "z = map Z [0..<length ?x]"
  have len_z[simp]: "length z = length ?x" by (simp add: z_def)

   have SR_sub_read0:
    "seenR_run ((!) ?x) ((!) z) ?T ⊆ Base.read0 M ?x"
    by (rule seenR_T0_subset_read0) (simp add: x0_is_enc)
  have read0_sub_may:
    "Base.read0 M ?x ⊆ may_read"
    unfolding may_read_def by (rule read0_subset_blocks_abs)

  have agree_on_seenR:
    "⋀i. i ∈ seenR_run ((!) ?x) ((!) z) ?T ⟹ (!) z i = oR i"
    by (simp add: z_def Z_def SR_sub_read0 read0_sub_may)

  have Good_normalize_R:
    "Good as s ((!) ?x) ((!) z) = Good as s ((!) ?x) oR"
  proof -
    have Rwin_eq:
      "⋀j. j < length (enumR as s kk) ⟹
           Rval_at as s ((!) z) j = Rval_at as s oR j"
    proof -
      fix j assume jR: "j < length (enumR as s kk)"
      let ?a = "length (enc0 as s) + offR as s kk j"
      let ?w = "W as s"
      have blk: "blockR_abs enc0 as s kk j = {?a ..< ?a + ?w}"
        by (simp add: blockR_abs_def)
      have slice_eq:
        "map ((!) z) [?a ..< ?a + ?w] = map oR [?a ..< ?a + ?w]"
      proof (rule nth_equalityI)
        show "length (map ((!) z) [?a..< ?a+?w]) = 
              length (map oR [?a..< ?a+?w])" by simp
      next
        fix t assume tlt: "t < length (map ((!) z) [?a..< ?a+?w])"
        hence tw: "t < ?w" by simp
        have idx: "[?a..< ?a+?w] ! t = ?a + t" using tw by simp
        have mem: "?a + t ∈ blockR_abs enc0 as s kk j" by (simp add: blk tw)
        have in_may: "?a + t ∈ may_read"
          unfolding may_read_def
          by (intro UnI2) (simp add: Rset_def blockR_abs_def UN_iff jR)
        show "map ((!) z) [?a..< ?a+?w] ! t = map oR [?a..< ?a+?w] ! t"
          by (simp add: idx z_def Z_def in_may)
      qed
      show "Rval_at as s ((!) z) j = Rval_at as s oR j"
        by (simp add: Rval_at_def slice_eq)
    qed
    show ?thesis
      unfolding Good_def good_def by (metis Rwin_eq)
  qed

  have run_xz_eq_xoR:
    "run ((!) ?x) ((!) z) ?T = run ((!) ?x) oR ?T"
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) ?x) ((!) z) ?T ⟹ (!) ?x i = (!) ?x i" by simp
  next
    show "⋀i. i ∈ seenR_run ((!) ?x) ((!) z) ?T ⟹ (!) z i = oR i"
      by (rule agree_on_seenR)
  qed

  have run_xx_eq_Good_xx:
    "run ((!) ?x) ((!) ?x) ?T = Good as s ((!) ?x) ((!) ?x)"
    by (rule correct_T0)

  have SR_sub_read0_x:
    "seenR_run ((!) ?x) ((!) ?x) ?T ⊆ Base.read0 M ?x"
    by (rule seenR_T0_subset_read0) simp

  have run_xz_eq_xx:
    "run ((!) ?x) ((!) z) ?T = run ((!) ?x) ((!) ?x) ?T"
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) ?x) ((!) z) ?T ⟹ (!) ?x i = (!) ?x i" 
      by simp
  next
    show "⋀i. i ∈ seenR_run ((!) ?x) ((!) z) ?T ⟹ (!) z i = (!) ?x i"
    proof -
      fix i assume iSR: "i ∈ seenR_run ((!) ?x) ((!) z) ?T"
      from SR_sub_read0 iSR have "i ∈ Base.read0 M ?x" by blast
      with read0_sub_may have "i ∈ may_read" by blast
      thus "(!) z i = (!) ?x i" by (simp add: z_def Z_def)
    qed
  qed

  have "run ((!) ?x) oR ?T = run ((!) ?x) ((!) z) ?T"
    by (simp add: run_xz_eq_xoR[symmetric])
  also have "... = run ((!) ?x) ((!) ?x) ?T"
    by (rule run_xz_eq_xx)
  also have "... = Good as s ((!) ?x) ((!) ?x)"
    by (rule run_xx_eq_Good_xx)
  also have "... = Good as s ((!) ?x) ((!) z)"
    by (simp add: Good_normalize_R[symmetric])
  also have "... = Good as s ((!) ?x) oR"
    by (simp add: Good_normalize_R)
  finally show ?thesis by (simp add: RUN0)
qed

lemma run_T0_mixed_bridge:
  "run oL ((!) (x0 as s)) (T0 as s) = Good as s oL ((!) (x0 as s))"
  by (simp add: run_drive_T0 drive_char_RHS_core)

lemma run_T0_left_bridge:
  "run ((!) (x0 as s)) oR (T0 as s) = Good as s ((!) (x0 as s)) oR"
  by (simp add: run_drive_T0 drive_char_LHS_core)

lemma run_T0_encR_catalog:
  "run oL ((!) (x0 as s)) (T0 as s)
   = (∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk))"
  by (simp add: run_T0_mixed_bridge Good_char_encR)

lemma run_T0_encL_catalog:
  "run ((!) (x0 as s)) oR (T0 as s)
   = (∃jR<length (enumR as s kk). Rval_at as s oR jR ∈ set (enumL as s kk))"
  by (simp add: run_T0_left_bridge Good_char_encL)

(* 3) Mixed bridge: run on T0 with (oL, encR) equals Good with (oL, encR) *)

lemma Lval_at_on_x0_block[simp]:
  assumes "jL < length (enumL as s kk)"
  shows   "Lval_at as s ((!) (x0 as s)) jL = enumL as s kk ! jL"
  using assms by (rule Lval_at_on_enc_block)  (* or whatever your base lemma is *)

lemma flipR_setval:
  assumes jR: "j < length (enumR as s kk)"
      and R2: "2 ≤ length (enumR as s kk)"
      and vR: "v ∈ set (enumR as s kk)"
  shows
    "∃oR'. (∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = (x0 as s) ! i)
         ∧  Rval_at as s oR' j = v"
proof -
  define a where "a = length (enc0 as s) + offR as s kk j"
  define w where "w = W as s"
  have BND: "a + w ≤ length (x0 as s)"
    by (simp add: a_def w_def offR_window_in_enc[OF jR])

  (* choose the fixed-width bit pattern for v *)
  obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v"
    using vR bits_roundtrip w_def by blast

  (* build oR' by overwriting exactly the j-th R block with pat *)
  define oR' where
    "oR' i = (if i ∈ {a ..< a + w} then pat ! (i - a) else (x0 as s) ! i)" for i

  have outside:
    "∀i. i ∉ blockR_abs enc0 as s kk j ⟶ oR' i = (x0 as s) ! i"
    by (simp add: oR'_def a_def w_def blockR_abs_def offR_def)

  (* slice [a ..< a+w] equals pat under oR' *)
  have slice_pat: "map oR' [a ..< a + w] = pat"
  proof (rule nth_equalityI)
    show "length (map oR' [a ..< a + w]) = length pat" by (simp add: pat_len)
  next
    fix t assume "t < length (map oR' [a ..< a + w])"
    hence tw: "t < w" by simp
    have idx: "[a ..< a + w] ! t = a + t" using tw by simp
    have inblk: "a ≤ a + t ∧ a + t < a + w" using tw by simp
    show "map oR' [a ..< a + w] ! t = pat ! t"
      using nth_map idx oR'_def inblk by (simp add: tw)
  qed

  (* compute Rval_at on that block: it becomes v *)
  have R_at_j: "Rval_at as s oR' j = v"
  proof -
    have "Rval_at as s oR' j
          = from_bits (map oR' [a ..< a + w])"
      by (simp add: Rval_at_def a_def w_def)
    also have "... = from_bits pat" by (simp add: slice_pat)
    also have "... = v" by (simp add: pat_val)
    finally show ?thesis .
  qed

  show ?thesis by (intro exI[of _ oR']) (use outside R_at_j in auto)
qed

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



lemma Good_unread_L_local:
  assumes disj: "Base.read0 M x ∩ blockL_abs enc0 as s j = {}"
  assumes out:  "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = x ! i"
  assumes X:    "x = enc as s kk"
  shows "Good as s ((!) y) ((!) x) = Good as s ((!) x) ((!) x)"
proof -
  (* turn X into the form needed by seenL_T0_subset_read0 *)
  have X0: "x = x0 as s" by (simp add: X x0_is_enc)

  (* T0’s left-seen set is contained in read0 on x0-inputs *)
  have SLsub:
    "seenL_run ((!) y) ((!) x) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenL_T0_subset_read0[OF X0])

  (* y and x agree on everything T0 ever looks at on the left *)
  have agree_on_seenL:
    "⋀i. i ∈ seenL_run ((!) y) ((!) x) (T0 as s) ⟹ (!) y i = (!) x i"
  proof -
    fix i assume "i ∈ seenL_run ((!) y) ((!) x) (T0 as s)"
    with SLsub have "i ∈ Base.read0 M x" by blast
    with disj have "i ∉ blockL_abs enc0 as s j" by auto
    with out show "(!) y i = (!) x i" by simp
  qed

  (* thus the runs coincide *)
  have RUN_eq:
    "run ((!) y) ((!) x) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
    by (rule run_agrees_on_seen) (simp_all add: agree_on_seenL)

  (* bridge Good ↔ run: do it in two tiny steps to avoid purple *)
  have G_yx_to_run0:
    "Good as s ((!) y) ((!) (x0 as s)) = run ((!) y) ((!) (x0 as s)) (T0 as s)"
    by (simp add: run_T0_mixed_bridge[symmetric])
  have G_yx_to_run:
    "Good as s ((!) y) ((!) x) = run ((!) y) ((!) x) (T0 as s)"
    by (simp add: X0 G_yx_to_run0)

  have G_xx_to_run0:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s))
       = run ((!) (x0 as s)) ((!) (x0 as s)) (T0 as s)"
    by (simp add: run_T0_mixed_bridge[symmetric])
  have G_xx_to_run:
    "Good as s ((!) x) ((!) x) = run ((!) x) ((!) x) (T0 as s)"
    by (simp add: X0 G_xx_to_run0)

  from G_yx_to_run RUN_eq G_xx_to_run[symmetric] show ?thesis by simp
qed

lemma coverage_for_enc_blocks_L:
  assumes L2:   "2 ≤ length (enumL as s kk)"
      and hit:  "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
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
    have blk_repr: "blockL_abs enc0 as s j = {a..<a + w}"
      by (simp add: a_def w_def blockL_abs_def offL_def)

    have X0: "?x = enc as s kk" by simp

    consider (G) "Good as s ((!) ?x) ((!) ?x)"
           | (NG) "¬ Good as s ((!) ?x) ((!) ?x)" by blast
    then show False
    proof cases
      case G
      from miss obtain v_out where vL: "v_out ∈ set (enumL as s kk)"
                               and vNR: "v_out ∉ set (enumR as s kk)" by blast
      obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v_out"
        using vL bits_roundtrip w_def by blast
      define oL' where "oL' i = (if i ∈ {a..<a + w} then pat ! (i - a) else ?x ! i)" for i
      define y where "y = splice a w ?x (map oL' [a..<a + w])"

      have LEN: "length (map oL' [a..<a + w]) = w" by simp
      have outside_y:
        "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockL_abs enc0 as s j"
        with blk_repr have nin': "i ∉ {a..<a + w}" by simp
        have AL: "a ≤ length ?x" using offL_window_in_enc[OF jL] a_def w_def by linarith
        show "y ! i = ?x ! i"
          using nin' by (cases "i < a")
                        (simp_all add: y_def splice_nth_left AL splice_nth_right[OF LEN])
      qed

      have slice_pat: "map oL' [a..<a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oL' [a..<a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oL' [a..<a + w])"
        then have tw: "t < w" by simp
        have idx: "[a..<a + w] ! t = a + t" using tw by simp
        show "map oL' [a..<a + w] ! t = pat ! t"
          by (simp add: oL'_def idx tw)
      qed

      have Lj_y: "Lval_at as s ((!) y) j = v_out"
        unfolding Lval_at_def a_def w_def
        by (simp add: slice_pat from_bits.simps)

      have Good_y: "¬ Good as s ((!) y) ((!) ?x)"
      proof -
        have "Lval_at as s ((!) y) j ∉ set (enumR as s kk)"
          using Lj_y vNR by simp
        moreover have
          "⋀j'. j' < length (enumL as s kk) ⟹ j' ≠ j ⟹
             Lval_at as s ((!) y) j' ∉ set (enumR as s kk)"
        proof -
          fix j' assume j'lt: "j' < length (enumL as s kk)" and ne: "j' ≠ j"
          have eq_other:
            "Lval_at as s ((!) y) j' = Lval_at as s ((!) ?x) j'"
          proof -
            define a' where "a' = length (enc0 as s) + offL as s j'"
            define w' where "w' = W as s"
            have blk': "blockL_abs enc0 as s j' = {a'..<a'+w'}"
              by (simp add: a'_def w'_def blockL_abs_def offL_def)
            have disj: "blockL_abs enc0 as s j ∩ blockL_abs enc0 as s j' = {}"
              using blockL_abs_disjoint[OF ne].
            have eq_on: "⋀i. i ∈ blockL_abs enc0 as s j' ⟹ y ! i = ?x ! i"
              using outside_y by (intro) (use disj in auto)
            show ?thesis
            proof (rule nth_equalityI)
              show "length (map ((!) y) [a'..<a'+w']) =
                    length (map ((!) ?x) [a'..<a'+w'])" by simp
            next
              fix t assume tlt: "t < length (map ((!) y) [a'..<a'+w'])"
              hence tw: "t < w'" by simp
              have idx: "[a'..<a'+w'] ! t = a' + t" using tw by simp
              have mem: "a' + t ∈ blockL_abs enc0 as s j'" by (simp add: blk' tw)
              show "map ((!) y) [a'..<a'+w'] ! t
                    = map ((!) ?x) [a'..<a'+w'] ! t"
                by (simp add: idx tw eq_on[OF mem])
            qed
          qed
          from baseline_only_j[OF G, of j'] j'lt ne show
            "Lval_at as s ((!) y) j' ∉ set (enumR as s kk)"
            by (simp add: eq_other)
        qed
        ultimately show ?thesis
          by (simp add: Good_char_encR)
      qed

      have unread_eq:
        "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_L_local[OF not_touch _ X0])
           (simp add: outside_y)
      from unread_eq G Good_y show False by simp

    next
      case NG
      from hit obtain v_in where vL: "v_in ∈ set (enumL as s kk)"
                             and vR: "v_in ∈ set (enumR as s kk)" by blast
      obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v_in"
        using vL bits_roundtrip w_def by blast
      define oL' where "oL' i = (if i ∈ {a..<a + w} then pat ! (i - a) else ?x ! i)" for i
      define y where "y = splice a w ?x (map oL' [a..<a + w])"

      have LEN: "length (map oL' [a..<a + w]) = w" by simp
      have outside_y:
        "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockL_abs enc0 as s j"
        with blk_repr have nin': "i ∉ {a..<a + w}" by simp
        have AL: "a ≤ length ?x" using offL_window_in_enc[OF jL] a_def w_def by linarith
        show "y ! i = ?x ! i"
          using nin' by (cases "i < a")
                        (simp_all add: y_def splice_nth_left AL splice_nth_right[OF LEN])
      qed

      have slice_pat: "map oL' [a..<a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oL' [a..<a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oL' [a..<a + w])"
        then have tw: "t < w" by simp
        have idx: "[a..<a + w] ! t = a + t" using tw by simp
        show "map oL' [a..<a + w] ! t = pat ! t"
          by (simp add: oL'_def idx tw)
      qed

      have Lj_y: "Lval_at as s ((!) y) j = v_in"
        unfolding Lval_at_def a_def w_def
        by (simp add: slice_pat from_bits.simps)

      have Good_y: "Good as s ((!) y) ((!) ?x)"
      proof -
        have "Lval_at as s ((!) y) j ∈ set (enumR as s kk)"
          using Lj_y vR by simp
        hence "∃jL<length (enumL as s kk).
                 Lval_at as s ((!) y) jL ∈ set (enumR as s kk)"
          using jL by blast
        thus ?thesis
          by (simp add: Good_char_encR)
      qed

      have unread_eq:
        "Good as s ((!) y) ((!) ?x) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_L_local[OF not_touch _ X0])
           (simp add: outside_y)
      from unread_eq Good_y NG show False by simp
    qed
  qed
qed

lemma Good_unread_R_local:
  assumes disj: "Base.read0 M x ∩ blockR_abs enc0 as s kk j = {}"
  assumes out:  "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = x ! i"
  assumes X:    "x = enc as s kk"
  shows "Good as s ((!) x) ((!) y) = Good as s ((!) x) ((!) x)"
proof -
  (* 1) T0 ignores the right oracle on this input, so these runs agree *)
  have RUN_eq:
    "run ((!) x) ((!) y) (T0 as s) = run ((!) x) ((!) x) (T0 as s)"
    by (rule Run_unread_R[OF disj out X])

  (* 2) Bridge both Goods to runs with LEFT fixed to encL *)
  have Gxy_to_run:
    "Good as s ((!) x) ((!) y) = run ((!) x) ((!) y) (T0 as s)"
    by (simp add: X correct_T0_encL)
  have Gxx_to_run:
    "Good as s ((!) x) ((!) x) = run ((!) x) ((!) x) (T0 as s)"
    by (simp add: X correct_T0_encL)

  (* 3) Chain equalities *)
  from Gxy_to_run RUN_eq Gxx_to_run[symmetric]
  show ?thesis by simp
qed

lemma coverage_for_enc_blocks_R:
  assumes R2:  "2 ≤ length (enumR as s kk)"
      and hitR:  "∃v∈set (enumR as s kk). v ∈ set (enumL as s kk)"
      and missR: "∃v∈set (enumR as s kk). v ∉ set (enumL as s kk)"
      and baseline_only_jR:
        "⋀j. Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟹
             (∀j'<length (enumR as s kk). j' ≠ j ⟶
                Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
  shows "∀j<length (enumR as s kk). touches (x0 as s) (blockR_abs enc0 as s kk j)"
proof (intro allI impI)
  fix j assume jR: "j < length (enumR as s kk)"
  let ?x = "x0 as s"

  show "touches ?x (blockR_abs enc0 as s kk j)"
  proof (rule ccontr)
    assume NT: "¬ touches ?x (blockR_abs enc0 as s kk j)"
    then have not_touch:
      "Base.read0 M ?x ∩ blockR_abs enc0 as s kk j = {}"
      by (simp add: touches_def)

    define a where "a = length (enc0 as s) + offR as s kk j"
    define w where "w = W as s"
    have BND: "a + w ≤ length ?x"
      by (simp add: a_def w_def offR_window_in_enc[OF jR])
    have blk_repr: "blockR_abs enc0 as s kk j = {a..<a + w}"
      by (simp add: a_def w_def blockR_abs_def offR_def length_padL)

    have X0: "?x = enc as s kk" by simp

    consider (G) "Good as s ((!) ?x) ((!) ?x)"
           | (NG) "¬ Good as s ((!) ?x) ((!) ?x)" by blast
    then show False
    proof cases
      case G
      from missR obtain v_out where vR: "v_out ∈ set (enumR as s kk)"
                               and vNL: "v_out ∉ set (enumL as s kk)" by blast
      obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v_out"
        using vR bits_roundtrip w_def by blast
      define oR' where "oR' i = (if i ∈ {a..<a + w} then pat ! (i - a) else ?x ! i)" for i
      have LEN: "length (map oR' [a..<a + w]) = w" by simp
      define y where "y = splice a w ?x (map oR' [a..<a + w])"

      have outside_y:
        "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockR_abs enc0 as s kk j"
        with blk_repr have nin': "i ∉ {a..<a + w}" by simp
        have AL: "a ≤ length ?x" using BND by linarith
        show "y ! i = ?x ! i"
          using nin'
          by (cases "i < a")
             (simp_all add: y_def splice_nth_left AL splice_nth_right[OF LEN BND])
      qed

      have slice_pat: "map oR' [a..<a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oR' [a..<a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oR' [a..<a + w])"
        then have tw: "t < w" by simp
        have idx: "[a..<a + w] ! t = a + t" using tw by simp
        show "map oR' [a..<a + w] ! t = pat ! t"
          by (simp add: oR'_def idx tw)
      qed

      have inside_y: "⋀i. i ∈ {a..<a + w} ⟹ y ! i = oR' i"
      proof -
        fix i assume "i ∈ {a..<a + w}"
        then have ai: "a ≤ i" and ilt: "i < a + w" by auto
        have "y ! i = (map oR' [a..<a + w]) ! (i - a)"
          by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
        also have "... = oR' i" using ai ilt by force
        finally show "y ! i = oR' i" .
      qed

      have Rj_y: "Rval_at as s ((!) y) j = v_out"
      proof -
        have "map ((!) y) [a..<a + w] = map oR' [a..<a + w]"
        proof (rule nth_equalityI)
          show "length (map ((!) y) [a..<a + w]) = length (map oR' [a..<a + w])" by simp
        next
          fix t assume "t < length (map ((!) y) [a..<a + w])"
          then have tw: "t < w" by simp
          have idx: "[a..<a + w] ! t = a + t" using tw by simp
          show "map ((!) y) [a..<a + w] ! t = map oR' [a..<a + w] ! t"
            by (simp add: idx tw inside_y)
        qed
        thus ?thesis
          by (simp add: Rval_at_def a_def w_def slice_pat pat_val)
      qed

      have same_others:
        "⋀j'. j' < length (enumR as s kk) ⟹ j' ≠ j ⟹
              Rval_at as s ((!) y) j' = Rval_at as s ((!) ?x) j'"
      proof -
        fix j' assume j'R: "j' < length (enumR as s kk)" and ne: "j' ≠ j"
        define a' where "a' = length (enc0 as s) + offR as s kk j'"
        define w' where "w' = W as s"
        have blk': "blockR_abs enc0 as s kk j' = {a'..<a' + w'}"
          by (simp add: a'_def w'_def blockR_abs_def offR_def length_padL)
        have disj0:
          "blockR_abs enc0 as s kk j' ∩ blockR_abs enc0 as s kk j = {}"
          by (rule blockR_pairwise_disjoint[OF j'R jR ne])
        have eq_on: "⋀i. i ∈ blockR_abs enc0 as s kk j' ⟹ y ! i = ?x ! i"
          using IntI disj0 outside_y by fastforce
        have "map ((!) y) [a'..<a' + w'] = map ((!) ?x) [a'..<a' + w']"
        proof (rule nth_equalityI)
          show "length (map ((!) y) [a'..<a' + w']) =
                length (map ((!) ?x) [a'..<a' + w'])" by simp
        next
          fix t assume "t < length (map ((!) y) [a'..<a' + w'])"
          then have tw: "t < w'" by simp
          have idx: "[a'..<a' + w'] ! t = a' + t" using tw by simp
          have mem: "a' + t ∈ blockR_abs enc0 as s kk j'"
            by (simp add: blk' tw)
          show "map ((!) y) [a'..<a' + w'] ! t
              = map ((!) ?x) [a'..<a' + w'] ! t"
            by (simp add: idx tw eq_on[OF mem])
        qed
        thus "Rval_at as s ((!) y) j' = Rval_at as s ((!) ?x) j'"
          using Rval_at_def a'_def w'_def by metis
      qed

      have not_good_y:
        "¬ Good as s ((!) ?x) ((!) y)"
      proof -
        have others:
          "⋀j'. j' < length (enumR as s kk) ⟹ j' ≠ j ⟹
              Rval_at as s ((!) y) j' ∉ set (enumL as s kk)"
          using baseline_only_jR[OF G] same_others by auto
        have "Rval_at as s ((!) y) j ∉ set (enumL as s kk)"
          using Rj_y vNL by simp
        hence "¬ (∃jR<length (enumR as s kk).
                     Rval_at as s ((!) y) jR ∈ set (enumL as s kk))"
          using others jR by auto
        thus ?thesis using Good_char_encL by blast
      qed

      have good_unread_eq:
        "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_R_local[OF not_touch outside_y X0])

      from good_unread_eq G not_good_y show False by simp

    next
      case NG
      from hitR obtain v_in where vR: "v_in ∈ set (enumR as s kk)"
                               and vL: "v_in ∈ set (enumL as s kk)" by blast
      obtain pat where pat_len: "length pat = w" and pat_val: "from_bits pat = v_in"
        using vR bits_roundtrip w_def by blast
      define oR' where "oR' i = (if i ∈ {a..<a + w} then pat ! (i - a) else ?x ! i)" for i
      have LEN: "length (map oR' [a..<a + w]) = w" by simp
      define y where "y = splice a w ?x (map oR' [a..<a + w])"

      have outside_y:
        "⋀i. i ∉ blockR_abs enc0 as s kk j ⟹ y ! i = ?x ! i"
      proof -
        fix i assume nin: "i ∉ blockR_abs enc0 as s kk j"
        with blk_repr have nin': "i ∉ {a..<a + w}" by simp
        have AL: "a ≤ length ?x" using BND by linarith
        show "y ! i = ?x ! i"
          using nin'
          by (cases "i < a")
             (simp_all add: y_def splice_nth_left AL splice_nth_right[OF LEN BND])
      qed

      have slice_pat: "map oR' [a..<a + w] = pat"
      proof (rule nth_equalityI)
        show "length (map oR' [a..<a + w]) = length pat" by (simp add: pat_len)
      next
        fix t assume "t < length (map oR' [a..<a + w])"
        then have tw: "t < w" by simp
        have idx: "[a..<a + w] ! t = a + t" using tw by simp
        show "map oR' [a..<a + w] ! t = pat ! t"
          by (simp add: oR'_def idx tw)
      qed

      have inside: "⋀i. i ∈ {a..<a + w} ⟹ y ! i = oR' i"
      proof -
        fix i assume iB: "i ∈ {a..<a + w}"
        then have ai: "a ≤ i" and ilt: "i < a + w" by auto
        have "y ! i = (map oR' [a..<a + w]) ! (i - a)"
          by (simp add: y_def splice_nth_inside[OF LEN BND ai ilt])
        also have "... = oR' i" using ai ilt by force
        finally show "y ! i = oR' i" .
      qed

      have slice_eq: "map ((!) y) [a..<a + w] = map oR' [a..<a + w]"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [a..<a + w]) = length (map oR' [a..<a + w])" by simp
      next
        fix t assume tlen: "t < length (map ((!) y) [a..<a + w])"
        then have tw: "t < w" by simp
        have y_eq_or': "y ! (a + t) = oR' (a + t)"
          using inside by (simp add: tw)
        show "map ((!) y) [a..<a + w] ! t = map oR' [a..<a + w] ! t"
          by (simp add: tw y_eq_or')
      qed

      have Rj_y: "Rval_at as s ((!) y) j = v_in"
        by (simp add: Rval_at_def a_def w_def slice_eq slice_pat pat_val)

      have Good_y: "Good as s ((!) ?x) ((!) y)"
      proof -
        have "Rval_at as s ((!) y) j ∈ set (enumL as s kk)"
          using Rj_y vL by simp
        hence "∃jR<length (enumR as s kk).
                 Rval_at as s ((!) y) jR ∈ set (enumL as s kk)"
          using jR by blast
        thus ?thesis by (simp add: Good_char_encL)
      qed

      have good_unread_eq:
        "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_R_local[OF not_touch outside_y X0])

      from good_unread_eq Good_y NG show False by simp
    qed
  qed
qed

(* 9) The coverage result you wanted, phrased on block families *)



lemma coverage_blocks:
  assumes "n = length as" "distinct_subset_sums as"
      and L2:   "2 ≤ length (enumL as s kk)"
      and hitL: "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)"
      and missL:"∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)"
      and base_only_L:
           "⋀j. Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟶
                (∀j'<length (enumL as s kk). j' ≠ j ⟶
                   Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))"
      and R2:   "2 ≤ length (enumR as s kk)"
      and hitR: "∃v∈set (enumR as s kk). v ∈ set (enumL as s kk)"
      and missR:"∃v∈set (enumR as s kk). v ∉ set (enumL as s kk)"
      and base_only_R:
           "⋀j. Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟶
                (∀j'<length (enumR as s kk). j' ≠ j ⟶
                   Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
  shows
   "(∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
    (∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof
  show "∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)"
    using coverage_for_enc_blocks_L[OF L2 hitL missL base_only_L] .

  have base_only_R':
  "⋀j. Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟹
       (∀j'<length (enumR as s kk). j' ≠ j ⟶
          Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))"
    using base_only_R by blast

  have Rcov:
  "∀j<length (enumR as s kk). touches (x0 as s) (blockR_abs enc0 as s kk j)"
    using R2 hitR missR base_only_R'
  by (rule coverage_for_enc_blocks_R)
  have "∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using Rcov by blast  (* relies on x0_is_enc[simp] *)
  show "∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using Rcov by blast  (* uses x0_is_enc[simp] *)
qed

lemma steps_lower_bound_core:
  assumes Lcov_ALL: "∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)"
      and Rcov_ALL: "∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j)"
      and n_def: "n = length as"
  shows "steps M (enc as s kk) ≥
           card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
  (* After you derived the two “forall … touches …” facts: *)
  have Lcov_ALL:
    "∀j<length (enumL as s kk). touches (x0 as s) (blockL_abs enc0 as s j)" by fact
  have Rcov_ALL:
    "∀j<length (enumR as s kk). touches (x0 as s) (blockR_abs enc0 as s kk j)" by fact

 (* Turn them into pointwise rules you can use later *)
  have Lcov: "⋀j. j < length (enumL as s kk) ⟹ touches (x0 as s) (blockL_abs enc0 as s j)"
    using Lcov_ALL by blast
  have Rcov: "⋀j. j < length (enumR as s kk) ⟹ touches (x0 as s) (blockR_abs enc0 as s kk j)"
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
    have jlt: "j < length (enumL as s kk)" using IL_def jIL by simp
    from Lcov[OF jlt] obtain i where
      i1: "i ∈ Base.read0 M x0" and i2: "i ∈ blockL_abs enc0 as s j"
      using touches_def x0_def by blast
    show "∃i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j"
      by (intro exI[of _ i]) (simp add: R0_def i1 i2)
  qed

  have exR:
    "⋀j. j ∈ IR ⟹ ∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    have jlt: "j < length (enumR as s kk)" using IR_def jIR by simp
    from Rcov[OF jlt] obtain i where
      i1: "i ∈ Base.read0 M x0" and i2: "i ∈ blockR_abs enc0 as s kk j"
      using touches_def x0_def by blast
    show "∃i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j"
      by (intro exI[of _ i]) (simp add: R0_def i1 i2)
  qed

  (* witnesses belong to R0 and their blocks *)
  have pickL_in:
    "⋀j. j ∈ IL ⟹ pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
  proof -
    fix j assume jIL: "j ∈ IL"
    from exL[OF jIL]
    show "pickL j ∈ R0 ∧ pickL j ∈ blockL_abs enc0 as s j"
      unfolding pickL_def by (rule someI_ex)
  qed

  have pickR_in:
    "⋀j. j ∈ IR ⟹ pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
  proof -
    fix j assume jIR: "j ∈ IR"
    from exR[OF jIR]
    show "pickR j ∈ R0 ∧ pickR j ∈ blockR_abs enc0 as s kk j"
      unfolding pickR_def by (rule someI_ex)
  qed

  (* images are subsets of R0 *)
  have subL: "pickL ` IL ⊆ R0"
  proof
    fix i assume "i ∈ pickL ` IL"
    then obtain j where jIL: "j ∈ IL" and i_eq: "i = pickL j" by auto
    from pickL_in[OF jIL] have "pickL j ∈ R0" by blast
    thus "i ∈ R0" by (simp add: i_eq)
  qed

  have subR: "pickR ` IR ⊆ R0"
  proof
    fix i assume "i ∈ pickR ` IR"
    then obtain j where jIR: "j ∈ IR" and i_eq: "i = pickR j" by auto
    from pickR_in[OF jIR] have "pickR j ∈ R0" by blast
    thus "i ∈ R0" by (simp add: i_eq)
  qed

  have union_sub: "pickL ` IL ∪ pickR ` IR ⊆ R0"
    using subL subR by auto

  (* injectivity inside L and inside R, by disjoint absolute blocks *)
  have injL: "inj_on pickL IL"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IL" and j2: "j2 ∈ IL" and eq: "pickL j1 = pickL j2"
    obtain i1 where i1: "i1 ∈ R0 ∧ i1 ∈ blockL_abs enc0 as s j1" using exL[OF j1] by blast
    obtain i2 where i2: "i2 ∈ R0 ∧ i2 ∈ blockL_abs enc0 as s j2" using exL[OF j2] by blast
    have in1: "pickL j1 ∈ blockL_abs enc0 as s j1"
      using ‹pickL ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j› j1 pickL_in by auto
    have in2: "pickL j2 ∈ blockL_abs enc0 as s j2"
      using ‹pickL ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockL_abs enc0 as s j› j2 pickL_in by auto
    have inter_nonempty:
      "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 ≠ {}"
      using eq in1 in2 by auto
    show "j1 = j2"
    proof (rule ccontr)
      assume "j1 ≠ j2"
      hence "blockL_abs enc0 as s j1 ∩ blockL_abs enc0 as s j2 = {}"
        by (rule blockL_abs_disjoint)
      with inter_nonempty show False by contradiction
    qed
  qed

  have injR: "inj_on pickR IR"
  proof (rule inj_onI)
    fix j1 j2 assume j1: "j1 ∈ IR" and j2: "j2 ∈ IR" and eq: "pickR j1 = pickR j2"
    obtain i1 where i1: "i1 ∈ R0 ∧ i1 ∈ blockR_abs enc0 as s kk j1" using exR[OF j1] by blast
    obtain i2 where i2: "i2 ∈ R0 ∧ i2 ∈ blockR_abs enc0 as s kk j2" using exR[OF j2] by blast
    have in1: "pickR j1 ∈ blockR_abs enc0 as s kk j1"
      using ‹pickR ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j› j1 pickR_in by blast
    have in2: "pickR j2 ∈ blockR_abs enc0 as s kk j2"
      using ‹pickR ≡ λj. SOME i. i ∈ R0 ∧ i ∈ blockR_abs enc0 as s kk j› j2 pickR_in by blast
    have inter_nonempty:
      "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 ≠ {}"
      using eq in1 in2 by auto
    show "j1 = j2"
    proof (rule ccontr)
      assume "j1 ≠ j2"
      hence "blockR_abs enc0 as s kk j1 ∩ blockR_abs enc0 as s kk j2 = {}"
        by (rule blockR_abs_disjoint)
      with inter_nonempty show False by contradiction
    qed
  qed

  (* images are disjoint across L and R *)
  have disj_images: "(pickL ` IL) ∩ (pickR ` IR) = {}"
  proof
    show "(pickL ` IL) ∩ (pickR ` IR) ⊆ {}"
    proof
      fix i assume iin: "i ∈ (pickL ` IL) ∩ (pickR ` IR)"
      then obtain jL where jL: "jL ∈ IL" and iL: "i = pickL jL" by blast
      from iin obtain jR where jR: "jR ∈ IR" and iR: "i = pickR jR" by blast
      have inL: "i ∈ blockL_abs enc0 as s jL"
        using iL pickL_in[OF jL] by auto
      have inR: "i ∈ blockR_abs enc0 as s kk jR"
        using iR pickR_in[OF jR] by auto
      have jL_lt: "jL < length (enumL as s kk)" using IL_def jL by auto
      have disj: "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        by (rule blockL_abs_blockR_abs_disjoint[OF jL_lt])
      from inL inR disj show "i ∈ {}" by auto
    qed
  qed simp

  (* count *)
  have fin_R0: "finite R0" using R0_def by simp
  have fin_imgL: "finite (pickL ` IL)" by (intro finite_imageI) (simp add: IL_def)
  have fin_imgR: "finite (pickR ` IR)" by (intro finite_imageI) (simp add: IR_def)

  have card_lower: "card (pickL ` IL ∪ pickR ` IR) ≤ card R0"
    by (rule card_mono[OF fin_R0 union_sub])

  have card_union:
    "card (pickL ` IL ∪ pickR ` IR) = card (pickL ` IL) + card (pickR ` IR)"
    by (subst card_Un_disjoint) (use disj_images fin_imgL fin_imgR in auto)

  have inj_cardL: "card (pickL ` IL) = card IL" by (rule card_image[OF injL])
  have inj_cardR: "card (pickR ` IR) = card IR" by (rule card_image[OF injR])

  from card_lower card_union inj_cardL inj_cardR
  have A: "card IL + card IR ≤ card R0" by simp

  have card_IL: "card IL = card (LHS (e_k as s kk) n)"
    by (simp add: IL_def enumL_def n_def)
  have card_IR: "card IR = card (RHS (e_k as s kk) n)"
    by (simp add: IR_def enumR_def n_def)

  have B:
   "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ card R0"
    using A by (simp add: card_IL card_IR)

  (* final sandwich with steps *)
  have "card R0 ≤ steps M x0"
    by (simp add: R0_def Base.card_read0_le_steps)
  from B this have "card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n) ≤ steps M x0"
    by (rule le_trans)
  thus ?thesis
    unfolding x0_def by blast
qed

(* Derive the eight coverage premises once, then reuse coverage_blocks. *)
lemma coverage_blocks_from_distinct:
  assumes n_def: "n = length as"
      and distinct: "distinct_subset_sums as"
      and kk_le:     "kk ≤ n"
      and kk_pos:    "1 ≤ kk"   (* keep if you really need nontrivial split *)
  shows
   "(∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
    (∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof -
  (* discharge the eight premises ONCE here; replace sorry by your lemmas *)
  have L2:   "2 ≤ length (enumL as s kk)" sorry
  have hitL: "∃v∈set (enumL as s kk). v ∈ set (enumR as s kk)" sorry
  have missL:"∃v∈set (enumL as s kk). v ∉ set (enumR as s kk)" sorry
  have base_only_L:
    "⋀j. Good as s ((!) (enc as s kk)) ((!) (enc as s kk)) ⟹
         (∀j'<length (enumL as s kk). j' ≠ j ⟶
            Lval_at as s ((!) (enc as s kk)) j' ∉ set (enumR as s kk))" sorry

  have R2:   "2 ≤ length (enumR as s kk)" sorry
  have hitR: "∃v∈set (enumR as s kk). v ∈ set (enumL as s kk)" sorry
  have missR:"∃v∈set (enumR as s kk). v ∉ set (enumL as s kk)" sorry
  have base_only_R:
    "⋀j. Good as s ((!) (x0 as s)) ((!) (x0 as s)) ⟹
         (∀j'<length (enumR as s kk). j' ≠ j ⟶
            Rval_at as s ((!) (x0 as s)) j' ∉ set (enumL as s kk))" sorry

  have cov_enc:
    "(∀j<length (enumL as s kk).
        touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
     (∀j<length (enumR as s kk).
        touches (enc as s kk) (blockR_abs enc0 as s kk j))"
    by (rule coverage_blocks[
          OF n_def distinct
             L2 hitL missL base_only_L
             R2 hitR missR base_only_R])

  show ?thesis by (rule cov_enc)
qed

lemma steps_lower_bound:
  assumes n_def: "n = length as"
      and distinct: "distinct_subset_sums as"
      and kk_le: "kk ≤ n"
      and kk_pos: "1 ≤ kk"   (* drop if not needed *)
  shows "steps M (enc as s kk)
         ≥ card (LHS (e_k as s kk) n) + card (RHS (e_k as s kk) n)"
proof -
  obtain Lcov_ALL Rcov_ALL where
    Lcov_ALL: "∀j<length (enumL as s kk).
                 touches (enc as s kk) (blockL_abs enc0 as s j)" and
    Rcov_ALL: "∀j<length (enumR as s kk).
                 touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using coverage_blocks_from_distinct[OF n_def distinct kk_le kk_pos] by blast

  (* From here: paste your existing counting proof unchanged,
     but use Lcov_ALL / Rcov_ALL in place of the old premises. *)
  (* ... pickL/pickR definitions, show images ⊆ read0, disjointness,
         card_Un_disjoint, card_image via inj_on, etc ...
     Exactly as you already had in your previous working proof. *)

  sorry  (* replace with your counting block; it should go through as-is *)
qed

end  (* context Coverage_TM *)

end  (* theory *)
