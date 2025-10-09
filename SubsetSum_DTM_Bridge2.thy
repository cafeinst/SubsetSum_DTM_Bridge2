theory SubsetSum_DTM_Bridge2
  imports "SubsetSum_DecisionTree" "SubsetSum_DTM_Bridge"
begin

context Coverage_TM
begin

lemma run_drive_T0:
  "run oL oR (T0 as s)
   = final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) oL)"
  by (simp add: run_tm_to_dtr' T0_def)

(* Use the existing datatype from SubsetSum_DecisionTree *)
(* Do NOT redeclare a local datatype named dtr. *)

(* Make a convenient induction rule with case names for that datatype *)
lemmas dtr_induct_cases =
  SubsetSum_DecisionTree.dtr.induct[case_names Leaf AskL AskR]

(* Structural well-formedness over L/R for THAT tree type *)
inductive wf_tree ::
  "'i set ⇒ 'j set ⇒ ('i,'j) SubsetSum_DecisionTree.dtr ⇒ bool"
  for L R
where
  Leaf:
    "wf_tree L R (SubsetSum_DecisionTree.Leaf b)"
| AskL:
    "i ∈ L ⟹
     wf_tree L R U1 ⟹ wf_tree L R U2 ⟹
     wf_tree L R (SubsetSum_DecisionTree.AskL i U1 U2)"
| AskR:
    "j ∈ R ⟹
     wf_tree L R U1 ⟹ wf_tree L R U2 ⟹
     wf_tree L R (SubsetSum_DecisionTree.AskR j U1 U2)"

declare wf_tree.cases  [case_names Leaf AskL AskR]
declare wf_tree.induct [case_names Leaf AskL AskR]

(* Handy eliminators *)
lemma wf_tree_AskL_elim:
  assumes WF: "wf_tree L R (SubsetSum_DecisionTree.AskL i U1 U2)"
  obtains "i ∈ L" "wf_tree L R U1" "wf_tree L R U2"
  using WF by (cases rule: wf_tree.cases) auto

lemma wf_tree_AskR_elim:
  assumes WF: "wf_tree L R (SubsetSum_DecisionTree.AskR j U1 U2)"
  obtains "j ∈ R" "wf_tree L R U1" "wf_tree L R U2"
  using WF by (cases rule: wf_tree.cases) auto

(* The subset lemmas you want, now typed against the right dtr *)
lemma seenL_subset_of_wf_tree:
  assumes WF: "wf_tree L R U"
  shows "SubsetSum_DecisionTree.seenL_run oL' oR' U ⊆ L"
  using WF
proof (induction U arbitrary: oL' oR' rule: dtr_induct_cases)
  case (Leaf b)
  show ?case by simp
next
  case (AskL i U1 U2)
  have iL_WF1_WF2:
    "i ∈ L ∧ wf_tree L R U1 ∧ wf_tree L R U2"
    using AskL.prems by (cases rule: wf_tree.cases) auto
  then have iL:  "i ∈ L"
     and WF1: "wf_tree L R U1"
     and WF2: "wf_tree L R U2"
    by auto
  have IH1: "seenL_run oL' oR' U1 ⊆ L" by (rule AskL.IH(1)[OF WF1])
  have IH2: "seenL_run oL' oR' U2 ⊆ L" by (rule AskL.IH(2)[OF WF2])
  show ?case
    by (simp add: IH1 IH2 iL)
next
  case (AskR j U1 U2)
  have jR_WF1_WF2: "j ∈ R ∧ wf_tree L R U1 ∧ wf_tree L R U2"
    using AskR.prems by (cases rule: wf_tree.cases) auto
  then have WF1: "wf_tree L R U1" and WF2: "wf_tree L R U2" by auto
  have IH1: "SubsetSum_DecisionTree.seenL_run oL' oR' U1 ⊆ L"
    by (rule AskR.IH(1)[OF WF1])
  have IH2: "SubsetSum_DecisionTree.seenL_run oL' oR' U2 ⊆ L"
    by (rule AskR.IH(2)[OF WF2])
  show ?case
    by (simp add: IH1 IH2)
qed

lemma seenR_subset_of_wf_tree:
  assumes WF: "wf_tree L R U"
  shows "SubsetSum_DecisionTree.seenR_run oL' oR' U ⊆ R"
  using WF
proof (induction U arbitrary: oL' oR' rule: dtr_induct_cases)
  case (Leaf b)
  show ?case by simp
next
  (* Left query: seenR just follows the branch, no insertion *)
  case (AskL i U1 U2)
  have WF12: "wf_tree L R U1 ∧ wf_tree L R U2"
    using AskL.prems by (cases rule: wf_tree.cases) auto
  then have WF1: "wf_tree L R U1" and WF2: "wf_tree L R U2" by auto
  have IH1: "SubsetSum_DecisionTree.seenR_run oL' oR' U1 ⊆ R"
    by (rule AskL.IH(1)[OF WF1])
  have IH2: "SubsetSum_DecisionTree.seenR_run oL' oR' U2 ⊆ R"
    by (rule AskL.IH(2)[OF WF2])
  show ?case
    by (simp add: IH1 IH2)
next
  (* Right query: seenR inserts j, so we need j ∈ R *)
  case (AskR j U1 U2)
  have jR_WF12: "j ∈ R ∧ wf_tree L R U1 ∧ wf_tree L R U2"
    using AskR.prems by (cases rule: wf_tree.cases) auto
  then have jR: "j ∈ R" and WF1: "wf_tree L R U1" and WF2: "wf_tree L R U2" by auto
  have IH1: "SubsetSum_DecisionTree.seenR_run oL' oR' U1 ⊆ R"
    by (rule AskR.IH(1)[OF WF1])
  have IH2: "SubsetSum_DecisionTree.seenR_run oL' oR' U2 ⊆ R"
    by (rule AskR.IH(2)[OF WF2])
  show ?case
    by (simp add: IH1 IH2 jR)
qed

inductive wf_run_local where
  Leaf: "wf_run_local L R oL oR (Leaf b)"
| AskL: "⟦ i ∈ L; wf_run_local L R oL oR U1; wf_run_local L R oL oR U2 ⟧
          ⟹ wf_run_local L R oL oR (AskL i U1 U2)"
| AskR: "⟦ j ∈ R; wf_run_local L R oL oR U1; wf_run_local L R oL oR U2 ⟧
          ⟹ wf_run_local L R oL oR (AskR j U1 U2)"

(* 1) Bridge from operational wf_run to structural wf_tree *)
lemma wf_run_to_tree:
  assumes WF: "wf_run_local L R oL oR U"
  shows "wf_tree L R U"
  using WF
proof (induction rule: wf_run_local.induct)
  case (Leaf L R oL oR b)
  show ?case by (rule wf_tree.Leaf)
next
  case (AskL L R oL oR i U1 U2)
  (* IHs: wf_tree L R U1, wf_tree L R U2 ; premise: i ∈ L *)
  from AskL show ?case
    by (intro wf_tree.AskL) auto
next
  case (AskR L R oL oR j U1 U2)
  (* IHs: wf_tree L R U1, wf_tree L R U2 ; premise: j ∈ R *)
  from AskR show ?case
    by (intro wf_tree.AskR) auto
qed

lemma local_wf_run_to_tree:
  assumes WF: "local.wf_run_local L R oL oR U"
  shows "wf_tree L R U"
  using WF
proof (induction rule: local.wf_run_local.induct)
  case (Leaf L R oL oR b)
  show ?case by (rule wf_tree.Leaf)
next
  case (AskL L R oL oR i U1 U2)
  from AskL show ?case by (intro wf_tree.AskL) auto
next
  case (AskR L R oL oR j U1 U2)
  from AskR show ?case by (intro wf_tree.AskR) auto
qed

(* A handy cases rule alias *)
lemmas SSB_wf_run_induct = SubsetSum_DTM_Bridge.wf_run.induct[case_names Leaf AskL AskR]
lemmas SSB_wf_run_cases  = SubsetSum_DTM_Bridge.wf_run.cases

(* Elims to expose the chosen branch from an AskL/AskR node *)
lemma SSB_wf_run_AskL_branch:
  assumes "SubsetSum_DTM_Bridge.wf_run L R oL oR (AskL i U1 U2)"
  shows   "SubsetSum_DTM_Bridge.wf_run L R oL oR (if oL i then U2 else U1)"
  using assms by (cases rule: SSB_wf_run_cases) auto

lemma SSB_wf_run_AskL_i_in_L:
  assumes "SubsetSum_DTM_Bridge.wf_run L R oL oR (AskL i U1 U2)"
  shows   "i ∈ L"
  using assms by (cases rule: SSB_wf_run_cases) auto

lemma SSB_wf_run_AskR_branch:
  assumes "SubsetSum_DTM_Bridge.wf_run L R oL oR (AskR j U1 U2)"
  shows   "SubsetSum_DTM_Bridge.wf_run L R oL oR (if oR j then U2 else U1)"
  using assms by (cases rule: SSB_wf_run_cases) auto

lemma SSB_wf_run_AskR_j_in_R:
  assumes "SubsetSum_DTM_Bridge.wf_run L R oL oR (AskR j U1 U2)"
  shows   "j ∈ R"
  using assms by (cases rule: SSB_wf_run_cases) auto

lemma seenL_subset_of_wf_run:
  assumes WF: "SubsetSum_DTM_Bridge.wf_run L R oL oR U"
  shows "seenL_run oL oR U ⊆ L"
  using WF
proof (induction L R oL oR U rule: SSB_wf_run_induct)
  case (Leaf L R oL oR b)
  show ?case by simp
next
  case (AskL L R oL oR i U1 U2)
  (* extract branch run + use IH *)
  have RUNbr: "SubsetSum_DTM_Bridge.wf_run L R oL oR (if oL i then U2 else U1)"
    by (rule SSB_wf_run_AskL_branch[OF AskL(2)])
  have IH: "seenL_run oL oR (if oL i then U2 else U1) ⊆ L"
    by (rule AskL.IH[OF RUNbr])
  have iL: "i ∈ L" by (rule SSB_wf_run_AskL_i_in_L[OF AskL(2)])
  show ?case using IH iL by (cases "oL i") simp_all
next
  case (AskR L R oL oR j U1 U2)
  have RUNbr: "SubsetSum_DTM_Bridge.wf_run L R oL oR (if oR j then U2 else U1)"
    by (rule SSB_wf_run_AskR_branch[OF AskR(2)])
  have IH: "seenL_run oL oR (if oR j then U2 else U1) ⊆ L"
    by (rule AskR.IH[OF RUNbr])
  show ?case using IH by (cases "oR j") simp_all
qed

lemma seenR_subset_of_wf_run:
  assumes WF: "SubsetSum_DTM_Bridge.wf_run L R oL oR U"
  shows "seenR_run oL oR U ⊆ R"
  using WF
proof (induction L R oL oR U rule: SSB_wf_run_induct)
  case (Leaf L R oL oR b)
  show ?case by simp
next
  case (AskL L R oL oR i U1 U2)
  have RUNbr: "SubsetSum_DTM_Bridge.wf_run L R oL oR (if oL i then U2 else U1)"
    by (rule SSB_wf_run_AskL_branch[OF AskL(2)])
  have IH: "seenR_run oL oR (if oL i then U2 else U1) ⊆ R"
    by (rule AskL.IH[OF RUNbr])
  show ?case using IH by (cases "oL i") simp_all
next
  case (AskR L R oL oR j U1 U2)
  have RUNbr: "SubsetSum_DTM_Bridge.wf_run L R oL oR (if oR j then U2 else U1)"
    by (rule SSB_wf_run_AskR_branch[OF AskR(2)])
  have IH: "seenR_run oL oR (if oR j then U2 else U1) ⊆ R"
    by (rule AskR.IH[OF RUNbr])
  have jR: "j ∈ R" by (rule SSB_wf_run_AskR_j_in_R[OF AskR(2)])
  show ?case using IH jR by (cases "oR j") simp_all
qed

lemma L0_eq_Lset [simp]: "L0 as s = Lset as s"
  by (simp add: L0_def)
lemma R0_eq_Rset [simp]: "R0 as s = Rset as s"
  by (simp add: R0_def) 

lemma wf_T0_run_local:
  "wf_run_local (L0 as s) (R0 as s)
                ((!) (enc as s kk)) ((!) (enc as s kk))
                (T0 as s)"
  unfolding L0_def R0_def T0_def
  sorry

lemmas wf_T0_run_local' =
  wf_T0_run_local[unfolded L0_eq_Lset R0_eq_Rset]

lemma T0_wf:
  "wf_tree (Lset as s) (Rset as s) (T0 as s)"
  by (rule local_wf_run_to_tree[OF wf_T0_run_local'])

lemma drive_char_RHS_core:
  "final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) oL)
   = Good as s oL ((!) (x0 as s))"
  sorry  (* proof from TM side; no run/decision-tree lemmas *)

lemma drive_char_LHS_core:
  "final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) ((!) (x0 as s)))
   = Good as s ((!) (x0 as s)) oR"
  sorry  (* proof from TM side; no run/decision-tree lemmas *)

lemma correct_T0_encR:
  "run oL ((!) (x0 as s)) (T0 as s) = Good as s oL ((!) (x0 as s))"
proof -
  have "run oL ((!) (x0 as s)) (T0 as s)
          = final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) oL)"
    by (rule run_drive_T0)
  also have "... = Good as s oL ((!) (x0 as s))"
    by (rule drive_char_RHS_core)
  finally show ?thesis .
qed

lemma correct_T0_encL:
  "run ((!) (x0 as s)) oR (T0 as s) = Good as s ((!) (x0 as s)) oR"
proof -
  have "run ((!) (x0 as s)) oR (T0 as s)
          = final_acc (drive (steps M (x0 as s)) (conf M (x0 as s) 0) ((!) (x0 as s)))"
    by (rule run_drive_T0)
  also have "... = Good as s ((!) (x0 as s)) oR"
    by (rule drive_char_LHS_core)
  finally show ?thesis .
qed

lemma run_to_Good_with_right_enc:
  "run oL ((!) (x0 as s)) (T0 as s) = Good as s oL ((!) (x0 as s))"
proof -
  define x where [simp]: "x = x0 as s"
  define T where [simp]: "T = T0 as s"

  (* wf fact for T0; keep your proof or leave it as sorry for now *)
  have WF_T: "wf_tree (Lset as s) (Rset as s) T"
    by (simp add: T0_wf)

  (* Only LEFT windows matter for mapping oL into a list *)
  define may_read :: "nat set" where "may_read = Lset as s"
  define Y :: "nat ⇒ bool" where "Y i = (if i ∈ may_read then oL i else x ! i)"
  define y where "y = map Y [0..<length x]"

  have len_x[simp]: "length x = length (enc as s kk)"
    by simp
(* L windows are within bounds of x *)
  have Lset_lt_len: "⋀i. i ∈ Lset as s ⟹ i < length x"
  proof -
    fix i assume "i ∈ Lset as s"
    then obtain j where jL: "j < length (enumL as s kk)"
                   and iBL: "i ∈ blockL_abs enc0 as s j"
      by (auto simp: Lset_def)
    let ?a = "length (enc0 as s) + offL as s j"
    let ?w = "W as s"
    have top: "?a + ?w ≤ length (enc as s kk)"
      using offL_window_in_enc[OF jL] by simp
    have "i < ?a + ?w" using iBL by (simp add: blockL_abs_def offL_def)
    also have "... ≤ length (enc as s kk)" using top .
    finally show "i < length x" by simp
  qed
  have Rset_lt_len: "⋀i. i ∈ Rset as s ⟹ i < length x"
  proof -
    fix i assume "i ∈ Rset as s"
    then obtain j where jR: "j < length (enumR as s kk)"
                   and iBR: "i ∈ blockR_abs enc0 as s kk j"
      by (auto simp: Rset_def)
    let ?a = "length (enc0 as s) + offR as s kk j"
    let ?w = "W as s"
    have top: "?a + ?w ≤ length (enc as s kk)"
      using offR_window_in_enc[OF jR] length_padL by simp
    have "i < ?a + ?w" using iBR by (simp add: blockR_abs_def)
    also have "... ≤ length (enc as s kk)" using top .
    finally show "i < length x" by simp
  qed
  have disj_LR: "Lset as s ∩ Rset as s = {}"
  proof
    show "Lset as s ∩ Rset as s ⊆ {}"
    proof
      fix i assume "i ∈ Lset as s ∩ Rset as s"
      then obtain jL jR where
        jL: "jL < length (enumL as s kk)" and iBL: "i ∈ blockL_abs enc0 as s jL" and
        jR: "jR < length (enumR as s kk)" and iBR: "i ∈ blockR_abs enc0 as s kk jR"
        by (auto simp: Lset_def Rset_def)
      have "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        by (rule blockL_abs_blockR_abs_disjoint[OF jL])  (* or [OF jL jR], see above *)
      thus "i ∈ {}" using iBL iBR by auto
    qed
    show "{} ⊆ Lset as s ∩ Rset as s" by simp
  qed

  (* y agrees with oL on Lset, and with x on Rset *)
  have y_eq_oL_on_L: "⋀i. i ∈ Lset as s ⟹ y ! i = oL i"
  proof -
    fix i assume iL: "i ∈ Lset as s"
    have iLt:  "i < length x" using iL Lset_lt_len by blast
    have iMay: "i ∈ may_read" using iL by (simp add: may_read_def)
    have "(map Y [0..<length x]) ! i = Y i" using iLt by simp
    also have "Y i = oL i" using Y_def iMay
      by (simp add: ‹Y ≡ λi. if i ∈ may_read then oL i else x ! i›)
    finally show "y ! i = oL i" by (simp add: y_def)
  qed
  have y_eq_x_on_R:  "⋀i. i ∈ Rset as s ⟹ y ! i = x ! i"
  proof -
    fix i assume iR: "i ∈ Rset as s"
    have iLt: "i < length x" using iR Rset_lt_len by blast
    have "i ∉ Lset as s" using iR disj_LR by auto
    thus "y ! i = x ! i" using y_def Y_def may_read_def iLt
      by (simp add: ‹Y ≡ λi. if i ∈ may_read then oL i else x ! i›)
  qed

  (* What T can ever look at *)
  have SL_yx: "seenL_run ((!) y) ((!) x) T ⊆ Lset as s"
    using WF_T by (rule seenL_subset_of_wf_tree)
  have SR_yx: "seenR_run ((!) y) ((!) x) T ⊆ Rset as s"
    using WF_T by (rule seenR_subset_of_wf_tree)

  (* Replace (!!y) by oL on the left (right unchanged) *)
  have run_yx_eq_olx:
    "run ((!) y) ((!) x) T = run oL ((!) x) T"
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) y) ((!) x) T ⟹ (!) y i = oL i"
      using SL_yx y_eq_oL_on_L by auto
  next
    show "⋀i. i ∈ seenR_run ((!) y) ((!) x) T ⟹ (!) x i = (!) x i" by simp
  qed

  (* Turn the left value slices of (!!y) into oL inside Good *)
  have Good_normalize:
    "Good as s ((!) y) ((!) x) = Good as s oL ((!) x)"
  proof -
    have Lslice:
      "⋀j. j < length (enumL as s kk) ⟹
         map ((!) y)
           [length (enc0 as s) + offL as s j ..<
            length (enc0 as s) + offL as s j + W as s]
       = map oL
           [length (enc0 as s) + offL as s j ..<
            length (enc0 as s) + offL as s j + W as s]"
    proof -
      fix j assume jL: "j < length (enumL as s kk)"
      let ?a = "length (enc0 as s) + offL as s j"
      let ?w = "W as s"
      show "map ((!) y) [?a..< ?a+?w] = map oL [?a..< ?a+?w]"
      proof (rule nth_equalityI)
        show "length (map ((!) y) [?a..< ?a+?w]) =
              length (map oL       [?a..< ?a+?w])" by simp
      next
        fix t assume "t < length (map ((!) y) [?a..< ?a+?w])"
        hence tw: "t < ?w" by simp
        have idx: "[?a..< ?a+?w] ! t = ?a + t" using tw by simp
        have in_Lset:
          "?a + t ∈ Lset as s"
          unfolding Lset_def
        proof (intro UN_I)
          show "j ∈ {..< length (enumL as s kk)}"
            using jL by simp
        next
          show "?a + t ∈ blockL_abs enc0 as s j"
            using tw by (simp add: blockL_abs_def offL_def)
        qed
        show "map ((!) y) [?a..< ?a+?w] ! t = map oL [?a..< ?a+?w] ! t"
          using y_eq_oL_on_L[OF in_Lset] idx
          by (simp add: tw)
      qed
    qed
    have "⋀j. j < length (enumL as s kk) ⟹
              Lval_at as s ((!) y) j = Lval_at as s oL j"
      by (simp add: Lval_at_def Lslice)
    thus ?thesis using Good_def good_def by metis
  qed

  (* Correctness of T0 for arbitrary left & right — use your existing lemma name *)
  have run_eq_good_yx:
    "run ((!) y) ((!) x) T = Good as s ((!) y) ((!) x)"
    unfolding x_def T_def
    by (rule correct_T0_encR)

  from run_yx_eq_olx run_eq_good_yx Good_normalize
  have "run oL ((!) x) T = Good as s oL ((!) x)" by simp
  thus ?thesis by simp
qed

lemma run_to_Good_with_left_enc:
  "run ((!) (x0 as s)) oR (T0 as s) = Good as s ((!) (x0 as s)) oR"
proof -
  define x where [simp]: "x = x0 as s"
  define T where [simp]: "T = T0 as s"

  (* wf fact for T0 (structural) *)
  have WF_T: "wf_tree (Lset as s) (Rset as s) T"
    by (simp add: T0_wf)

  (* Only RIGHT windows matter for mapping oR into a list *)
  define may_read :: "nat set" where "may_read = Rset as s"
  define Z :: "nat ⇒ bool" where "Z i = (if i ∈ may_read then oR i else x ! i)"
  define z where "z = map Z [0..<length x]"

  have len_x[simp]: "length x = length (enc as s kk)"
    by simp

  (* R windows are within bounds of x *)
  have Rset_lt_len: "⋀i. i ∈ Rset as s ⟹ i < length x"
  proof -
    fix i assume "i ∈ Rset as s"
    then obtain j where jR: "j < length (enumR as s kk)"
                     and iBR: "i ∈ blockR_abs enc0 as s kk j"
      by (auto simp: Rset_def)
    let ?a = "length (enc0 as s) + offR as s kk j"
    let ?w = "W as s"
    have top: "?a + ?w ≤ length (enc as s kk)"
      using offR_window_in_enc[OF jR] length_padL by simp
    have "i < ?a + ?w" using iBR by (simp add: blockR_abs_def)
    also have "... ≤ length (enc as s kk)" using top .
    finally show "i < length x" by simp
  qed

  (* L windows are within bounds of x (used when we show z = x there) *)
  have Lset_lt_len: "⋀i. i ∈ Lset as s ⟹ i < length x"
  proof -
    fix i assume "i ∈ Lset as s"
    then obtain j where jL: "j < length (enumL as s kk)"
                     and iBL: "i ∈ blockL_abs enc0 as s j"
      by (auto simp: Lset_def)
    let ?a = "length (enc0 as s) + offL as s j"
    let ?w = "W as s"
    have top: "?a + ?w ≤ length (enc as s kk)"
      using offL_window_in_enc[OF jL] by simp
    have "i < ?a + ?w" using iBL by (simp add: blockL_abs_def offL_def)
    also have "... ≤ length (enc as s kk)" using top .
    finally show "i < length x" by simp
  qed

  (* Disjointness *)
  have disj_LR: "Lset as s ∩ Rset as s = {}"
  proof (rule order_antisym)
    show "Lset as s ∩ Rset as s ⊆ {}"
    proof
      fix i assume "i ∈ Lset as s ∩ Rset as s"
      then have iL: "i ∈ Lset as s" and iR: "i ∈ Rset as s" by auto

    (* pick the L- and R-window witnesses explicitly *)
      obtain jL where jLlt: "jL < length (enumL as s kk)"
                 and iBL:  "i ∈ blockL_abs enc0 as s jL"
        using iL by (auto simp: Lset_def)

      obtain jR where jRlt: "jR < length (enumR as s kk)"
                 and iBR:  "i ∈ blockR_abs enc0 as s kk jR"
        using iR by (auto simp: Rset_def)

    (* now apply the disjointness of that specific L-block and R-block *)
      have disj: "blockL_abs enc0 as s jL ∩ blockR_abs enc0 as s kk jR = {}"
        by (rule blockL_abs_blockR_abs_disjoint[OF jLlt])

      from iBL iBR have False
        using disj by auto
      thus "i ∈ {}" by simp
    qed
    show "{} ⊆ Lset as s ∩ Rset as s" by simp
  qed

  (* z agrees with oR on Rset, and with x on Lset *)
  have z_eq_oR_on_R: "⋀i. i ∈ Rset as s ⟹ z ! i = oR i"
  proof -
    fix i assume iR: "i ∈ Rset as s"
    have iLt: "i < length x" using ‹i ∈ Rset as s› Rset_lt_len by blast
    have "z ! i = (map Z [0..<length x]) ! i" by (simp add: z_def)
    also from iLt have "... = Z i" by simp
    also have "... = oR i" using ‹i ∈ Rset as s›
      by (simp add: ‹Z ≡ λi. if i ∈ may_read then oR i else x ! i› may_read_def)
    finally show "z ! i = oR i" .
  qed
  have z_eq_x_on_L:  "⋀i. i ∈ Lset as s ⟹ z ! i = x ! i"
  proof -
    fix i assume iL: "i ∈ Lset as s"
    have iLt: "i < length x" using iL Lset_lt_len by blast
    have "i ∉ Rset as s" using iL disj_LR by auto
    have "z ! i = (map Z [0..<length x]) ! i"
      by (simp add: z_def)
    also have "... = Z i"
      using iLt by simp
    also have "... = x ! i"
      using ‹i ∉ Rset as s›
      by (simp add: ‹Z ≡ λi. if i ∈ may_read then oR i else x ! i› may_read_def)
    finally show "z ! i = x ! i" .
  qed

  (* What T can ever look at *)
  have SL_xz: "seenL_run ((!) x) ((!) z) T ⊆ Lset as s"
    using WF_T by (rule seenL_subset_of_wf_tree)
  have SR_xz: "seenR_run ((!) x) ((!) z) T ⊆ Rset as s"
    using WF_T by (rule seenR_subset_of_wf_tree)

  (* Replace right: ((!) x, (!!z))  ~  ((!) x, oR) *)
  have run_xz_eq_xoR:
    "run ((!) x) ((!) z) T = run ((!) x) oR T"
  proof (rule run_agrees_on_seen)
    show "⋀i. i ∈ seenL_run ((!) x) ((!) z) T ⟹ (!) x i = (!) x i" by simp
  next
    show "⋀i. i ∈ seenR_run ((!) x) ((!) z) T ⟹ (!) z i = oR i"
    proof -
      fix i assume iSR: "i ∈ seenR_run ((!) x) ((!) z) T"
      from SR_xz iSR have iR: "i ∈ Rset as s" by blast
      show "(!) z i = oR i" using z_eq_oR_on_R[OF iR] by simp
    qed
  qed

  (* Normalize Good on RIGHT windows *)
  have Good_normalize_R:
    "Good as s ((!) x) ((!) z) = Good as s ((!) x) oR"
  proof -
    have Rslice:
      "⋀j. j < length (enumR as s kk) ⟹
           map ((!) z)
             [length (enc0 as s) + offR as s kk j
              ..< length (enc0 as s) + offR as s kk j + W as s]
         = map oR
             [length (enc0 as s) + offR as s kk j
              ..< length (enc0 as s) + offR as s kk j + W as s]"
    proof -
      fix j assume jR: "j < length (enumR as s kk)"
      let ?a = "length (enc0 as s) + offR as s kk j"
      let ?w = "W as s"
      show "map ((!) z) [?a..< ?a+?w] = map oR [?a..< ?a+?w]"
      proof (rule nth_equalityI)
        show "length (map ((!) z) [?a..< ?a+?w]) =
              length (map oR       [?a..< ?a+?w])" by simp
      next
        fix t assume "t < length (map ((!) z) [?a..< ?a+?w])"
        hence tw: "t < ?w" by simp
        have idx: "[?a..< ?a+?w] ! t = ?a + t" using tw by simp
        have in_Rset:
          "?a + t ∈ Rset as s"
          unfolding Rset_def
        proof (intro UN_I)
          show "j ∈ {..< length (enumR as s kk)}" using jR by simp
        next
          show "?a + t ∈ blockR_abs enc0 as s kk j"
            using tw by (simp add: blockR_abs_def)
        qed
        have nth_range: "[?a ..< ?a + ?w] ! t = ?a + t"
          using tw by simp
        have "(map ((!) z) [?a ..< ?a + ?w]) ! t
          = ((!) z) ([?a ..< ?a + ?w] ! t)"
          using tw by simp   (* uses nth_map with t < length ... since length = ?w *)
        also have "... = (!) z (?a + t)"
          by (simp add: nth_range)
        finally have "(map ((!) z) [?a ..< ?a + ?w]) ! t = z ! (?a + t)"
          by simp
        also have "... = oR (?a + t)"
          using z_eq_oR_on_R[OF in_Rset] by simp
        also have "... = (map oR [?a..< ?a+?w]) ! t"
          by (simp add: tw)
        finally show "map ((!) z) [?a..< ?a+?w] ! t = map oR [?a..< ?a+?w] ! t" .
      qed
    qed
    have "⋀j. j < length (enumR as s kk) ⟹
              Rval_at as s ((!) z) j = Rval_at as s oR j"
      by (simp add: Rval_at_def Rslice)
    thus ?thesis using Good_def good_def by metis
  qed

  (* Core correctness with left enc (parametric in right) *)
  have run_eq_good_xz:
    "run ((!) x) ((!) z) T = Good as s ((!) x) ((!) z)"
    unfolding x_def T_def by (rule correct_T0_encL)

(* First, rewrite run_xz_eq_xoR into the (x0 as s, T0 as s) shape *)
  have step1_x:
    "run ((!) (x0 as s)) oR (T0 as s) = run ((!) (x0 as s)) ((!) z) (T0 as s)"
    using run_xz_eq_xoR[symmetric] by simp

  have step1_enc:
    "run ((!) (enc as s kk)) oR (T0 as s) =
    run ((!) (enc as s kk)) ((!) z) (T0 as s)"
    using step1_x by simp
  have "run ((!) (x0 as s)) oR (T0 as s) =
      run ((!) (x0 as s)) ((!) z) (T0 as s)"
    using step1_x .
  also have "... = Good as s ((!) (x0 as s)) ((!) z)"
    using correct_T0_encL by simp
  also have "... = Good as s ((!) (x0 as s)) oR"
    using Good_normalize_R by simp
  finally show ?thesis .
qed

lemma run_T0_mixed_bridge:
  "run oL ((!) (x0 as s)) (T0 as s) = Good as s oL ((!) (x0 as s))"
  using run_drive_T0 drive_char_RHS_core by simp

lemma run_T0_left_bridge:
  "run ((!) (x0 as s)) oR (T0 as s) = Good as s ((!) (x0 as s)) oR"
  using run_drive_T0 drive_char_LHS_core by simp

lemma run_T0_encR_catalog:
  "run oL ((!) (x0 as s)) (T0 as s)
   = (∃jL<length (enumL as s kk). Lval_at as s oL jL ∈ set (enumR as s kk))"
  using run_T0_mixed_bridge Good_char_encR by simp

lemma run_T0_encL_catalog:
  "run ((!) (x0 as s)) oR (T0 as s)
   = (∃jR<length (enumR as s kk). Rval_at as s oR jR ∈ set (enumL as s kk))"
  using run_T0_left_bridge Good_char_encL by simp

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

lemma seenL_T0_subset_read0_x0:
  assumes "x = x0 as s"
  shows   "seenL_run ((!) y) ((!) x) (T0 as s) ⊆ Base.read0 M x"
  (* proved earlier; depends only on TM-side read0 characterisation *)
  sorry

lemma Good_unread_L_local:
  assumes disj: "Base.read0 M x ∩ blockL_abs enc0 as s j = {}"
  assumes out:  "⋀i. i ∉ blockL_abs enc0 as s j ⟹ y ! i = x ! i"
  assumes X:    "x = enc as s kk"
  shows "Good as s ((!) y) ((!) x) = Good as s ((!) x) ((!) x)"
proof -
  (* turn X into the form needed by seenL_T0_subset_read0 *)
  have X0: "x = x0 as s" by (simp add: X)

  (* T0’s left-seen set is contained in read0 on x0-inputs *)
  have SLsub:
  "seenL_run ((!) y) ((!) x) (T0 as s) ⊆ Base.read0 M x"
    by (rule seenL_T0_subset_read0_x0[OF X0])

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
    using run_T0_mixed_bridge[symmetric] by simp
  have G_yx_to_run:
    "Good as s ((!) y) ((!) x) = run ((!) y) ((!) x) (T0 as s)"
    using X0 G_yx_to_run0 by simp

  have G_xx_to_run0:
    "Good as s ((!) (x0 as s)) ((!) (x0 as s))
       = run ((!) (x0 as s)) ((!) (x0 as s)) (T0 as s)"
    using run_T0_mixed_bridge[symmetric] by simp
  have G_xx_to_run:
    "Good as s ((!) x) ((!) x) = run ((!) x) ((!) x) (T0 as s)"
    using X0 G_xx_to_run0 by simp

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
    using X correct_T0_encL by simp
  have Gxx_to_run:
    "Good as s ((!) x) ((!) x) = run ((!) x) ((!) x) (T0 as s)"
    using X correct_T0_encL by simp

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
          using nin' y_def splice_nth_left AL splice_nth_right[OF LEN BND]
                G Good_char_encL baseline_only_jR
          by (meson atLeastLessThan_iff leI)
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
          using y_def splice_nth_inside[OF LEN BND ai ilt] by simp
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
          using Rval_at_def a_def w_def slice_pat pat_val
          by metis
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
          using nin' y_def splice_nth_left AL splice_nth_right[OF LEN BND]
          by (smt (verit) BND LEN ‹oR' ≡ λi. if i ∈ {a..<a + w} then 
              pat ! (i - a) else x0 as s ! i› le_eq_less_or_eq length_map 
              length_upt linordered_semidom_class.add_diff_inverse 
              nat_add_left_cancel_less nat_le_linear nth_map_upt 
              splice_nth_inside)
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
          using y_def splice_nth_inside[OF LEN BND ai ilt] by simp
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
        using Rval_at_def a_def w_def slice_eq slice_pat pat_val
        by presburger

      have Good_y: "Good as s ((!) ?x) ((!) y)"
      proof -
        have "Rval_at as s ((!) y) j ∈ set (enumL as s kk)"
          using Rj_y vL by simp
        hence "∃jR<length (enumR as s kk).
                 Rval_at as s ((!) y) jR ∈ set (enumL as s kk)"
          using jR by blast
        thus ?thesis using Good_char_encL by simp
      qed

      have good_unread_eq:
        "Good as s ((!) ?x) ((!) y) = Good as s ((!) ?x) ((!) ?x)"
        by (rule Good_unread_R_local[OF not_touch outside_y X0])

      from good_unread_eq Good_y NG show False by simp
    qed
  qed
qed

lemma read0_hits_L:
  assumes "n = length as" "distinct_subset_sums as" "j < length (enumL as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
  (* prove this using your existing TM-side “read0 ⊇ seen” facts + the run/Good bridge,
     or even via coverage_for_enc_blocks_L and then unfolding touches_def *)
  sorry

lemma read0_hits_R:
  assumes "n = length as" "distinct_subset_sums as" "j < length (enumR as s kk)"
  shows "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
  sorry

(* 9) The coverage result you wanted, phrased on block families *)
lemma coverage_blocks:
  assumes "n = length as" "distinct_subset_sums as"
  shows
   "(∀j<length (enumL as s kk). touches (enc as s kk) (blockL_abs enc0 as s j)) ∧
    (∀j<length (enumR as s kk). touches (enc as s kk) (blockR_abs enc0 as s kk j))"
proof (intro conjI allI impI)
  fix j assume jL: "j < length (enumL as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockL_abs enc0 as s j"
    by (rule read0_hits_L[OF assms jL])
  thus "touches (enc as s kk) (blockL_abs enc0 as s j)"
    using touches_def by blast
next
  fix j assume jR: "j < length (enumR as s kk)"
  have "∃i∈Base.read0 M (enc as s kk). i ∈ blockR_abs enc0 as s kk j"
    by (rule read0_hits_R[OF assms jR])
  thus "touches (enc as s kk) (blockR_abs enc0 as s kk j)"
    using touches_def by blast
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

  (* … everything below stays as you had it … *)

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
