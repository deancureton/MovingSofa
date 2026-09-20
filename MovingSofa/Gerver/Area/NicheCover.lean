import MovingSofa.Classical.Area
import MovingSofa.ForMathlib.MeasureTheory.EuclideanSpace
import MovingSofa.Gerver.Area.Evaluator
import MovingSofa.Gerver.Niche.RoofProperties

/-!
# The rectangle cover of the literal Gerver niche

The literal niche is the union of the strict vertical fills under the three pieces of its
roof (`gerver_niche_vertical_fills`).  Each piece is traversed with monotone horizontal
coordinate, so subdividing the seven monotone roof stretches at the grid angles covers the
niche by `7 * NN` coordinate rectangles whose widths and heights the certificate encloses
(`gerverNicheRect_covers`).  The kernel-checked numeric conclusion
`GerverAreaCert.nicheOK_true` bounds the total rectangle area, hence `|N₀| ≤ 3301 / 5000`.
-/

noncomputable section

namespace MovingSofa

open MeasureTheory
open GerverAreaCert

/-- The literal niche is Borel measurable: it is a closed half-plane intersected with a
countable union of open sets. -/
theorem measurableSet_gerverLiteralNiche : MeasurableSet gerverLiteralNiche := by
  have h : gerverLiteralNiche =
      {q : Point | 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))} ∩
        ⋃ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          ({q : Point | inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0} ∩
            {q : Point |
              inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0}) := by
    ext q
    simp only [gerverLiteralNiche, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion₂,
      inner_normalVector_pi_div_two]
    tauto
  rw [h]
  refine MeasurableSet.inter
    ((isClosed_le continuous_const (continuous_id.inner continuous_const)).measurableSet) ?_
  refine IsOpen.measurableSet (isOpen_biUnion fun t _ ↦ IsOpen.inter ?_ ?_)
  · exact isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const
  · exact isOpen_lt ((continuous_id.sub continuous_const).inner continuous_const) continuous_const

/-! ### The rectangle cover and the niche upper bound -/

/-- The covering rectangle of the `j`-th subinterval of roof piece `r`. -/
def gerverNicheRect (r j : ℕ) : Set Point :=
  {p : Point | p 0 ∈ Set.Icc (((rectLoZ r j : ℤ) : ℝ) / (M : ℝ))
      (((rectHiZ r j : ℤ) : ℝ) / (M : ℝ)) ∧
    p 1 ∈ Set.Icc 0 (((rectHZ r j : ℤ) : ℝ) / (M : ℝ))}

/-- A strict vertical fill splits along a subdivision of its parameter interval. -/
theorem strictVerticalFill_Icc_union {f : ℝ → Point} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    strictVerticalFill f (Set.Icc a c) =
      strictVerticalFill f (Set.Icc a b) ∪ strictVerticalFill f (Set.Icc b c) := by
  ext q
  simp only [strictVerticalFill, Set.mem_ofPred_eq, Set.mem_union, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, h3⟩
    rcases le_total t b with h | h
    · exact Or.inl ⟨t, ⟨h1, h⟩, h3⟩
    · exact Or.inr ⟨t, ⟨h, h2⟩, h3⟩
  · rintro (⟨t, ⟨h1, h2⟩, h3⟩ | ⟨t, ⟨h1, h2⟩, h3⟩)
    · exact ⟨t, ⟨h1, h2.trans hbc⟩, h3⟩
    · exact ⟨t, ⟨hab.trans h1, h2⟩, h3⟩

/-- The strictly increasing chain of the six `ℕ`-indexed stage endpoints. -/
private theorem gerverStageTime_chain :
    gerverStageTime 0 = 0 ∧ gerverStageTime 0 < gerverStageTime 1 ∧
      gerverStageTime 1 < gerverStageTime 2 ∧ gerverStageTime 2 < gerverStageTime 3 ∧
      gerverStageTime 3 < gerverStageTime 4 ∧ gerverStageTime 4 < gerverStageTime 5 ∧
      gerverStageTime 5 = Real.pi / 2 :=
  ⟨gerverStageTime_zero, gerverStageTime_lt_succ 0 (by norm_num),
    gerverStageTime_lt_succ 1 (by norm_num), gerverStageTime_lt_succ 2 (by norm_num),
    gerverStageTime_lt_succ 3 (by norm_num), gerverStageTime_lt_succ 4 (by norm_num),
    gerverStageTime_five⟩

/-- `gerverRoofReverseTime` written in the `ℕ`-indexed stage endpoints. -/
private theorem gerverRoofReverseTime_eq_stageTime (s : ℝ) :
    gerverRoofReverseTime s = gerverStageTime 4 -
      (gerverStageTime 4 - gerverStageTime 1) / (gerverStageTime 3 - gerverStageTime 2) *
        (s - gerverStageTime 2) := rfl

/-- The first roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_D {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : s ≤ gerverStageTime 2) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 3 :=
  gerverNicheRoof_of_le_two hs h

/-- The middle roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_path {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h2 : gerverStageTime 2 ≤ s) (h3 : s ≤ gerverStageTime 3) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverPath (gerverRoofReverseTime s) :=
  gerverNicheRoof_mid hs h2 h3

/-- The last roof piece, in the `ℕ`-indexed stage endpoints. -/
private theorem gerverNicheRoof_eq_B {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h3 : gerverStageTime 3 ≤ s) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 1 :=
  gerverNicheRoof_of_ge_three hs h3

/-- Two roof arguments compare as their underlying reals. -/
private theorem gerverNicheRoof_fst_le_of_le {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (hb : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) (hab : a ≤ b) :
    gerverNicheRoof ⟨a, ha⟩ 0 ≤ gerverNicheRoof ⟨b, hb⟩ 0 :=
  gerver_niche_roof_strictMono.monotone (Subtype.mk_le_mk.mpr hab)

/-- The `D` piece has monotone horizontal coordinate. -/
private theorem monotoneOn_paperGerverContacts_three_fst :
    MonotoneOn (fun t ↦ paperGerverContacts t 3 0)
      (Set.Icc (gerverStageTime 0) (gerverStageTime 2)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  intro a ha b hb hab
  have hA : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hB : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h := gerverNicheRoof_fst_le_of_le hA hB hab
  rwa [gerverNicheRoof_eq_D hA ha.2, gerverNicheRoof_eq_D hB hb.2] at h

/-- The `B` piece has monotone horizontal coordinate. -/
private theorem monotoneOn_paperGerverContacts_one_fst :
    MonotoneOn (fun t ↦ paperGerverContacts t 1 0)
      (Set.Icc (gerverStageTime 3) (gerverStageTime 5)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  intro a ha b hb hab
  have hA : a ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hB : b ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have h := gerverNicheRoof_fst_le_of_le hA hB hab
  rwa [gerverNicheRoof_eq_B hA ha.1, gerverNicheRoof_eq_B hB hb.1] at h

/-- The ambient path has antitone horizontal coordinate over the middle roof piece. -/
private theorem antitoneOn_paperGerverPath_fst :
    AntitoneOn (fun t ↦ paperGerverPath t 0)
      (Set.Icc (gerverStageTime 1) (gerverStageTime 4)) := by
  obtain ⟨h0, c01, c12, c23, c34, c45, h5⟩ := gerverStageTime_chain
  have hne32 : gerverStageTime 3 - gerverStageTime 2 ≠ 0 :=
    sub_ne_zero_of_ne (by intro hz; linarith)
  have hne41 : gerverStageTime 4 - gerverStageTime 1 ≠ 0 :=
    sub_ne_zero_of_ne (by intro hz; linarith)
  have hc : 0 < (gerverStageTime 4 - gerverStageTime 1) /
      (gerverStageTime 3 - gerverStageTime 2) := div_pos (by linarith) (by linarith)
  have hcne : (gerverStageTime 4 - gerverStageTime 1) /
      (gerverStageTime 3 - gerverStageTime 2) ≠ 0 := ne_of_gt hc
  set c := (gerverStageTime 4 - gerverStageTime 1) /
    (gerverStageTime 3 - gerverStageTime 2) with hcdef
  -- The reverse-time map is inverted by `t ↦ e₂ + (e₄ - t) / c`.
  have hinv : ∀ t : ℝ, gerverRoofReverseTime (gerverStageTime 2 +
      (gerverStageTime 4 - t) / c) = t := by
    intro t
    rw [gerverRoofReverseTime_eq_stageTime, ← hcdef]
    field_simp
    ring
  have heq : (gerverStageTime 4 - gerverStageTime 1) / c =
      gerverStageTime 3 - gerverStageTime 2 := by
    rw [hcdef]
    field_simp
  have hmem : ∀ t : ℝ, gerverStageTime 1 ≤ t → t ≤ gerverStageTime 4 →
      gerverStageTime 2 ≤ gerverStageTime 2 + (gerverStageTime 4 - t) / c ∧
        gerverStageTime 2 + (gerverStageTime 4 - t) / c ≤ gerverStageTime 3 := by
    intro t ht1 ht4
    have hnn : 0 ≤ (gerverStageTime 4 - t) / c := div_nonneg (by linarith) hc.le
    have hstep : (gerverStageTime 4 - gerverStageTime 1) / c -
        (gerverStageTime 4 - t) / c = (t - gerverStageTime 1) / c := by
      field_simp
      ring
    have hnn2 : 0 ≤ (t - gerverStageTime 1) / c := div_nonneg (by linarith) hc.le
    exact ⟨by linarith, by linarith⟩
  intro a ha b hb hab
  obtain ⟨ha2, ha3⟩ := hmem a ha.1 ha.2
  obtain ⟨hb2, hb3⟩ := hmem b hb.1 hb.2
  have hAmem : gerverStageTime 2 + (gerverStageTime 4 - a) / c ∈
      Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hBmem : gerverStageTime 2 + (gerverStageTime 4 - b) / c ∈
      Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hba : gerverStageTime 2 + (gerverStageTime 4 - b) / c ≤
      gerverStageTime 2 + (gerverStageTime 4 - a) / c := by
    have hsub : (gerverStageTime 4 - a) / c - (gerverStageTime 4 - b) / c = (b - a) / c := by
      field_simp
      ring
    have hnn : 0 ≤ (b - a) / c := div_nonneg (by linarith) hc.le
    linarith
  have h := gerverNicheRoof_fst_le_of_le hBmem hAmem hba
  rwa [gerverNicheRoof_eq_path hBmem hb2 hb3, gerverNicheRoof_eq_path hAmem ha2 ha3,
    hinv a, hinv b] at h

/-- Each roof piece has monotone horizontal coordinate in the direction recorded by
`rowFwd`. -/
theorem gerverNicheRow_monotone (r : ℕ) (hr : r < 7) :
    (rowFwd r = true → MonotoneOn (fun t ↦ gerverContactPoint (rowKind r) t 0)
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)))) ∧
      (rowFwd r = false → AntitoneOn (fun t ↦ gerverContactPoint (rowKind r) t 0)
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)))) := by
  obtain ⟨-, c01, c12, c23, c34, c45, -⟩ := gerverStageTime_chain
  have sD0 : Set.Icc (gerverStageTime 0) (gerverStageTime 1) ⊆
      Set.Icc (gerverStageTime 0) (gerverStageTime 2) := Set.Icc_subset_Icc le_rfl c12.le
  have sD1 : Set.Icc (gerverStageTime 1) (gerverStageTime 2) ⊆
      Set.Icc (gerverStageTime 0) (gerverStageTime 2) := Set.Icc_subset_Icc c01.le le_rfl
  have sP2 : Set.Icc (gerverStageTime 3) (gerverStageTime 4) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) :=
    Set.Icc_subset_Icc (c12.trans c23).le le_rfl
  have sP3 : Set.Icc (gerverStageTime 2) (gerverStageTime 3) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) := Set.Icc_subset_Icc c12.le c34.le
  have sP4 : Set.Icc (gerverStageTime 1) (gerverStageTime 2) ⊆
      Set.Icc (gerverStageTime 1) (gerverStageTime 4) :=
    Set.Icc_subset_Icc le_rfl (c23.trans c34).le
  have sB5 : Set.Icc (gerverStageTime 3) (gerverStageTime 4) ⊆
      Set.Icc (gerverStageTime 3) (gerverStageTime 5) := Set.Icc_subset_Icc le_rfl c45.le
  have sB6 : Set.Icc (gerverStageTime 4) (gerverStageTime 5) ⊆
      Set.Icc (gerverStageTime 3) (gerverStageTime 5) := Set.Icc_subset_Icc c34.le le_rfl
  interval_cases r
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_three_fst.mono sD0, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_three_fst.mono sD1, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP2⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP3⟩
  · exact ⟨fun h ↦ absurd h (by decide), fun _ ↦ antitoneOn_paperGerverPath_fst.mono sP4⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_one_fst.mono sB5, fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ monotoneOn_paperGerverContacts_one_fst.mono sB6, fun h ↦ absurd h (by decide)⟩

/-- An integer lower bound at scale `M` read as a bound on the real quotient. -/
private theorem div_M_le_of_le {p : ℤ} {x : ℝ} (h : (p : ℝ) ≤ (M : ℝ) * x) :
    (p : ℝ) / (M : ℝ) ≤ x :=
  (div_le_iff₀ SI.Mpos).2 (by linarith)

/-- An integer upper bound at scale `M` read as a bound on the real quotient. -/
private theorem le_div_M_of_le {p : ℤ} {x : ℝ} (h : (M : ℝ) * x ≤ (p : ℝ)) :
    x ≤ (p : ℝ) / (M : ℝ) :=
  (le_div_iff₀ SI.Mpos).2 (by linarith)

/-- A strict vertical fill over an increasing subdivision of its parameter interval is the
union of the fills of the pieces.  Iterated form of `strictVerticalFill_Icc_union`. -/
private theorem strictVerticalFill_Icc_biUnion {f : ℝ → Point} (a : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n → (∀ i j, i ≤ j → j ≤ n → a i ≤ a j) →
      strictVerticalFill f (Set.Icc (a 0) (a n)) =
        ⋃ i ∈ Finset.range n, strictVerticalFill f (Set.Icc (a i) (a (i + 1))) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by omega)
  | succ n ih =>
    intro _ ha
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rw [strictVerticalFill_Icc_union (ha 0 n (Nat.zero_le _) (by omega))
        (ha n (n + 1) (by omega) le_rfl),
        ih hpos fun i j hij hj => ha i j hij (by omega),
        Finset.range_add_one, Finset.set_biUnion_insert, Set.union_comm]

/-- Each covering rectangle contains the strict vertical fill of its subinterval. -/
theorem gerverNicheRect_covers (r j : ℕ) (hr : r < 7) (hj : j < NN) :
    strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r j)) (gerverGridTime (rowBase r j + 1))) ⊆
      gerverNicheRect r j := by
  have hNN : NN = 64 := rfl
  have hM := SI.Mpos
  have hk : rowKind r ≤ 4 := by interval_cases r <;> decide
  have hS1 : 1 ≤ rowStage r := by interval_cases r <;> decide
  have hS5 : rowStage r ≤ 5 := by interval_cases r <;> decide
  have hj64 : j < 64 := by rwa [hNN] at hj
  have hm1 : rowBase r j + 1 ≤ 5 * NN := by simp only [rowBase, hNN]; omega
  have hm : rowBase r j ≤ 5 * NN := by omega
  have hlo : gerverStageTime (rowStage r - 1) ≤ gerverGridTime (rowBase r j) := by
    have h := gerverGridTime_le_of_le
      (show (rowStage r - 1) * NN ≤ rowBase r j by simp only [rowBase]; omega) hm
    rwa [gerverGridTime_mul_NN] at h
  have hhi : gerverGridTime (rowBase r j + 1) ≤ gerverStageTime (rowStage r) := by
    have h := gerverGridTime_le_of_le
      (show rowBase r j + 1 ≤ rowStage r * NN by simp only [rowBase, hNN]; omega)
      (Nat.mul_le_mul_right NN hS5)
    rwa [gerverGridTime_mul_NN] at h
  have hstep : gerverGridTime (rowBase r j) ≤ gerverGridTime (rowBase r j + 1) :=
    gerverGridTime_le_of_le (Nat.le_succ _) hm1
  have hmemL : gerverGridTime (rowBase r j) ∈
      Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo, hstep.trans hhi⟩
  have hmemR : gerverGridTime (rowBase r j + 1) ∈
      Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo.trans hstep, hhi⟩
  obtain ⟨hmono, hanti⟩ := gerverNicheRow_monotone r hr
  rintro q ⟨t, ⟨htl, htr⟩, hq0, hq1a, hq1b⟩
  have hmemt : t ∈ Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r)) :=
    ⟨hlo.trans htl, htr.trans hhi⟩
  have hHmax : rectHZ r j = max
      (evalZ (stageOf (rowBase r j + 1))
        ⟨(ttZ (rowBase r j)).lo, (ttZ (rowBase r j + 1)).hi⟩ (rowKind r)).2.hi
      (contactZ (rowBase r j) (rowKind r)).2.hi := by
    simp only [rectHZ, SI.imax_eq_max]
  have hH : (M : ℝ) * gerverContactPoint (rowKind r) t 1 ≤ (rectHZ r j : ℝ) := by
    rcases eq_or_lt_of_le htl with heq | hlt
    · have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).2.2
      rw [← heq]
      refine h.trans ?_
      rw [hHmax]
      exact_mod_cast le_max_right _ _
    · have h := (evalZ_interval_sound (rowBase r j) hm1 (rowKind r) hk ⟨hlt, htr⟩).2.2
      refine h.trans ?_
      rw [hHmax]
      exact_mod_cast le_max_left _ _
  refine ⟨⟨?_, ?_⟩, hq1a, ?_⟩
  · rcases Bool.eq_false_or_eq_true (rowFwd r) with hf | hf
    · have hlo' : rectLoZ r j = (contactZ (rowBase r j) (rowKind r)).1.lo := by
        simp [rectLoZ, hf]
      have hx : gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j)) 0 ≤
          gerverContactPoint (rowKind r) t 0 := hmono hf hmemL hmemt htl
      have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).1.1
      refine div_M_le_of_le ?_
      rw [hq0, hlo']
      exact h.trans (mul_le_mul_of_nonneg_left hx hM.le)
    · have hlo' : rectLoZ r j = (contactZ (rowBase r j + 1) (rowKind r)).1.lo := by
        simp [rectLoZ, hf]
      have hx : gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j + 1)) 0 ≤
          gerverContactPoint (rowKind r) t 0 := hanti hf hmemt hmemR htr
      have h := (contactZ_sound (rowBase r j + 1) hm1 (rowKind r) hk).1.1
      refine div_M_le_of_le ?_
      rw [hq0, hlo']
      exact h.trans (mul_le_mul_of_nonneg_left hx hM.le)
  · rcases Bool.eq_false_or_eq_true (rowFwd r) with hf | hf
    · have hhi' : rectHiZ r j = (contactZ (rowBase r j + 1) (rowKind r)).1.hi := by
        simp [rectHiZ, hf]
      have hx : gerverContactPoint (rowKind r) t 0 ≤
          gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j + 1)) 0 :=
        hmono hf hmemt hmemR htr
      have h := (contactZ_sound (rowBase r j + 1) hm1 (rowKind r) hk).1.2
      refine le_div_M_of_le ?_
      rw [hq0, hhi']
      exact (mul_le_mul_of_nonneg_left hx hM.le).trans h
    · have hhi' : rectHiZ r j = (contactZ (rowBase r j) (rowKind r)).1.hi := by
        simp [rectHiZ, hf]
      have hx : gerverContactPoint (rowKind r) t 0 ≤
          gerverContactPoint (rowKind r) (gerverGridTime (rowBase r j)) 0 :=
        hanti hf hmemL hmemt htl
      have h := (contactZ_sound (rowBase r j) hm (rowKind r) hk).1.2
      refine le_div_M_of_le ?_
      rw [hq0, hhi']
      exact (mul_le_mul_of_nonneg_left hx hM.le).trans h
  · have h2 : (M : ℝ) * q 1 ≤ (M : ℝ) * gerverContactPoint (rowKind r) t 1 :=
      mul_le_mul_of_nonneg_left hq1b.le hM.le
    exact le_div_M_of_le (h2.trans hH)

/-- The `NN` rectangles of a row cover the strict vertical fill of its whole stage. -/
private theorem strictVerticalFill_row_subset (r : ℕ) (hr : r < 7) :
    strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r))) ⊆
      ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
  have hNN : NN = 64 := rfl
  have hS1 : 1 ≤ rowStage r := by interval_cases r <;> decide
  have hS5 : rowStage r ≤ 5 := by interval_cases r <;> decide
  have ha0 : gerverGridTime (rowBase r 0) = gerverStageTime (rowStage r - 1) := by
    simpa [rowBase] using gerverGridTime_mul_NN (rowStage r - 1)
  have haN : gerverGridTime (rowBase r NN) = gerverStageTime (rowStage r) := by
    have hb : rowBase r NN = rowStage r * NN := by simp only [rowBase, hNN]; omega
    rw [hb, gerverGridTime_mul_NN]
  have hmono : ∀ i j, i ≤ j → j ≤ NN →
      gerverGridTime (rowBase r i) ≤ gerverGridTime (rowBase r j) := by
    intro i j hij hj
    refine gerverGridTime_le_of_le (by simp only [rowBase]; omega) ?_
    simp only [rowBase, hNN]; omega
  have hsplit : strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r 0)) (gerverGridTime (rowBase r NN))) =
      ⋃ i ∈ Finset.range NN, strictVerticalFill (gerverContactPoint (rowKind r))
        (Set.Icc (gerverGridTime (rowBase r i)) (gerverGridTime (rowBase r i + 1))) :=
    strictVerticalFill_Icc_biUnion (fun i => gerverGridTime (rowBase r i)) NN
      (by simp [hNN]) hmono
  rw [← ha0, ← haN, hsplit]
  refine Set.iUnion₂_subset fun i hi q hq => ?_
  simp only [Set.mem_iUnion, exists_prop]
  exact ⟨i, hi, gerverNicheRect_covers r i hr (Finset.mem_range.1 hi) hq⟩

/-- The `7 * NN` rectangles cover the literal niche. -/
theorem gerverLiteralNiche_subset_rects :
    gerverLiteralNiche ⊆
      ⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
  have e0 : gerverStageTimes 0 = gerverStageTime 0 := rfl
  have e1 : gerverStageTimes 1 = gerverStageTime 1 := rfl
  have e2 : gerverStageTimes 2 = gerverStageTime 2 := rfl
  have e3 : gerverStageTimes 3 = gerverStageTime 3 := rfl
  have e4 : gerverStageTimes 4 = gerverStageTime 4 := rfl
  have e5 : gerverStageTimes 5 = gerverStageTime 5 := rfl
  have h01 : gerverStageTime 0 ≤ gerverStageTime 1 := (gerverStageTime_lt_succ 0 (by norm_num)).le
  have h12 : gerverStageTime 1 ≤ gerverStageTime 2 := (gerverStageTime_lt_succ 1 (by norm_num)).le
  have h23 : gerverStageTime 2 ≤ gerverStageTime 3 := (gerverStageTime_lt_succ 2 (by norm_num)).le
  have h34 : gerverStageTime 3 ≤ gerverStageTime 4 := (gerverStageTime_lt_succ 3 (by norm_num)).le
  have h45 : gerverStageTime 4 ≤ gerverStageTime 5 := (gerverStageTime_lt_succ 4 (by norm_num)).le
  have hrow : ∀ r, r < 7 → strictVerticalFill (gerverContactPoint (rowKind r))
      (Set.Icc (gerverStageTime (rowStage r - 1)) (gerverStageTime (rowStage r))) ⊆
      ⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j := by
    intro r hr q hq
    have h := strictVerticalFill_row_subset r hr hq
    simp only [Set.mem_iUnion, exists_prop] at h ⊢
    obtain ⟨j, hj, hjq⟩ := h
    exact ⟨r, Finset.mem_range.2 hr, j, hj, hjq⟩
  rw [gerver_niche_vertical_fills, e0, e1, e2, e3, e4, e5]
  refine Set.union_subset (Set.union_subset ?_ ?_) ?_
  · rw [strictVerticalFill_Icc_union h01 h12]
    exact Set.union_subset (hrow 0 (by norm_num)) (hrow 1 (by norm_num))
  · rw [strictVerticalFill_Icc_union h12 (h23.trans h34), strictVerticalFill_Icc_union h23 h34]
    exact Set.union_subset (hrow 4 (by norm_num))
      (Set.union_subset (hrow 3 (by norm_num)) (hrow 2 (by norm_num)))
  · rw [strictVerticalFill_Icc_union h34 h45]
    exact Set.union_subset (hrow 5 (by norm_num)) (hrow 6 (by norm_num))

/-- The planar volume of one covering rectangle. -/
theorem volume_gerverNicheRect (r j : ℕ) :
    volume (gerverNicheRect r j) =
      ENNReal.ofReal ((((rectHiZ r j - rectLoZ r j : ℤ)) : ℝ) / (M : ℝ)) *
        ENNReal.ofReal (((rectHZ r j : ℤ) : ℝ) / (M : ℝ)) := by
  rw [gerverNicheRect, EuclideanSpace.volume_setOf_apply_mem_Icc]
  congr 2
  · push_cast
    ring
  · ring

/-- The certificate bounds the total rectangle volume. -/
theorem gerverNicheRect_volume_sum_le :
    ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j) ≤
      ENNReal.ofReal ((3301 : ℝ) / 5000) := by
  have hM := SI.Mpos
  have hQ : (0 : ℝ) < (M : ℝ) * (M : ℝ) := mul_pos hM hM
  -- `unfold` rather than a type ascription: matching `nicheOK` against `decide _` by
  -- unification would force the elaborator to evaluate the whole certificate.
  have hcert : 5000 * nicheSumZ ≤ 3301 * M * M := by
    have h := nicheOK_true
    unfold nicheOK at h
    exact of_decide_eq_true h
  have harea : ∀ r j : ℕ,
      rectAreaZ r j = max 0 (rectHiZ r j - rectLoZ r j) * max 0 (rectHZ r j) := by
    intro r j
    simp only [rectAreaZ, SI.imax_eq_max]
  have hnn : ∀ r j : ℕ, (0 : ℝ) ≤ (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ)) := by
    intro r j
    refine div_nonneg ?_ hQ.le
    have : (0 : ℤ) ≤ rectAreaZ r j := by
      rw [harea]
      exact mul_nonneg (le_max_left _ _) (le_max_left _ _)
    exact_mod_cast this
  have hcell : ∀ r j : ℕ, volume (gerverNicheRect r j) ≤
      ENNReal.ofReal ((rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) := by
    intro r j
    have hA : ((rectHiZ r j - rectLoZ r j : ℤ) : ℝ) / (M : ℝ) ≤
        ((max 0 (rectHiZ r j - rectLoZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      gcongr
      exact_mod_cast le_max_right (0 : ℤ) (rectHiZ r j - rectLoZ r j)
    have hB : ((rectHZ r j : ℤ) : ℝ) / (M : ℝ) ≤
        ((max 0 (rectHZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      gcongr
      exact_mod_cast le_max_right (0 : ℤ) (rectHZ r j)
    have hA0 : (0 : ℝ) ≤ ((max 0 (rectHiZ r j - rectLoZ r j) : ℤ) : ℝ) / (M : ℝ) := by
      refine div_nonneg ?_ hM.le
      exact_mod_cast le_max_left (0 : ℤ) (rectHiZ r j - rectLoZ r j)
    rw [volume_gerverNicheRect]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hA) (ENNReal.ofReal_le_ofReal hB)) ?_
    rw [← ENNReal.ofReal_mul hA0]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [harea]
    push_cast
    field_simp
  have hns : nicheSumZ = ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, rectAreaZ r j := by
    rw [nicheSumZ, SI.foldl_range_int]
    exact Finset.sum_congr rfl fun r _ => by rw [rowSumZ, SI.foldl_range_int]
  have hsum : ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
      (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ)) =
        (nicheSumZ : ℝ) / ((M : ℝ) * (M : ℝ)) := by
    rw [hns]
    push_cast
    simp only [← Finset.sum_div]
  calc ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j)
      ≤ ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
          ENNReal.ofReal ((rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun j _ => hcell r j
    _ = ∑ r ∈ Finset.range 7, ENNReal.ofReal
          (∑ j ∈ Finset.range NN, (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        Finset.sum_congr rfl fun r _ =>
          (ENNReal.ofReal_sum_of_nonneg fun j _ => hnn r j).symm
    _ = ENNReal.ofReal (∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN,
          (rectAreaZ r j : ℝ) / ((M : ℝ) * (M : ℝ))) :=
        (ENNReal.ofReal_sum_of_nonneg fun r _ => Finset.sum_nonneg fun j _ => hnn r j).symm
    _ ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hsum, div_le_div_iff₀ hQ (by norm_num)]
        have hR : (5000 : ℝ) * (nicheSumZ : ℝ) ≤ 3301 * (M : ℝ) * (M : ℝ) := by
          exact_mod_cast hcert
        linarith

/-- The niche volume bound. -/
theorem gerver_niche_volume_le :
    volume gerverLiteralNiche ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := by
  calc volume gerverLiteralNiche
      ≤ volume (⋃ r ∈ Finset.range 7, ⋃ j ∈ Finset.range NN, gerverNicheRect r j) :=
        measure_mono gerverLiteralNiche_subset_rects
    _ ≤ ∑ r ∈ Finset.range 7, volume (⋃ j ∈ Finset.range NN, gerverNicheRect r j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range 7, ∑ j ∈ Finset.range NN, volume (gerverNicheRect r j) :=
        Finset.sum_le_sum fun _ _ => measure_biUnion_finset_le _ _
    _ ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) := gerverNicheRect_volume_sum_le

end MovingSofa
