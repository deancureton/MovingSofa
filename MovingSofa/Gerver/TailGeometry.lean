import MovingSofa.Bounds.MonotonicityIntervals
import MovingSofa.Cap.Tail.Arcs
import MovingSofa.Convex.EnvelopeFace
import MovingSofa.Gerver.ContactGeometry

/-!
# The left and right tails of the Gerver cap

`gerver_tailGeometry` identifies the two tails cut out of the Gerver cap by the inner hallway
walls.  Each tail is cut out by a one-parameter family of supporting half-planes whose contact
points are the two inner Gerver contact curves `B` and `D`, so the envelope-tangency lemmas of
`MovingSofa/Convex/EnvelopeFace.lean` identify every intervening face of a tail with a single
point of the corresponding contact curve, and the stagewise monotonicity of the contact curves
against a fixed frame direction (`MovingSofa/Gerver/StageRegularity.lean`) supplies both the
containment of the contact curves in the tails and the injectivity of the two
parametrizations.  The support sums are the cut identity `h_L (s + π) = -m s`.
-/

noncomputable section

namespace MovingSofa

def ParametrizesDirectedArc (f : ℝ → Point) (a b : ℝ) (Γ : DirectedArcData) : Prop :=
  a < b ∧ ContinuousOn f (Set.Icc a b) ∧ Set.InjOn f (Set.Icc a b) ∧
    f '' Set.Icc a b = Γ.carrier ∧ f a = Γ.startPoint ∧ f b = Γ.endPoint

theorem gerver_tailGeometry (K : SpecialCapSpace) (B D : ConvexBody Point)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    (∀ t ∈ Set.Ioo (gerverStageTimes 0) (gerverStageTimes 2),
      edgeVertices D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) =
        (paperGerverContacts t 3, paperGerverContacts t 3)) ∧
    (∀ t ∈ Set.Ioo (gerverStageTimes 3) (gerverStageTimes 5),
      edgeVertices B ((Real.pi + t : ℝ) : Real.Angle) =
        (paperGerverContacts t 1, paperGerverContacts t 1)) ∧
    (distinguishedCapSides K.val).2.corner = paperGerverContacts (gerverStageTimes 2) 3 ∧
    (rightLeftTailArcs B D).2.endPoint = paperGerverContacts (gerverStageTimes 2) 3 ∧
    edgeVertices D ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle) =
      (paperGerverContacts (gerverStageTimes 2) 3, paperGerverContacts (gerverStageTimes 2) 3) ∧
    ParametrizesDirectedArc (fun t ↦ paperGerverContacts t 3)
      (gerverStageTimes 0) (gerverStageTimes 2) (rightLeftTailArcs B D).2 ∧
    (distinguishedCapSides K.val).1.corner = paperGerverContacts (gerverStageTimes 3) 1 ∧
    (rightLeftTailArcs B D).1.startPoint = paperGerverContacts (gerverStageTimes 3) 1 ∧
    edgeVertices B ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) =
      (paperGerverContacts (gerverStageTimes 3) 1, paperGerverContacts (gerverStageTimes 3) 1) ∧
    ParametrizesDirectedArc (fun t ↦ paperGerverContacts t 1)
      (gerverStageTimes 3) (gerverStageTimes 5) (rightLeftTailArcs B D).1 ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      supportValue K.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      supportValue K.val.val (t : Real.Angle) +
        supportValue B ((Real.pi + t : ℝ) : Real.Angle) = 1) := by
  -- ### One cap serves every clause, and it carries the literal contact geometry
  obtain ⟨-, hGeq, -, -, hcapeq, -, -⟩ := gerver_capSupport_identification
  have hcarrier : (K.val.val : Set Point) = gerverOuterCap := by rw [hK, hGeq, hcapeq]
  obtain ⟨-, K', hK'set, hdens, hsel, -, -, hBwall, -, hDwall, -, -⟩ :=
    paperGerver_contact_geometry
  have hKeq : K' = K.val := Subtype.ext (SetLike.coe_injective (hK'set.trans hK.symm))
  subst hKeq
  -- ### The strictly increasing stage times
  have ht0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have ht5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have hr : paperGerverConstants.2.1 = gerverStageTimes 1 := rfl
  have hl : paperGerverConstants.2.2 = gerverStageTimes 4 := rfl
  have h01' : gerverStageTimes 0 < gerverStageTimes 1 := gerverStageTimes_strictMono (by decide)
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have h45' : gerverStageTimes 4 < gerverStageTimes 5 := gerverStageTimes_strictMono (by decide)
  have h01 : (0 : ℝ) < gerverStageTimes 1 := ht0 ▸ h01'
  have h45 : gerverStageTimes 4 < Real.pi / 2 := ht5 ▸ h45'
  -- ### The support coordinates of the cap along the path
  have hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), capInnerCorner K.val t = paperGerverPath t :=
    fun t ht ↦ (hsel ⟨t, ht⟩).2.2
  have hsupu : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      inner ℝ (paperGerverPath t) (normalVector (t : Real.Angle)) =
        supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 := by
    intro t ht
    rw [← hcorner t ht]
    exact inner_capInnerCorner_normalVector K.val t
  have hsupv : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) =
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    intro t ht
    rw [← hcorner t ht]
    exact inner_capInnerCorner_tangentVector K.val t
  -- ### The two families of supporting lines cutting the tails out of the cap
  set mD : ℝ → ℝ := fun s ↦ inner ℝ (paperGerverPath (s - Real.pi / 2))
    (tangentVector ((s - Real.pi / 2 : ℝ) : Real.Angle)) with hmDdef
  set mB : ℝ → ℝ := fun s ↦ inner ℝ (paperGerverPath s) (normalVector (s : Real.Angle))
    with hmBdef
  have hmDval : ∀ t : ℝ, mD (t + Real.pi / 2) =
      inner ℝ (paperGerverPath t) (tangentVector (t : Real.Angle)) := by
    intro t
    simp only [hmDdef, add_sub_cancel_right]
  have hmDsup : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), mD (t + Real.pi / 2) =
      supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    fun t ht ↦ (hmDval t).trans (hsupv t ht)
  have hmDderiv : ∀ t : ℝ, HasDerivAt mD
      (inner ℝ (paperGerverContacts t 3) (tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle)))
      (t + Real.pi / 2) := by
    intro t
    have h := (hasDerivAt_inner_paperGerverPath_tangentVector (t + Real.pi / 2 - Real.pi / 2)).comp
      (t + Real.pi / 2) ((hasDerivAt_id (t + Real.pi / 2)).sub_const (Real.pi / 2))
    rw [add_sub_cancel_right] at h
    rw [tangentVector_add_pi_div_two, inner_neg_right]
    simpa only [hmDdef, Function.comp_def, mul_one, id_eq] using h
  have hmBderiv : ∀ t : ℝ, HasDerivAt mB
      (inner ℝ (paperGerverContacts t 1) (tangentVector (t : Real.Angle))) t := by
    intro t
    simpa only [hmBdef] using hasDerivAt_inner_paperGerverPath_normalVector t
  have hDle : ∀ q ∈ (D : Set Point), ∀ s ∈ Set.Icc (Real.pi / 2)
      (gerverStageTimes 4 + Real.pi / 2), mD s ≤ inner ℝ q (normalVector (s : Real.Angle)) := by
    intro q hq s hs
    rw [hD] at hq
    have hs' : s - Real.pi / 2 ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2 :=
      ⟨by linarith only [hs.1], by rw [hl]; linarith only [hs.2]⟩
    have h : supportValue (K.val.val : Set Point)
        ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ q (normalVector ((s - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)) :=
      Set.mem_iInter₂.mp hq.2 (s - Real.pi / 2) hs'
    rw [sub_add_cancel] at h
    have hmem : s - Real.pi / 2 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨hs'.1, by linarith only [hs'.2, hl ▸ hs'.2, h45, ht5]⟩
    rw [show mD s = mD (s - Real.pi / 2 + Real.pi / 2) by rw [sub_add_cancel],
      hmDsup _ hmem, sub_add_cancel]
    exact h
  have hBle : ∀ q ∈ (B : Set Point), ∀ s ∈ Set.Icc (gerverStageTimes 1) (Real.pi / 2),
      mB s ≤ inner ℝ q (normalVector (s : Real.Angle)) := by
    intro q hq s hs
    rw [hB] at hq
    have h : supportValue (K.val.val : Set Point) (s : Real.Angle) - 1 ≤
        inner ℝ q (normalVector (s : Real.Angle)) :=
      Set.mem_iInter₂.mp hq.2 s ⟨by rw [hr]; exact hs.1, hs.2⟩
    simp only [hmBdef]
    rw [hsupu s ⟨by linarith only [hs.1, h01], hs.2⟩]
    exact h
  -- ### The two contact curves touch their defining lines
  have hDtouch : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      inner ℝ (paperGerverContacts t 3) (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        mD (t + Real.pi / 2) := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨ht0 ▸ ht.1, by linarith only [ht.2, h23, h34, h45]⟩
    have h := (mem_rotatingHallwayParts_dRay_iff _ _ _).mp (hDwall t ht).2
    rw [normalVector_add_pi_div_two_real, hmDval t, h.2, hsupv t htI, Real.Angle.coe_add]
  have hBtouch : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      inner ℝ (paperGerverContacts t 1) (normalVector (t : Real.Angle)) = mB t := by
    intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [ht.1, h01, h12, h23], ht5 ▸ ht.2⟩
    have h := (mem_rotatingHallwayParts_bRay_iff _ _ _).mp (hBwall t ht).2
    simp only [hmBdef]
    rw [hsupu t htI]
    exact h.1
  -- ### The cap lies in the upper half-plane, and both contact curves lie in the cap
  have hcapupper : ∀ q ∈ (K.val.val : Set Point), 0 ≤ q 1 := fun q hq ↦ by
    simpa only [inner_normalVector_pi_div_two] using
      K.val.inner_normalVector_pi_div_two_nonneg hq
  have hcapD : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ (K.val.val : Set Point) := fun t ht ↦
    hcarrier ▸ gerver_niche_roof_membership.1 t ht
  have hcapB : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ (K.val.val : Set Point) := fun t ht ↦
    hcarrier ▸ gerver_niche_roof_membership.2.2 t ht
  -- ### Each contact curve stays above its own distinguished wall
  have hantiD : ∀ i : Fin 5, (i = 0 ∨ i = 1) →
      StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3)
        (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle))) (gerverStageIntervals i) := by
    intro i hi
    refine strictAntiOn_inner_paperGerverContacts_three hi ?_ ?_ <;> intro s hs <;>
      rcases hi with rfl | rfl
    · rw [gerverStageIntervals_zero] at hs; linarith only [hs.2, h12, h23, h34]
    · rw [gerverStageIntervals_one] at hs; linarith only [hs.2, h23, h34]
    · rw [gerverStageIntervals_zero] at hs; linarith only [hs.1, ht0, h45, Real.pi_pos]
    · rw [gerverStageIntervals_one] at hs; linarith only [hs.1, h01, h45, Real.pi_pos]
  have hmonoB : ∀ i : Fin 5, (i = 3 ∨ i = 4) →
      StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1)
        (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle))) (gerverStageIntervals i) := by
    intro i hi
    refine strictMonoOn_inner_paperGerverContacts_one hi ?_ ?_ <;> intro s hs <;>
      rcases hi with rfl | rfl
    · rw [gerverStageIntervals_three] at hs; linarith only [hs.1, h12, h23]
    · rw [gerverStageIntervals_four] at hs; linarith only [hs.1, h12, h23, h34]
    · rw [gerverStageIntervals_three] at hs; linarith only [hs.2, h45, h01, Real.pi_pos]
    · rw [gerverStageIntervals_four] at hs; linarith only [hs.2, ht5, h01, Real.pi_pos]
  have hstrictD : StrictAntiOn (fun s ↦ inner ℝ (paperGerverContacts s 3)
      (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)))
      (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) := by
    rw [← Set.Icc_union_Icc_eq_Icc h01'.le h12.le]
    exact (gerverStageIntervals_zero ▸ hantiD 0 (Or.inl rfl)).union
      (gerverStageIntervals_one ▸ hantiD 1 (Or.inr rfl))
      (isGreatest_Icc h01'.le) (isLeast_Icc h12.le)
  have hstrictB : StrictMonoOn (fun s ↦ inner ℝ (paperGerverContacts s 1)
      (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)))
      (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := by
    rw [← Set.Icc_union_Icc_eq_Icc h34.le h45'.le]
    exact (gerverStageIntervals_three ▸ hmonoB 3 (Or.inl rfl)).union
      (gerverStageIntervals_four ▸ hmonoB 4 (Or.inr rfl))
      (isGreatest_Icc h34.le) (isLeast_Icc h45'.le)
  have hkeyD : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      inner ℝ (paperGerverContacts (gerverStageTimes 2) 3)
          (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)) ≤
        inner ℝ (paperGerverContacts t 3)
          (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle)) :=
    fun t ht ↦ hstrictD.antitoneOn ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2
  have hkeyB : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      inner ℝ (paperGerverContacts (gerverStageTimes 3) 1)
          (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)) ≤
        inner ℝ (paperGerverContacts t 1)
          (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)) :=
    fun t ht ↦ hstrictB.monotoneOn ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1
  have hDfix : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ (innerWallUpperHalfPlanes K.val (gerverStageTimes 4)).2 := by
    intro t ht
    have hl4 : gerverStageTimes 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [h01, h12, h23, h34], h45.le⟩
    show supportValue (K.val.val : Set Point)
        ((gerverStageTimes 4 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ (paperGerverContacts t 3)
        (normalVector ((gerverStageTimes 4 + Real.pi / 2 : ℝ) : Real.Angle))
    rw [← hmDsup _ hl4, hmDval, normalVector_add_pi_div_two_real,
      ← gerver_niche_piece_endpoints.2.1]
    exact hkeyD t ht
  have hBfix : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ (innerWallUpperHalfPlanes K.val (gerverStageTimes 1)).1 := by
    intro t ht
    have hr1 : gerverStageTimes 1 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨h01.le, by linarith only [h12, h23, h34, h45]⟩
    show supportValue (K.val.val : Set Point) ((gerverStageTimes 1 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ (paperGerverContacts t 1) (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle))
    rw [← hsupu _ hr1, ← gerver_niche_piece_endpoints.1]
    exact hkeyB t ht
  -- ### The remaining walls are excluded by the niche
  have hiq : ∀ s : ℝ, (rotatingHallwayParts (K.val.val : Set Point) (s : Real.Angle)).innerQuadrant
      = innerQuadrant (K.val.val : Set Point) s := by
    intro s
    rw [(rotatingHallwayParts_formulas (K.val.val : Set Point)
      (s : Real.Angle)).2.2.2.2.2.2.2.2, innerQuadrant, ← Real.Angle.coe_add]
  have hDside : (distinguishedCapSides K.val).2.upperHalfPlane =
      (innerWallUpperHalfPlanes K.val (gerverStageTimes 4)).2 := by rw [← hl]; rfl
  have hBside : (distinguishedCapSides K.val).1.upperHalfPlane =
      (innerWallUpperHalfPlanes K.val (gerverStageTimes 1)).1 := by rw [← hr]; rfl
  have hDwedge : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      ∀ s ∈ Set.Ioo (0 : ℝ) (gerverStageTimes 4),
      paperGerverContacts t 3 ∈ (innerWallUpperHalfPlanes K.val s).2 := by
    intro t ht s hs
    by_contra hmem
    have hquad := (cap_tail_monotonicity_intervals K).2.2.2 s
      ⟨hs.1.le, by rw [hl]; exact hs.2⟩ ⟨hs.1, by linarith only [hs.2, h45]⟩
    have hfix : paperGerverContacts t 3 ∈ (distinguishedCapSides K.val).2.upperHalfPlane := by
      rw [hDside]
      exact hDfix t ht
    have hin : paperGerverContacts t 3 ∈
        ((distinguishedCapSides K.val).2.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val s).2 :=
      ⟨⟨hfix, hcapupper _ (hcapD t ht)⟩, hmem⟩
    rw [← hquad] at hin
    exact (hDwall t ht).1 ⟨hin.2.1, Set.mem_iUnion₂.2
      ⟨s, ⟨hs.1, by linarith only [hs.2, h45]⟩, (hiq s) ▸ hin.2.2⟩⟩
  have hBwedge : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      ∀ s ∈ Set.Ioo (gerverStageTimes 1) (Real.pi / 2),
      paperGerverContacts t 1 ∈ (innerWallUpperHalfPlanes K.val s).1 := by
    intro t ht s hs
    by_contra hmem
    have hquad := (cap_tail_monotonicity_intervals K).2.2.1 s
      ⟨by rw [hr]; exact hs.1, hs.2.le⟩ ⟨by linarith only [hs.1, h01], hs.2⟩
    have hfix : paperGerverContacts t 1 ∈ (distinguishedCapSides K.val).1.upperHalfPlane := by
      rw [hBside]
      exact hBfix t ht
    have hin : paperGerverContacts t 1 ∈
        ((distinguishedCapSides K.val).1.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val s).1 :=
      ⟨⟨hfix, hcapupper _ (hcapB t ht)⟩, hmem⟩
    rw [← hquad] at hin
    exact (hBwall t ht).1 ⟨hin.2.1, Set.mem_iUnion₂.2
      ⟨s, ⟨by linarith only [hs.1, h01], hs.2⟩, (hiq s) ▸ hin.2.2⟩⟩
  -- ### Both contact curves lie in their tails
  have hDmem : ∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ (D : Set Point) := by
    intro t ht
    rw [hD]
    refine ⟨hcapD t ht, Set.mem_iInter₂.2 fun s hs ↦ ?_⟩
    rw [hl] at hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · show supportValue (K.val.val : Set Point) ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
        inner ℝ (paperGerverContacts t 3) (normalVector ((s + Real.pi / 2 : ℝ) : Real.Angle))
      rw [← h0, zero_add, K.val.property.2.2.2.1, inner_normalVector_pi_div_two]
      simpa only [sub_self] using hcapupper _ (hcapD t ht)
    rcases eq_or_lt_of_le hs.2 with h4 | h4
    · exact h4 ▸ hDfix t ht
    · exact hDwedge t ht s ⟨h0, h4⟩
  have hBmem : ∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ (B : Set Point) := by
    intro t ht
    rw [hB]
    refine ⟨hcapB t ht, Set.mem_iInter₂.2 fun s hs ↦ ?_⟩
    rw [hr] at hs
    rcases eq_or_lt_of_le hs.2 with hT | hT
    · show supportValue (K.val.val : Set Point) (s : Real.Angle) - 1 ≤
        inner ℝ (paperGerverContacts t 1) (normalVector (s : Real.Angle))
      rw [hT, K.val.property.2.2.2.1, inner_normalVector_pi_div_two]
      simpa only [sub_self] using hcapupper _ (hcapB t ht)
    rcases eq_or_lt_of_le hs.1 with h1 | h1
    · exact h1 ▸ hBfix t ht
    · exact hBwedge t ht s ⟨h1, hT⟩
  -- ### The singleton faces along the two contact curves
  have hcast : ∀ x y : ℝ, x = y → ((x : ℝ) : Real.Angle) = ((y : ℝ) : Real.Angle) :=
    fun x y h ↦ by rw [h]
  have h02 : (0 : ℝ) < gerverStageTimes 2 := by linarith only [h01, h12]
  have h24 : gerverStageTimes 2 < gerverStageTimes 4 := by linarith only [h23, h34]
  have hl4I : gerverStageTimes 4 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith only [h01, h12, h23, h34], h45.le⟩
  have hmemD0 : (0 : ℝ) ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨ht0.le, h02.le⟩
  have hmemD2 : gerverStageTimes 2 ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨by linarith only [ht0.le, h02], le_rfl⟩
  have hmemB3 : gerverStageTimes 3 ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩
  have hmemB5 : Real.pi / 2 ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨by linarith only [h34, h45], ht5.ge⟩
  have hDleIoo : ∀ q ∈ (D : Set Point), ∀ s ∈ Set.Ioo (Real.pi / 2)
      (gerverStageTimes 4 + Real.pi / 2), mD s ≤ inner ℝ q (normalVector (s : Real.Angle)) :=
    fun q hq s hs ↦ hDle q hq s ⟨hs.1.le, hs.2.le⟩
  have hBleIoo : ∀ q ∈ (B : Set Point), ∀ s ∈ Set.Ioo (gerverStageTimes 1) (Real.pi / 2),
      mB s ≤ inner ℝ q (normalVector (s : Real.Angle)) :=
    fun q hq s hs ↦ hBle q hq s ⟨hs.1.le, hs.2.le⟩
  have hDface : ∀ t ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2),
      exposedEdge D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = {paperGerverContacts t 3} := by
    intro t ht
    have htI : t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) := ⟨ht.1.le, ht.2⟩
    rw [ht0] at ht
    have h := exposedEdge_add_pi_eq_singleton_of_mem_Ioo (L := D) (m := mD) (t := t + Real.pi / 2)
      ⟨by linarith only [ht.1], by linarith only [ht.2, h24]⟩ hDleIoo (hDmem t htI)
      (hDtouch t htI) (hmDderiv t)
    rwa [hcast _ _ (show t + Real.pi / 2 + Real.pi = 3 * Real.pi / 2 + t by ring)] at h
  have hBface : ∀ t ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5),
      exposedEdge B ((Real.pi + t : ℝ) : Real.Angle) = {paperGerverContacts t 1} := by
    intro t ht
    have htI : t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) := ⟨ht.1, ht.2.le⟩
    rw [ht5] at ht
    have h := exposedEdge_add_pi_eq_singleton_of_mem_Ioo (L := B) (m := mB) (t := t)
      ⟨by linarith only [ht.1, h12, h23], ht.2⟩ hBleIoo (hBmem t htI) (hBtouch t htI)
      (hmBderiv t)
    rwa [hcast _ _ (show t + Real.pi = Real.pi + t by ring)] at h
  -- ### The two exact joins are contacts of the outer walls as well
  have hDjoin : inner ℝ (paperGerverContacts (gerverStageTimes 2) 3)
      (normalVector ((gerverStageTimes 4 + Real.pi / 2 : ℝ) : Real.Angle)) =
      mD (gerverStageTimes 4 + Real.pi / 2) := by
    rw [hmDval, normalVector_add_pi_div_two_real, gerver_niche_piece_endpoints.2.1]
  have hBjoin : inner ℝ (paperGerverContacts (gerverStageTimes 3) 1)
      (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle)) = mB (gerverStageTimes 1) := by
    simp only [hmBdef]
    rw [gerver_niche_piece_endpoints.1]
  have hDouter : paperGerverContacts (gerverStageTimes 2) 3 ∈
      exposedEdge D ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle) := by
    have h := exposedEdge_add_pi_eq_of_forall_le
      (fun q hq ↦ hDle q hq _ ⟨by linarith only [hl4I.1], le_rfl⟩) (hDmem _ hmemD2) hDjoin
    rw [hcast _ _ (show gerverStageTimes 4 + Real.pi / 2 + Real.pi =
      3 * Real.pi / 2 + gerverStageTimes 4 by ring)] at h
    rw [h]
    exact ⟨hDmem _ hmemD2, hDjoin⟩
  have hBouter : paperGerverContacts (gerverStageTimes 3) 1 ∈
      exposedEdge B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle) := by
    have h := exposedEdge_add_pi_eq_of_forall_le
      (fun q hq ↦ hBle q hq _ ⟨le_rfl, by linarith only [h12, h23, h34, h45]⟩)
      (hBmem _ hmemB3) hBjoin
    rw [hcast _ _ (show gerverStageTimes 1 + Real.pi = Real.pi + gerverStageTimes 1 by ring)] at h
    rw [h]
    exact ⟨hBmem _ hmemB3, hBjoin⟩
  -- ### The two arc endpoints at the outer normals
  have hDend : (edgeVertices D ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle)).2 =
      paperGerverContacts (gerverStageTimes 2) 3 := by
    have hsin : Real.sin (3 * Real.pi / 2 + gerverStageTimes 2 -
        (3 * Real.pi / 2 + gerverStageTimes 4)) ≠ 0 := by
      have : Real.sin (gerverStageTimes 4 - gerverStageTimes 2) > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith only [h24])
          (by linarith only [h45, h02, Real.pi_pos])
      rw [show 3 * Real.pi / 2 + gerverStageTimes 2 - (3 * Real.pi / 2 + gerverStageTimes 4) =
        -(gerverStageTimes 4 - gerverStageTimes 2) by ring, Real.sin_neg]
      linarith only [this]
    have hp := eq_supportingIntersection_of_mem_exposedEdge hsin
      ((hDface _ ⟨by linarith only [ht0.le, h02], le_rfl⟩) ▸ rfl) hDouter
    have hmem : supportingIntersection D ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle)
        ((3 * Real.pi / 2 + gerverStageTimes 4 : ℝ) : Real.Angle) ∈ D := by
      rw [← hp]
      exact hDmem _ hmemD2
    rw [← supportingIntersection_eq_edgeVertices_snd_of_mem D (by linarith only [h24])
      (by linarith only [h45, h02, Real.pi_pos]) hmem, ← hp]
  have hBstart : (edgeVertices B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle)).1 =
      paperGerverContacts (gerverStageTimes 3) 1 := by
    have hsin : Real.sin (Real.pi + gerverStageTimes 1 - (Real.pi + gerverStageTimes 3)) ≠ 0 := by
      have : Real.sin (gerverStageTimes 3 - gerverStageTimes 1) > 0 :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith only [h12, h23])
          (by linarith only [h34, h45, h01, Real.pi_pos])
      rw [show Real.pi + gerverStageTimes 1 - (Real.pi + gerverStageTimes 3) =
        -(gerverStageTimes 3 - gerverStageTimes 1) by ring, Real.sin_neg]
      linarith only [this]
    have hp := eq_supportingIntersection_of_mem_exposedEdge hsin hBouter
      ((hBface _ ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩) ▸ rfl)
    have hmem : supportingIntersection B ((Real.pi + gerverStageTimes 1 : ℝ) : Real.Angle)
        ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) ∈ B := by
      rw [← hp]
      exact hBmem _ hmemB3
    rw [← supportingIntersection_eq_edgeVertices_fst_of_mem B (by linarith only [h12, h23])
      (by linarith only [h34, h45, h01, Real.pi_pos]) hmem, ← hp]
  have hDstart : (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      paperGerverContacts 0 3 := by
    have hpm : inner ℝ (paperGerverContacts 0 3)
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = mD (Real.pi / 2) := by
      have h := hDtouch 0 hmemD0
      rwa [zero_add] at h
    have h := edgeVertices_add_pi_fst_eq_of_lt (L := D) (m := mD)
      (a := Real.pi / 2) (b := gerverStageTimes 4 + Real.pi / 2)
      (by linarith only [hl4I.1, h01, h12, h23, h34]) hDleIoo
      (fun q hq ↦ hDle q hq _ ⟨le_rfl, by linarith only [hl4I.1]⟩) (hDmem 0 hmemD0) hpm
      (by simpa only [zero_add] using hmDderiv 0)
    rwa [hcast _ _ (show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring)] at h
  have hBend : (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
      paperGerverContacts (Real.pi / 2) 1 := by
    have h := edgeVertices_add_pi_snd_eq_of_lt (L := B) (m := mB)
      (a := gerverStageTimes 1) (b := Real.pi / 2)
      (by linarith only [h12, h23, h34, h45]) hBleIoo
      (fun q hq ↦ hBle q hq _ ⟨by linarith only [h12, h23, h34, h45], le_rfl⟩)
      (hBmem _ hmemB5) (hBtouch _ hmemB5) (hmBderiv _)
    rwa [hcast _ _ (show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring)] at h
  -- ### Injectivity of the two contact parametrizations
  have hinjD : Set.InjOn (fun t ↦ paperGerverContacts t 3)
      (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) := fun x hx y hy hxy ↦
    hstrictD.injOn hx hy (by
      simpa only using congrArg (fun p : Point ↦ inner ℝ p
        (tangentVector ((gerverStageTimes 4 : ℝ) : Real.Angle))) hxy)
  have hinjB : Set.InjOn (fun t ↦ paperGerverContacts t 1)
      (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := fun x hx y hy hxy ↦
    hstrictB.injOn hx hy (by
      simpa only using congrArg (fun p : Point ↦ inner ℝ p
        (normalVector ((gerverStageTimes 1 : ℝ) : Real.Angle))) hxy)
  -- ### Assembling the twelve conclusions
  have hmemD2' : gerverStageTimes 2 ∈ Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2) :=
    ⟨by linarith only [ht0.le, h02], le_rfl⟩
  have hmemB3' : gerverStageTimes 3 ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) :=
    ⟨le_rfl, by linarith only [ht5.ge, h34, h45]⟩
  have hr1I : gerverStageTimes 1 ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨h01.le, by linarith only [h12, h23, h34, h45]⟩
  have hDinner : paperGerverContacts (gerverStageTimes 2) 3 ∈
      exposedEdge D ((3 * Real.pi / 2 + gerverStageTimes 2 : ℝ) : Real.Angle) := by
    rw [hDface _ hmemD2']
    rfl
  have hBinner : paperGerverContacts (gerverStageTimes 3) 1 ∈
      exposedEdge B ((Real.pi + gerverStageTimes 3 : ℝ) : Real.Angle) := by
    rw [hBface _ hmemB3']
    rfl
  refine ⟨fun t ht ↦ edgeVertices_eq_of_exposedEdge_singleton (hDface t ⟨ht.1, ht.2.le⟩),
    fun t ht ↦ edgeVertices_eq_of_exposedEdge_singleton (hBface t ⟨ht.1.le, ht.2⟩), ?_, ?_,
    edgeVertices_eq_of_exposedEdge_singleton (hDface _ hmemD2'), ?_, ?_, ?_,
    edgeVertices_eq_of_exposedEdge_singleton (hBface _ hmemB3'), ?_, ?_, ?_⟩
  · show capInnerCorner K.val paperGerverConstants.2.2 = _
    rw [hl, hcorner _ hl4I]
    exact gerver_niche_piece_endpoints.2.1.symm
  · show (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 = _
    rw [hl]
    exact hDend
  · refine ⟨by linarith only [ht0.le, h02], (continuous_paperGerverContact 3).continuousOn,
      hinjD, ?_, ?_, ?_⟩
    · show (fun t ↦ paperGerverContacts t 3) ''
        Set.Icc (gerverStageTimes 0) (gerverStageTimes 2) =
        convexBoundaryArc D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)
      rw [hl, convexBoundaryArc]
      refine Set.Subset.antisymm ?_ ?_
      · rintro p ⟨t, ht, rfl⟩
        rcases eq_or_lt_of_le ht.1 with h0 | h0
        · exact Or.inl (Or.inl (by rw [Set.mem_singleton_iff, hDstart, ← h0, ht0]))
        · refine Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨3 * Real.pi / 2 + t,
            ⟨by linarith only [h0, ht0.ge], by linarith only [ht.2, h24]⟩, ?_⟩))
          rw [hDface t ⟨h0, ht.2⟩]
          rfl
      · rintro p ((hp | hp) | hp)
        · rw [Set.mem_singleton_iff, hDstart] at hp
          exact ⟨0, hmemD0, hp.symm⟩
        · obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.1 hp
          rcases le_or_gt (s - 3 * Real.pi / 2) (gerverStageTimes 2) with h | h
          · have hmem : s - 3 * Real.pi / 2 ∈
                Set.Ioc (gerverStageTimes 0) (gerverStageTimes 2) :=
              ⟨by linarith only [hs.1, ht0.le], h⟩
            have hface := hDface (s - 3 * Real.pi / 2) hmem
            rw [hcast _ _ (show 3 * Real.pi / 2 + (s - 3 * Real.pi / 2) = s by ring)] at hface
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨s - 3 * Real.pi / 2, ⟨hmem.1.le, hmem.2⟩, hps.symm⟩
          · have hface := exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo
              (L := D) (a := 3 * Real.pi / 2 + gerverStageTimes 2)
              (b := 3 * Real.pi / 2 + gerverStageTimes 4) (s := s)
              (by linarith only [h45, h02, Real.pi_pos])
              ⟨by linarith only [h], hs.2⟩ hDinner hDouter
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨gerverStageTimes 2, hmemD2, hps.symm⟩
        · rw [Set.mem_singleton_iff, hDend] at hp
          exact ⟨gerverStageTimes 2, hmemD2, hp.symm⟩
    · show paperGerverContacts (gerverStageTimes 0) 3 =
        (edgeVertices D ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
      rw [hDstart, ht0]
    · show paperGerverContacts (gerverStageTimes 2) 3 =
        (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
      rw [hl, hDend]
  · show capInnerCorner K.val paperGerverConstants.2.1 = _
    rw [hr, hcorner _ hr1I]
    exact gerver_niche_piece_endpoints.1.symm
  · show (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 = _
    rw [hr]
    exact hBstart
  · refine ⟨by linarith only [h34, h45, ht5.ge], (continuous_paperGerverContact 1).continuousOn,
      hinjB, ?_, ?_, ?_⟩
    · show (fun t ↦ paperGerverContacts t 1) ''
        Set.Icc (gerverStageTimes 3) (gerverStageTimes 5) =
        convexBoundaryArc B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)
      rw [hr, convexBoundaryArc]
      refine Set.Subset.antisymm ?_ ?_
      · rintro p ⟨t, ht, rfl⟩
        rcases eq_or_lt_of_le ht.2 with hT | hT
        · exact Or.inr (by rw [Set.mem_singleton_iff, hBend, hT, ht5])
        · refine Or.inl (Or.inr (Set.mem_iUnion₂.2 ⟨Real.pi + t,
            ⟨by linarith only [ht.1, h12, h23], by linarith only [hT, ht5.le]⟩, ?_⟩))
          rw [hBface t ⟨ht.1, hT⟩]
          rfl
      · rintro p ((hp | hp) | hp)
        · rw [Set.mem_singleton_iff, hBstart] at hp
          exact ⟨gerverStageTimes 3, hmemB3, hp.symm⟩
        · obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.1 hp
          rcases lt_or_ge (s - Real.pi) (gerverStageTimes 3) with h | h
          · have hface := exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo
              (L := B) (a := Real.pi + gerverStageTimes 1)
              (b := Real.pi + gerverStageTimes 3) (s := s)
              (by linarith only [h34, h45, h01, Real.pi_pos])
              ⟨hs.1, by linarith only [h]⟩ hBouter hBinner
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨gerverStageTimes 3, hmemB3, hps.symm⟩
          · have hmem : s - Real.pi ∈ Set.Ico (gerverStageTimes 3) (gerverStageTimes 5) :=
              ⟨h, by rw [ht5]; linarith only [hs.2]⟩
            have hface := hBface (s - Real.pi) hmem
            rw [hcast _ _ (show Real.pi + (s - Real.pi) = s by ring)] at hface
            rw [hface, Set.mem_singleton_iff] at hps
            exact ⟨s - Real.pi, ⟨hmem.1, hmem.2.le⟩, hps.symm⟩
        · rw [Set.mem_singleton_iff, hBend] at hp
          exact ⟨Real.pi / 2, hmemB5, hp.symm⟩
    · show paperGerverContacts (gerverStageTimes 3) 1 =
        (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
      rw [hr, hBstart]
    · show paperGerverContacts (gerverStageTimes 5) 1 =
        (edgeVertices B ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
      rw [hBend, ht5]
  · intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨ht0 ▸ ht.1, by linarith only [ht.2, h23, h34, h45]⟩
    have hsup : supportValue D ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) =
        -mD (t + Real.pi / 2) := by
      have h := supportValue_add_pi_eq_neg_of_forall_le (L := D)
        (fun q hq ↦ hDle q hq (t + Real.pi / 2)
          ⟨by linarith only [htI.1], by linarith only [ht.2, h23, h34]⟩)
        (hDmem t ht) (hDtouch t ht)
      rwa [hcast _ _ (show t + Real.pi / 2 + Real.pi = 3 * Real.pi / 2 + t by ring)] at h
    rw [hsup, hmDsup t htI, hcast _ _ (show Real.pi / 2 + t = t + Real.pi / 2 by ring)]
    ring
  · intro t ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [ht.1, h01, h12, h23], ht5 ▸ ht.2⟩
    have hsup : supportValue B ((Real.pi + t : ℝ) : Real.Angle) = -mB t := by
      have h := supportValue_add_pi_eq_neg_of_forall_le (L := B)
        (fun q hq ↦ hBle q hq t ⟨by linarith only [ht.1, h12, h23], htI.2⟩)
        (hBmem t ht) (hBtouch t ht)
      rwa [hcast _ _ (show t + Real.pi = Real.pi + t by ring)] at h
    rw [hsup]
    simp only [hmBdef]
    rw [hsupu t htI]
    ring

end MovingSofa
