import MovingSofa.Cap.Tail.Bodies

/-! # Monotonicity intervals for the distinguished cap sides

`cap_tail_monotonicity_intervals` records that on the right interval
`(φ, π/2]` the inner corner has left the distinguished right half-plane, and
that inside that half-plane the inner quadrant is cut out by the single inner
wall `b(t)`; symmetrically on `[0, π/2 - φ)` for the left side.  Intersecting
with the fan gives the two wedge forms.
-/

noncomputable section

namespace MovingSofa

theorem cap_tail_monotonicity_intervals (K : SpecialCapSpace) :
    (∀ t ∈ Set.Ioc paperGerverConstants.2.1 (Real.pi / 2),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).1.upperHalfPlane ∧
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).1.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) paperGerverConstants.2.2,
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).2.upperHalfPlane ∧
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).2.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).2) ∧
    (∀ t ∈ Set.Ioc paperGerverConstants.2.1 (Real.pi / 2),
      t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ capWedge K.val t =
        ((distinguishedCapSides K.val).1.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val t).1) ∧
    (∀ t ∈ Set.Ico (0 : ℝ) paperGerverConstants.2.2,
      t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ capWedge K.val t =
        ((distinguishedCapSides K.val).2.upperHalfPlane ∩ {p : Point | 0 ≤ p 1}) \
          (innerWallUpperHalfPlanes K.val t).2) := by
  have hpi := Real.pi_pos
  have hφ0 : (0 : ℝ) ≤ GerversSofa.φ := GerversSofa.ABφθSpec.existsUnique.choose_spec.1.1
  have hφ4 : GerversSofa.φ ≤ Real.pi / 4 :=
    le_trans GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.1
      GerversSofa.ABφθSpec.existsUnique.choose_spec.1.2.2.1
  -- frame coordinates of the inner corner path
  have hxu := inner_capInnerCorner_normalVector K.val
  have hxv := inner_capInnerCorner_tangentVector K.val
  -- membership descriptions relative to the moving corner
  have hHb : ∀ (t : ℝ) (p : Point), p ∈ (innerWallUpperHalfPlanes K.val t).1 ↔
      0 ≤ inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) := by
    intro t p
    rw [inner_sub_left, hxu]
    show (supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 ≤
      inner ℝ p (normalVector (t : Real.Angle))) ↔ _
    constructor <;> intro hp <;> linarith
  have hHd : ∀ (t : ℝ) (p : Point), p ∈ (innerWallUpperHalfPlanes K.val t).2 ↔
      0 ≤ inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) := by
    intro t p
    rw [inner_sub_left, hxv]
    show (supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) ↔ _
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
    constructor <;> intro hp <;> linarith
  have hQ : ∀ (t : ℝ) (p : Point), p ∈ innerQuadrant (K.val.val : Set Point) t ↔
      inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) < 0 ∧
        inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) < 0 := by
    intro t p
    rw [inner_sub_left, inner_sub_left, hxu, hxv]
    show (inner ℝ p (normalVector (t : Real.Angle)) <
        supportValue (K.val.val : Set Point) (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        supportValue (K.val.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ↔ _
    rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩
  have hfan : capFan (Real.pi / 2) = {p : Point | 0 ≤ p 1} := by
    ext p
    have hval : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = p 1 := by
      simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
    constructor
    · intro hp
      have := hp.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
      rw [hval] at this
      exact this
    · intro hp
      have hp' : (0 : ℝ) ≤ p 1 := hp
      exact ⟨by change 0 ≤ inner ℝ p _; rw [hval]; exact hp',
        by change 0 ≤ inner ℝ p _; rw [hval]; exact hp'⟩
  have hwedge : ∀ t : ℝ, capWedge K.val t =
      {p : Point | 0 ≤ p 1} ∩ innerQuadrant (K.val.val : Set Point) t := by
    intro t
    have hiq : (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerQuadrant =
        innerQuadrant (K.val.val : Set Point) t := by
      rw [(rotatingHallwayParts_formulas (K.val.val : Set Point)
        (t : Real.Angle)).2.2.2.2.2.2.2.2, innerQuadrant, ← Real.Angle.coe_add]
    show capFan (Real.pi / 2) ∩
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerQuadrant = _
    rw [hfan, hiq]
  -- the injectivity condition: a continuously differentiable corner with strict interior signs
  obtain ⟨-, hcd, hsign⟩ := K.2.1
  set D : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2)) with hDdef
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (D s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs => (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  -- monotone comparison of the corner path against the two distinguished frames
  have hkeyR : ∀ t ∈ Set.Ioc GerversSofa.φ (Real.pi / 2),
      inner ℝ (capInnerCorner K.val t - capInnerCorner K.val GerversSofa.φ)
        (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) < 0 := by
    have hsub : Set.Icc GerversSofa.φ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      Set.Icc_subset_Icc hφ0 le_rfl
    have hanti : StrictAntiOn
        (fun s : ℝ ↦ inner ℝ (capInnerCorner K.val s)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
        (Set.Icc GerversSofa.φ (Real.pi / 2)) := by
      refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
        ((hcont.mono hsub).inner continuousOn_const)
        (f' := fun s ↦ inner ℝ (D s) (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
        ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs ⊢
        have hsub' : Set.Ioo GerversSofa.φ (Real.pi / 2) ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) :=
          fun z hz => ⟨hφ0.trans hz.1.le, hz.2.le⟩
        simpa using
          ((hdw s (hsub' hs)).mono hsub').inner ℝ
            (hasDerivWithinAt_const s _
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)))
      · intro s hs
        rw [interior_Icc] at hs
        obtain ⟨hs1, hs2⟩ := hs
        obtain ⟨hα, hβ⟩ := hsign s ⟨hφ0.trans_lt hs1, hs2⟩
        rw [inner_normalVector_eq_frame_rotate (D s) s GerversSofa.φ]
        have hcos : 0 < Real.cos (s - GerversSofa.φ) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
        have hsin : 0 < Real.sin (s - GerversSofa.φ) :=
          Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
        nlinarith
    intro t ht
    have h := hanti ⟨le_rfl, le_trans hφ4 (by linarith)⟩ ⟨ht.1.le, ht.2⟩ ht.1
    rw [inner_sub_left]
    simpa using h
  have hkeyL : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2 - GerversSofa.φ),
      inner ℝ (capInnerCorner K.val t -
          capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
        (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) < 0 := by
    have hsub : Set.Icc (0 : ℝ) (Real.pi / 2 - GerversSofa.φ) ⊆
        Set.Icc (0 : ℝ) (Real.pi / 2) := Set.Icc_subset_Icc le_rfl (by linarith)
    have hmono : StrictMonoOn
        (fun s : ℝ ↦ inner ℝ (capInnerCorner K.val s)
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
        (Set.Icc (0 : ℝ) (Real.pi / 2 - GerversSofa.φ)) := by
      refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
        ((hcont.mono hsub).inner continuousOn_const)
        (f' := fun s ↦ inner ℝ (D s)
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
        ?_ ?_
      · intro s hs
        rw [interior_Icc] at hs ⊢
        have hsub' : Set.Ioo (0 : ℝ) (Real.pi / 2 - GerversSofa.φ) ⊆
            Set.Icc (0 : ℝ) (Real.pi / 2) := fun z hz => ⟨hz.1.le, by linarith [hz.2]⟩
        simpa using
          ((hdw s (hsub' hs)).mono hsub').inner ℝ
            (hasDerivWithinAt_const s _
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)))
      · intro s hs
        rw [interior_Icc] at hs
        obtain ⟨hs1, hs2⟩ := hs
        obtain ⟨hα, hβ⟩ := hsign s ⟨hs1, by linarith⟩
        rw [inner_tangentVector_eq_frame_rotate (D s) s (Real.pi / 2 - GerversSofa.φ)]
        have hcos : 0 < Real.cos (s - (Real.pi / 2 - GerversSofa.φ)) :=
          Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
        have hsin : Real.sin (s - (Real.pi / 2 - GerversSofa.φ)) < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
        nlinarith
    intro t ht
    have h := hmono ⟨ht.1, ht.2.le⟩ ⟨by linarith, le_rfl⟩ ht.2
    rw [inner_sub_left]
    simpa using h
  -- the right-hand quadrant identity, at all quadrant times
  have partR : ∀ t ∈ Set.Ioc GerversSofa.φ (Real.pi / 2),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).1.upperHalfPlane ∧
      (distinguishedCapSides K.val).1.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).1.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).1 := by
    intro t ht
    have hR := hkeyR t ht
    have hside : (distinguishedCapSides K.val).1.upperHalfPlane =
        (innerWallUpperHalfPlanes K.val GerversSofa.φ).1 := rfl
    have hcos : 0 ≤ Real.cos (t - GerversSofa.φ) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsin : 0 ≤ Real.sin (t - GerversSofa.φ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
    rw [hside]
    constructor
    · intro hmem
      exact absurd ((hHb _ _).mp hmem) (not_le.mpr hR)
    refine Set.Subset.antisymm ?_ ?_
    · rintro p ⟨hA, hQp⟩
      refine ⟨hA, ?_⟩
      rw [hHb t p]
      exact not_le.mpr ((hQ t p).mp hQp).1
    · rintro p ⟨hA, hH⟩
      refine ⟨hA, ?_⟩
      rw [hQ t p]
      have ha : inner ℝ (p - capInnerCorner K.val t) (normalVector (t : Real.Angle)) < 0 :=
        not_le.mp fun h => hH ((hHb t p).mpr h)
      refine ⟨ha, ?_⟩
      by_contra hb
      rw [not_lt] at hb
      have hAmem : 0 ≤ inner ℝ (p - capInnerCorner K.val GerversSofa.φ)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) := (hHb _ p).mp hA
      have hsplit : inner ℝ (p - capInnerCorner K.val GerversSofa.φ)
            (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) =
          inner ℝ (p - capInnerCorner K.val t)
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) +
            inner ℝ (capInnerCorner K.val t - capInnerCorner K.val GerversSofa.φ)
              (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) := by
        rw [← inner_add_left]
        congr 1
        abel
      have hle : inner ℝ (p - capInnerCorner K.val t)
          (normalVector ((GerversSofa.φ : ℝ) : Real.Angle)) ≤ 0 := by
        rw [inner_normalVector_eq_frame_rotate (p - capInnerCorner K.val t) t GerversSofa.φ]
        linarith [mul_nonneg hb hsin, mul_nonneg (neg_nonneg.mpr ha.le) hcos]
      linarith
  -- the left-hand quadrant identity, at all quadrant times
  have partL : ∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2 - GerversSofa.φ),
      capInnerCorner K.val t ∉ (distinguishedCapSides K.val).2.upperHalfPlane ∧
      (distinguishedCapSides K.val).2.upperHalfPlane ∩ innerQuadrant K.val.val t =
        (distinguishedCapSides K.val).2.upperHalfPlane \
          (innerWallUpperHalfPlanes K.val t).2 := by
    intro t ht
    have hL := hkeyL t ht
    have hside : (distinguishedCapSides K.val).2.upperHalfPlane =
        (innerWallUpperHalfPlanes K.val (Real.pi / 2 - GerversSofa.φ)).2 := rfl
    have hcos : 0 ≤ Real.cos (t - (Real.pi / 2 - GerversSofa.φ)) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hsin : Real.sin (t - (Real.pi / 2 - GerversSofa.φ)) ≤ 0 := by
      have hpos : 0 ≤ Real.sin (Real.pi / 2 - GerversSofa.φ - t) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.2]) (by linarith [ht.1])
      rw [show t - (Real.pi / 2 - GerversSofa.φ) =
        -(Real.pi / 2 - GerversSofa.φ - t) by ring, Real.sin_neg]
      linarith
    rw [hside]
    constructor
    · intro hmem
      exact absurd ((hHd _ _).mp hmem) (not_le.mpr hL)
    refine Set.Subset.antisymm ?_ ?_
    · rintro p ⟨hA, hQp⟩
      refine ⟨hA, ?_⟩
      rw [hHd t p]
      exact not_le.mpr ((hQ t p).mp hQp).2
    · rintro p ⟨hA, hH⟩
      refine ⟨hA, ?_⟩
      rw [hQ t p]
      have hb : inner ℝ (p - capInnerCorner K.val t) (tangentVector (t : Real.Angle)) < 0 :=
        not_le.mp fun h => hH ((hHd t p).mpr h)
      refine ⟨?_, hb⟩
      by_contra ha
      rw [not_lt] at ha
      have hAmem : 0 ≤ inner ℝ
          (p - capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) := (hHd _ p).mp hA
      have hsplit : inner ℝ (p - capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
            (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) =
          inner ℝ (p - capInnerCorner K.val t)
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) +
            inner ℝ (capInnerCorner K.val t -
                capInnerCorner K.val (Real.pi / 2 - GerversSofa.φ))
              (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) := by
        rw [← inner_add_left]
        congr 1
        abel
      have hle : inner ℝ (p - capInnerCorner K.val t)
          (tangentVector ((Real.pi / 2 - GerversSofa.φ : ℝ) : Real.Angle)) ≤ 0 := by
        rw [inner_tangentVector_eq_frame_rotate (p - capInnerCorner K.val t) t
          (Real.pi / 2 - GerversSofa.φ)]
        linarith [mul_nonneg ha (neg_nonneg.mpr hsin),
          mul_nonneg (neg_nonneg.mpr hb.le) hcos]
      linarith
  -- the wedge identities are the quadrant identities intersected with the fan
  refine ⟨partR, partL, ?_, ?_⟩
  · intro t ht _
    rw [hwedge t, Set.inter_left_comm, (partR t ht).2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto
  · intro t ht _
    rw [hwedge t, Set.inter_left_comm, (partL t ht).2]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    tauto

/-- On any subinterval of `[0, π/2]` the inner corner of a special cap has strictly decreasing
horizontal coordinate: the injectivity condition makes its horizontal derivative negative. -/
theorem strictAntiOn_capInnerCorner_fst (K : SpecialCapSpace) {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) :
    StrictAntiOn (fun t ↦ capInnerCorner K.val t 0) (Set.Icc a b) := by
  obtain ⟨-, hcd, hsign⟩ := K.property.1
  set Dv : ℝ → Point := derivWithin (capInnerCorner K.val) (Set.Icc 0 (Real.pi / 2))
  have hIccsub : Set.Icc a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1, le_trans ht.2 hb⟩
  have hIoosub : Set.Ioo a b ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := fun t ht ↦
    ⟨le_trans ha ht.1.le, le_trans ht.2.le hb⟩
  have hdw : ∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K.val) (Dv s) (Set.Icc (0 : ℝ) (Real.pi / 2)) s :=
    fun s hs ↦ (hcd.differentiableOn_one s hs).hasDerivWithinAt
  have hcont : ContinuousOn (capInnerCorner K.val) (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    hcd.continuousOn
  have hinner0 : ∀ p : Point, inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) = p 0 := by
    intro p
    rw [inner_normalVector_real]
    simp
  have hmono0 : StrictAntiOn
      (fun t ↦ inner ℝ (capInnerCorner K.val t) (normalVector ((0 : ℝ) : Real.Angle)))
      (Set.Icc a b) := by
    refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      ((hcont.mono hIccsub).inner continuousOn_const)
      (f' := fun s ↦ inner ℝ (Dv s) (normalVector ((0 : ℝ) : Real.Angle))) ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs ⊢
      simpa using ((hdw s (hIoosub hs)).mono hIoosub).inner ℝ
        (hasDerivWithinAt_const s _ (normalVector ((0 : ℝ) : Real.Angle)))
    · intro s hs
      rw [interior_Icc] at hs
      obtain ⟨hα, hβ⟩ := hsign s ⟨lt_of_le_of_lt ha hs.1, lt_of_lt_of_le hs.2 hb⟩
      rw [inner_normalVector_eq_frame_rotate (Dv s) s 0]
      have hcos : 0 < Real.cos (s - 0) := by
        rw [sub_zero]
        exact Real.cos_pos_of_mem_Ioo ⟨by linarith only [Real.pi_pos, hs.1, ha],
          by linarith only [hs.2, hb]⟩
      have hsin : 0 < Real.sin (s - 0) := by
        rw [sub_zero]
        exact Real.sin_pos_of_pos_of_lt_pi (lt_of_le_of_lt ha hs.1)
          (by linarith only [hs.2, hb, Real.pi_pos])
      have h1 : inner ℝ (Dv s) (normalVector (s : Real.Angle)) * Real.cos (s - 0) < 0 :=
        mul_neg_of_neg_of_pos hα hcos
      have h2 : 0 < inner ℝ (Dv s) (tangentVector (s : Real.Angle)) * Real.sin (s - 0) :=
        mul_pos hβ hsin
      linarith only [h1, h2]
  intro u hu w hw huw
  simpa only [hinner0] using hmono0 hu hw huw

end MovingSofa
