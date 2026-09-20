import MovingSofa.Cap.Tail.Canonical
import MovingSofa.Cap.Tail.Contacts
import MovingSofa.Geometry.NormalLines
import MovingSofa.Gerver.ParameterIdentification

noncomputable section

namespace MovingSofa

/-- The distinguished inner wall, upper half-plane, fan point and corner on one side. -/
structure DistinguishedCapSide where
  wall : Set Point
  upperHalfPlane : Set Point
  fanPoint : Point
  corner : Point

/-- The right and left cap geometry at the two distinguished Gerver angles. -/
def distinguishedCapSides (K : RightAngleCapSpace) : DistinguishedCapSide × DistinguishedCapSide :=
  let r := paperGerverConstants.2.1
  let l := paperGerverConstants.2.2
  (⟨(rotatingHallwayParts (K.1 : Set Point) (r : Real.Angle)).b,
      (innerWallUpperHalfPlanes K r).1, (wedgeEndpoints K r).1, capInnerCorner K r⟩,
    ⟨(rotatingHallwayParts (K.1 : Set Point) (l : Real.Angle)).d,
      (innerWallUpperHalfPlanes K l).2, (wedgeEndpoints K l).2, capInnerCorner K l⟩)

/-- The right distinguished fan point is the right wedge endpoint at the right Gerver angle. -/
theorem distinguishedCapSides_fst_fanPoint (K : RightAngleCapSpace) :
    (distinguishedCapSides K).1.fanPoint = (wedgeEndpoints K paperGerverConstants.2.1).1 := rfl

/-- The right distinguished corner is the inner corner at the right Gerver angle. -/
theorem distinguishedCapSides_fst_corner (K : RightAngleCapSpace) :
    (distinguishedCapSides K).1.corner = capInnerCorner K paperGerverConstants.2.1 := rfl

/-- The left distinguished fan point is the left wedge endpoint at the left Gerver angle. -/
theorem distinguishedCapSides_snd_fanPoint (K : RightAngleCapSpace) :
    (distinguishedCapSides K).2.fanPoint = (wedgeEndpoints K paperGerverConstants.2.2).2 := rfl

/-- The left distinguished corner is the inner corner at the left Gerver angle. -/
theorem distinguishedCapSides_snd_corner (K : RightAngleCapSpace) :
    (distinguishedCapSides K).2.corner = capInnerCorner K paperGerverConstants.2.2 := rfl

/-- Canonical tails are convex bodies and satisfy all support and endpoint-line identities. -/
theorem canonicalTailSets_properties (K : SpecialCapSpace) :
    (canonicalTailSets K).1.Nonempty ∧ IsCompact (canonicalTailSets K).1 ∧ Convex ℝ (canonicalTailSets K).1 ∧ (canonicalTailSets K).1 ⊆ (K.1.1 : Set Point) ∧
    (canonicalTailSets K).2.Nonempty ∧ IsCompact (canonicalTailSets K).2 ∧ Convex ℝ (canonicalTailSets K).2 ∧ (canonicalTailSets K).2 ⊆ (K.1.1 : Set Point) ∧
    (∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      supportValue K.1.1 (t : Real.Angle) +
        supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) ≤ 1) ∧
    (∀ t ∈ ({paperGerverConstants.2.1, Real.pi / 2} : Set ℝ),
      supportValue K.1.1 (t : Real.Angle) +
        supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) = 1) ∧
    (supportingLineHalfPlane (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∧
    (supportingLineHalfPlane (canonicalTailSets K).1 ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 =
      (distinguishedCapSides K.1).1.wall ∧
    (∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      supportValue K.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤ 1) ∧
    (∀ t ∈ ({0, paperGerverConstants.2.2} : Set ℝ),
      supportValue K.1.1 ((Real.pi / 2 + t : ℝ) : Real.Angle) +
        supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) = 1) ∧
    (supportingLineHalfPlane (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∧
    (supportingLineHalfPlane (canonicalTailSets K).2 ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).1 =
      (distinguishedCapSides K.1).2.wall := by
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  obtain ⟨hr, hl, -⟩ := paperGerverConstants_snd_mem_Ioo
  have htop : supportValue (K.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    K.1.property.2.2.2.1
  -- membership characterizations of the two tails
  have hBmem : ∀ p : Point, p ∈ (canonicalTailSets K).1 ↔
      (p ∈ (K.1.1 : Set Point) ∧ ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
        supportValue (K.1.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ p (normalVector (t : Real.Angle))) := by
    intro p
    simp [canonicalTailSets, innerWallUpperHalfPlanes, normalHalfPlane]
  have hDmem : ∀ p : Point, p ∈ (canonicalTailSets K).2 ↔
      (p ∈ (K.1.1 : Set Point) ∧ ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
        supportValue (K.1.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) := by
    intro p
    simp [canonicalTailSets, innerWallUpperHalfPlanes, normalHalfPlane]
  -- domain properties
  obtain ⟨pR, hpRK, pL, hpLK, hpRy, hpLy, hpRcut, hpLcut⟩ := exists_cap_base_points K.1
  have hpRB : pR ∈ (canonicalTailSets K).1 :=
    (hBmem pR).mpr ⟨hpRK, fun t ht => hpRcut t ⟨le_trans hr.1.le ht.1, ht.2⟩⟩
  have hpLD : pL ∈ (canonicalTailSets K).2 :=
    (hDmem pL).mpr ⟨hpLK, fun t ht => hpLcut t ⟨ht.1, le_trans ht.2 hl.2.le⟩⟩
  have hBne : (canonicalTailSets K).1.Nonempty := ⟨pR, hpRB⟩
  have hDne : (canonicalTailSets K).2.Nonempty := ⟨pL, hpLD⟩
  have hBsub : (canonicalTailSets K).1 ⊆ (K.1.1 : Set Point) := fun p hp => ((hBmem p).mp hp).1
  have hDsub : (canonicalTailSets K).2 ⊆ (K.1.1 : Set Point) := fun p hp => ((hDmem p).mp hp).1
  have hBcomp : IsCompact (canonicalTailSets K).1 :=
    K.1.1.isCompact.inter_right (isClosed_biInter fun t _ => isClosed_normalHalfPlane _ _ true)
  have hDcomp : IsCompact (canonicalTailSets K).2 :=
    K.1.1.isCompact.inter_right (isClosed_biInter fun t _ => isClosed_normalHalfPlane _ _ true)
  have hBconv : Convex ℝ (canonicalTailSets K).1 :=
    K.1.1.convex.inter (convex_iInter fun t => convex_iInter fun _ =>
      convex_normalHalfPlane _ _ true)
  have hDconv : Convex ℝ (canonicalTailSets K).2 :=
    K.1.1.convex.inter (convex_iInter fun t => convex_iInter fun _ =>
      convex_normalHalfPlane _ _ true)
  -- the two support inequalities
  have hBbound : ∀ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      supportValue (canonicalTailSets K).1 ((Real.pi + t : ℝ) : Real.Angle) ≤
        1 - supportValue (K.1.1 : Set Point) (t : Real.Angle) := by
    intro t ht
    have h := supportValue_le_of_cut hBne (a := t) (b := Real.pi + t)
      (hcast _ _ (by ring)) (fun p hp => ((hBmem p).mp hp).2 t ht)
    linarith only [h]
  have hDbound : ∀ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) ≤
        1 - supportValue (K.1.1 : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) := by
    intro t ht
    have hc : ∀ p ∈ (canonicalTailSets K).2,
        supportValue (K.1.1 : Set Point) ((Real.pi / 2 + t : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((Real.pi / 2 + t : ℝ) : Real.Angle)) := by
      intro p hp
      have h := ((hDmem p).mp hp).2 t ht
      rwa [hcast _ _ (show t + Real.pi / 2 = Real.pi / 2 + t by ring)] at h
    have h := supportValue_le_of_cut hDne (a := Real.pi / 2 + t) (b := 3 * Real.pi / 2 + t)
      (hcast _ _ (by ring)) hc
    linarith only [h]
  -- the four endpoint equalities
  have hBzero :
      supportValue (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm ?_ ?_
    · have h := hBbound (Real.pi / 2) ⟨hr.2.le, le_refl _⟩
      rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
      linarith only [h]
    · have h := le_supportValue_of_cut hBcomp (a := Real.pi / 2) (b := 3 * Real.pi / 2)
        (hcast _ _ (by ring)) hpRB hpRy
      linarith only [h]
  have hDzero :
      supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm ?_ ?_
    · have h := hDbound 0 ⟨le_refl _, hl.1.le⟩
      rw [hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring),
        hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring), htop] at h
      linarith only [h]
    · have h := le_supportValue_of_cut hDcomp (a := Real.pi / 2) (b := 3 * Real.pi / 2)
        (hcast _ _ (by ring)) hpLD hpLy
      linarith only [h]
  obtain ⟨pr, hprK, hprline, hprcut⟩ := exists_right_tail_contact K.1 K.property.1 hr
  obtain ⟨pl, hplK, hplline, hplcut⟩ := exists_left_tail_contact K.1 K.property.1 hl
  have hprB : pr ∈ (canonicalTailSets K).1 := (hBmem pr).mpr ⟨hprK, hprcut⟩
  have hplD : pl ∈ (canonicalTailSets K).2 := (hDmem pl).mpr ⟨hplK, hplcut⟩
  have hBeqR : supportValue (canonicalTailSets K).1
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    refine le_antisymm (hBbound _ ⟨le_refl _, hr.2.le⟩) ?_
    have h := le_supportValue_of_cut hBcomp (a := paperGerverConstants.2.1)
      (b := Real.pi + paperGerverConstants.2.1) (hcast _ _ (by ring)) hprB hprline
    linarith only [h]
  have hDeqL : supportValue (canonicalTailSets K).2
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    refine le_antisymm (hDbound _ ⟨hl.1.le, le_refl _⟩) ?_
    rw [hcast _ _ (show paperGerverConstants.2.2 + Real.pi / 2 =
      Real.pi / 2 + paperGerverConstants.2.2 by ring)] at hplline
    have h := le_supportValue_of_cut hDcomp (a := Real.pi / 2 + paperGerverConstants.2.2)
      (b := 3 * Real.pi / 2 + paperGerverConstants.2.2) (hcast _ _ (by ring)) hplD hplline
    linarith only [h]
  -- the distinguished walls
  have hwallR : (distinguishedCapSides K.1).1.wall =
      normalLine ((paperGerverConstants.2.1 : ℝ) : Real.Angle)
        (supportValue (K.1.1 : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) :=
    (rotatingHallwayParts_formulas (K.1.1 : Set Point)
      ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).2.2.2.2.1
  have hwallL : (distinguishedCapSides K.1).2.wall =
      normalLine
        (((paperGerverConstants.2.2 : ℝ) : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle))
        (supportValue (K.1.1 : Set Point)
          (((paperGerverConstants.2.2 : ℝ) : Real.Angle) +
            ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) :=
    (rotatingHallwayParts_formulas (K.1.1 : Set Point)
      ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).2.2.2.2.2.2.1
  have hangL :
      ((paperGerverConstants.2.2 : ℝ) : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
    exact hcast _ _ (by ring)
  refine ⟨hBne, hBcomp, hBconv, hBsub, hDne, hDcomp, hDconv, hDsub,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    linarith only [hBbound t ht]
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · linarith only [hBeqR]
    · rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), hBzero, htop]
      ring
  · show normalLine ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hBzero, normalLine_eq_of_cut (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (hcast _ _ (by ring)), neg_zero]
  · show normalLine ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).1
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)) = _
    rw [hBeqR, normalLine_eq_of_cut (a := paperGerverConstants.2.1)
      (b := Real.pi + paperGerverConstants.2.1) (hcast _ _ (by ring)), hwallR]
    congr 1
    ring
  · intro t ht
    linarith only [hDbound t ht]
  · intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · rw [hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring),
        hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring), hDzero, htop]
      ring
    · linarith only [hDeqL]
  · show normalLine ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).2 ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hDzero, normalLine_eq_of_cut (a := Real.pi / 2) (b := 3 * Real.pi / 2)
      (hcast _ _ (by ring)), neg_zero]
  · show normalLine ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)
      (supportValue (canonicalTailSets K).2
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)) = _
    rw [hDeqL, normalLine_eq_of_cut (a := Real.pi / 2 + paperGerverConstants.2.2)
      (b := 3 * Real.pi / 2 + paperGerverConstants.2.2) (hcast _ _ (by ring)), hwallL, hangL]
    congr 1
    ring

/-- The inner corner's normal support coordinate is the cap's support value less one. -/
theorem inner_capInnerCorner_normalVector (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) (t : Real.Angle) - 1 := by
  have hform := (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1
  show inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
    (normalVector (t : Real.Angle)) = _
  rw [hform, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_normalVector_self, inner_tangentVector_normalVector_real]
  simp

/-- The inner corner's tangent support coordinate is the quarter-turned support value less one. -/
theorem inner_capInnerCorner_tangentVector (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
  have hform := (rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.1
  show inner ℝ (rotatingHallwayParts (K.val : Set Point) (t : Real.Angle)).innerCorner
    (tangentVector (t : Real.Angle)) = _
  rw [hform, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_tangentVector_tangentVector, inner_normalVector_tangentVector,
    ← Real.Angle.coe_add]
  simp

/-- A point whose displacement from the inner corner has negative coordinates in the rotating
frame at time `t` lies in the open inward quadrant at that time. -/
theorem mem_innerQuadrant_of_frame_coordinates_neg (K : RightAngleCapSpace) (t : ℝ) (q : Point)
    (h1 : (q 0 - capInnerCorner K t 0) * Real.cos t +
      (q 1 - capInnerCorner K t 1) * Real.sin t < 0)
    (h2 : -((q 0 - capInnerCorner K t 0) * Real.sin t) +
      (q 1 - capInnerCorner K t 1) * Real.cos t < 0) :
    q ∈ innerQuadrant (K.val : Set Point) t := by
  have e1 : inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue (K.val : Set Point) (t : Real.Angle) - 1 := by
    rw [← inner_capInnerCorner_normalVector K t, inner_normalVector_real,
      inner_normalVector_real]
    linarith only [h1]
  have e2 : inner ℝ q (tangentVector (t : Real.Angle)) <
      supportValue (K.val : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
    rw [← inner_capInnerCorner_tangentVector K t, inner_tangentVector_real,
      inner_tangentVector_real]
    linarith only [h2]
  refine ⟨e1, ?_⟩
  show inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) < _
  rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
  exact e2

end MovingSofa
