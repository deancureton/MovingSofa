import MovingSofa.Geometry.HallwayParts

noncomputable section

namespace MovingSofa

/-- A supporting hallway lies in its outer quadrant. -/
theorem supportingHallway_subset_outerQuadrant (s : Set Point) (t : Real.Angle) :
    supportingHallway s t ⊆ (rotatingHallwayParts s t).outerQuadrant := by
  change supportingPlacement s t '' hallway ⊆
    supportingPlacement s t '' hallwayParts.outerQuadrant
  apply Set.image_mono
  rw [hallway_eq_outerQuadrant_sdiff_innerQuadrant]
  exact Set.sdiff_subset

theorem rotatingHallwayParts_formulas (s : Set Point) (t : Real.Angle) :
    supportingHallway s t = (rotatingHallwayParts s t).outerQuadrant \ (rotatingHallwayParts s t).innerQuadrant ∧
    (rotatingHallwayParts s t).innerCorner = (supportValue s t - 1) • normalVector t + (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t ∧
    (rotatingHallwayParts s t).outerCorner = supportValue s t • normalVector t + supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) • tangentVector t ∧
    (rotatingHallwayParts s t).a = normalLine t (supportValue s t) ∧
    (rotatingHallwayParts s t).b = normalLine t (supportValue s t - 1) ∧
    (rotatingHallwayParts s t).c = normalLine (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle))) ∧
    (rotatingHallwayParts s t).d = normalLine (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) ∧
    (rotatingHallwayParts s t).outerQuadrant =
      normalHalfPlane t (supportValue s t) false false ∩
        normalHalfPlane (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle))) false false ∧
    (rotatingHallwayParts s t).innerQuadrant =
      normalHalfPlane t (supportValue s t - 1) false true ∩
        normalHalfPlane (t + ((Real.pi / 2 : ℝ) : Real.Angle)) (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) false true := by
  have hinj : Function.Injective (supportingPlacement s t) := by
    intro p q h
    apply (EuclideanGeometry.o.rotation t).injective
    simpa only [supportingPlacement, rotationMap, add_left_inj] using h
  have hsurj : Function.Surjective (supportingPlacement s t) := by
    intro q
    obtain ⟨p, hp⟩ := (EuclideanGeometry.o.rotation t).surjective
      (q - (supportValue s t - 1) • normalVector t -
        (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
    refine ⟨p, ?_⟩
    simp only [supportingPlacement, rotationMap, hp]
    abel
  have himage (A B : Set Point)
      (h : ∀ p, p ∈ A ↔ supportingPlacement s t p ∈ B) :
      supportingPlacement s t '' A = B := by
    apply (Set.preimage_eq_preimage hsurj).mp
    rw [Set.preimage_image_eq A hinj]
    exact Set.ext h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Set.preimage_eq_preimage hsurj).mp
    change supportingPlacement s t ⁻¹' (supportingPlacement s t '' hallway) =
      supportingPlacement s t ⁻¹' (supportingPlacement s t '' hallwayParts.outerQuadrant \
        supportingPlacement s t '' hallwayParts.innerQuadrant)
    rw [Set.preimage_sdiff, Set.preimage_image_eq _ hinj,
      Set.preimage_image_eq _ hinj, Set.preimage_image_eq _ hinj]
    exact hallway_eq_outerQuadrant_sdiff_innerQuadrant
  · simp [rotatingHallwayParts, supportingPlacement, hallwayParts, rotationMap]
  · simp only [rotatingHallwayParts, supportingPlacement, hallwayParts,
      rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
    ext i
    fin_cases i <;> simp [normalVector, tangentVector, frame] <;> ring
  · apply himage
    intro p
    change p 0 = 1 ↔ inner ℝ (supportingPlacement s t p) (normalVector t) = _
    rw [inner_supportingPlacement_normalVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 0 = 0 ↔ inner ℝ (supportingPlacement s t p) (normalVector t) = _
    rw [inner_supportingPlacement_normalVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 1 = 1 ↔ inner ℝ (supportingPlacement s t p)
      (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) = _
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change p 1 = 0 ↔ inner ℝ (supportingPlacement s t p)
      (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) = _
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    constructor <;> intro h <;> linarith
  · apply himage
    intro p
    change (p 0 ≤ 1 ∧ p 1 ≤ 1) ↔
      (inner ℝ (supportingPlacement s t p) (normalVector t) ≤ _) ∧
      (inner ℝ (supportingPlacement s t p)
        (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) ≤ _)
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_normalVector,
      inner_supportingPlacement_tangentVector]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  · apply himage
    intro p
    change (p 0 < 0 ∧ p 1 < 0) ↔
      (inner ℝ (supportingPlacement s t p) (normalVector t) < _) ∧
      (inner ℝ (supportingPlacement s t p)
        (normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle))) < _)
    rw [normalVector_add_pi_div_two, inner_supportingPlacement_normalVector,
      inner_supportingPlacement_tangentVector]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith

end MovingSofa
