import MovingSofa.Geometry.Hallway

noncomputable section

namespace MovingSofa

theorem rightAngleRotation_apply (p : Point) :
    EuclideanGeometry.o.rightAngleRotation p = !₂[-p 1, p 0] := by
  apply (ext_inner_left (𝕜 := ℝ))
  intro y
  rw [Orientation.inner_rightAngleRotation_right, Orientation.areaForm_to_volumeForm,
    EuclideanGeometry.o.volumeForm_robust (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply]
  simp [Matrix.det_fin_two, Module.Basis.toMatrix, PiLp.inner_apply]
  ring

theorem inner_rotationMap_normalVector (p : Point) (t : Real.Angle) :
    inner ℝ (rotationMap t p) (normalVector t) = p 0 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp [normalVector, frame, PiLp.inner_apply]
  linear_combination p 0 * Real.Angle.cos_sq_add_sin_sq t

theorem inner_rotationMap_tangentVector (p : Point) (t : Real.Angle) :
    inner ℝ (rotationMap t p) (tangentVector t) = p 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp [tangentVector, frame, PiLp.inner_apply]
  linear_combination p 1 * Real.Angle.cos_sq_add_sin_sq t

theorem normalVector_add_pi_div_two (t : Real.Angle) :
    normalVector (t + ((Real.pi / 2 : ℝ) : Real.Angle)) = tangentVector t := by
  simp [normalVector, tangentVector, frame, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two]

/-- Rotating a real normal direction by a right angle gives the tangent direction. -/
theorem normalVector_add_pi_div_two_real (t : ℝ) :
    normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) = tangentVector (t : Real.Angle) := by
  rw [Real.Angle.coe_add, normalVector_add_pi_div_two]

theorem inner_supportingPlacement_normalVector (s : Set Point) (t : Real.Angle)
    (p : Point) :
    inner ℝ (supportingPlacement s t p) (normalVector t) =
      p 0 + supportValue s t - 1 := by
  simp only [supportingPlacement, inner_add_left, real_inner_smul_left,
    inner_rotationMap_normalVector]
  simp [normalVector, tangentVector, frame, PiLp.inner_apply,
    PiLp.norm_sq_eq_of_L2, Real.Angle.cos_sq_add_sin_sq]
  ring

theorem inner_supportingPlacement_tangentVector (s : Set Point) (t : Real.Angle)
    (p : Point) :
    inner ℝ (supportingPlacement s t p) (tangentVector t) =
      p 1 + supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1 := by
  simp only [supportingPlacement, inner_add_left, real_inner_smul_left,
    inner_rotationMap_tangentVector]
  simp [normalVector, tangentVector, frame, PiLp.inner_apply,
    PiLp.norm_sq_eq_of_L2, Real.Angle.cos_sq_add_sin_sq, add_comm]
  ring

theorem hallway_eq_outerQuadrant_sdiff_innerQuadrant :
    hallway = hallwayParts.outerQuadrant \ hallwayParts.innerQuadrant := by
  ext p
  constructor
  · rintro (⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩)
    · change (a ≤ 1 ∧ b ≤ 1) ∧ ¬(a < 0 ∧ b < 0)
      exact ⟨⟨h.1, h.2.2⟩, fun hn ↦ (not_lt_of_ge h.2.1) hn.2⟩
    · change (a ≤ 1 ∧ b ≤ 1) ∧ ¬(a < 0 ∧ b < 0)
      exact ⟨⟨h.2.1, h.2.2⟩, fun hn ↦ (not_lt_of_ge h.1) hn.1⟩
  · intro hp
    change (p 0 ≤ 1 ∧ p 1 ≤ 1) ∧ ¬(p 0 < 0 ∧ p 1 < 0) at hp
    have heq : (!₂[p 0, p 1] : Point) = p := by
      ext i
      fin_cases i <;> rfl
    by_cases h : 0 ≤ p 0
    · exact Or.inr ⟨p 0, p 1, ⟨h, hp.1.1, hp.1.2⟩, heq⟩
    · exact Or.inl ⟨p 0, p 1,
        ⟨hp.1.1, le_of_not_gt (fun hy ↦ hp.2 ⟨lt_of_not_ge h, hy⟩), hp.1.2⟩, heq⟩


/-- The first coordinate of a rotated point. -/
theorem rotationMap_apply_zero (θ : Real.Angle) (x : Point) :
    rotationMap θ x 0 = θ.cos * x 0 - θ.sin * x 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp
  ring

/-- The second coordinate of a rotated point. -/
theorem rotationMap_apply_one (θ : Real.Angle) (x : Point) :
    rotationMap θ x 1 = θ.sin * x 0 + θ.cos * x 1 := by
  rw [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply]
  simp
  ring

/-- Coordinate bounds for a point of the horizontal side of the hallway. -/
theorem mem_horizontalHallway_coordinates {p : Point} (hp : p ∈ horizontalHallway) :
    p 0 ≤ 1 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 := by
  obtain ⟨x, y, h, rfl⟩ := hp
  simpa using h

/-- Coordinate bounds for a point of the vertical side of the hallway. -/
theorem mem_verticalHallway_coordinates {p : Point} (hp : p ∈ verticalHallway) :
    0 ≤ p 0 ∧ p 0 ≤ 1 ∧ p 1 ≤ 1 := by
  obtain ⟨x, y, h, rfl⟩ := hp
  simpa using h

/-- A point lies in the hallway exactly when it lies in the outer quadrant and is not
strictly inside the inner one. -/
theorem mem_hallway_iff (q : Point) : q ∈ hallway ↔
    (q 0 ≤ 1 ∧ q 1 ≤ 1) ∧ (0 ≤ q 0 ∨ 0 ≤ q 1) := by
  constructor
  · rintro (⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩)
    · exact ⟨⟨h.1, h.2.2⟩, Or.inr h.2.1⟩
    · exact ⟨⟨h.2.1, h.2.2⟩, Or.inl h.1⟩
  · rintro ⟨⟨hx, hy⟩, h⟩
    have heq : (!₂[q 0, q 1] : Point) = q := by
      ext i
      fin_cases i <;> rfl
    rcases h with hx0 | hy0
    · exact Or.inr ⟨q 0, q 1, ⟨hx0, hx, hy⟩, heq⟩
    · exact Or.inl ⟨q 0, q 1, ⟨hx, hy0, hy⟩, heq⟩

/-- Coordinate bounds place a point in the horizontal side of the hallway. -/
theorem mem_horizontalHallway_of_coordinates (p : Point)
    (hx : p 0 ≤ 1) (hy : p 1 ∈ Set.Icc (0 : ℝ) 1) : p ∈ horizontalHallway := by
  refine ⟨p 0, p 1, ⟨hx, hy⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

/-- Coordinate bounds place a point in the vertical side of the hallway. -/
theorem mem_verticalHallway_of_coordinates (p : Point)
    (hx : p 0 ∈ Set.Icc (0 : ℝ) 1) (hy : p 1 ≤ 1) : p ∈ verticalHallway := by
  refine ⟨p 0, p 1, ⟨hx.1, hx.2, hy⟩, ?_⟩
  ext i
  fin_cases i <;> rfl

end MovingSofa
