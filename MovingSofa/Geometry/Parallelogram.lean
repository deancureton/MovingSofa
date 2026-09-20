import MovingSofa.Geometry.HallwayParts

noncomputable section

namespace MovingSofa

/-- The strip intersection is described by its vertical and rotated coordinates. -/
theorem mem_stripParallelogram_iff (ω : ℝ) (p : Point) :
    p ∈ (stripParallelogram ω).1 ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
        inner ℝ p (normalVector (ω : Real.Angle)) ≤ 1) := by
  change ((0 ≤ p 1 ∧ p 1 ≤ 1) ∧
    p ∈ rotationMap (ω : Real.Angle) '' {q : Point | 0 ≤ q 0 ∧ q 0 ≤ 1}) ↔ _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [inner_rotationMap_normalVector, Set.mem_ofPred_eq] using hq
  · intro hp
    obtain ⟨q, rfl⟩ := (EuclideanGeometry.o.rotation (ω : Real.Angle)).surjective p
    change 0 ≤ inner ℝ (rotationMap (ω : Real.Angle) q)
        (normalVector (ω : Real.Angle)) ∧
      inner ℝ (rotationMap (ω : Real.Angle) q) (normalVector (ω : Real.Angle)) ≤ 1 at hp
    exact ⟨q, by
      simpa only [inner_rotationMap_normalVector, Set.mem_ofPred_eq] using hp, rfl⟩

/-- Projection on the downward unit normal negates the vertical coordinate. -/
theorem inner_normalVector_three_pi_div_two (p : Point) :
    inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = -p 1 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add]

/-- The horizontal coordinate is the projection on the normal at angle zero. -/
theorem inner_normalVector_zero (p : Point) :
    inner ℝ p (normalVector ((0 : ℝ) : Real.Angle)) = p 0 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The vertical coordinate is the projection on the tangent at angle zero. -/
theorem inner_tangentVector_zero (p : Point) :
    inner ℝ p (tangentVector ((0 : ℝ) : Real.Angle)) = p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The vertical coordinate is the projection on the upward unit normal. -/
theorem inner_normalVector_pi_div_two (p : Point) :
    inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = p 1 := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- Projection on the leftward tangent at a right angle negates the horizontal coordinate. -/
theorem inner_tangentVector_pi_div_two (p : Point) :
    inner ℝ p (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) = -p 0 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- Projection on the leftward tangent at the straight angle negates the vertical coordinate. -/
theorem inner_tangentVector_pi (p : Point) :
    inner ℝ p (tangentVector ((Real.pi : ℝ) : Real.Angle)) = -p 1 := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

/-- The projection of a multiple of the horizontal normal on another unit normal. -/
theorem inner_smul_normalVector_zero (x t : ℝ) :
    inner ℝ (x • normalVector (0 : Real.Angle)) (normalVector (t : Real.Angle)) =
      x * Real.cos t := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The horizontal bottom of the strip intersection has zero downward support. -/
theorem supportValue_stripParallelogram_bottom (ω : ℝ) :
    supportValue (stripParallelogram ω).1 ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
  have hzero : (0 : Point) ∈ (stripParallelogram ω).1 := by
    rw [mem_stripParallelogram_iff]
    simp
  have hbound : ∀ y ∈ (fun p ↦ inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle))) ''
      (stripParallelogram ω).1, y ≤ 0 := by
    rintro y ⟨p, hp, rfl⟩
    dsimp only
    rw [inner_normalVector_three_pi_div_two]
    exact neg_nonpos.mpr ((mem_stripParallelogram_iff ω p).1 hp).1.1
  have hmem : (0 : ℝ) ∈ (fun p ↦ inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle))) ''
      (stripParallelogram ω).1 := ⟨0, hzero, by simp⟩
  exact le_antisymm (csSup_le ⟨0, hmem⟩ hbound) (le_csSup ⟨0, hbound⟩ hmem)

end MovingSofa
