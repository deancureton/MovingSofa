import MovingSofa.Analysis.SurfaceMeasure.Linearity
import MovingSofa.Cap.DensityExistence

/-!
# Minkowski interpolation of right-angle caps

The cap conditions of `IsCap (π / 2)` and the injectivity condition of
`SatisfiesInjectivityCondition` are preserved by the Minkowski interpolation
`convexBodyCombination t K L = (1 - t) • K + t • L` of two right-angle caps.  Each statement
about the interpolation is phrased for an arbitrary cap whose underlying convex body is that
interpolation, so that it applies both to the cap produced by `isCap_convexBodyCombination`
and to an interpolated cap obtained by choice.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Pointwise unitInterval

namespace MovingSofa

/-- Lowering a point of an interpolated right-angle cap onto the base line keeps it inside,
because the same projection can be applied to both summands. -/
theorem base_projection_mem_convexBodyCombination (t : I) (K L : CapSpace (Real.pi / 2))
    {q : Point} (hq : q ∈ (convexBodyCombination t K.val L.val : Set Point)) :
    q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈
      (convexBodyCombination t K.val L.val : Set Point) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_convexBodyCombination_iff t K.val L.val q).1 hq
  refine (mem_convexBodyCombination_iff t K.val L.val _).2
    ⟨_, K.base_projection_mem ha, _, L.base_projection_mem hb, ?_⟩
  have hcoord : ((1 - (t : ℝ)) • a + (t : ℝ) • b) 1 =
      (1 - (t : ℝ)) * a 1 + (t : ℝ) * b 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hcoord]
  module

/-- Right-angle caps are closed under Minkowski interpolation. -/
theorem isCap_convexBodyCombination (t : I) (K L : RightAngleCapSpace) :
    IsCap (Real.pi / 2) (convexBodyCombination t K.val L.val) := by
  have hsup := supportValue_convexBodyCombination t K.val L.val
  have hbase : supportValue (convexBodyCombination t K.val L.val)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    rw [hsup, K.property.2.2.2.2.2.1, L.property.2.2.2.2.2.1]; ring
  refine ⟨by positivity, le_rfl, ?_, ?_, ?_, hbase,
    hasHalfPlaneRepresentation_of_base_projection _ hbase
      (fun q hq ↦ base_projection_mem_convexBodyCombination t K L hq)⟩
  · rw [hsup, K.property.2.2.1, L.property.2.2.1]; ring
  · rw [hsup, K.property.2.2.2.1, L.property.2.2.2.1]; ring
  · rw [hsup, K.property.2.2.2.2.1, L.property.2.2.2.2.1]; ring

/-- An interpolated right-angle cap carries the interpolated surface densities: its surface
measure is the interpolation of the two surface measures, and pushing a weighted measure
forward is linear in the weight. -/
theorem hasCapDensities_of_eq_convexBodyCombination {t : I} {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val)
    {r₁ s₁ r₂ s₂ : ℝ → ℝ≥0} (hK : HasCapDensities K r₁ s₁) (hL : HasCapDensities L r₂ s₂) :
    HasCapDensities M (fun x ↦ (1 - (t : ℝ)).toNNReal * r₁ x + (t : ℝ).toNNReal * r₂ x)
      (fun x ↦ (1 - (t : ℝ)).toNNReal * s₁ x + (t : ℝ).toNNReal * s₂ x) := by
  have hmeasure : surfaceAreaMeasure M.val =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K.val +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L.val := by
    rw [hM]; exact surfaceAreaMeasure_convexBodyCombination t K.val L.val
  refine ⟨(measurable_const.mul hK.1).add (measurable_const.mul hL.1),
    (measurable_const.mul hK.2.1).add (measurable_const.mul hL.2.1), ?_, ?_⟩
  · rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hK.2.2.1, hL.2.2.1]
    exact (Measure.map_withDensity_eq_smul_add_smul _ Real.Angle.continuous_coe.measurable _ _
      hK.1.coe_nnreal_ennreal hL.1.coe_nnreal_ennreal (fun x ↦ by simp [ENNReal.ofReal])).symm
  · rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hK.2.2.2, hL.2.2.2]
    exact (Measure.map_withDensity_eq_smul_add_smul _
      (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable _ _
      hK.2.1.coe_nnreal_ennreal hL.2.1.coe_nnreal_ennreal
      (fun x ↦ by simp [ENNReal.ofReal])).symm

/-- The inner corner of an interpolated cap is the interpolation of the two inner corners. -/
theorem capInnerCorner_of_eq_convexBodyCombination {t : I} {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val) (x : ℝ) :
    capInnerCorner M x =
      (1 - (t : ℝ)) • capInnerCorner K x + (t : ℝ) • capInnerCorner L x := by
  simp only [capInnerCorner, (rotatingHallwayParts_formulas _ _).2.1, hM,
    supportValue_convexBodyCombination]
  module

/-- The injectivity condition is inherited by Minkowski interpolations of right-angle caps: the
inner corner interpolates, so its two frame velocity components are the same combinations of
the original ones, and a combination with nonnegative weights summing to one preserves their
strict signs even at the two degenerate weights. -/
theorem satisfiesInjectivityCondition_of_eq_convexBodyCombination {t : I}
    {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val)
    (hK : SatisfiesInjectivityCondition K) (hL : SatisfiesInjectivityCondition L) :
    SatisfiesInjectivityCondition M := by
  obtain ⟨⟨r₁, s₁, hd₁, -⟩, hC₁, hsign₁⟩ := hK
  obtain ⟨⟨r₂, s₂, hd₂, -⟩, hC₂, hsign₂⟩ := hL
  have hcornerfun : capInnerCorner M =
      fun x ↦ (1 - (t : ℝ)) • capInnerCorner K x + (t : ℝ) • capInnerCorner L x :=
    funext (capInnerCorner_of_eq_convexBodyCombination hM)
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  -- A combination of two negative quantities with weights summing to one is negative.
  have hneg : ∀ a b : ℝ, a < 0 → b < 0 → (1 - (t : ℝ)) * a + (t : ℝ) * b < 0 := by
    intro a b ha hb
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h]; simpa using ha
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht1 ha.le, mul_neg_of_pos_of_neg h hb]
  have hpos : ∀ a b : ℝ, 0 < a → 0 < b → 0 < (1 - (t : ℝ)) * a + (t : ℝ) * b := by
    intro a b ha hb
    have := hneg (-a) (-b) (by linarith) (by linarith)
    linarith
  -- Density uniqueness needs no proof here: it holds for every right-angle cap.
  have hdens := hasCapDensities_of_eq_convexBodyCombination hM hd₁ hd₂
  refine ⟨⟨_, _, hdens, fun _ _ h' ↦ hdens.ae_eq h'⟩, ?_, ?_⟩
  · rw [hcornerfun]
    exact (hC₁.const_smul _).add (hC₂.const_smul _)
  · intro x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx.1.le, hx.2.le⟩
    have hdK := ((hC₁.differentiableOn one_ne_zero) x hxmem).hasDerivWithinAt
    have hdL := ((hC₂.differentiableOn one_ne_zero) x hxmem).hasDerivWithinAt
    have hdM : HasDerivWithinAt (capInnerCorner M)
        ((1 - (t : ℝ)) • derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) x +
          (t : ℝ) • derivWithin (capInnerCorner L) (Set.Icc 0 (Real.pi / 2)) x)
        (Set.Icc 0 (Real.pi / 2)) x := by
      rw [hcornerfun]
      exact (hdK.const_smul (1 - (t : ℝ))).add (hdL.const_smul (t : ℝ))
    rw [hdM.derivWithin (uniqueDiffOn_Icc hpi x hxmem), inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    exact ⟨hneg _ _ (hsign₁ x hx).1 (hsign₂ x hx).1,
      hpos _ _ (hsign₁ x hx).2 (hsign₂ x hx).2⟩

end MovingSofa
