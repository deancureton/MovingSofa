import MovingSofa.Polygon.Nef.Variation

noncomputable section
namespace MovingSofa

private def PlanarHalfPlaneData.reverseOrientation
    (H : PlanarHalfPlaneData) : PlanarHalfPlaneData :=
  ⟨H.angle + ((Real.pi : ℝ) : Real.Angle), -H.height, !H.upper, H.strict⟩

private theorem PlanarHalfPlaneData.carrier_reverseOrientation (H : PlanarHalfPlaneData) :
    H.reverseOrientation.carrier = H.carrier := by
  ext p
  simp only [reverseOrientation, carrier, normalHalfPlane, Set.mem_ofPred_eq,
    normalVector_add_pi_angle, inner_neg_right]
  cases H.upper <;> cases H.strict <;> simp

private theorem PlanarHalfPlaneData.boundaryLine_reverseOrientation (H : PlanarHalfPlaneData) :
    H.reverseOrientation.boundaryLine = H.boundaryLine := by
  ext p
  simp [reverseOrientation, boundaryLine, normalLine, normalVector_add_pi_angle]

private theorem PlanarHalfPlaneData.carrier_reverseOrientation_add_height
    (H : PlanarHalfPlaneData) (δ : ℝ) :
    ({H.reverseOrientation with height := H.reverseOrientation.height + δ}).carrier =
      ({H with height := H.height + -δ}).carrier := by
  have heq : {H.reverseOrientation with height := H.reverseOrientation.height + δ} =
      ({H with height := H.height + -δ}).reverseOrientation := by
    cases H
    simp [reverseOrientation, add_comm]
  rw [heq, carrier_reverseOrientation]

private theorem perturbNefHeight_reverseOrientation {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (δ : ℝ) :
    perturbNefHeight E (fun j ↦ (H j).reverseOrientation) i δ =
      perturbNefHeight E H i (-δ) := by
  unfold perturbNefHeight
  congr 1
  funext j
  split_ifs
  · exact PlanarHalfPlaneData.carrier_reverseOrientation_add_height _ _
  · exact PlanarHalfPlaneData.carrier_reverseOrientation _

/-- Quadratic area variation when the moved half-plane is a lower constraint. -/
theorem simpleNefPolygon_area_variation_lower {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (hSide : (H i).upper = true) (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) +
          (MeasureTheory.Measure.hausdorffMeasure 1
            (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  have hLines' : Function.Injective (fun j ↦ (H j).reverseOrientation.boundaryLine) := by
    simpa only [PlanarHalfPlaneData.boundaryLine_reverseOrientation] using hLines
  have hSide' : (H i).reverseOrientation.upper = false := by
    simp [PlanarHalfPlaneData.reverseOrientation, hSide]
  obtain ⟨C, ε, hC, hε, hε₀', h⟩ := simpleNefPolygon_area_variation E
    (fun j ↦ (H j).reverseOrientation) i hE hLines' hSide' R ε₀ hR hε₀ (by
      intro δ hδ
      rw [perturbNefHeight_reverseOrientation]
      exact hBound (-δ) (by simpa only [abs_neg] using hδ))
  refine ⟨C, ε, hC, hε, hε₀', fun δ hδ ↦ ?_⟩
  have hb := h (-δ) (by simpa only [abs_neg] using hδ)
  simpa only [perturbNefHeight_reverseOrientation, neg_neg, neg_zero,
    PlanarHalfPlaneData.boundaryLine_reverseOrientation, mul_neg, sub_neg_eq_add,
    neg_sq] using hb
/-- Signed quadratic area variation for either orientation of a simple Nef wall. -/
theorem simpleNefPolygon_area_variation_signed {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          (if (H i).upper then -1 else 1) *
            (MeasureTheory.Measure.hausdorffMeasure 1
              (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  cases hs : (H i).upper
  · simpa only [hs, Bool.false_eq_true, ite_false, one_mul] using
      simpleNefPolygon_area_variation E H i hE hLines hs R ε₀ hR hε₀ hBound
  · simpa only [hs, ite_true, neg_one_mul, neg_mul, one_mul, sub_neg_eq_add] using
      simpleNefPolygon_area_variation_lower E H i hE hLines hs R ε₀ hR hε₀ hBound

end MovingSofa
