import MovingSofa.Polygon.Nef.Variation.Area
import MovingSofa.Polygon.Nef.Variation.Boundary

noncomputable section

namespace MovingSofa

open Filter Topology
open Nef

theorem simpleNefPolygon_area_variation {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hE : IsMonotoneBooleanFunction E)
    (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (hSide : (H i).upper = false) (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀)
    (hBound : ∀ δ : ℝ, |δ| ≤ ε₀ →
      perturbNefHeight E H i δ ⊆ Metric.closedBall 0 R) :
    ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ε ≤ ε₀ ∧
      ∀ δ : ℝ, |δ| ≤ ε →
        |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          (MeasureTheory.Measure.hausdorffMeasure 1
            (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal * δ| ≤
          C * δ ^ 2 := by
  let M := |(H i).height| + ε₀ + R + 1
  have hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height := by
    exact noParallelBoundaryAt_auxiliary H i hLines R ε₀ hR hε₀
  rcases exists_parallel_stability_radius (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height hno with
    ⟨ρ, hρ, hstable⟩
  let C := ((activeBooleanPatterns E i).card : ℝ) *
    (2 * slopeBound (H i).angle (auxiliaryHalfPlaneFamily H i M))
  let ε := min ε₀ ρ
  refine ⟨C, ε, ?_, ?_, ?_, ?_⟩
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (slopeBound_nonneg _ _))
  · exact lt_min hε₀ hρ
  · exact min_le_left _ _
  · intro δ hδ
    have hM : (H i).height + ε₀ ≤ M := by
      dsimp [M]
      linarith [le_abs_self (H i).height]
    have hzero : |(0 : ℝ)| ≤ ε₀ := by simpa using hε₀.le
    have hBoundZero := hBound 0 hzero
    rw [perturbNefHeight_zero] at hBoundZero
    have hcoefficient :
        (MeasureTheory.Measure.hausdorffMeasure 1
          (frontier (perturbNefHeight E H i 0) ∩ (H i).boundaryLine)).toReal =
        activeSliceLength (H i).angle E
          (auxiliaryHalfPlaneFamily H i M) i R (H i).height := by
      rw [perturbNefHeight_zero]
      exact hausdorffMeasure_frontier_toReal_eq_activeSliceLength
        hE H i hSide M R (le_trans (le_add_of_nonneg_right hε₀.le) hM)
          hBoundZero hno
    have hremainder := area_perturb_remainder_le hE H i hSide R ε₀ M ρ
      hε₀ hρ hM hBound hstable δ hδ
    rw [hcoefficient]
    exact hremainder

end MovingSofa
