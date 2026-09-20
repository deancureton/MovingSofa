import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

open scoped Pointwise

namespace MeasureTheory

/-- The square root of planar volume scales linearly under nonnegative dilations. -/
theorem volume_smul_rpow_half (S : Set (EuclideanSpace ℝ (Fin 2))) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S) ^ (2 : ℝ)⁻¹ = ENNReal.ofReal a * volume S ^ (2 : ℝ)⁻¹ := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := volume) ha]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  congr 1
  rw [ENNReal.ofReal_pow ha]
  simpa using ENNReal.pow_rpow_inv_natCast (by norm_num : (2 : ℕ) ≠ 0) (ENNReal.ofReal a)


end MeasureTheory
