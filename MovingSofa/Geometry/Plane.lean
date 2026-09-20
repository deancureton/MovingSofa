import Mathlib.Analysis.InnerProductSpace.PiL2

namespace MovingSofa

abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The squared norm of a planar point in coordinates. -/
theorem Point.norm_sq_eq (z : Point) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

/-- Cauchy-Schwarz for the coordinate form of the planar inner product. -/
theorem Point.abs_inner_coords_le (w d : Point) :
    |w 0 * d 0 + w 1 * d 1| ≤ ‖w‖ * ‖d‖ := by
  have hinner : (inner ℝ w d : ℝ) = w 0 * d 0 + w 1 * d 1 := by
    simp [inner, Fin.sum_univ_two]
    ring
  rw [← hinner]
  exact abs_real_inner_le_norm w d


/-- Each coordinate of a planar point is bounded by its norm. -/
theorem Point.abs_apply_le_norm (z : Point) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa [PiLp.norm_single, EuclideanSpace.inner_single_right] using
    abs_real_inner_le_norm z (EuclideanSpace.single i (1 : ℝ))

end MovingSofa
