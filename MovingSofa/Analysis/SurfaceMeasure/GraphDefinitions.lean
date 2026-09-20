import MovingSofa.Analysis.SurfaceMeasure.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

namespace MovingSofa

def horizontalProjection (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : Set ℝ :=
  (fun p : Point ↦ e (p - o) 0) '' (K : Set Point)

def horizontalBounds (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) : ℝ × ℝ :=
  (sInf (horizontalProjection K o e), sSup (horizontalProjection K o e))

def upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (x : ℝ) : ℝ :=
  sSup {y : ℝ | o + e.symm !₂[x, y] ∈ (K : Set Point)}

def vectorNormalAngle (p : Point) : Real.Angle :=
  (Complex.arg ⟨p 0, p 1⟩ : ℝ)

/-- The normal vector associated to a nonzero planar vector is its normalization. -/
theorem normalVector_vectorNormalAngle {p : Point} (hp : p ≠ 0) :
    normalVector (vectorNormalAngle p) = ‖p‖⁻¹ • p := by
  let z : ℂ := ⟨p 0, p 1⟩
  have hz : z ≠ 0 := by
    intro hz
    apply hp
    ext i
    fin_cases i
    · exact congrArg Complex.re hz
    · exact congrArg Complex.im hz
  have hnorm : ‖z‖ = ‖p‖ := by
    rw [Complex.norm_def, EuclideanSpace.norm_eq]
    congr 1
    simp only [z, Complex.normSq_apply, Fin.sum_univ_two]
    simp [Real.norm_eq_abs, pow_two]
  ext i
  fin_cases i
  · simpa [vectorNormalAngle, normalVector, frame, z, hnorm, div_eq_inv_mul] using
      Complex.cos_arg hz
  · simpa [vectorNormalAngle, normalVector, frame, z, hnorm, div_eq_inv_mul] using
      Complex.sin_arg z

def upperGraphSurfaceIntegrand (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (x : ℝ) : ℝ :=
  ψ (vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1])) *
    Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)

end MovingSofa
