import MovingSofa.Curve.Jordan.Winding
import MovingSofa.Geometry.Frame
import Mathlib.Tactic

noncomputable section
namespace MovingSofa

/-- The parameter angle lifts a positive radial loop about its center. -/
lemma isCurveAngleLift_radial {a b : ℝ} (o : Point) (r : Set.Icc a b → ℝ)
    (hr : ∀ t, 0 < r t) :
    IsCurveAngleLift (fun t ↦ o + r t • normalVector ((t : ℝ) : Real.Angle)) o
      (fun t ↦ (t : ℝ)) := by
  refine ⟨continuous_subtype_val, fun t ↦ ?_⟩
  have hn : ‖r t • normalVector ((t : ℝ) : Real.Angle)‖ = r t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hr t), norm_normalVector_real, mul_one]
  simp only [add_sub_cancel_left, hn]
  constructor
  · change Real.cos (t : ℝ) = r t * Real.cos (t : ℝ) / r t
    field_simp [(hr t).ne']
  · change Real.sin (t : ℝ) = r t * Real.sin (t : ℝ) / r t
    field_simp [(hr t).ne']

/-- A positive radial loop winds once around its center. -/
lemma curveWinding_radial_center (o : Point) (r : Set.Icc (0 : ℝ) (2 * Real.pi) → ℝ)
    (hr : ∀ t, 0 < r t) :
    curveWinding (by positivity)
      (fun t ↦ o + r t • normalVector ((t : ℝ) : Real.Angle)) o = 1 := by
  rw [(isCurveAngleLift_radial o r hr).curveWinding_eq]
  simp

end MovingSofa
