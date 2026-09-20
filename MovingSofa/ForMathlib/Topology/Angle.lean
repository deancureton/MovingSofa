import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

open scoped unitInterval

namespace Real.Angle

/-- A continuous angle path starting at zero has a continuous real lift starting at zero. -/
theorem exists_continuous_lift_zero (θ : I → Real.Angle) (hθ : Continuous θ)
    (hzero : θ 0 = 0) :
    ∃ α : I → ℝ, Continuous α ∧ α 0 = 0 ∧ ∀ t, (α t : Real.Angle) = θ t := by
  have hcov : IsCoveringMap ((↑) : ℝ → Real.Angle) := AddCircle.isCoveringMap_coe (2 * Real.pi)
  obtain ⟨α, hα, hα0⟩ := hcov.exists_path_lifts
    (⟨θ, hθ⟩ : C(I, Real.Angle)) (0 : ℝ) (by simpa using hzero)
  exact ⟨α, α.continuous, hα0, fun t ↦ congrFun hα t⟩

end Real.Angle
