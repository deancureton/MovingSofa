import Mathlib.Analysis.Calculus.Deriv.Basic

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The right and left derivative relations of a function on a closed interval at a point: the
first holds of `v` when the right difference quotient tends to `v`, the second for the left one. -/
def intervalOneSidedDerivativeRelations {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (a b : ℝ) (_hab : a < b) (f : Set.Icc a b → E)
    (t : Set.Icc a b) : (E → Prop) × (E → Prop) :=
  (fun v ↦ (t : ℝ) < b ∧
      Tendsto (fun s : Set.Icc a b ↦ ((s : ℝ) - t)⁻¹ • (f s - f t))
        (𝓝[Set.Ioi t] t) (𝓝 v),
   fun v ↦ a < (t : ℝ) ∧
      Tendsto (fun s : Set.Icc a b ↦ ((s : ℝ) - t)⁻¹ • (f s - f t))
        (𝓝[Set.Iio t] t) (𝓝 v))

end MovingSofa
