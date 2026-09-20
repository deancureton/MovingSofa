import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Linearity of a real inner product in its left argument

`Mathlib.Analysis.InnerProductSpace.Basic` provides the continuous linear map
`innerSL ℝ v = fun x ↦ ⟪v, x⟫`; the bundled form of the symmetric slot is what the
half-space convexity lemmas `convex_halfSpace_le` and `convex_halfSpace_ge` consume.
-/

/-- `x ↦ ⟪x, v⟫` is a linear map of a real inner product space. -/
theorem isLinearMap_inner_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : IsLinearMap ℝ fun x : E ↦ inner ℝ x v :=
  ⟨fun a b ↦ inner_add_left a b v, fun c a ↦ real_inner_smul_left a v c⟩
