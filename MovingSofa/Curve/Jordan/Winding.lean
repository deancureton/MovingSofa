import MovingSofa.Curve.Jordan.Orientation
import MovingSofa.ForMathlib.Analysis.SpecialFunctions.AngleLift
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace MovingSofa

/-- Two continuous angle lifts have the same endpoint increment. -/
theorem IsCurveAngleLift.endpoint_increment_eq {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ ψ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) (hψ : IsCurveAngleLift x p ψ) :
    θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩ =
      ψ ⟨b, hab, le_rfl⟩ - ψ ⟨a, le_rfl, hab⟩ := by
  let _ : PreconnectedSpace (Set.Icc a b) := Subtype.preconnectedSpace isPreconnected_Icc
  have h := Real.sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin hθ.1 hψ.1
    (fun t ↦ (hθ.2 t).1.trans (hψ.2 t).1.symm)
    (fun t ↦ (hθ.2 t).2.trans (hψ.2 t).2.symm)
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩
  linarith

/-- Compute the winding value from any continuous angle lift. -/
theorem IsCurveAngleLift.curveWinding_eq {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) :
    curveWinding hab x p = (θ ⟨b, hab, le_rfl⟩ - θ ⟨a, le_rfl, hab⟩) / (2 * Real.pi) := by
  unfold curveWinding
  rw [dite_eq_left ⟨θ, hθ⟩]
  congr 1
  exact IsCurveAngleLift.endpoint_increment_eq hab (Exists.choose_spec ⟨θ, hθ⟩) hθ

/-- A nonzero winding value provides a continuous angle lift. -/
theorem exists_curveAngleLift_of_curveWinding_ne_zero {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} (h : curveWinding hab x p ≠ 0) :
    ∃ θ, IsCurveAngleLift x p θ := by
  by_contra hn
  apply h
  simp only [curveWinding, dite_eq_right hn]

/-- Pull back an angle lift along a continuous parameter map. -/
theorem IsCurveAngleLift.comp {a b c d : ℝ}
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ) :
    IsCurveAngleLift (x ∘ φ) p (θ ∘ φ) :=
  ⟨hθ.1.comp hφ, fun t ↦ hθ.2 (φ t)⟩

/-- Compute winding after continuous reparametrization from lifted endpoint values. -/
theorem IsCurveAngleLift.curveWinding_comp {a b c d : ℝ} (hcd : c ≤ d)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ) :
    curveWinding hcd (x ∘ φ) p =
      (θ (φ ⟨d, hcd, le_rfl⟩) - θ (φ ⟨c, le_rfl, hcd⟩)) / (2 * Real.pi) :=
  (hθ.comp hφ).curveWinding_eq hcd

/-- A continuous reparametrization preserving endpoints preserves winding. -/
theorem curveWinding_comp_of_endpoints {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {x : Set.Icc a b → Point} {p : Point}
    (hx : ∃ θ, IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩) :
    curveWinding hcd (x ∘ φ) p = curveWinding hab x p := by
  obtain ⟨θ, hθ⟩ := hx
  rw [hθ.curveWinding_comp hcd hφ, hφa, hφb, hθ.curveWinding_eq hab]

/-- A continuous reparametrization exchanging endpoints negates winding. -/
theorem curveWinding_comp_of_reversed_endpoints {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) {x : Set.Icc a b → Point} {p : Point}
    (hx : ∃ θ, IsCurveAngleLift x p θ) {φ : Set.Icc c d → Set.Icc a b} (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩) :
    curveWinding hcd (x ∘ φ) p = -curveWinding hab x p := by
  obtain ⟨θ, hθ⟩ := hx
  rw [hθ.curveWinding_comp hcd hφ, hφa, hφb, hθ.curveWinding_eq hab]
  ring

end MovingSofa
