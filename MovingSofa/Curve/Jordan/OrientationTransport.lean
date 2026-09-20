import MovingSofa.Curve.Jordan.Winding
import MovingSofa.Curve.Jordan.Interior

noncomputable section
namespace MovingSofa

/-- Endpoint-preserving continuous parameter changes preserve Jordan orientation. -/
theorem IsOrientedJordanParametrization.orientation_eq_of_comp
    {a b c d : ℝ} {hab : a ≤ b} {hcd : c ≤ d} {Γ : Set Point}
    {ccw₁ ccw₂ : Bool} {x : Set.Icc a b → Point} {y : Set.Icc c d → Point}
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y)
    (φ : Set.Icc c d → Set.Icc a b) (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩)
    (hxy : y = x ∘ φ) : ccw₂ = ccw₁ := by
  obtain ⟨p, hp⟩ := hx.2.1.jordanInterior_nonempty
  have hxw := hx.2.2.2.2.2.2 p hp
  have hyw := hy.2.2.2.2.2.2 p hp
  have hn : curveWinding hab x p ≠ 0 := by
    rw [hxw]
    cases ccw₁ <;> norm_num
  have hw := curveWinding_comp_of_endpoints hab hcd
    (exists_curveAngleLift_of_curveWinding_ne_zero hab hn) hφ hφa hφb
  rw [← hxy, hxw, hyw] at hw
  cases ccw₁ <;> cases ccw₂ <;> first | rfl | norm_num at hw

/-- Exchanging the parameter endpoints reverses Jordan orientation. -/
theorem IsOrientedJordanParametrization.orientation_eq_not_of_comp
    {a b c d : ℝ} {hab : a ≤ b} {hcd : c ≤ d} {Γ : Set Point}
    {ccw₁ ccw₂ : Bool} {x : Set.Icc a b → Point} {y : Set.Icc c d → Point}
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y)
    (φ : Set.Icc c d → Set.Icc a b) (hφ : Continuous φ)
    (hφa : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩)
    (hφb : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩)
    (hxy : y = x ∘ φ) : ccw₂ = !ccw₁ := by
  obtain ⟨p, hp⟩ := hx.2.1.jordanInterior_nonempty
  have hxw := hx.2.2.2.2.2.2 p hp
  have hyw := hy.2.2.2.2.2.2 p hp
  have hn : curveWinding hab x p ≠ 0 := by
    rw [hxw]
    cases ccw₁ <;> norm_num
  have hw := curveWinding_comp_of_reversed_endpoints hab hcd
    (exists_curveAngleLift_of_curveWinding_ne_zero hab hn) hφ hφa hφb
  rw [← hxy, hxw, hyw] at hw
  cases ccw₁ <;> cases ccw₂ <;> first | rfl | norm_num at hw

end MovingSofa
