import MovingSofa.Curve.Jordan.Winding
import MovingSofa.ForMathlib.Topology.Order.Concatenation

noncomputable section

namespace MovingSofa

private theorem cos_sin_add_sub {α β : ℝ}
    (hc : Real.cos α = Real.cos β) (hs : Real.sin α = Real.sin β) (t : ℝ) :
    Real.cos (t + (α - β)) = Real.cos t ∧
      Real.sin (t + (α - β)) = Real.sin t := by
  have hcd : Real.cos (α - β) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.cos_sq_add_sin_sq β]
  have hsd : Real.sin (α - β) = 0 := by
    rw [Real.sin_sub, hc, hs]
    ring
  simp [Real.cos_add, Real.sin_add, hcd, hsd]

/-- Winding is additive for two paths joined at a common endpoint. -/
theorem curveWinding_concatUnitIntervals
    {x y : Set.Icc (0 : ℝ) 1 → Point} {p : Point}
    {θ ψ : Set.Icc (0 : ℝ) 1 → ℝ}
    (hθ : IsCurveAngleLift x p θ) (hψ : IsCurveAngleLift y p ψ)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    curveWinding (by norm_num) (Function.concatUnitIntervals x y) p =
      curveWinding (by norm_num) x p + curveWinding (by norm_num) y p := by
  let δ := θ ⟨1, by norm_num⟩ - ψ ⟨0, by norm_num⟩
  have htrig (t : Set.Icc (0 : ℝ) 1) :
      Real.cos (ψ t + δ) = Real.cos (ψ t) ∧
      Real.sin (ψ t + δ) = Real.sin (ψ t) := by
    apply cos_sin_add_sub
    · rw [(hθ.2 _).1, (hψ.2 _).1, hjoin]
    · rw [(hθ.2 _).2, (hψ.2 _).2, hjoin]
  let η := Function.concatUnitIntervals θ (fun t ↦ ψ t + δ)
  have hη : IsCurveAngleLift (Function.concatUnitIntervals x y) p η := by
    refine ⟨Function.continuous_concatUnitIntervals hθ.1
      (hψ.1.add continuous_const) (by dsimp [δ]; ring), ?_⟩
    intro t
    dsimp [η, Function.concatUnitIntervals]
    split_ifs with ht
    · exact hθ.2 _
    · exact ⟨(htrig _).1.trans (hψ.2 _).1, (htrig _).2.trans (hψ.2 _).2⟩
  rw [hη.curveWinding_eq, hθ.curveWinding_eq, hψ.curveWinding_eq]
  simp only [η, Function.concatUnitIntervals]
  norm_num
  dsimp [δ]
  change (ψ ⟨1, _⟩ + (θ ⟨1, _⟩ - ψ ⟨0, _⟩) - θ ⟨0, _⟩) / (2 * Real.pi) =
    (θ ⟨1, _⟩ - θ ⟨0, _⟩) / (2 * Real.pi) +
      (ψ ⟨1, _⟩ - ψ ⟨0, _⟩) / (2 * Real.pi)
  ring

/-- Moving a closed path's cut point preserves winding. -/
theorem curveWinding_concat_of_cyclic_endpoints {a b : ℝ} (hab : a ≤ b)
    {x : Set.Icc a b → Point} {p : Point} {θ : Set.Icc a b → ℝ}
    (hθ : IsCurveAngleLift x p θ)
    (hx : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s : Set.Icc a b) (φ ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hφ₀ : φ ⟨0, by norm_num⟩ = s)
    (hφ₁ : φ ⟨1, by norm_num⟩ = ⟨b, hab, le_rfl⟩)
    (hψ₀ : ψ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩)
    (hψ₁ : ψ ⟨1, by norm_num⟩ = s) :
    curveWinding (by norm_num) (Function.concatUnitIntervals (x ∘ φ) (x ∘ ψ)) p =
      curveWinding hab x p := by
  have hjoin : (x ∘ φ) ⟨1, by norm_num⟩ = (x ∘ ψ) ⟨0, by norm_num⟩ := by
    simp only [Function.comp_apply, hφ₁, hψ₀]
    exact hx.symm
  rw [curveWinding_concatUnitIntervals (hθ.comp hφ) (hθ.comp hψ) hjoin,
    hθ.curveWinding_comp (by norm_num) hφ, hθ.curveWinding_comp (by norm_num) hψ,
    hφ₀, hφ₁, hψ₀, hψ₁, hθ.curveWinding_eq hab]
  ring

end MovingSofa
