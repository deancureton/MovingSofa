import MovingSofa.Curve.Jordan.ArcArea
import MovingSofa.Curve.Jordan.ClosedArea

namespace MovingSofa

theorem curveArea_reparametrization :
    (∀ (a b c d : ℝ), a < b → c < d →
      ∀ (x : ContinuousBVPaths a b) (φ : Set.Icc c d → Set.Icc a b),
      Continuous φ → Function.Surjective φ → (Monotone φ ∨ Antitone φ) →
      ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ ∧
        (Monotone φ → curveAreaFunctional y = curveAreaFunctional x) ∧
        (Antitone φ → curveAreaFunctional y = -curveAreaFunctional x)) ∧
    (∀ (Γ Δ : OrientedJordanArc) (x : ArcBVParametrization Γ)
      (y : ArcBVParametrization Δ), Γ.carrier = Δ.carrier →
      (Γ.startPoint = Δ.startPoint → Γ.endPoint = Δ.endPoint →
        curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
      (Γ.startPoint = Δ.endPoint → Γ.endPoint = Δ.startPoint →
        curveAreaFunctional x.path = -curveAreaFunctional y.path)) ∧
    (∀ (Γ Δ : OrientedJordanCurve) (x : ClosedBVParametrization Γ)
      (y : ClosedBVParametrization Δ), Γ.carrier = Δ.carrier →
      (Γ.counterclockwise = Δ.counterclockwise →
        curveAreaFunctional x.path = curveAreaFunctional y.path) ∧
      (Γ.counterclockwise ≠ Δ.counterclockwise →
        curveAreaFunctional x.path = -curveAreaFunctional y.path)) ∧
    (∀ (a b : ℝ) (x : ContinuousBVPaths a b) (p : Point),
      (∀ t, x.val t = p) → curveAreaFunctional x = 0) := by
  refine ⟨?_, curveArea_arc_same_carrier, ?_, ?_⟩
  · intro a b c d hab hcd x φ hφc hφs hφ
    exact curveArea_comp_monotone_or_antitone_surjective hab.le hcd.le x φ hφc hφs hφ
  · exact curveArea_closed_same_carrier
  · intro a b x p hx
    exact curveAreaFunctional_eq_zero_of_constant x p hx

end MovingSofa
