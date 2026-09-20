import MovingSofa.Curve.AreaTransport
import MovingSofa.Curve.Jordan.OrientationTransport

namespace MovingSofa

/-- A monotone or antitone transition between oriented Jordan paths determines their
signed areas. -/
theorem curveArea_eq_of_oriented_reparametrization
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {Γ : Set Point} {ccw₁ ccw₂ : Bool}
    (x : ContinuousBVPaths a b) (y : ContinuousBVPaths c d)
    (hx : IsOrientedJordanParametrization hab Γ ccw₁ x.val)
    (hy : IsOrientedJordanParametrization hcd Γ ccw₂ y.val)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφs : Function.Surjective φ) (hφ : Monotone φ ∨ Antitone φ)
    (hcomp : y.val = x.val ∘ φ) :
    (ccw₁ = ccw₂ → curveAreaFunctional x = curveAreaFunctional y) ∧
    (ccw₁ ≠ ccw₂ → curveAreaFunctional x = -curveAreaFunctional y) := by
  obtain ⟨z, hz, hmarea, haarea⟩ :=
    curveArea_comp_monotone_or_antitone_surjective hab hcd x φ hφc hφs hφ
  have hzy : z = y := Subtype.ext (hz.trans hcomp.symm)
  subst z
  obtain ⟨u, hu⟩ := hφs ⟨a, le_rfl, hab⟩
  obtain ⟨v, hv⟩ := hφs ⟨b, hab, le_rfl⟩
  rcases hφ with hm | ha
  · have hleft : φ ⟨c, le_rfl, hcd⟩ = ⟨a, le_rfl, hab⟩ := by
      apply le_antisymm
      · simpa only [hu] using
          hm (show (⟨c, le_rfl, hcd⟩ : Set.Icc c d) ≤ u from u.property.1)
      · exact (φ ⟨c, le_rfl, hcd⟩).property.1
    have hright : φ ⟨d, hcd, le_rfl⟩ = ⟨b, hab, le_rfl⟩ := by
      apply le_antisymm
      · exact (φ ⟨d, hcd, le_rfl⟩).property.2
      · simpa only [hv] using
          hm (show v ≤ (⟨d, hcd, le_rfl⟩ : Set.Icc c d) from v.property.2)
    have horient := hx.orientation_eq_of_comp hy φ hφc hleft hright hcomp
    exact ⟨fun _ ↦ (hmarea hm).symm, fun hn ↦ (hn horient.symm).elim⟩
  · have hleft : φ ⟨c, le_rfl, hcd⟩ = ⟨b, hab, le_rfl⟩ := by
      apply le_antisymm
      · exact (φ ⟨c, le_rfl, hcd⟩).property.2
      · simpa only [hv] using
          ha (show (⟨c, le_rfl, hcd⟩ : Set.Icc c d) ≤ v from v.property.1)
    have hright : φ ⟨d, hcd, le_rfl⟩ = ⟨a, le_rfl, hab⟩ := by
      apply le_antisymm
      · simpa only [hu] using
          ha (show u ≤ (⟨d, hcd, le_rfl⟩ : Set.Icc c d) from u.property.2)
      · exact (φ ⟨d, hcd, le_rfl⟩).property.1
    have horient := hx.orientation_eq_not_of_comp hy φ hφc hleft hright hcomp
    constructor
    · intro heq
      have hf : ccw₁ = !ccw₁ := heq.trans horient
      cases ccw₁ <;> contradiction
    · intro _
      have heq := haarea ha
      linarith

end MovingSofa
