import MovingSofa.Curve.Jordan.Area
import MovingSofa.Curve.Jordan.WindingLocalConstancy
import MovingSofa.Curve.Jordan.RadialLoop
import MovingSofa.Curve.Jordan.RadialWinding
import MovingSofa.Curve.Jordan.UnitSphere
import MovingSofa.ForMathlib.Analysis.Convex.GaugeRescale
import MovingSofa.Geometry.Convex.FrontierInterior

noncomputable section

namespace MovingSofa

theorem convexBody_radial_boundary (K : ConvexBody Point) (o : Point)
    (ho : o ∈ interior (K : Set Point)) :
    ∃ (ρ : Point → ℝ)
      (e : {u : Point | ‖u‖ = 1} ≃ₜ ↥(frontier (K : Set Point)))
      (C : NNReal) (γ : ContinuousBVPaths 0 (2 * Real.pi)),
      (∀ u : Point, ‖u‖ = 1 →
        0 < ρ u ∧ o + ρ u • u ∈ frontier (K : Set Point) ∧
        ∀ r : ℝ, 0 < r → o + r • u ∈ frontier (K : Set Point) → r = ρ u) ∧
      (∀ u : {u : Point | ‖u‖ = 1}, (e u : Point) = o + ρ u • (u : Point)) ∧
      LipschitzWith C (fun u ↦ (e u : Point)) ∧
      (∀ t : Set.Icc (0 : ℝ) (2 * Real.pi),
        γ.val t = o + ρ (normalVector ((t : ℝ) : Real.Angle)) •
          normalVector ((t : ℝ) : Real.Angle)) ∧
      IsOrientedJordanParametrization (by positivity)
        (frontier (K : Set Point)) true γ.val ∧
      jordanInterior (frontier (K : Set Point)) = interior (K : Set Point) := by
  obtain ⟨ρ, e, C, hρ, he, hC⟩ := exists_radial_homeomorph K.convex K.isCompact.isBounded o ho
  let f := fun u ↦ (e u : Point)
  let γ := radialBVLoop f hC
  have hrange : Set.range γ.val = frontier (K : Set Point) := by
    rw [range_radialBVLoop]
    ext p
    constructor
    · rintro ⟨u, rfl⟩
      exact (e u).property
    · intro hp
      obtain ⟨u, hu⟩ := e.surjective ⟨p, hp⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  have hclosed := radialBVLoop_closed f hC
  have hinj := radialBVLoop_injOn f hC (Subtype.val_injective.comp e.injective)
  have hformula (t : Set.Icc (0 : ℝ) (2 * Real.pi)) : γ.val t =
      o + ρ (normalVector ((t : ℝ) : Real.Angle)) • normalVector ((t : ℝ) : Real.Angle) := by
    rw [radialBVLoop_apply]
    exact he _
  have hinter := jordanInterior_frontier_eq_interior K.convex K.isCompact.isClosed
    K.isCompact.isBounded K.nonempty
  have hwcenter : curveWinding (by positivity) γ.val o = 1 := by
    have hx := funext hformula
    rw [hx]
    exact curveWinding_radial_center o _ (fun t ↦ (hρ _ (norm_normalVector_real t)).1)
  let : PreconnectedSpace ↥(interior (K : Set Point)) :=
    Subtype.preconnectedSpace K.convex.interior.isPreconnected
  have hlc : IsLocallyConstant
      (fun p : ↥(interior (K : Set Point)) ↦ curveWinding (by positivity) γ.val p.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro p
    have hp : p.val ∉ Set.range γ.val := by
      rw [hrange]
      exact fun h ↦ h.2 p.property
    obtain ⟨U, hU, hpU, hUeq⟩ :=
      curveWinding_locally_constant_off_range (by positivity) γ.property.1 hclosed hp
    exact ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hpU,
      fun q hq ↦ hUeq q.val hq⟩
  refine ⟨ρ, e, C, γ, hρ, he, hC, hformula, ?_, hinter⟩
  refine ⟨by positivity, isJordanCurve_of_unitSphere_homeomorph e,
    γ.property.1, hrange, hclosed, hinj, ?_⟩
  intro p hp
  rw [hinter] at hp
  exact (hlc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨o, ho⟩).trans hwcenter

end MovingSofa
