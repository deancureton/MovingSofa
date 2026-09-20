import JordanPick.JordanCurve
import MovingSofa.Curve.Jordan.Basic
import Mathlib.Topology.Connected.Basic

namespace MovingSofa

private theorem IsJordanCurve.exists_sphere_parametrization {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) :
    ∃ r : Metric.sphere (0 : Point) 1 → Point,
      Continuous r ∧ Function.Injective r ∧ Set.range r = Γ := by
  obtain ⟨f, hf, hfi, hfr⟩ := hΓ
  let e := Complex.orthonormalBasisOneI.repr.symm
  let φ : Metric.sphere (0 : Point) 1 → Circle := fun p ↦
    ⟨e p.val, mem_sphere_zero_iff_norm.mpr (by
      rw [e.norm_map]
      exact mem_sphere_zero_iff_norm.mp p.property)⟩
  have hφc : Continuous φ := (e.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Function.Injective φ := by
    intro p q h
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val h)
  have hφs : Function.Surjective φ := by
    intro z
    refine ⟨⟨e.symm z.val, mem_sphere_zero_iff_norm.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [e.symm.norm_map]
      exact Circle.norm_coe z
    · exact e.apply_symm_apply z.val
  refine ⟨f ∘ φ, hf.comp hφc, hfi.comp hφi, ?_⟩
  rw [Set.range_comp, hφs.range_eq, Set.image_univ, hfr]


theorem jordan_separation {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    ∃ U V : Set Point,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Bornology.IsBounded U ∧ ¬Bornology.IsBounded V ∧
      Disjoint U V ∧ U ∪ V = Γᶜ ∧ frontier U = Γ ∧ frontier V = Γ ∧
      (∀ p ∈ U, connectedComponentIn Γᶜ p = U) ∧
      (∀ p ∈ V, connectedComponentIn Γᶜ p = V) := by
  obtain ⟨r, hr, hri, hrΓ⟩ := hΓ.exists_sphere_parametrization
  rw [← hrΓ]
  obtain ⟨u, hu, hub⟩ := JordanCurve.step_A_exists_bounded JordanCurve.Brouwer.brouwerFPT hr hri
  obtain ⟨v, hv, hvu⟩ := JordanCurve.exists_unbounded_component r hr
  let U := connectedComponentIn (Set.range r)ᶜ u
  let V := connectedComponentIn (Set.range r)ᶜ v
  have hne : U ≠ V := by
    intro h
    change connectedComponentIn (Set.range r)ᶜ u = connectedComponentIn (Set.range r)ᶜ v at h
    exact hvu (h ▸ hub)
  have hdis : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro p hpU hpV
    exact hne ((connectedComponentIn_eq hpU).trans (connectedComponentIn_eq hpV).symm)
  have hcover : U ∪ V = (Set.range r)ᶜ := by
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)
    · intro p hp
      by_cases hpb : Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ p)
      · left
        have h := JordanCurve.step_B_bounded_unique JordanCurve.Brouwer.brouwerFPT hr hri
          p hp u hu hpb hub
        simpa only [U, ← h] using mem_connectedComponentIn hp
      · right
        have h := JordanCurve.unbounded_component_unique r hr hpb hvu
        simpa only [V, ← h] using mem_connectedComponentIn hp
  refine ⟨U, V, JordanCurve.isOpen_component r hr u, JordanCurve.isOpen_component r hr v,
    isConnected_connectedComponentIn_iff.mpr hu, isConnected_connectedComponentIn_iff.mpr hv,
    hub, hvu, hdis, hcover, ?_, ?_, ?_, ?_⟩
  · exact JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hr hri hu
      ⟨v, hv, hne.symm⟩
  · exact JordanCurve.component_boundary_eq JordanCurve.Brouwer.brouwerFPT hr hri hv
      ⟨u, hu, hne⟩
  · intro p hp
    exact (connectedComponentIn_eq hp).symm
  · intro p hp
    exact (connectedComponentIn_eq hp).symm

end MovingSofa
