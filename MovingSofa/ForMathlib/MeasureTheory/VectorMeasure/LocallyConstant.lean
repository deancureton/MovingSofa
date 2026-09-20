import MovingSofa.ForMathlib.Topology.Order.Interval
import Mathlib.MeasureTheory.VectorMeasure.BoundedVariation

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- Local constancy away from the initial endpoint gives a variation-null neighborhood. -/
theorem BoundedVariationOn.exists_nhds_variation_vectorMeasure_eq_zero_of_eventuallyEq_const
    {a b : ℝ} (hab : a < b) {g : Set.Icc a b → ℝ}
    (hg : BoundedVariationOn g Set.univ)
    (hr : ∀ y, ContinuousWithinAt g (Set.Ici y) y) (x : Set.Icc a b)
    (hxbot : a < (x : ℝ))
    (hx : g =ᶠ[𝓝 x] fun _ ↦ g x) :
    ∃ U ∈ 𝓝 x, hg.vectorMeasure.variation U = 0 := by
  let _ : Fact (a ≤ b) := ⟨hab.le⟩
  let _ : Nontrivial (Set.Icc a b) :=
    ⟨⟨⟨a, le_rfl, hab.le⟩, ⟨b, hab.le, le_rfl⟩, fun h ↦
      hab.ne (congrArg Subtype.val h)⟩⟩
  have hright (y : Set.Icc a b) : Function.rightLim g y = g y :=
    (hr y).rightLim_eq
  by_cases hxtop : x = ⊤
  · subst x
    obtain ⟨c, hc, hsub⟩ := (nhds_top_basis.mem_iff.mp hx)
    refine ⟨Set.Ioi c, nhds_top_basis.mem_iff.mpr ⟨c, hc, subset_rfl⟩, ?_⟩
    rw [hg.variation_vectorMeasure_Ioi]
    rw [show Function.rightLim g = g from funext hright]
    apply eVariationOn.constant_on
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hsub hy).trans (hsub hz).symm
  · have hxlt : x < ⊤ := lt_top_iff_ne_top.mpr hxtop
    have hxgt : ⊥ < x := hxbot
    obtain ⟨c, d, hxcd, hsub⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨⊥, hxgt⟩ ⟨⊤, hxlt⟩).mp hx
    refine ⟨Set.Ioo c d, Ioo_mem_nhds hxcd.1 hxcd.2, ?_⟩
    rw [hg.variation_vectorMeasure_Ioo_right]
    rw [show Function.rightLim g = g from funext hright]
    apply eVariationOn.constant_on
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact (hsub hy).trans (hsub hz).symm

