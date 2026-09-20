import MovingSofa.Analysis.BoundedVariation
import MovingSofa.ForMathlib.MeasureTheory.Hausdorff.Arclength

/-!
# The range of an almost injective continuous BV path is null

A continuous planar BV path that is injective on `[a, b)` sweeps a Lebesgue null set: each
compact initial subarc has finite Hausdorff length, hence vanishing Hausdorff `2`-measure,
and a rational exhaustion together with the terminal point covers the whole range.
-/

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- The range of a continuous planar BV path injective on `[a, b)` is Lebesgue null. -/
theorem ContinuousBVPaths.volume_range_eq_zero_of_injOn
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (hinj : Set.InjOn x.val {t | (t : ℝ) < b}) : volume (Set.range x.val) = 0 := by
  let γ : ℝ → Point := x.val ∘ Set.projIcc a b hab
  have hγcont : Continuous γ := x.property.1.comp continuous_projIcc
  have hγBV (q : ℝ) : BoundedVariationOn γ (Icc a q) := by
    apply ne_top_of_le_ne_top x.boundedVariationOn
    exact eVariationOn.comp_le_of_monotoneOn x.val (Set.projIcc a b hab)
      ((Set.monotone_projIcc hab).monotoneOn _) (fun _ _ ↦ mem_univ _)
  have hnull (q : {q : ℚ // a ≤ (q : ℝ) ∧ (q : ℝ) < b}) :
      volume (γ '' Icc a (q : ℝ)) = 0 := by
    apply volume_image_Icc_eq_zero_of_boundedVariationOn γ q.property.1 hγcont.continuousOn
      _ (hγBV _)
    intro u hu v hv huv
    have huab : u ∈ Icc a b := ⟨hu.1, hu.2.trans q.property.2.le⟩
    have hvab : v ∈ Icc a b := ⟨hv.1, hv.2.trans q.property.2.le⟩
    have heq := hinj (show (Set.projIcc a b hab u : ℝ) < b by
        rw [Set.projIcc_of_mem hab huab]; exact hu.2.trans_lt q.property.2)
      (show (Set.projIcc a b hab v : ℝ) < b by
        rw [Set.projIcc_of_mem hab hvab]; exact hv.2.trans_lt q.property.2) huv
    have hval := congrArg Subtype.val heq
    simpa only [Set.projIcc_of_mem hab huab, Set.projIcc_of_mem hab hvab] using hval
  apply measure_mono_null (t := {x.val ⟨b, hab, le_rfl⟩} ∪
    ⋃ q : {q : ℚ // a ≤ (q : ℝ) ∧ (q : ℝ) < b}, γ '' Icc a (q : ℝ))
  · rintro y ⟨t, rfl⟩
    by_cases ht : (t : ℝ) = b
    · exact Or.inl (congrArg x.val (show t = ⟨b, hab, le_rfl⟩ from Subtype.ext ht))
    · have htb : (t : ℝ) < b := lt_of_le_of_ne t.property.2 ht
      obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
      apply Or.inr
      apply mem_iUnion.2
      refine ⟨⟨q, t.property.1.trans htq.le, hqb⟩, (t : ℝ), ⟨t.property.1, htq.le⟩, ?_⟩
      dsimp [γ]
      rw [Set.projIcc_of_mem hab t.property]
  · exact measure_union_null (measure_singleton _) (measure_iUnion_null hnull)

end MovingSofa
