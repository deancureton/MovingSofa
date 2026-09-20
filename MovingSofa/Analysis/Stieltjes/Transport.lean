import MovingSofa.Analysis.Stieltjes.Integral
import MovingSofa.ForMathlib.MeasureTheory.StieltjesTransport
import MovingSofa.ForMathlib.Order.IntervalPartition

noncomputable section

open MeasureTheory Set
open scoped Function

namespace MovingSofa

/-- Continuous monotone surjective reparametrization preserves the Stieltjes integral. -/
theorem intervalStieltjesIntegral_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (F : RightContinuousIntervalBV a b)
    (hFc : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hgc : Continuous g)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ) (hφ : Monotone φ)
    (hφs : Function.Surjective φ) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral
        { toFun := F.toFun ∘ φ
          boundedVariation := BoundedVariationOn.comp_monotone_surjective_Icc
            hab F.boundedVariation hφ hφs
          right_continuous := fun _ ↦
            (hFc.comp hφc).continuousAt.continuousWithinAt }
        (g ∘ φ) Set.univ := by
  let Fφ : RightContinuousIntervalBV c d :=
    { toFun := F.toFun ∘ φ
      boundedVariation := BoundedVariationOn.comp_monotone_surjective_Icc
        hab F.boundedVariation hφ hφs
      right_continuous := fun _ ↦
        (hFc.comp hφc).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fφ).map φ = intervalStieltjesMeasure F :=
    BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
      hab hcd F.boundedVariation hFc hφc hφ hφs
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fφ).variation := by
    change IsFiniteMeasure Fφ.boundedVariation.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure Fφ.boundedVariation
  have hgint : (intervalStieltjesMeasure Fφ).Integrable (g ∘ φ) :=
    (hgc.comp hφc).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fφ).variation.map φ) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← hmap, MeasureTheory.VectorMeasure.integral_map hφc.measurable hgm hgint]
  rfl

/-- Restricting a continuous Stieltjes integral agrees with integration on the subinterval. -/
theorem intervalStieltjesIntegral_Ioc_eq_inclusion
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hFc : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hgc : Continuous g) (l u : Set.Icc a b) (hlu : l ≤ u) :
    let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hfr : BoundedVariationOn (F.toFun ∘ ι) Set.univ :=
      ne_top_of_le_ne_top F.boundedVariation (eVariationOn.comp_le_of_monotoneOn F.toFun ι
        (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    intervalStieltjesIntegral F g (Ioc l u) =
      intervalStieltjesIntegral
        { toFun := F.toFun ∘ ι
          boundedVariation := hfr
          right_continuous := fun _ ↦
            (hFc.comp (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
        (g ∘ ι) Set.univ := by
  dsimp only
  let ι : Set.Icc (l : ℝ) u → Set.Icc a b := fun x ↦
    ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
  let hfr : BoundedVariationOn (F.toFun ∘ ι) Set.univ :=
    ne_top_of_le_ne_top F.boundedVariation (eVariationOn.comp_le_of_monotoneOn F.toFun ι
      (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
  let Fr : RightContinuousIntervalBV (l : ℝ) u :=
    { toFun := F.toFun ∘ ι
      boundedVariation := hfr
      right_continuous := fun _ ↦
        (hFc.comp (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fr).map ι =
      (intervalStieltjesMeasure F).restrict (Ioc l u) :=
    BoundedVariationOn.vectorMeasure_map_Icc_inclusion F.boundedVariation hFc l u hlu
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fr).variation := by
    change IsFiniteMeasure hfr.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure hfr
  have hgint : (intervalStieltjesMeasure Fr).Integrable (g ∘ ι) :=
    (hgc.comp (continuous_subtype_val.subtype_mk _)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fr).variation.map ι) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← hmap, MeasureTheory.VectorMeasure.integral_map
    (continuous_subtype_val.subtype_mk _).measurable hgm hgint]
  rfl

/-- A continuous Stieltjes integral splits over a finite monotone partition. -/
theorem intervalStieltjesIntegral_eq_sum_Ioc
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hFc : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hgc : Continuous g) {n : ℕ}
    (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b) :
    intervalStieltjesIntegral F g Set.univ =
      ∑ i : Fin n, intervalStieltjesIntegral F g (Ioc (cuts i.castSucc) (cuts i.succ)) := by
  have hab : a ≤ b := by
    calc
      a = cuts 0 := hzero.symm
      _ ≤ cuts (Fin.last n) := hcuts (Fin.zero_le _)
      _ = b := hlast
  let _ : Fact (a ≤ b) := ⟨hab⟩
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation := by
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  have hmeas (i : Fin n) : MeasurableSet (Ioc (cuts i.castSucc) (cuts i.succ)) :=
    measurableSet_Ioc
  have hall : (intervalStieltjesMeasure F).Integrable g :=
    hgc.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hint (i : Fin n) :
      (intervalStieltjesMeasure F).IntegrableOn g (Ioc (cuts i.castSucc) (cuts i.succ)) :=
    hall.integrableOn
  have hpair : Set.Pairwise ((Finset.univ : Finset (Fin n)) : Set (Fin n))
      (Disjoint on fun i ↦ Ioc (cuts i.castSucc) (cuts i.succ)) := by
    intro i _ j _ hij
    change Disjoint (Ioc (cuts i.castSucc) (cuts i.succ))
      (Ioc (cuts j.castSucc) (cuts j.succ))
    rw [Set.disjoint_left]
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hij_fin : i.succ ≤ j.castSucc := by
        simpa using Nat.succ_le_of_lt hij'
      exact (not_lt_of_ge (le_trans hxi.2 (hcuts hij_fin))) hxj.1
    · have hji_fin : j.succ ≤ i.castSucc := by
        simpa using Nat.succ_le_of_lt hji'
      exact (not_lt_of_ge (le_trans hxj.2 (hcuts hji_fin))) hxi.1
  rw [← MeasureTheory.VectorMeasure.setIntegral_biUnion_finset Finset.univ
    (fun i _ ↦ hmeas i) hpair (fun i _ ↦ hint i)]
  have hunion :
      (⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ)) = Set.univ \ {cuts 0} := by
    rw [hcuts.iUnion_Ioc_fin]
    ext x
    simp only [mem_Ioc, mem_sdiff, mem_univ, true_and, mem_singleton_iff]
    constructor
    · rintro ⟨hx0, _⟩ hxe
      exact hx0.ne' hxe
    · intro hxe
      exact ⟨lt_of_le_of_ne (by
        change (cuts 0 : ℝ) ≤ (x : ℝ)
        simpa [hzero] using x.property.1) (fun hx ↦ hxe hx.symm),
        by
          change (x : ℝ) ≤ (cuts (Fin.last n) : ℝ)
          simpa [hlast] using x.property.2⟩
  simp only [Finset.mem_univ, iUnion_true]
  rw [hunion]
  rw [MeasureTheory.VectorMeasure.setIntegral_sdiff (s := Set.univ) (t := {cuts 0})
    MeasurableSet.univ (measurableSet_singleton _) hall.integrableOn (subset_univ _)]
  rw [MeasureTheory.VectorMeasure.integral_singleton]
  have hz : intervalStieltjesMeasure F {cuts 0} = 0 :=
    BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous F.boundedVariation hFc _
  rw [hz]
  simp

/-- Reversing both continuous integrand and BV integrator negates their Stieltjes integral. -/
theorem intervalStieltjesIntegral_comp_reverse
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b)
    (hFc : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hgc : Continuous g) :
    let r := Set.Icc.reverse hab
    let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab F.boundedVariation
      (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
    intervalStieltjesIntegral
        { toFun := F.toFun ∘ r
          boundedVariation := hfr
          right_continuous := fun _ ↦
            (hFc.comp (Set.Icc.continuous_reverse hab)).continuousAt.continuousWithinAt }
        (g ∘ r) Set.univ =
      -intervalStieltjesIntegral F g Set.univ := by
  dsimp only
  let r := Set.Icc.reverse hab
  let hfr := BoundedVariationOn.comp_antitone_surjective_Icc hab F.boundedVariation
    (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)
  let Fr : RightContinuousIntervalBV a b :=
    { toFun := F.toFun ∘ r
      boundedVariation := hfr
      right_continuous := fun _ ↦
        (hFc.comp (Set.Icc.continuous_reverse hab)).continuousAt.continuousWithinAt }
  have hmap : (intervalStieltjesMeasure Fr).map r = -intervalStieltjesMeasure F :=
    BoundedVariationOn.vectorMeasure_map_reverse_Icc hab F.boundedVariation hFc
  let _ : IsFiniteMeasure (intervalStieltjesMeasure Fr).variation := by
    change IsFiniteMeasure hfr.vectorMeasure.variation
    exact BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure hfr
  have hgint : (intervalStieltjesMeasure Fr).Integrable (g ∘ r) :=
    (hgc.comp (Set.Icc.continuous_reverse hab)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))
  have hgm : AEStronglyMeasurable g
      ((intervalStieltjesMeasure Fr).variation.map r) :=
    hgc.aestronglyMeasurable
  unfold intervalStieltjesIntegral
  simp only [MeasureTheory.VectorMeasure.restrict_univ]
  rw [← MeasureTheory.VectorMeasure.integral_neg_vectorMeasure, ← hmap,
    MeasureTheory.VectorMeasure.integral_map
      (Set.Icc.continuous_reverse hab).measurable hgm hgint]
  rfl

end MovingSofa
