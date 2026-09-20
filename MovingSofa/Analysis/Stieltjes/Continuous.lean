import MovingSofa.Analysis.Stieltjes.Calculus
import MovingSofa.Analysis.Stieltjes.Transport

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- A continuous function is integrable against a BV Stieltjes measure on a compact interval. -/
theorem RightContinuousIntervalBV.integrable_of_continuous {a b : ℝ} (F : RightContinuousIntervalBV a b)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) : (intervalStieltjesMeasure F).Integrable g := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  exact hg.integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _))


private theorem intervalStieltjesIntegral_univ_eq_Ioc_of_continuous
    {a b : ℝ} (hab : a ≤ b) (F : RightContinuousIntervalBV a b)
    (hF : Continuous F.toFun) (g : Set.Icc a b → ℝ) (hg : Continuous g) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral F g {t | a < (t : ℝ)} := by
  let a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  let b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  let cuts : Fin 2 → Set.Icc a b := Fin.cases a' (fun _ ↦ b')
  have hcuts : Monotone cuts := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [cuts, a', b'] at hij ⊢
    exact hab
  have hparts := intervalStieltjesIntegral_eq_sum_Ioc F hF g hg cuts hcuts rfl rfl
  have hset : Set.Ioc a' b' = {t : Set.Icc a b | a < (t : ℝ)} := by
    ext t
    simp only [Set.mem_Ioc, Set.mem_ofPred_eq]
    constructor
    · exact fun ht ↦ ht.1
    · exact fun ht ↦ ⟨ht, t.property.2⟩
  dsimp [cuts] at hparts
  simpa [Fin.sum_univ_succ, hset] using hparts

/-- For a continuous driver and a continuous integrand, the closed-interval Stieltjes integral
agrees with the open-interval one: neither endpoint carries an atom. -/
theorem intervalStieltjesIntegral_univ_eq_Ioo_of_continuous {a b : ℝ} (hab : a ≤ b)
    (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    (g : Set.Icc a b → ℝ) (hg : Continuous g) :
    intervalStieltjesIntegral F g Set.univ =
      intervalStieltjesIntegral F g (Set.Ioo ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩) := by
  set a' : Set.Icc a b := ⟨a, le_rfl, hab⟩
  set b' : Set.Icc a b := ⟨b, hab, le_rfl⟩
  have hdiff : (Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b' ⊆ {a'} ∪ {b'} := by
    intro t ht
    rcases lt_or_ge a' t with hlt | hle
    · exact Or.inr (le_antisymm t.property.2 (not_lt.mp fun h ↦ ht.2 ⟨hlt, h⟩))
    · exact Or.inl (le_antisymm hle t.property.1)
  have hzero : intervalStieltjesIntegral F g
      ((Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b') = 0 := by
    refine VectorMeasure.setIntegral_of_variation_apply_eq_zero _ (measure_mono_null hdiff ?_)
    refine measure_union_null ?_ ?_ <;>
      · rw [intervalStieltjesMeasure, F.boundedVariation.variation_vectorMeasure_singleton,
          hF.continuousAt.continuousWithinAt.rightLim_eq,
          hF.continuousAt.continuousWithinAt.leftLim_eq]
        simp
  have hsplit := VectorMeasure.setIntegral_inter_add_sdiff
    (μ := intervalStieltjesMeasure F) (B := ContinuousLinearMap.mul ℝ ℝ) (f := g)
    (s := (Set.univ : Set (Set.Icc a b))) (t := Set.Ioo a' b')
    MeasurableSet.univ measurableSet_Ioo (F.integrable_of_continuous hg).integrableOn
  rw [Set.univ_inter] at hsplit
  change intervalStieltjesIntegral F g (Set.Ioo a' b') +
    intervalStieltjesIntegral F g ((Set.univ : Set (Set.Icc a b)) \ Set.Ioo a' b') =
    intervalStieltjesIntegral F g Set.univ at hsplit
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

/-- Integration by parts for continuous BV functions on the full compact interval. -/
theorem intervalStieltjes_integration_by_parts_of_continuous
    (a b : ℝ) (hab : a ≤ b) (F G : RightContinuousIntervalBV a b)
    (hF : Continuous F.toFun) (hG : Continuous G.toFun) :
    intervalStieltjesIntegral F G.toFun Set.univ +
        intervalStieltjesIntegral G F.toFun Set.univ =
      F.toFun ⟨b, hab, le_rfl⟩ * G.toFun ⟨b, hab, le_rfl⟩ -
        F.toFun ⟨a, le_rfl, hab⟩ * G.toFun ⟨a, le_rfl, hab⟩ := by
  obtain ⟨left, hleft, hparts⟩ := intervalStieltjes_integration_by_parts a b hab F G
  have hleft_eq : Set.EqOn left F.toFun {t | a < (t : ℝ)} := by
    intro t ht
    change a < (t : ℝ) at ht
    have hnonempty : (Set.Iio t).Nonempty := by
      let s : Set.Icc a b := ⟨(a + (t : ℝ)) / 2, by constructor <;> linarith [t.property.2]⟩
      exact ⟨s, by change (a + (t : ℝ)) / 2 < (t : ℝ); linarith⟩
    have hne : (nhdsWithin t (Set.Iio t)).NeBot :=
      nhdsWithin_Iio_neBot' hnonempty le_rfl
    let _ : (nhdsWithin t (Set.Iio t)).NeBot := hne
    have hcont : Filter.Tendsto F.toFun (nhdsWithin t (Set.Iio t))
        (nhds (F.toFun t)) := hF.continuousAt.continuousWithinAt
    exact tendsto_nhds_unique (hleft t ht) hcont
  have hintegrand : intervalStieltjesIntegral G left {t | a < (t : ℝ)} =
      intervalStieltjesIntegral G F.toFun {t | a < (t : ℝ)} := by
    unfold intervalStieltjesIntegral
    exact MeasureTheory.VectorMeasure.setIntegral_congr_fun hleft_eq
  rw [intervalStieltjesIntegral_univ_eq_Ioc_of_continuous hab F hF G.toFun hG,
    intervalStieltjesIntegral_univ_eq_Ioc_of_continuous hab G hG F.toFun hF,
    ← hintegrand]
  exact hparts

end MovingSofa
