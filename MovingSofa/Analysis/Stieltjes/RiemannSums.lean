import MovingSofa.Analysis.Stieltjes.Continuous

/-!
# Riemann-Stieltjes sums for continuous integrands

Left-endpoint sums over finite monotone partitions converge to the interval Stieltjes
integral of a continuous integrand against a continuous BV integrator, uniformly in the
mesh of the partition.
-/

noncomputable section

open MeasureTheory Set

namespace MovingSofa

/-- Two Stieltjes integrals differ by at most the uniform distance of their integrands
times the total variation of the integrator. -/
theorem intervalStieltjesIntegral_sub_le_of_abs_sub_le
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {g h : Set.Icc a b → ℝ}
    (hg : (intervalStieltjesMeasure F).Integrable g)
    (hh : (intervalStieltjesMeasure F).Integrable h)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hbound : ∀ᵐ t ∂(intervalStieltjesMeasure F).variation, |g t - h t| ≤ ε) :
    |intervalStieltjesIntegral F g univ - intervalStieltjesIntegral F h univ| ≤
      ε * (intervalStieltjesMeasure F).variation.real univ := by
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  simp only [VectorMeasure.restrict_univ]
  rw [← VectorMeasure.integral_sub hg hh, ← Real.norm_eq_abs]
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (B := ContinuousLinearMap.mul ℝ ℝ) (by simpa only [Real.norm_eq_abs] using hbound)
  refine h.trans ?_
  calc
    ε * ‖ContinuousLinearMap.mul ℝ ℝ‖ * (intervalStieltjesMeasure F).variation.real univ ≤
        ε * 1 * (intervalStieltjesMeasure F).variation.real univ := by
      gcongr
      exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
    _ = _ := by ring

private theorem intervalStieltjesIntegral_sum_indicator_Ioc
    {a b : ℝ} (F : RightContinuousIntervalBV a b) {ι : Type*}
    (s : Finset ι) (l u : ι → Set.Icc a b) (c : ι → ℝ)
    (hlu : ∀ i ∈ s, l i ≤ u i) :
    intervalStieltjesIntegral F
        (fun t ↦ ∑ i ∈ s, (Ioc (l i) (u i)).indicator (fun _ ↦ c i) t) univ =
      ∑ i ∈ s, c i * (F.toFun (u i) - F.toFun (l i)) := by
  classical
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  unfold intervalStieltjesIntegral
  rw [VectorMeasure.restrict_univ, VectorMeasure.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [VectorMeasure.integral_indicator_const _ measurableSet_Ioc]
    change c i * F.boundedVariation.vectorMeasure (Ioc (l i) (u i)) = _
    rw [F.boundedVariation.vectorMeasure_Ioc (hlu i hi),
      (F.right_continuous (u i)).rightLim_eq, (F.right_continuous (l i)).rightLim_eq]
  · intro i _
    exact (MeasureTheory.integrable_const (c i)).indicator measurableSet_Ioc

/-- The error in a left-endpoint Stieltjes sum is controlled by the cell oscillation of the
integrand times the total variation of the integrator. -/
theorem intervalStieltjesIntegral_sub_sum_le_of_oscillation
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) {n : ℕ}
    (cuts : Fin (n + 1) → Set.Icc a b) (hcuts : Monotone cuts)
    (hzero : (cuts 0 : ℝ) = a) (hlast : (cuts (Fin.last n) : ℝ) = b)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ (i : Fin n) t, t ∈ Ioc (cuts i.castSucc) (cuts i.succ) →
      |g t - g (cuts i.castSucc)| ≤ ε) :
    |intervalStieltjesIntegral F g univ -
        ∑ i : Fin n, g (cuts i.castSucc) *
          (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc))| ≤
      ε * (intervalStieltjesMeasure F).variation.real univ := by
  classical
  let _ : IsFiniteMeasure (intervalStieltjesMeasure F).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure F.boundedVariation
  let step : Set.Icc a b → ℝ := fun t ↦ ∑ i : Fin n,
    (Ioc (cuts i.castSucc) (cuts i.succ)).indicator (fun _ ↦ g (cuts i.castSucc)) t
  have hstep : (intervalStieltjesMeasure F).Integrable step := by
    apply MeasureTheory.integrable_finsetSum
    intro i _
    exact (MeasureTheory.integrable_const _).indicator measurableSet_Ioc
  have heval : intervalStieltjesIntegral F step univ =
      ∑ i : Fin n, g (cuts i.castSucc) *
        (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc)) :=
    intervalStieltjesIntegral_sum_indicator_Ioc (ι := Fin n) F Finset.univ
      (fun i ↦ cuts i.castSucc) (fun i ↦ cuts i.succ)
      (fun i ↦ g (cuts i.castSucc)) (fun i _ ↦ hcuts (Fin.castSucc_le_succ i))
  rw [← heval]
  apply intervalStieltjesIntegral_sub_le_of_abs_sub_le F
    (F.integrable_of_continuous hg) hstep hε
  have hatom : (intervalStieltjesMeasure F).variation {cuts 0} = 0 := by
    rw [VectorMeasure.variation_apply_singleton]
    have hz : intervalStieltjesMeasure F {cuts 0} = 0 :=
      BoundedVariationOn.vectorMeasure_singleton_eq_zero_of_continuous
        F.boundedVariation hF _
    simp [hz]
  have hae : ∀ᵐ t ∂(intervalStieltjesMeasure F).variation, t ≠ cuts 0 := by
    rw [ae_iff]
    have hset : {x : Set.Icc a b | ¬x ≠ cuts 0} = {cuts 0} := by
      ext x
      simp
    rw [hset]
    exact hatom
  filter_upwards [hae] with t ht
  have htcell : t ∈ ⋃ i : Fin n, Ioc (cuts i.castSucc) (cuts i.succ) := by
    rw [hcuts.iUnion_Ioc_fin]
    refine ⟨lt_of_le_of_ne ?_ (Ne.symm ht), ?_⟩
    · change (cuts 0 : ℝ) ≤ (t : ℝ)
      simpa [hzero] using t.property.1
    · change (t : ℝ) ≤ (cuts (Fin.last n) : ℝ)
      simpa [hlast] using t.property.2
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htcell
  have hvalue : step t = g (cuts i.castSucc) := by
    dsimp [step]
    rw [Finset.sum_eq_single i]
    · exact Set.indicator_of_mem hi _
    · intro j _ hji
      apply Set.indicator_of_notMem
      intro hj
      rcases lt_or_gt_of_ne hji with hji | hij
      · have hji' : j.succ ≤ i.castSucc := by simpa using Nat.succ_le_of_lt hji
        exact (not_lt_of_ge (hj.2.trans (hcuts hji'))) hi.1
      · have hij' : i.succ ≤ j.castSucc := by simpa using Nat.succ_le_of_lt hij
        exact (not_lt_of_ge (hi.2.trans (hcuts hij'))) hj.1
    · simp
  rw [hvalue]
  exact hosc i t hi

/-- Sufficiently fine partitions approximate a continuous Stieltjes integrand uniformly. -/
theorem exists_mesh_bound_intervalStieltjesIntegral_sub_sum
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {n : ℕ} (cuts : Fin (n + 1) → Set.Icc a b),
      Monotone cuts → (cuts 0 : ℝ) = a → (cuts (Fin.last n) : ℝ) = b →
      (∀ i : Fin n, (cuts i.succ : ℝ) - (cuts i.castSucc : ℝ) < δ) →
      |intervalStieltjesIntegral F g univ -
          ∑ i : Fin n, g (cuts i.castSucc) *
            (F.toFun (cuts i.succ) - F.toFun (cuts i.castSucc))| ≤
        ε * (intervalStieltjesMeasure F).variation.real univ := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hg) ε hε
  refine ⟨δ, hδ, fun cuts hcuts hzero hlast hmesh ↦ ?_⟩
  apply intervalStieltjesIntegral_sub_sum_le_of_oscillation F hF hg cuts hcuts hzero hlast
    hε.le
  intro i t ht
  have hdist : dist t (cuts i.castSucc) < δ := by
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg
      (sub_nonneg.mpr (show (cuts i.castSucc : ℝ) ≤ (t : ℝ) from ht.1.le))]
    exact (sub_le_sub_right (show (t : ℝ) ≤ (cuts i.succ : ℝ) from ht.2) _).trans_lt
      (hmesh i)
  simpa only [Real.dist_eq] using (hmod hdist).le

/-- Left-endpoint Stieltjes sums converge along any family of partitions whose mesh
tends to zero. -/
theorem tendsto_stieltjesSum_of_mesh_tendsto_zero
    {a b : ℝ} (F : RightContinuousIntervalBV a b) (hF : Continuous F.toFun)
    {g : Set.Icc a b → ℝ} (hg : Continuous g) (N : ℕ → ℕ)
    (cuts : ∀ k, Fin (N k + 1) → Set.Icc a b)
    (hcuts : ∀ k, Monotone (cuts k))
    (hzero : ∀ k, (cuts k 0 : ℝ) = a)
    (hlast : ∀ k, (cuts k (Fin.last (N k)) : ℝ) = b)
    (hmesh : ∀ δ > 0, ∀ᶠ k in Filter.atTop, ∀ i : Fin (N k),
      (cuts k i.succ : ℝ) - (cuts k i.castSucc : ℝ) < δ) :
    Filter.Tendsto (fun k ↦ ∑ i : Fin (N k), g (cuts k i.castSucc) *
      (F.toFun (cuts k i.succ) - F.toFun (cuts k i.castSucc)))
      Filter.atTop (nhds (intervalStieltjesIntegral F g univ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := (intervalStieltjesMeasure F).variation.real univ with hVdef
  have hV : 0 ≤ V := measureReal_nonneg
  have hpos : 0 < ε / (V + 1) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, happrox⟩ :=
    exists_mesh_bound_intervalStieltjesIntegral_sub_sum F hF hg hpos
  filter_upwards [hmesh δ hδ] with k hk
  have hbound := happrox (cuts k) (hcuts k) (hzero k) (hlast k) hk
  rw [Real.dist_eq, abs_sub_comm]
  apply hbound.trans_lt
  have hcancel : ε / (V + 1) * (V + 1) = ε :=
    div_mul_cancel₀ ε (by positivity)
  change ε / (V + 1) * V < ε
  nlinarith

end MovingSofa
