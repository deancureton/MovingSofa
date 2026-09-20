import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import MovingSofa.ForMathlib.MeasureTheory.EuclideanSpace

open EuclideanSpace MeasureTheory Set

theorem volume_setOf_mem_Icc_eq_volume_regionBetween {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_cc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, Set.preimage_ofPred_eq, hx, true_and]
    change volume (Icc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Icc, Real.volume_Ioo]
  · simp [regionBetween, hx]

theorem volume_regionBetween_triangle {b h : ℝ} (hb : 0 < b) (hh : 0 ≤ h) :
    volume (regionBetween (fun _ : ℝ ↦ 0) (fun x ↦ h - h / b * x) (Ioc 0 b)) =
      ENNReal.ofReal (b * h / 2) := by
  have hc : Continuous (fun x : ℝ ↦ h - h / b * x) := by fun_prop
  have hi := hc.intervalIntegrable (μ := volume) 0 b
  have hz := (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ))).intervalIntegrable
    (μ := volume) 0 b
  change (volume.prod volume) _ = _
  rw [volume_regionBetween_eq_integral
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hz)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mp hi) measurableSet_Ioc]
  · congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [← intervalIntegral.integral_of_le hb.le]
    have hm : IntervalIntegrable (fun x : ℝ ↦ h / b * x) volume 0 b :=
      (continuous_const.mul continuous_id).intervalIntegrable 0 b
    have hh' : IntervalIntegrable (fun _ : ℝ ↦ h) volume 0 b :=
      continuous_const.intervalIntegrable 0 b
    rw [intervalIntegral.integral_sub hh' hm,
      intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, integral_id]
    simp only [sub_zero, smul_eq_mul]
    field_simp
    ring
  · intro x hx
    have := mul_le_mul_of_nonneg_left hx.2 (div_nonneg hh hb.le)
    have heq : h / b * b = h := div_mul_cancel₀ h hb.ne'
    linarith

theorem volume_setOf_mem_Ioc_eq_volume_regionBetween
    {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    volume {p : ℝ × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioc (f p.1) (g p.1)} =
      volume (regionBetween f g s) := by
  change (volume.prod volume) _ = (volume.prod volume) _
  rw [Measure.prod_apply (measurableSet_region_between_oc hf hg hs),
    Measure.prod_apply (measurableSet_regionBetween hf hg hs)]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp only [regionBetween, Set.preimage_ofPred_eq, hx, true_and]
    change volume (Ioc (f x) (g x)) = volume (Ioo (f x) (g x))
    rw [Real.volume_Ioc, Real.volume_Ioo]
  · simp [regionBetween, hx]

/-- The planar volume of the horizontal band between the graphs of `f` and `g` over `s`,
where the first coordinate is the one squeezed between the two graphs. -/
theorem volume_horizontalIcc {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} =
      ENNReal.ofReal (∫ x in s, (g - f) x) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
  have hT : MeasurableSet T := measurableSet_region_between_cc hf hg hs
  rw [show {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} =
      finTwoCoordinatesSwap ⁻¹' T by rfl,
    volume_preserving_finTwoCoordinatesSwap.measure_preimage hT.nullMeasurableSet]
  change volume T = _
  rw [volume_setOf_mem_Icc_eq_volume_regionBetween hf hg hs]
  change (volume.prod volume) (regionBetween f g s) = _
  rw [volume_regionBetween_eq_integral hfi hgi hs hfg]

/-- The half-open variant of `volume_horizontalIcc`. -/
theorem volume_horizontalIoc {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfi : IntegrableOn f s) (hgi : IntegrableOn g s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} =
      ENNReal.ofReal (∫ x in s, (g - f) x) := by
  let T : Set (ℝ × ℝ) :=
    {p | p.1 ∈ s ∧ p.2 ∈ Ioc (f p.1) (g p.1)}
  have hT : MeasurableSet T := measurableSet_region_between_oc hf hg hs
  rw [show {p : EuclideanSpace ℝ (Fin 2) | p 1 ∈ s ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} =
      finTwoCoordinatesSwap ⁻¹' T by rfl,
    volume_preserving_finTwoCoordinatesSwap.measure_preimage hT.nullMeasurableSet]
  change volume T = _
  rw [volume_setOf_mem_Ioc_eq_volume_regionBetween hf hg hs]
  change (volume.prod volume) (regionBetween f g s) = _
  rw [volume_regionBetween_eq_integral hfi hgi hs hfg]

/-- A planar set whose second coordinate lies in `[0, 1]` and whose first coordinate is
squeezed between a continuous graph and its horizontal translate by `c` has volume at
most `c`. Only the upper bound is asserted, so no measurability of the set is needed. -/
theorem volume_le_of_subset_horizontalBand {X : Set (EuclideanSpace ℝ (Fin 2))}
    {f : ℝ → ℝ} {c : ℝ} (hf : Continuous f) (hc : 0 ≤ c)
    (hX : ∀ p ∈ X, (0 ≤ p 1 ∧ p 1 ≤ 1) ∧ f (p 1) ≤ p 0 ∧ p 0 ≤ f (p 1) + c) :
    volume X ≤ ENNReal.ofReal c := by
  have hg : Continuous (fun y ↦ f y + c) := hf.add continuous_const
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (hf.intervalIntegrable 0 1)
  have hgi : IntegrableOn (fun y ↦ f y + c) (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      (hg.intervalIntegrable 0 1)
  have key := volume_horizontalIcc (f := f) (g := fun y ↦ f y + c)
    (s := Icc (0 : ℝ) 1) hf.measurable hg.measurable measurableSet_Icc hfi hgi
    (fun x _ ↦ by simp [hc])
  have hint : ∫ x in Icc (0 : ℝ) 1, ((fun y ↦ f y + c) - f) x = c := by
    have hdiff : ((fun y ↦ f y + c) - f) = fun _ ↦ c := by funext y; simp
    rw [hdiff, setIntegral_const]
    simp
  rw [hint] at key
  refine le_trans (measure_mono ?_) key.le
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hX p hp
  exact ⟨h1, h2, h3⟩

/-- The horizontal unit strip meets the band `c ≤ a * x + b * y ≤ c + 1` in a
parallelogram of area `1 / |a|`. Only the upper bound is asserted. -/
theorem volume_horizontalBand_inter_le (a b c : ℝ) (ha : a ≠ 0) :
    volume {p : EuclideanSpace ℝ (Fin 2) | (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (c ≤ a * p 0 + b * p 1 ∧ a * p 0 + b * p 1 ≤ c + 1)} ≤
      ENNReal.ofReal (1 / |a|) := by
  have habs : 0 < |a| := abs_pos.mpr ha
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · refine volume_le_of_subset_horizontalBand (f := fun y ↦ (c + 1 - b * y) / a)
      (c := 1 / |a|) (by fun_prop) (by positivity) ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [div_le_iff_of_neg hneg]
      linarith
    · have hrw : (c + 1 - b * p 1) / a + 1 / |a| = (c - b * p 1) / a := by
        rw [abs_of_neg hneg]
        field_simp
        ring
      rw [hrw, le_div_iff_of_neg hneg]
      linarith
  · refine volume_le_of_subset_horizontalBand (f := fun y ↦ (c - b * y) / a)
      (c := 1 / |a|) (by fun_prop) (by positivity) ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [div_le_iff₀ hpos]
      linarith
    · have hrw : (c - b * p 1) / a + 1 / |a| = (c + 1 - b * p 1) / a := by
        rw [abs_of_pos hpos]
        field_simp
        ring
      rw [hrw, le_div_iff₀ hpos]
      linarith
