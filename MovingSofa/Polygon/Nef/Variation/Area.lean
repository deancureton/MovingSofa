import MovingSofa.Polygon.Nef.Variation.LocalSlices

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma volume_perturbSdiff_toReal_eq_integral_slice {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ δ ε : ℝ) (hδ : |δ| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    (MeasureTheory.volume
      (perturbNefHeight E H i δ \ perturbNefHeight E H i ε)).toReal =
      ∫ x in heightInterval (H i).strict (H i).height δ ε,
        (MeasureTheory.volume
          (activeRegionSlice (H i).angle E H i R x)).toReal := by
  let S := perturbNefHeight E H i δ \ perturbNefHeight E H i ε
  have hS : MeasurableSet S :=
    MeasurableSet.diff (measurableSet_perturbNefHeight E H i δ)
      (measurableSet_perturbNefHeight E H i ε)
  have hSfinite : MeasureTheory.volume S ≠ ⊤ := by
    apply ne_of_lt
    calc
      MeasureTheory.volume S ≤ MeasureTheory.volume (perturbNefHeight E H i δ) :=
        MeasureTheory.measure_mono Set.sdiff_subset
      _ ≤ MeasureTheory.volume (Metric.closedBall (0 : Point) R) :=
        MeasureTheory.measure_mono (hBound δ hδ)
      _ < ⊤ := MeasureTheory.measure_closedBall_lt_top
  rw [show (MeasureTheory.volume S).toReal =
      ∫ x : ℝ, (MeasureTheory.volume
        {y : ℝ | framePoint (H i).angle x y ∈ S}).toReal by
    exact volume_toReal_eq_integral_frameSlice (H i).angle hS hSfinite]
  rw [← MeasureTheory.integral_indicator
    (measurableSet_heightInterval (H i).strict (H i).height δ ε)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ heightInterval (H i).strict (H i).height δ ε
  · rw [(frameSlice_perturbSdiff_eq hE H i hSide R ε₀ δ ε x hδ hBound).1 hx]
    simp [hx]
  · rw [(frameSlice_perturbSdiff_eq hE H i hSide R ε₀ δ ε x hδ hBound).2 hx]
    simp [hx]

lemma area_perturb_sub_eq_integral_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ M δ ε : ℝ)
    (hεδ : ε ≤ δ) (hδ : |δ| ≤ ε₀) (hε : |ε| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hxM : ∀ x ∈ heightInterval (H i).strict (H i).height δ ε, x ≤ M)
    (hxregular : ∀ x ∈ heightInterval (H i).strict (H i).height δ ε,
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    ClassicalResults.area (perturbNefHeight E H i δ) -
        ClassicalResults.area (perturbNefHeight E H i ε) =
      ∫ x in heightInterval (H i).strict (H i).height δ ε,
        activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R x := by
  rw [area_perturb_sub_eq_volume_sdiff hE H i hSide R ε₀ δ ε hεδ hδ hε hBound,
    volume_perturbSdiff_toReal_eq_integral_slice hE H i hSide R ε₀ δ ε hδ hBound]
  apply MeasureTheory.setIntegral_congr_fun
    (measurableSet_heightInterval (H i).strict (H i).height δ ε)
  intro x hx
  exact volume_activeRegionSlice_toReal_eq_activeSliceLength E H i M R x
    (hxM x hx) (hxregular x hx)

lemma area_perturb_sub_eq_intervalIntegral_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hSide : (H i).upper = false) (R ε₀ M ρ : ℝ)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ)
    (hM : (H i).height + ε₀ ≤ M)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hregular : ∀ x, |x - (H i).height| ≤ ρ →
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    ∀ δ : ℝ, |δ| ≤ min ε₀ ρ →
      ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) =
        ∫ x in (H i).height..(H i).height + δ,
          activeSliceLength (H i).angle E
            (auxiliaryHalfPlaneFamily H i M) i R x := by
  intro δ hδ
  have hδε₀ : |δ| ≤ ε₀ := hδ.trans (min_le_left _ _)
  have hδρ : |δ| ≤ ρ := hδ.trans (min_le_right _ _)
  have hzero : |(0 : ℝ)| ≤ ε₀ := by simpa using hε₀.le
  by_cases hδ0 : 0 ≤ δ
  · have hformula := area_perturb_sub_eq_integral_activeSliceLength
      hE H i hSide R ε₀ M δ 0 hδ0 hδε₀ hzero hBound
      (fun x hx ↦ by
        have hxb := mem_heightInterval_bounds hx
        linarith [le_abs_self δ])
      (fun x hx ↦ by
        apply hregular
        have hxb := mem_heightInterval_bounds hx
        rw [abs_le]
        constructor <;> linarith [le_abs_self δ, neg_le_abs δ])
    rw [integral_heightInterval_eq_intervalIntegral _ _ _ _ _ hδ0] at hformula
    simpa using hformula
  · have hδle : δ ≤ 0 := le_of_not_ge hδ0
    have hformula := area_perturb_sub_eq_integral_activeSliceLength
      hE H i hSide R ε₀ M 0 δ hδle hzero hδε₀ hBound
      (fun x hx ↦ by
        have hxb := mem_heightInterval_bounds hx
        linarith)
      (fun x hx ↦ by
        apply hregular
        have hxb := mem_heightInterval_bounds hx
        rw [abs_le]
        constructor <;> linarith [le_abs_self δ, neg_le_abs δ])
    rw [integral_heightInterval_eq_intervalIntegral _ _ _ _ _ hδle] at hformula
    simp only [add_zero] at hformula
    rw [intervalIntegral.integral_symm] at hformula
    linarith

lemma area_perturb_remainder_le {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ M ρ : ℝ)
    (hε₀ : 0 < ε₀) (hρ : 0 < ρ) (hM : (H i).height + ε₀ ≤ M)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R)
    (hstable : ∀ x, |x - (H i).height| ≤ ρ →
      noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible (H i).angle (auxiliaryHalfPlaneFamily H i M) P x ↔
            parallelCellFeasible (H i).angle (auxiliaryHalfPlaneFamily H i M) P
              (H i).height)) :
    ∀ δ : ℝ, |δ| ≤ min ε₀ ρ →
      |ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) -
          activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R
            (H i).height * δ| ≤
        (((activeBooleanPatterns E i).card : ℝ) *
          (2 * slopeBound (H i).angle (auxiliaryHalfPlaneFamily H i M))) * δ ^ 2 := by
  intro δ hδ
  let a := (H i).angle
  let h := (H i).height
  let G := frozenActiveSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R h
  let L := ((activeBooleanPatterns E i).card : ℝ) *
    (2 * slopeBound a (auxiliaryHalfPlaneFamily H i M))
  have hδρ : |δ| ≤ ρ := hδ.trans (min_le_right _ _)
  have harea := area_perturb_sub_eq_intervalIntegral_activeSliceLength
    hE H i hSide R ε₀ M ρ hε₀ hρ hM hBound (fun x hx ↦ (hstable x hx).1) δ hδ
  have hGh : activeSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R h = G h := by
    apply activeSliceLength_eq_frozen_of_stable
    intro P
    rfl
  have hFG : (∫ x in h..h + δ,
      activeSliceLength a E (auxiliaryHalfPlaneFamily H i M) i R x) =
      ∫ x in h..h + δ, G x := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply activeSliceLength_eq_frozen_of_stable
    apply (hstable x ?_).2
    rw [abs_le]
    rcases Set.mem_uIcc.mp hx with hx | hx <;>
      constructor <;> linarith [le_abs_self δ, neg_le_abs δ]
  rw [show (H i).angle = a by rfl, show (H i).height = h by rfl] at harea ⊢
  rw [hFG] at harea
  rw [hGh]
  have hGint : IntervalIntegrable G MeasureTheory.volume h (h + δ) :=
    (continuous_frozenActiveSliceLength a E
      (auxiliaryHalfPlaneFamily H i M) i R h).intervalIntegrable h (h + δ)
  have hcint : IntervalIntegrable (fun _ : ℝ ↦ G h) MeasureTheory.volume h (h + δ) :=
    continuous_const.intervalIntegrable h (h + δ)
  have hremainder :
      ClassicalResults.area (perturbNefHeight E H i δ) -
          ClassicalResults.area (perturbNefHeight E H i 0) - G h * δ =
        ∫ x in h..h + δ, (G x - G h) := by
    rw [intervalIntegral.integral_sub hGint hcint,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    rw [← harea]
    ring
  have hL : 0 ≤ L :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (by norm_num) (slopeBound_nonneg _ _))
  rw [hremainder, ← Real.norm_eq_abs]
  calc
    ‖∫ x in h..h + δ, (G x - G h)‖ ≤ (L * |δ|) * |(h + δ) - h| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs]
      calc
        |G x - G h| ≤ L * |x - h| := by
          exact abs_frozenActiveSliceLength_sub_le a E
            (auxiliaryHalfPlaneFamily H i M) i R h x h
        _ ≤ L * |δ| := by
          apply mul_le_mul_of_nonneg_left _ hL
          rw [abs_le]
          rcases Set.mem_uIoc.mp hx with hx | hx <;>
            constructor <;> linarith [le_abs_self δ, neg_le_abs δ]
    _ = L * δ ^ 2 := by
      rw [show (h + δ) - h = δ by ring]
      calc
        L * |δ| * |δ| = L * |δ| ^ 2 := by ring
        _ = L * δ ^ 2 := by rw [sq_abs]
    _ = (((activeBooleanPatterns E i).card : ℝ) *
          (2 * slopeBound a (auxiliaryHalfPlaneFamily H i M))) * δ ^ 2 := rfl

end MovingSofa.Nef
