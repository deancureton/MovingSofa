import MovingSofa.Curve.Jordan.Area
import MovingSofa.Curve.Jordan.Interior
import MovingSofa.Curve.Jordan.WindingKernel
import MovingSofa.Curve.Jordan.WindingLifts
import MovingSofa.Curve.NullRange
import MovingSofa.Curve.StieltjesChainRule
import MovingSofa.Classical.Area
import MovingSofa.ForMathlib.Analysis.SpecialFunctions.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem windingKernel_disk_integral (R : ℝ) (hR : 0 < R) (z : Point) (hz : ‖z‖ < R) :
    Integrable (windingKernel z) (volume.restrict (Metric.ball 0 R)) ∧
    (∀ i : Fin 2, Integrable (fun p ↦ windingKernel z p i)
      (volume.restrict (Metric.ball 0 R))) ∧
    (∫ p in Metric.ball 0 R, ‖windingKernel z p‖) ≤ 4 * Real.pi * R ∧
    (∫ p in Metric.ball 0 R, windingKernel z p) = Real.pi • z := by
  have hInt := integrableOn_windingKernel_ball R z hz
  exact ⟨hInt, fun i ↦ by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp hInt,
    setIntegral_norm_windingKernel_ball_le R hR z hz,
    setIntegral_windingKernel_ball R z hz⟩

theorem jordanBV_winding_integral (a b : ℝ) (hab : a < b) (x : ContinuousBVPaths a b)
    (hclosed : x.val ⟨a, le_rfl, hab.le⟩ = x.val ⟨b, hab.le, le_rfl⟩)
    (hinj : Set.InjOn x.val {t | (t : ℝ) < b}) :
    volume (Set.range x.val) = 0 ∧
    (∀ p ∉ Set.range x.val,
      (∀ i : Fin 2, Continuous (fun t ↦ windingKernel (x.val t) p i) ∧
        ∃ C : ℝ, ∀ t, |windingKernel (x.val t) p i| ≤ C) ∧
      2 * Real.pi * curveWinding hab.le x.val p =
        intervalStieltjesIntegral (continuousBVCoordinate x 1)
          (fun t ↦ windingKernel (x.val t) p 0) Set.univ -
        intervalStieltjesIntegral (continuousBVCoordinate x 0)
          (fun t ↦ windingKernel (x.val t) p 1) Set.univ) ∧
    (∀ p ∉ Set.range x.val, ∃ U : Set Point, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, q ∉ Set.range x.val ∧
        curveWinding hab.le x.val q = curveWinding hab.le x.val p) ∧
    (∀ p ∉ Set.range x.val,
      ¬Bornology.IsBounded (connectedComponentIn (Set.range x.val)ᶜ p) →
      curveWinding hab.le x.val p = 0) := by
  refine ⟨x.volume_range_eq_zero_of_injOn hab.le hinj, ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨fun i ↦ windingKernel_coord_continuous_bounded x.property.1 hp i, ?_⟩
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_avoids hab x.property.1 hp
    have hnormpos : ∀ t, 0 < ‖x.val t - p‖ := by
      intro t
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      exact hp ⟨t, h⟩
    have : Nonempty (Set.Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
    obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty)
      ((x.property.1.sub continuous_const).norm).continuousOn
    set m : ℝ := ‖x.val t₀ - p‖ with hmdef
    have hmpos : 0 < m := hnormpos t₀
    have hmle : ∀ t, m ≤ ‖x.val t - p‖ := fun t ↦ ht₀ (Set.mem_univ t)
    obtain ⟨δ₀, hδ₀, hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous x.property.1) (m / 2) (by linarith)
    have hclose : ∀ t u : Set.Icc a b, |(u : ℝ) - (t : ℝ)| < δ₀ →
        ‖x.val u - x.val t‖ < m / 2 := by
      intro t u hlt
      have hd : dist u t < δ₀ := by
        rw [Subtype.dist_eq, Real.dist_eq]; exact hlt
      simpa only [dist_eq_norm] using hmod hd
    set D : Point → Fin 2 → ℝ := fun z ↦ ![windingKernel z p 1, windingKernel z p 0] with hDdef
    have hD0 : ∀ z, D z 0 = windingKernel z p 1 := fun z ↦ rfl
    have hD1 : ∀ z, D z 1 = windingKernel z p 0 := fun z ↦ rfl
    have hDcont : ∀ i, Continuous (fun t ↦ D (x.val t) i) := by
      intro i
      fin_cases i
      · show Continuous (fun t ↦ D (x.val t) 0)
        simpa only [hD0] using (windingKernel_coord_continuous_bounded x.property.1 hp 1).1
      · show Continuous (fun t ↦ D (x.val t) 1)
        simpa only [hD1] using (windingKernel_coord_continuous_bounded x.property.1 hp 0).1
    have hcoordsub : ∀ (v w : Point) (i : Fin 2), (v - w) i = v i - w i := by
      intro v w i; simp
    have hkey : ∀ t u : Set.Icc a b, (t : ℝ) ≤ (u : ℝ) → (u : ℝ) - (t : ℝ) < δ₀ →
        |θ u - θ t -
          (D (x.val t) 1 * (x.val u 1 - x.val t 1) -
            D (x.val t) 0 * (x.val u 0 - x.val t 0))| ≤
          6 / m ^ 2 * ‖x.val u - x.val t‖ ^ 2 := by
      intro t u htu hlt
      have hnwpos : 0 < ‖x.val t - p‖ := hnormpos t
      have hnw2 : ‖x.val t - p‖ ^ 2 = (x.val t - p) 0 ^ 2 + (x.val t - p) 1 ^ 2 :=
        Point.norm_sq_eq _
      have hnd2 : ‖x.val u - x.val t‖ ^ 2 =
          (x.val u - x.val t) 0 ^ 2 + (x.val u - x.val t) 1 ^ 2 := Point.norm_sq_eq _
      have hndlt : ‖x.val u - x.val t‖ < m / 2 :=
        hclose t u (by rw [abs_of_nonneg (by linarith)]; exact hlt)
      have hsmall : 2 * ‖x.val u - x.val t‖ ≤ ‖x.val t - p‖ := by
        have := hmle t; linarith
      have hposdot : ∀ s : Set.Icc a b, (t : ℝ) ≤ (s : ℝ) → (s : ℝ) ≤ (u : ℝ) →
          0 < (x.val t - p) 0 * (x.val s - p) 0 + (x.val t - p) 1 * (x.val s - p) 1 := by
        intro s hts hsu
        have hds : ‖x.val s - x.val t‖ < m / 2 :=
          hclose t s (by rw [abs_of_nonneg (by linarith)]; linarith)
        have hdot := Point.abs_inner_coords_le (x.val t - p) (x.val s - x.val t)
        have he0 : (x.val s - p) 0 = (x.val t - p) 0 + (x.val s - x.val t) 0 := by
          rw [hcoordsub, hcoordsub, hcoordsub]; ring
        have he1 : (x.val s - p) 1 = (x.val t - p) 1 + (x.val s - x.val t) 1 := by
          rw [hcoordsub, hcoordsub, hcoordsub]; ring
        rw [he0, he1]
        have hmt := hmle t
        have hnn := norm_nonneg (x.val s - x.val t)
        nlinarith [abs_le.mp hdot, hnw2]
      have hangle := hθ.sub_eq_arctan_of_dot_pos x.property.1 htu hposdot
      have hest := Real.abs_arctan_div_sub_le_of_small (w0 := (x.val t - p) 0)
        (w1 := (x.val t - p) 1) (d0 := (x.val u - x.val t) 0)
        (d1 := (x.val u - x.val t) 1) (nw := ‖x.val t - p‖)
        (nd := ‖x.val u - x.val t‖) hnwpos hnw2 (norm_nonneg _) hnd2 hsmall
      have he0 : (x.val u - p) 0 = (x.val t - p) 0 + (x.val u - x.val t) 0 := by
        rw [hcoordsub, hcoordsub, hcoordsub]; ring
      have he1 : (x.val u - p) 1 = (x.val t - p) 1 + (x.val u - x.val t) 1 := by
        rw [hcoordsub, hcoordsub, hcoordsub]; ring
      have harg :
          ((x.val t - p) 0 * (x.val u - x.val t) 1 -
              (x.val t - p) 1 * (x.val u - x.val t) 0) /
            (‖x.val t - p‖ ^ 2 +
              ((x.val t - p) 0 * (x.val u - x.val t) 0 +
                (x.val t - p) 1 * (x.val u - x.val t) 1)) =
          ((x.val t - p) 0 * (x.val u - p) 1 - (x.val t - p) 1 * (x.val u - p) 0) /
            ((x.val t - p) 0 * (x.val u - p) 0 + (x.val t - p) 1 * (x.val u - p) 1) := by
        have hquot : ∀ A B C E : ℝ,
            (A * E - B * C) / (A ^ 2 + B ^ 2 + (A * C + B * E)) =
              (A * (B + E) - B * (A + C)) / (A * (A + C) + B * (B + E)) := by
          intro A B C E
          congr 1 <;> ring
        rw [hnw2, he0, he1]
        exact hquot _ _ _ _
      rw [harg, ← hangle] at hest
      have hlin : D (x.val t) 1 * (x.val u 1 - x.val t 1) -
          D (x.val t) 0 * (x.val u 0 - x.val t 0) =
          ((x.val t - p) 0 * (x.val u - x.val t) 1 -
            (x.val t - p) 1 * (x.val u - x.val t) 0) / ‖x.val t - p‖ ^ 2 := by
        have hne : ‖x.val t - p‖ ≠ 0 := ne_of_gt hnwpos
        rw [hD0, hD1]
        simp only [windingKernel, PiLp.smul_apply, smul_eq_mul, hcoordsub]
        field_simp
      rw [hlin]
      refine hest.trans ?_
      have hmsq : m ^ 2 ≤ ‖x.val t - p‖ ^ 2 := by
        have := hmle t; nlinarith
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) hmsq
    have hchain := ContinuousBVPaths.stieltjes_chain_rule_of_local_quadratic_remainder
      hab.le x x.boundedVariationOn θ D hDcont (by positivity) hδ₀ hkey
    simp only [hD0, hD1] at hchain
    rw [hθ.curveWinding_eq hab.le, ← hchain]
    have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
    field_simp
  · intro p hp
    exact curveWinding_locally_constant_on_compl_range hab.le x.property.1 hclosed hp
  · intro p hp hub
    exact curveWinding_eq_zero_of_unbounded_component hab.le x.property.1 hclosed hp hub

/-- Joint measurability of the winding kernel along a continuous path. -/
private theorem measurable_windingKernel_prod {a b : ℝ} (x : ContinuousBVPaths a b) :
    Measurable fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1 := by
  have h1 : Measurable fun q : Point × Set.Icc a b ↦ x.val q.2 - q.1 :=
    (x.property.1.measurable.comp measurable_snd).sub measurable_fst
  have h2 : Measurable fun q : Point × Set.Icc a b ↦
      (‖x.val q.2 - q.1‖ ^ 2)⁻¹ • (x.val q.2 - q.1) :=
    Measurable.smul ((h1.norm.pow_const 2).inv) h1
  exact h2

/-- The winding kernel of a path is product-integrable against area on an enclosing disk
and any finite measure in the time variable. -/
private theorem integrable_windingKernel_prod {a b : ℝ} (x : ContinuousBVPaths a b)
    {R : ℝ} (hR : 0 < R) (hxR : ∀ t, ‖x.val t‖ < R)
    (ν : Measure (Set.Icc a b)) [IsFiniteMeasure ν] :
    Integrable (fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1)
      ((volume.restrict (Metric.ball (0 : Point) R)).prod ν) := by
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hmeas := measurable_windingKernel_prod x
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hbound : ∀ t : Set.Icc a b,
      (∫⁻ p, ‖windingKernel (x.val t) p‖ₑ ∂(volume.restrict (Metric.ball (0 : Point) R)))
        ≤ ENNReal.ofReal (4 * Real.pi * R) := by
    intro t
    obtain ⟨hint, -, hnorm, -⟩ := windingKernel_disk_integral R hR (x.val t) (hxR t)
    rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
    exact ENNReal.ofReal_le_ofReal hnorm
  rw [HasFiniteIntegral, lintegral_prod_symm _ hmeas.enorm.aemeasurable]
  calc
    (∫⁻ t, ∫⁻ p, ‖windingKernel (x.val t) p‖ₑ
        ∂(volume.restrict (Metric.ball (0 : Point) R)) ∂ν)
        ≤ ∫⁻ _, ENNReal.ofReal (4 * Real.pi * R) ∂ν := lintegral_mono hbound
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top ν Set.univ)

/-- Fubini exchange between the coordinate Stieltjes measure of a continuous BV path and
planar area on an enclosing disk, evaluated through the disk mean of the winding kernel. -/
private theorem setIntegral_ball_stieltjes_windingKernel {a b : ℝ} (x : ContinuousBVPaths a b)
    {R : ℝ} (hR : 0 < R) (hxR : ∀ t, ‖x.val t‖ < R) (i j : Fin 2) :
    Integrable (fun p ↦ intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ windingKernel (x.val t) p i) Set.univ)
      (volume.restrict (Metric.ball (0 : Point) R)) ∧
    (∫ p in Metric.ball (0 : Point) R, intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ windingKernel (x.val t) p i) Set.univ) =
      Real.pi * intervalStieltjesIntegral (continuousBVCoordinate x j)
        (fun t ↦ x.val t i) Set.univ := by
  have hfinball : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Point) R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hfinvar : IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure
      (continuousBVCoordinate x j).boundedVariation
  have hfinmu : IsFiniteMeasure
      ((volume.restrict (Metric.ball (0 : Point) R)).toSignedMeasure).variation := by
    rw [Measure.variation_toSignedMeasure]
    infer_instance
  simp only [intervalStieltjesIntegral_univ]
  have hprodK : Integrable (fun q : Point × Set.Icc a b ↦ windingKernel (x.val q.2) q.1 i)
      ((volume.restrict (Metric.ball (0 : Point) R)).prod
        (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation) := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp
      (integrable_windingKernel_prod x hR hxR
        (intervalStieltjesMeasure (continuousBVCoordinate x j)).variation)
  have hintI : Integrable (fun p ↦ VectorMeasure.integral
      (intervalStieltjesMeasure (continuousBVCoordinate x j))
      (fun t ↦ windingKernel (x.val t) p i) (ContinuousLinearMap.mul ℝ ℝ))
      (volume.restrict (Metric.ball (0 : Point) R)) := by
    have hh := Integrable.integral_vectorMeasure_prod_left
      (B := ContinuousLinearMap.mul ℝ ℝ) hprodK
    simpa using hh
  refine ⟨hintI, ?_⟩
  have hinner : ∀ t : Set.Icc a b,
      (∫ p in Metric.ball (0 : Point) R, windingKernel (x.val t) p i) =
        Real.pi * x.val t i := by
    intro t
    obtain ⟨hint, -, -, heq⟩ := windingKernel_disk_integral R hR (x.val t) (hxR t)
    have hc := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hint
    rw [heq] at hc
    simpa using hc
  have hfub := VectorMeasure.integral_integral_swap
    (μ := (volume.restrict (Metric.ball (0 : Point) R)).toSignedMeasure)
    (ν := intervalStieltjesMeasure (continuousBVCoordinate x j))
    (B := ContinuousLinearMap.mul ℝ ℝ)
    (C := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (A := (ContinuousLinearMap.lsmul ℝ ℝ).flip)
    (D := ContinuousLinearMap.mul ℝ ℝ)
    (f := fun (p : Point) (t : Set.Icc a b) ↦ windingKernel (x.val t) p i)
    (by rw [Measure.variation_toSignedMeasure]; exact hprodK)
    (by intro u v w; simp; ring)
  simp only [VectorMeasure.integral_toSignedMeasure] at hfub
  rw [hfub]
  simp only [hinner]
  simpa [smul_eq_mul] using VectorMeasure.integral_fun_smul
    (μ := intervalStieltjesMeasure (continuousBVCoordinate x j))
    (B := ContinuousLinearMap.mul ℝ ℝ) Real.pi (fun t ↦ x.val t i)

theorem curveArea_eq_jordanInterior_area (a b : ℝ) (hab : a ≤ b)
    (Γ : Set Point) (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ true x.val) :
    curveAreaFunctional x = ClassicalResults.area (jordanInterior Γ) := by
  obtain ⟨hlt, hΓ, hcont, hrange, hclosed, hinj, hwind⟩ := hx
  subst hrange
  obtain ⟨U, V, hUopen, -, -, -, hUbdd, hVunbdd, -, hcover, -, -, hUcomp, hVcomp⟩ :=
    jordan_separation hΓ
  obtain ⟨hnull, hwindint, -, hext⟩ := jordanBV_winding_integral a b hlt x hclosed hinj
  have hUeq : jordanInterior (Set.range x.val) = U := by
    ext p
    simp only [jordanInterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpΓ, hpb⟩
      have hpc : p ∈ U ∪ V := by rw [hcover]; exact hpΓ
      rcases hpc with h | h
      · exact h
      · rw [hVcomp p h] at hpb
        exact absurd hpb hVunbdd
    · intro hpU
      refine ⟨?_, ?_⟩
      · have hmem : p ∈ (Set.range x.val)ᶜ := by rw [← hcover]; exact Or.inl hpU
        exact hmem
      · rw [hUcomp p hpU]
        exact hUbdd
  obtain ⟨R, hR, hxR, hUR⟩ :
      ∃ R : ℝ, 0 < R ∧ (∀ t, ‖x.val t‖ < R) ∧ U ⊆ Metric.ball (0 : Point) R := by
    have hcpt : IsCompact (Set.range x.val) := isCompact_range hcont
    obtain ⟨r, hr⟩ := (hcpt.isBounded.union hUbdd).subset_closedBall (0 : Point)
    refine ⟨max r 0 + 1, by have := le_max_right r 0; linarith, ?_, ?_⟩
    · intro t
      have h1 : x.val t ∈ Metric.closedBall (0 : Point) r :=
        hr (Set.mem_union_left _ ⟨t, rfl⟩)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      have := le_max_left r 0
      linarith
    · intro p hp
      have h1 : p ∈ Metric.closedBall (0 : Point) r := hr (Set.mem_union_right _ hp)
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      rw [Metric.mem_ball, dist_zero_right]
      have := le_max_left r 0
      linarith
  have hae : ∀ᵐ p ∂(volume : Measure Point), p ∉ Set.range x.val :=
    measure_eq_zero_iff_ae_notMem.mp hnull
  -- winding equals the indicator of the bounded component off the curve
  have hwind_eq : ∀ p ∉ Set.range x.val,
      curveWinding hab x.val p = U.indicator (fun _ ↦ (1 : ℝ)) p := by
    intro p hp
    by_cases hpU : p ∈ U
    · rw [Set.indicator_of_mem hpU]
      have hw := hwind p (by rw [hUeq]; exact hpU)
      simpa using hw
    · rw [Set.indicator_of_notMem hpU]
      have hpV : p ∈ V := by
        have hpc : p ∈ U ∪ V := by rw [hcover]; exact hp
        rcases hpc with h | h
        · exact absurd h hpU
        · exact h
      refine hext p hp ?_
      rw [hVcomp p hpV]
      exact hVunbdd
  have hArea : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
      ClassicalResults.area (jordanInterior (Set.range x.val)) := by
    have h1 : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
        ∫ p in Metric.ball (0 : Point) R, U.indicator (fun _ ↦ (1 : ℝ)) p := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [hae] with p hp _
      exact hwind_eq p hp
    rw [h1, setIntegral_indicator hUopen.measurableSet,
      Set.inter_eq_self_of_subset_right hUR, setIntegral_const, hUeq]
    simp [ClassicalResults.area, measureReal_def]
  have hFunctional : (∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p) =
      curveAreaFunctional x := by
    obtain ⟨hint01, heq01⟩ := setIntegral_ball_stieltjes_windingKernel x hR hxR 0 1
    obtain ⟨hint10, heq10⟩ := setIntegral_ball_stieltjes_windingKernel x hR hxR 1 0
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hL : (∫ p in Metric.ball (0 : Point) R, 2 * Real.pi * curveWinding hab x.val p) =
        2 * Real.pi * ∫ p in Metric.ball (0 : Point) R, curveWinding hab x.val p :=
      integral_const_mul _ _
    have hcong : (∫ p in Metric.ball (0 : Point) R, 2 * Real.pi * curveWinding hab x.val p)
        = ∫ p in Metric.ball (0 : Point) R,
            (intervalStieltjesIntegral (continuousBVCoordinate x 1)
              (fun t ↦ windingKernel (x.val t) p 0) Set.univ -
             intervalStieltjesIntegral (continuousBVCoordinate x 0)
              (fun t ↦ windingKernel (x.val t) p 1) Set.univ) := by
      refine setIntegral_congr_ae measurableSet_ball ?_
      filter_upwards [hae] with p hp _
      exact (hwindint p hp).2
    rw [hcong, integral_sub hint01 hint10, heq01, heq10] at hL
    refine mul_left_cancel₀ (ne_of_gt hpi) ?_
    rw [← hL, curveAreaFunctional]
    ring
  rw [← hFunctional, hArea]

end MovingSofa
