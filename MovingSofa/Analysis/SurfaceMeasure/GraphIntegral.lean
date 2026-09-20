import MovingSofa.Analysis.SurfaceMeasure.RegularBoundaryHelpers
import MovingSofa.ForMathlib.MeasureTheory.Integral.IntervalExhaustion

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private theorem exteriorNormalAngle_upperGraph_eq (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2)
    (hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x) :
    exteriorNormalAngle K (o + e.symm !₂[x, upperGraphHeight K o e x]) =
      vectorNormalAngle (e.symm !₂[-deriv (upperGraphHeight K o e) x, 1]) := by
  have hp := upperGraph_mem_regularBoundary K hK o e hx hdiff
  have hu := hp.2
  have hn : IsExteriorNormal K (o + e.symm !₂[x, upperGraphHeight K o e x])
      (exteriorNormalAngle K (o + e.symm !₂[x, upperGraphHeight K o e x])) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left hu]
    exact hu.exists.choose_spec
  exact hu.unique hn (upperGraph_deriv_isExteriorNormal K o e hx hdiff)

private theorem coordinate_normalVector_vectorNormalAngle_second
    (e : Point ≃ₗᵢ[ℝ] Point) (m : ℝ) :
    e (normalVector (vectorNormalAngle (e.symm !₂[-m, 1]))) 1 =
      (Real.sqrt (1 + m ^ 2))⁻¹ := by
  let q : Point := e.symm !₂[-m, 1]
  have hq : q ≠ 0 := by
    intro h
    have h1 := congrFun (congrArg WithLp.ofLp (congrArg e h)) 1
    simp [q] at h1
  rw [normalVector_vectorNormalAngle hq, map_smul, PiLp.smul_apply]
  have hnorm : ‖q‖ = Real.sqrt (1 + m ^ 2) := by
    rw [← e.norm_map q, LinearIsometryEquiv.apply_symm_apply, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
    ring
  rw [hnorm]
  simp [q]

private theorem upperGraphSurfaceIntegrand_eq_zero_of_speed_gt
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) {x : ℝ}
    (hx : ε⁻¹ < Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)) :
    upperGraphSurfaceIntegrand K o e ψ x = 0 := by
  rw [upperGraphSurfaceIntegrand, hsupport, zero_mul]
  rw [coordinate_normalVector_vectorNormalAngle_second]
  exact (inv_lt_comm₀ (Real.sqrt_pos.2 (by positivity)) hε).2 hx

private theorem measurable_vectorNormalAngle : Measurable vectorNormalAngle := by
  unfold vectorNormalAngle
  apply Real.Angle.continuous_coe.measurable.comp
  apply Complex.measurable_arg.comp
  have hp0 : Measurable (fun p : Point ↦ p 0) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 0).continuous.measurable
  have hp1 : Measurable (fun p : Point ↦ p 1) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) 1).continuous.measurable
  have h0 : Measurable (fun p : Point ↦ (p 0 : ℂ)) :=
    Complex.measurable_ofReal.comp hp0
  have h1 : Measurable (fun p : Point ↦ (p 1 : ℂ)) :=
    Complex.measurable_ofReal.comp hp1
  convert h0.add (h1.mul_const Complex.I) using 1
  funext p
  apply Complex.ext <;> simp

private theorem measurable_upperGraphSurfaceIntegrand (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) :
    Measurable (upperGraphSurfaceIntegrand K o e ψ) := by
  unfold upperGraphSurfaceIntegrand
  have hd : Measurable (deriv (upperGraphHeight K o e)) := measurable_deriv _
  have hv : Measurable (fun x ↦ e.symm !₂[-deriv (upperGraphHeight K o e) x, 1]) := by
    fun_prop
  apply (hψ.measurable.comp (measurable_vectorNormalAngle.comp ?_)).mul
    ((measurable_const.add (hd.pow_const 2)).sqrt)
  exact hv

/-- A normal support cutoff gives a uniform bound on the weighted graph density. -/
theorem norm_upperGraphSurfaceIntegrand_le
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) {ε M : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0)
    (hM : ∀ t, ‖ψ t‖ ≤ M) (x : ℝ) :
    ‖upperGraphSurfaceIntegrand K o e ψ x‖ ≤ M * ε⁻¹ := by
  have hM0 : 0 ≤ M := (norm_nonneg (ψ 0)).trans (hM 0)
  let s := Real.sqrt (1 + (deriv (upperGraphHeight K o e) x) ^ 2)
  by_cases hs : s ≤ ε⁻¹
  · rw [upperGraphSurfaceIntegrand, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul (hM _) hs (Real.sqrt_nonneg _) hM0
  · rw [upperGraphSurfaceIntegrand_eq_zero_of_speed_gt K o e ψ hε hsupport
      (lt_of_not_ge hs), norm_zero]
    exact mul_nonneg hM0 (le_of_lt (inv_pos.mpr hε))

/-- The weighted surface integrand of an upper graph is integrable on its
horizontal projection interval. -/
theorem integrable_upperGraphSurfaceIntegrand (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) (a b : ℝ) :
    Integrable (upperGraphSurfaceIntegrand K o e ψ) (volume.restrict (Set.Icc a b)) := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ t‖
  have hM (u : Real.Angle) : ‖ψ u‖ ≤ M := ht trivial
  apply (integrable_const (μ := volume.restrict (Set.Icc a b))
    (c := M * ε⁻¹)).mono'
    (measurable_upperGraphSurfaceIntegrand K o e ψ hψ).aestronglyMeasurable
  exact Eventually.of_forall fun x ↦
    norm_upperGraphSurfaceIntegrand_le K o e ψ hε hsupport hM x

private theorem upperCoordinateGraph_mem_frontier (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    o + e.symm !₂[x, upperGraphHeight K o e x] ∈ frontier (K : Set Point) := by
  have hxproj : x ∈ horizontalProjection K o e := by
    rw [horizontalProjection_eq_Icc]
    exact hx
  let p := o + e.symm !₂[x, upperGraphHeight K o e x]
  have hpK : p ∈ K := upperGraphHeight_mem K o e hxproj
  rw [mem_frontier_iff_notMem_interior hpK]
  intro hpint
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let q := p + (r / 2) • e.symm !₂[0, 1]
  have hqp : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - p = (r / 2) • e.symm !₂[0, 1] by simp [q], norm_smul,
      e.symm.norm_map, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, Real.norm_eq_abs]
    rw [abs_of_pos hr]
    linarith))
  have hqfiber : o + e.symm !₂[x, upperGraphHeight K o e x + r / 2] ∈ K := by
    convert hqp using 1
    apply e.injective
    ext i
    fin_cases i
    · simp [p, q, map_add, map_smul]
    · simp [p, q, map_add, map_smul]
      ring
  have hle := (upperGraphHeight_isGreatest K o e hxproj).2 hqfiber
  linarith

private def upperGraphWeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (p : Point) : ℝ :=
  ψ (vectorNormalAngle (e.symm !₂[
    -deriv (upperGraphHeight K o e) (e (p - o) 0), 1]))

private theorem measurable_upperGraphWeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) :
    Measurable (upperGraphWeight K o e ψ) := by
  unfold upperGraphWeight
  apply hψ.measurable.comp (measurable_vectorNormalAngle.comp ?_)
  have hx : Measurable (fun p : Point ↦ e (p - o) 0) := by fun_prop
  have hd : Measurable (fun p : Point ↦
      deriv (upperGraphHeight K o e) (e (p - o) 0)) :=
    (measurable_deriv _).comp hx
  fun_prop

private theorem integral_restrict_upperCoordinateGraph_eq_integral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {a b : ℝ}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆
      Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc a b)) =
      ∫ x in a..b, upperGraphSurfaceIntegrand K o e ψ x := by
  have hlocal : LocallyLipschitzOn (Set.Icc a b) (upperGraphHeight K o e) :=
    (locallyLipschitzOn_upperGraphHeight K o e).mono hsub
  obtain ⟨C, hC⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_Icc hlocal
  rw [MeasureTheory.integral_restrict_coordinateGraph_eq_integral_sqrt_mul hab hC o e
    (measurable_upperGraphWeight K o e ψ hψ)]
  apply intervalIntegral.integral_congr
  intro x _
  unfold upperGraphWeight upperGraphSurfaceIntegrand
  simp
  apply mul_comm

private theorem integral_restrict_upperCoordinateGraph_eq_setIntegral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {a b : ℝ}
    (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆
      Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc a b)) =
      ∫ x in Set.Icc a b, upperGraphSurfaceIntegrand K o e ψ x := by
  rw [integral_restrict_upperCoordinateGraph_eq_integral K o e ψ hψ hab hsub,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]

private theorem upperCoordinateGraph_image_subset_frontier (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) {s : Set ℝ}
    (hs : s ⊆ Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2) :
    (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) '' s ⊆
      frontier (K : Set Point) := by
  rintro _ ⟨x, hx, rfl⟩
  exact upperCoordinateGraph_mem_frontier K o e (hs hx)

private theorem hausdorffMeasure_upperGraph_endpoints_eq_zero (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ)) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  apply Set.Finite.measure_zero
  exact (Set.toFinite _).image _

private theorem eventually_innerIcc_nonempty {a b : ℝ} (hab : a < b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      a + 1 / ((n : ℝ) + 1) ≤ b - 1 / ((n : ℝ) + 1) := by
  have hevent := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (Iio_mem_nhds (half_pos (sub_pos.mpr hab)))
  exact hevent.mono fun n hn ↦ by linarith

/-- Integrals over the inner upper graph equal integrals over its coordinate interval. -/
theorem eventually_integral_innerUpperGraph_eq_innerIcc
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    (hwidth : (horizontalBounds K o e).1 < (horizontalBounds K o e).2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
        ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)))) =
        ∫ x in Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)),
          upperGraphSurfaceIntegrand K o e ψ x := by
  filter_upwards [eventually_innerIcc_nonempty hwidth] with n hn
  exact integral_restrict_upperCoordinateGraph_eq_setIntegral K o e ψ hψ hn
    (innerIcc_subset_Ioo _ _ n)

private theorem measurableSet_innerUpperGraph (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) (n : ℕ) :
    MeasurableSet
      ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))) := by
  let s := Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
    ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
  have hs : s ⊆ Set.Ioo (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := innerIcc_subset_Ioo _ _ n
  have hcont : ContinuousOn (upperGraphHeight K o e) s :=
    ((locallyLipschitzOn_upperGraphHeight K o e).mono hs).continuousOn
  exact (isCompact_Icc.image_of_continuousOn (by fun_prop)).measurableSet

private theorem tendsto_innerUpperGraph_indicator_at_regularPoint
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) {p : Point}
    (hp : p ∈ regularBoundary K)
    (hpend : p ∉ (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
      ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ))
    (hpirr : p ∉ irregularUpperGraph K o e) :
    Filter.Tendsto (fun n : ℕ ↦
      (((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))).indicator
            (upperGraphWeight K o e ψ) p)) Filter.atTop
      (nhds (ψ (exteriorNormalAngle K p))) := by
  let a := exteriorNormalAngle K p
  have ha : IsExteriorNormal K p a := by
    dsimp only [a]
    unfold exteriorNormalAngle
    rw [dite_eq_left hp.2]
    exact hp.2.exists.choose_spec
  have hpK : p ∈ K := by
    show p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp.1
  by_cases hψa : ψ a = 0
  · apply tendsto_const_nhds.congr'
    filter_upwards [] with n
    by_cases hpn : p ∈ (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
          ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
    · obtain ⟨x, hx, rfl⟩ := hpn
      have hxint := innerIcc_subset_Ioo (horizontalBounds K o e).1
        (horizontalBounds K o e).2 n hx
      have hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x := by
        by_contra hndiff
        exact hpirr ⟨x, ⟨hxint, hndiff⟩, rfl⟩
      have hmem : (o + e.symm !₂[x, upperGraphHeight K o e x]) ∈
          (fun y ↦ o + e.symm !₂[y, upperGraphHeight K o e y] : ℝ → Point) ''
            Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
              ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)) := ⟨x, hx, rfl⟩
      rw [Set.indicator_of_mem hmem]
      unfold upperGraphWeight
      simp
      rw [← exteriorNormalAngle_upperGraph_eq K hK o e hxint hdiff]
    · change ψ a = _
      rw [Set.indicator]
      simp only [hpn, ↓reduceIte]
      exact hψa
  · have hcoord : ε ≤ e (normalVector a) 1 := by
      apply le_of_not_gt
      exact fun h ↦ hψa (hsupport a h)
    have hpos : 0 < e (normalVector a) 1 := hε.trans_le hcoord
    have hgraph := eq_upperCoordinateGraph_of_isExteriorNormal_of_pos K o e hpK ha hpos
    let x := e (p - o) 0
    have hxproj : x ∈ horizontalProjection K o e := ⟨p, hpK, rfl⟩
    have hxIcc : x ∈ Set.Icc (horizontalBounds K o e).1
        (horizontalBounds K o e).2 := by
      rw [← horizontalProjection_eq_Icc]
      exact hxproj
    have hxneleft : x ≠ (horizontalBounds K o e).1 := by
      intro hx
      apply hpend
      refine ⟨x, by simp [hx], ?_⟩
      exact hgraph.symm
    have hxneright : x ≠ (horizontalBounds K o e).2 := by
      intro hx
      apply hpend
      refine ⟨x, by simp [hx], ?_⟩
      exact hgraph.symm
    have hxint : x ∈ Set.Ioo (horizontalBounds K o e).1
        (horizontalBounds K o e).2 :=
      ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxneleft), lt_of_le_of_ne hxIcc.2 hxneright⟩
    have hdiff : DifferentiableAt ℝ (upperGraphHeight K o e) x := by
      by_contra hndiff
      apply hpirr
      refine ⟨x, ⟨hxint, hndiff⟩, ?_⟩
      exact hgraph.symm
    have hweight : upperGraphWeight K o e ψ p = ψ a := by
      unfold upperGraphWeight
      dsimp only [x]
      have haeq : a = vectorNormalAngle
          (e.symm !₂[-deriv (upperGraphHeight K o e) (e (p - o) 0), 1]) := by
        have he := exteriorNormalAngle_upperGraph_eq K hK o e hxint hdiff
        dsimp only [x] at he
        calc
          a = exteriorNormalAngle K p := rfl
          _ = exteriorNormalAngle K
              (o + e.symm !₂[e (p - o) 0, upperGraphHeight K o e (e (p - o) 0)]) :=
            congrArg (exteriorNormalAngle K) hgraph
          _ = _ := he
      rw [haeq]
    have hev := eventually_mem_innerIcc_of_mem_Ioo hxint
    apply tendsto_const_nhds.congr'
    exact hev.mono fun n hn ↦ by
      have hmem : p ∈ (fun y ↦ o + e.symm !₂[y, upperGraphHeight K o e y] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)) := ⟨x, hn, hgraph.symm⟩
      change ψ (exteriorNormalAngle K p) = _
      simp only [Set.indicator, hmem, ↓reduceIte, hweight]
      rfl

/-- Weighted integrals over compact inner upper graphs converge to the weighted
integral over the full frontier. -/
theorem tendsto_integral_innerUpperGraph
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ) (hψ : Continuous ψ)
    {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    Filter.Tendsto (fun n : ℕ ↦
      ∫ p, upperGraphWeight K o e ψ p ∂(Measure.hausdorffMeasure 1).restrict
        ((fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
          Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
            ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1)))) Filter.atTop
      (nhds (∫ p in frontier (K : Set Point), ψ (exteriorNormalAngle K p)
        ∂Measure.hausdorffMeasure 1)) := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let t := frontier (K : Set Point)
  let g : ℕ → Set Point := fun n ↦
    (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
      Set.Icc ((horizontalBounds K o e).1 + 1 / ((n : ℝ) + 1))
        ((horizontalBounds K o e).2 - 1 / ((n : ℝ) + 1))
  obtain ⟨u, -, hu⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ u‖
  have hM (v : Real.Angle) : ‖ψ v‖ ≤ M := hu trivial
  have hM0 : 0 ≤ M := norm_nonneg _
  have hgt (n : ℕ) : g n ⊆ t :=
    upperCoordinateGraph_image_subset_frontier K o e
      ((innerIcc_subset_Ioo _ _ n).trans Set.Ioo_subset_Icc_self)
  have hgmeas (n : ℕ) : MeasurableSet (g n) := measurableSet_innerUpperGraph K o e n
  have hFmeas (n : ℕ) : AEStronglyMeasurable
      ((g n).indicator (upperGraphWeight K o e ψ)) μ :=
    (measurable_upperGraphWeight K o e ψ hψ).aestronglyMeasurable.indicator (hgmeas n)
  have hbound (n : ℕ) : ∀ᵐ p ∂μ,
      ‖(g n).indicator (upperGraphWeight K o e ψ) p‖ ≤ t.indicator (fun _ ↦ M) p :=
    Filter.Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ g n
      · have hpt := hgt n hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpt]
        exact hM _
      · rw [Set.indicator]
        simp only [hp, ↓reduceIte, norm_zero]
        by_cases hpt : p ∈ t <;> simp [hpt, hM0]
  have hboundInt : Integrable (t.indicator fun _ ↦ M) μ := by
    apply MeasureTheory.IntegrableOn.integrable_indicator
    · exact MeasureTheory.integrableOn_const
        (lt_top_iff_ne_top.mp (K.hausdorffMeasure_frontier_lt_top hK))
    · exact measurableSet_frontier
  have hae : t =ᵐ[μ] regularBoundary K := by
    rw [ae_eq_set]
    exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hK,
      measure_mono_null (fun _ hp ↦ (hp.2 hp.1.1).elim) measure_empty⟩
  have hpreg : ∀ᵐ p ∂μ, p ∈ t → p ∈ regularBoundary K := by
    filter_upwards [hae] with p hp
    exact fun hpt ↦ hp.mp hpt
  have hpend : ∀ᵐ p ∂μ, p ∉
      (fun x ↦ o + e.symm !₂[x, upperGraphHeight K o e x] : ℝ → Point) ''
        ({(horizontalBounds K o e).1, (horizontalBounds K o e).2} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp (hausdorffMeasure_upperGraph_endpoints_eq_zero K o e)
  have hpirr : ∀ᵐ p ∂μ, p ∉ irregularUpperGraph K o e :=
    measure_eq_zero_iff_ae_notMem.mp (hausdorffMeasure_irregularUpperGraph_eq_zero K o e)
  have hlim : ∀ᵐ p ∂μ, Filter.Tendsto
      (fun n ↦ (g n).indicator (upperGraphWeight K o e ψ) p) Filter.atTop
      (nhds (t.indicator (fun p ↦ ψ (exteriorNormalAngle K p)) p)) := by
    filter_upwards [hpreg, hpend, hpirr] with p hpreg hpend hpirr
    by_cases hpt : p ∈ t
    · rw [Set.indicator_of_mem hpt]
      exact tendsto_innerUpperGraph_indicator_at_regularPoint K hK o e ψ hε hsupport
        (hpreg hpt) hpend hpirr
    · simp only [Set.indicator, hpt, ↓reduceIte]
      apply tendsto_const_nhds.congr'
      filter_upwards [] with n
      have hpgn : p ∉ g n := fun h ↦ hpt (hgt n h)
      simp [hpgn]
  have ht := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := μ)
    (t.indicator fun _ ↦ M) hFmeas hboundInt hbound hlim
  have htarget : (∫ p, t.indicator (fun p ↦ ψ (exteriorNormalAngle K p)) p ∂μ) =
      ∫ p in t, ψ (exteriorNormalAngle K p) ∂μ := by
    rw [MeasureTheory.integral_indicator measurableSet_frontier]
  rw [← htarget]
  simpa only [μ, g, MeasureTheory.integral_indicator, hgmeas] using ht

/-- A planar convex body with nonempty interior has distinct horizontal bounds
in every isometric coordinate frame. -/
theorem horizontalBounds_lt_of_interior_nonempty (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 < (horizontalBounds K o e).2 := by
  obtain ⟨z, hz⟩ := hK
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let v := e.symm (normalVector 0)
  let q := z + (ε / 2) • v
  have hq : q ∈ K := interior_subset (hball (by
    rw [Metric.mem_ball, dist_eq_norm]
    rw [show q - z = (ε / 2) • v by simp [q], norm_smul]
    simp only [v, e.symm.norm_map, norm_normalVector, mul_one, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    linarith))
  have hzI : e (z - o) 0 ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc]
    exact ⟨z, interior_subset hz, rfl⟩
  have hqI : e (q - o) 0 ∈ Set.Icc (horizontalBounds K o e).1
      (horizontalBounds K o e).2 := by
    rw [← horizontalProjection_eq_Icc]
    exact ⟨q, hq, rfl⟩
  have hcoord : e (q - o) 0 = e (z - o) 0 + ε / 2 := by
    rw [show q - o = (z - o) + (ε / 2) • v by simp [q]; module]
    simp [v, normalVector, frame]
  linarith [hzI.1, hqI.2]


end MovingSofa
