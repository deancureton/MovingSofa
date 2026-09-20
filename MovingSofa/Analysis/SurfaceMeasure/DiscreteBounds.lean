import MovingSofa.Analysis.SurfaceMeasure.BoundaryLimit
import MovingSofa.ForMathlib.MeasureTheory.Integral.AtomicBounds

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The integral of tangent vectors gives the increment of the positive supporting vertex. -/
theorem integral_tangentVector_surfaceAreaMeasure (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b,
      tangentVector u ∂surfaceAreaMeasure K) =
      (edgeVertices K (b : Real.Angle)).1 - (edgeVertices K (a : Real.Angle)).1 := by
  let A := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  ext i
  have hi := ContinuousLinearMap.integral_comp_comm
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
  change (∫ u in A, tangentVector u i ∂surfaceAreaMeasure K) =
    (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) i at hi
  rw [← hi]
  exact (positiveVertex_sub_eq_integral K hab hturn i).symm

/-- The projected boundary integral computes the support value relative to the initial vertex. -/
theorem integral_inner_tangentVector_eq_support_sub (K : ConvexBody Point)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi) :
    (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s,
      inner ℝ (normalVector (s : Real.Angle)) (tangentVector u) ∂surfaceAreaMeasure K) =
      supportValue K (s : Real.Angle) -
        inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  let A := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hi := ContinuousLinearMap.integral_comp_comm
    (innerSL ℝ (normalVector (s : Real.Angle))) hu
  change (∫ u in A, inner ℝ (normalVector (s : Real.Angle)) (tangentVector u)
    ∂surfaceAreaMeasure K) = inner ℝ (normalVector (s : Real.Angle))
      (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) at hi
  rw [show (∫ u in A, tangentVector u ∂surfaceAreaMeasure K) =
      (edgeVertices K (s : Real.Angle)).1 - (edgeVertices K 0).1 from
        integral_tangentVector_surfaceAreaMeasure K hs.1 (by linarith [hs.2, Real.pi_pos]),
    inner_sub_right,
    real_inner_comm (edgeVertices K (s : Real.Angle)).1 (normalVector (s : Real.Angle)),
    (edgeVertices_fst_mem K (s : Real.Angle)).2] at hi
  exact hi

/-- Positive atomic sine contributions are bounded by the corresponding support increment. -/
theorem sum_surfaceAreaMeasure_mul_pos_sin_le (K : ConvexBody Point)
    (D : Finset ℝ) (hD : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi) :
    ∑ t ∈ D, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
      max (Real.sin (s - t)) 0 ≤ supportValue K (s : Real.Angle) -
        inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  classical
  let F := D.filter (fun t ↦ t ≤ s)
  let E := (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc 0 s
  let g : Real.Angle → ℝ :=
    fun u ↦ inner ℝ (normalVector (s : Real.Angle)) (tangentVector u)
  have hcoe : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Set.Ioc 0 s) :=
    Real.Angle.injOn_coe_Ioc (by linarith [hs.2, Real.pi_pos])
  have hE : MeasurableSet E := measurableSet_Ioc.image_of_continuousOn_injOn
    Real.Angle.continuous_coe.continuousOn hcoe
  have hF (t : ℝ) (ht : t ∈ F) : t ∈ Set.Ioc 0 s :=
    ⟨(hD t (Finset.mem_filter.mp ht).1).1, (Finset.mem_filter.mp ht).2⟩
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hgcont : Continuous g := by
    apply Continuous.inner continuous_const
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hg : IntegrableOn g E (surfaceAreaMeasure K) :=
    by
    have hall : Integrable g (surfaceAreaMeasure K) := by
      rw [← integrableOn_univ]
      exact hgcont.continuousOn.integrableOn_compact isCompact_univ
    exact hall.integrableOn
  have hgnonneg : ∀ u ∈ E, 0 ≤ g u := by
    rintro u ⟨t, ht, rfl⟩
    change 0 ≤ inner ℝ (normalVector (s : Real.Angle)) (tangentVector (t : Real.Angle))
    rw [real_inner_comm (tangentVector (t : Real.Angle)), inner_tangentVector_normalVector_real]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [ht.2], by linarith [ht.1, hs.2]⟩
  have hb := sum_measureReal_mul_le_setIntegral (surfaceAreaMeasure K)
    (F.image fun t : ℝ ↦ (t : Real.Angle)) hE
    (by rintro u hu; obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu; exact ⟨t, hF t ht, rfl⟩)
    hg hgnonneg
  rw [Finset.sum_image (fun x hx y hy hxy ↦ hcoe (hF x hx) (hF y hy) hxy)] at hb
  have heval (t : ℝ) : g (t : Real.Angle) = Real.sin (s - t) := by
    dsimp [g]
    rw [real_inner_comm (tangentVector (t : Real.Angle)), inner_tangentVector_normalVector_real]
  simp_rw [heval] at hb
  change (∑ t ∈ F, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
    Real.sin (s - t)) ≤ _ at hb
  have hsum : (∑ t ∈ D, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal *
      max (Real.sin (s - t)) 0) =
      ∑ t ∈ F, (surfaceAreaMeasure K {(t : Real.Angle)}).toReal * Real.sin (s - t) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hts : t ≤ s
    · rw [ite_eq_left hts, max_eq_left (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith, by linarith [(hD t ht).1, hs.2]⟩)]
    · have hsin : Real.sin (s - t) ≤ 0 := by
        have h := Real.sin_nonneg_of_mem_Icc
          (show t - s ∈ Set.Icc 0 Real.pi from
            ⟨by linarith, by linarith [(hD t ht).2, hs.1]⟩)
        rw [show s - t = -(t - s) by ring, Real.sin_neg]
        linarith
      rw [ite_eq_right hts, max_eq_right hsin, mul_zero]
  rw [hsum]
  exact hb.trans_eq (integral_inner_tangentVector_eq_support_sub K hs)

/-- For upper normals, the negative zero-angle vertex projects below the positive vertex. -/
theorem inner_negativeVertex_zero_le_positiveVertex (K : ConvexBody Point)
    {s : ℝ} (hs : s ∈ Set.Icc 0 Real.pi) :
    inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).2 ≤
      inner ℝ (normalVector (s : Real.Angle)) (edgeVertices K 0).1 := by
  have hy : inner ℝ (edgeVertices K 0).2 (tangentVector 0) ≤
      inner ℝ (edgeVertices K 0).1 (tangentVector 0) := by
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le ((isCompact_exposedEdge K 0).image
      (continuous_id.inner continuous_const)).bddBelow
      ⟨(edgeVertices K 0).1, edgeVertices_fst_mem K 0, rfl⟩
  have hx := (edgeVertices_fst_mem K 0).2.trans (edgeVertices_snd_mem K 0).2.symm
  simp [tangentVector, normalVector, frame, PiLp.inner_apply] at hx hy ⊢
  have hsin := Real.sin_nonneg_of_mem_Icc hs
  rw [hx]
  linarith [mul_le_mul_of_nonneg_right hy hsin]

end MovingSofa
