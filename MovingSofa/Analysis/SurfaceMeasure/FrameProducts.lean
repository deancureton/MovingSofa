import MovingSofa.Analysis.SurfaceMeasure.VertexBoundary
import MovingSofa.Analysis.SurfaceMeasure.WeightedBoundary
import MovingSofa.Analysis.Stieltjes.DensityIntegration
import MovingSofa.Analysis.Stieltjes.Frame
import MovingSofa.Analysis.Stieltjes.InnerProduct

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- The normal and tangent projections of the positive vertex, with their Stieltjes measures. -/
theorem exists_positiveVertex_frame_products
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ H P : RightContinuousIntervalBV a b,
      (∀ t, H.toFun t = inner ℝ (edgeVertices K (((t : ℝ) : Real.Angle))).1
        (normalVector (((t : ℝ) : Real.Angle)))) ∧
      (∀ t, P.toFun t = inner ℝ (edgeVertices K (((t : ℝ) : Real.Angle))).1
        (tangentVector (((t : ℝ) : Real.Angle)))) ∧
      ∀ E : Set (Icc a b), MeasurableSet E → (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure H E =
          ∫ t in (Subtype.val : Icc a b → ℝ) '' E,
            inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) ∧
        intervalStieltjesMeasure P E =
          (surfaceAreaMeasure K
              ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal -
            ∫ t in (Subtype.val : Icc a b → ℝ) '' E,
              inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) := by
  obtain ⟨v, hv, hvm⟩ := positiveVertex_stieltjes_surface K a b hab hturn
  choose n hn hnd using fun i : Fin 2 ↦ exists_normalVector_coordinate_intervalBV hab.le i
  choose τ hτ hτd using fun i : Fin 2 ↦ exists_tangentVector_coordinate_intervalBV hab.le i
  have hnc (i : Fin 2) : Continuous (n i).toFun := by
    convert ((by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin :
        Continuous (fun u : Real.Angle ↦ normalVector u i))).comp
          (Real.Angle.continuous_coe.comp continuous_subtype_val) using 1
    funext t
    exact hn i t
  have hτc (i : Fin 2) : Continuous (τ i).toFun := by
    convert ((by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos :
        Continuous (fun u : Real.Angle ↦ tangentVector u i))).comp
          (Real.Angle.continuous_coe.comp continuous_subtype_val) using 1
    funext t
    exact hτ i t
  obtain ⟨H, hH, hHm⟩ := intervalStieltjes_inner_fin_two hab.le v n hnc
  obtain ⟨P, hP, hPm⟩ := intervalStieltjes_inner_fin_two hab.le v τ hτc
  refine ⟨H, P, ?_, ?_, ?_⟩
  · intro t
    rw [hH]
    simp_rw [hv, hn]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  · intro t
    rw [hP]
    simp_rw [hv, hτ]
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply]
  · intro E hE hEa
    have hnormal := sum_intervalStieltjesIntegral_positiveVertex_normal
      K hab hturn v hvm E hE hEa
    have htangent := sum_intervalStieltjesIntegral_positiveVertex_tangent
      K hab hturn v hvm E hE hEa
    have hnfun (i : Fin 2) : (n i).toFun =
        fun t : Icc a b ↦ normalVector (((t : ℝ) : Real.Angle)) i :=
      funext (hn i)
    have hτfun (i : Fin 2) : (τ i).toFun =
        fun t : Icc a b ↦ tangentVector (((t : ℝ) : Real.Angle)) i :=
      funext (hτ i)
    have hnormal' :
        (∑ i : Fin 2, intervalStieltjesIntegral (v i) (n i).toFun E) = 0 := by
      simpa only [hnfun] using hnormal
    have htangent' :
        (∑ i : Fin 2, intervalStieltjesIntegral (v i) (τ i).toFun E) =
          (surfaceAreaMeasure K
            ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal := by
      simpa only [hτfun] using htangent
    have hfinite : IsFiniteMeasure (volume.comap (Subtype.val : Icc a b → ℝ)) :=
      ⟨by
        rw [comap_subtype_coe_apply measurableSet_Icc]
        simp only [image_univ, Subtype.range_val]
        exact measure_Icc_lt_top⟩
    let _ := hfinite
    have hsmoothN (i : Fin 2) :
        intervalStieltjesIntegral (n i) (v i).toFun E =
          ∫ t in E, (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ) :=
      intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (n i) (hnd i)
        (v i).boundedVariation E hE
    have hsmoothT (i : Fin 2) :
        intervalStieltjesIntegral (τ i) (v i).toFun E =
          ∫ t in E, (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ) :=
      intervalStieltjesIntegral_eq_integral_mul_of_density_bv hab.le (τ i) (hτd i)
        (v i).boundedVariation E hE
    have hintN (i : Fin 2) : Integrable
        (fun t : Icc a b ↦ (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i)
        (volume.comap (Subtype.val : Icc a b → ℝ)) := by
      apply (v i).boundedVariation.integrable.mul_bdd
      · exact ((by
          fin_cases i
          · exact Real.Angle.continuous_sin.neg
          · exact Real.Angle.continuous_cos :
            Continuous (fun u : Real.Angle ↦ tangentVector u i))).comp
              (Real.Angle.continuous_coe.comp continuous_subtype_val) |>.aestronglyMeasurable
      · filter_upwards with t
        fin_cases i
        · simpa [tangentVector, frame] using Real.abs_sin_le_one (t : ℝ)
        · simpa [tangentVector, frame] using Real.abs_cos_le_one (t : ℝ)
    have hintT (i : Fin 2) : Integrable
        (fun t : Icc a b ↦ (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i)
        (volume.comap (Subtype.val : Icc a b → ℝ)) := by
      apply (v i).boundedVariation.integrable.mul_bdd
      · exact ((by
          fin_cases i
          · exact Real.Angle.continuous_cos.neg
          · exact Real.Angle.continuous_sin.neg :
            Continuous (fun u : Real.Angle ↦ -normalVector u i))).comp
              (Real.Angle.continuous_coe.comp continuous_subtype_val) |>.aestronglyMeasurable
      · filter_upwards with t
        fin_cases i
        · simpa [normalVector, frame] using Real.abs_cos_le_one (t : ℝ)
        · simpa [normalVector, frame] using Real.abs_sin_le_one (t : ℝ)
    let R := (Subtype.val : Icc a b → ℝ) '' E
    have hR : MeasurableSet R :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hE
    have hRsub : R ⊆ Icc a b := by
      rintro x ⟨t, -, rfl⟩
      exact t.property
    have hpre : {t : Icc a b | (t : ℝ) ∈ R} = E :=
      Set.preimage_image_eq E Subtype.val_injective
    have hsubN :
        (∑ i : Fin 2, ∫ t in E,
          (v i).toFun t * tangentVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ)) =
          ∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (tangentVector (t : Real.Angle)) := by
      rw [Fin.sum_univ_two, ← integral_add (hintN 0).integrableOn (hintN 1).integrableOn]
      have hsubtype := integral_subtype_preimage (μ := volume) (s := Icc a b) (t := R)
        measurableSet_Icc hR
        (fun t : ℝ ↦ inner ℝ (edgeVertices K (t : Real.Angle)).1
          (tangentVector (t : Real.Angle)))
      rw [hpre, Measure.restrict_restrict_of_subset hRsub] at hsubtype
      rw [← hsubtype]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv 0 t, hv 1 t]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    have hsubT :
        (∑ i : Fin 2, ∫ t in E,
          (v i).toFun t * -normalVector (((t : ℝ) : Real.Angle)) i
            ∂volume.comap (Subtype.val : Icc a b → ℝ)) =
          -(∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) := by
      rw [Fin.sum_univ_two, ← integral_add (hintT 0).integrableOn (hintT 1).integrableOn]
      have hsubtype := integral_subtype_preimage (μ := volume) (s := Icc a b) (t := R)
        measurableSet_Icc hR
        (fun t : ℝ ↦ inner ℝ (edgeVertices K (t : Real.Angle)).1
          (normalVector (t : Real.Angle)))
      rw [hpre, Measure.restrict_restrict_of_subset hRsub] at hsubtype
      rw [← hsubtype, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with t
      rw [hv 0 t, hv 1 t]
      simp [PiLp.inner_apply, Fin.sum_univ_two]
      ring
    constructor
    · rw [hHm E hE, Finset.sum_add_distrib, hnormal']
      simp only [zero_add]
      simpa only [hsmoothN] using hsubN
    · rw [hPm E hE, Finset.sum_add_distrib, htangent']
      rw [show (∑ i : Fin 2, intervalStieltjesIntegral (τ i) (v i).toFun E) =
          -(∫ t in R, inner ℝ (edgeVertices K (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) by simpa only [hsmoothT] using hsubT]
      ring

end MovingSofa
