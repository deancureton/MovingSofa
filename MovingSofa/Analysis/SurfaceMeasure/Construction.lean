import MovingSofa.Analysis.SurfaceMeasure.GraphIntegral

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem surfaceAreaMeasure_construction (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) ∧
    ((K : Set Point).Subsingleton → surfaceAreaMeasure K = 0) ∧
    (∀ d, IsSegmentPresentation K d → surfaceAreaMeasure K =
      ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))) ∧
    ((interior (K : Set Point)).Nonempty →
      Measure.hausdorffMeasure 1 (frontier (K : Set Point)) < ⊤ ∧
      Measure.hausdorffMeasure 1 (frontier (K : Set Point) \ regularBoundary K) = 0 ∧
      ∀ ν : Point → Real.Angle, (∀ p ∈ regularBoundary K, ν p = exteriorNormalAngle K p) →
        surfaceAreaMeasure K = Measure.map ν
          ((Measure.hausdorffMeasure 1).restrict (frontier (K : Set Point)))) ∧
    (∀ (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) (ψ : Real.Angle → ℝ), Continuous ψ →
      ∀ ε : ℝ, 0 < ε → (∀ t, e (normalVector t) 1 < ε → ψ t = 0) →
      ((horizontalBounds K o e).1 < (horizontalBounds K o e).2 →
        Integrable (upperGraphSurfaceIntegrand K o e ψ)
          (volume.restrict (Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2)) ∧
        (∫ t, ψ t ∂surfaceAreaMeasure K) =
          ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
            upperGraphSurfaceIntegrand K o e ψ x) ∧
      ((horizontalBounds K o e).1 = (horizontalBounds K o e).2 →
        (∫ t, ψ t ∂surfaceAreaMeasure K) = 0)) := by
  by_cases hsub : (K : Set Point).Subsingleton
  · refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_subsingleton K hsub,
      fun _ ↦ surfaceAreaMeasure_eq_zero_of_subsingleton K hsub, ?_, ?_, ?_⟩
    · intro d hd
      exact (not_subsingleton_of_isSegmentPresentation K hd hsub).elim
    · intro hint
      obtain ⟨p, hp⟩ := K.nonempty
      have hset : (K : Set Point) = {p} :=
        Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hsub hx hp⟩
      rw [hset, interior_singleton] at hint
      exact hint.ne_empty rfl |>.elim
    · intro o e ψ _ ε _ _
      have hbounds := horizontalBounds_eq_of_subsingleton K hsub o e
      constructor
      · intro hlt
        exact (hlt.ne hbounds).elim
      · intro _
        exact surfaceAreaMeasure_integral_eq_zero_of_subsingleton K hsub ψ
  · by_cases hint : (interior (K : Set Point)).Nonempty
    · refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_interior_nonempty K hint,
        fun hs ↦ (not_subsingleton_of_interior_nonempty K hint hs).elim, ?_, ?_, ?_⟩
      · intro d hd
        exact (not_exists_segmentPresentation_of_interior_nonempty K hint ⟨d, hd⟩).elim
      · intro _
        refine ⟨K.hausdorffMeasure_frontier_lt_top hint, ?_, ?_⟩
        · exact hausdorffMeasure_irregularBoundary_eq_zero K hint
        · intro ν hν
          exact surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary K hint ν hν
      · intro o e ψ hψ ε hε hsupport
        constructor
        · intro hwidth
          have hintg := integrable_upperGraphSurfaceIntegrand K o e ψ hψ hε hsupport
            (horizontalBounds K o e).1 (horizontalBounds K o e).2
          refine ⟨hintg, ?_⟩
          rw [surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary K hint
            (exteriorNormalAngle K) (fun _ _ ↦ rfl)]
          rw [MeasureTheory.integral_map]
          · apply tendsto_nhds_unique
              (tendsto_integral_innerUpperGraph K hint o e ψ hψ hε hsupport)
            apply (tendsto_integral_innerIcc hintg).congr'
            filter_upwards [eventually_integral_innerUpperGraph_eq_innerIcc
              K o e ψ hψ hwidth] with n hn
            exact hn.symm
          · have hae : frontier (K : Set Point) =ᵐ[Measure.hausdorffMeasure 1]
                regularBoundary K := by
              rw [ae_eq_set]
              exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hint,
                measure_mono_null (fun _ hp ↦ (hp.2 hp.1.1).elim) measure_empty⟩
            have hrestrict : (Measure.hausdorffMeasure 1).restrict
                (frontier (K : Set Point)) =
                (Measure.hausdorffMeasure 1).restrict (regularBoundary K) :=
              Measure.restrict_congr_set hae
            rw [hrestrict]
            exact aemeasurable_exteriorNormalAngle_restrict_regularBoundary K
              (Measure.hausdorffMeasure 1)
          · exact hψ.aestronglyMeasurable
        · intro hwidth
          exact ((horizontalBounds_lt_of_interior_nonempty K hint o e).ne hwidth).elim
    · have hinterior : interior (K : Set Point) = ∅ := Set.not_nonempty_iff_eq_empty.mp hint
      have hseg := exists_segmentPresentation_of_interior_empty K hsub hinterior
      refine ⟨isFiniteMeasure_surfaceAreaMeasure_of_segmentPresentation K hseg.choose_spec,
        fun hs ↦ (hsub hs).elim, ?_, ?_, ?_⟩
      · intro d hd
        exact surfaceAreaMeasure_eq_segmentPresentation K d hd
      · exact fun hi ↦ (hint hi).elim
      · intro o e ψ _ ε hε hsupport
        constructor
        · intro hbounds
          exact segment_graph_formula K o e ψ hε hsupport hseg.choose hseg.choose_spec hbounds
        · intro hbounds
          exact segment_integral_eq_zero_of_horizontalBounds_eq K o e ψ ε hε hsupport
            hseg.choose hseg.choose_spec hbounds

end MovingSofa
