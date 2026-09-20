import MovingSofa.Analysis.SurfaceMeasure.BoundaryLimit
import MovingSofa.Analysis.SurfaceMeasure.BoundaryExtension

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem positiveVertex_stieltjes_surface (K : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      (∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
        (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure (f i) E =
          ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
            tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab.le
  refine ⟨f, hf, ?_⟩
  apply intervalStieltjesMeasure_eq_surfaceIntegral_of_increment K hab hturn f hf
  intro c d hcd i
  have hcdturn : (d : ℝ) ≤ (c : ℝ) + 2 * Real.pi :=
    d.property.2.trans (hturn.trans (by linarith [c.property.1]))
  exact positiveVertex_sub_eq_integral K hcd hcdturn i

end MovingSofa
