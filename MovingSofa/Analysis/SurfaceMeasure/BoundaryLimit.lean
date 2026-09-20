import MovingSofa.Analysis.SurfaceMeasure.ArcConvergence
import MovingSofa.Analysis.SurfaceMeasure.Polygon

noncomputable section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace MovingSofa

/-- Face-preserving polygon approximation transfers the boundary increment identity. -/
private theorem positiveVertex_sub_eq_integral_of_polygon_identity
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (hpoly : ∀ (P : ConvexBody Point) (V : Finset Point),
      (P : Set Point) = convexHull ℝ (V : Set Point) → ∀ i : Fin 2,
      (edgeVertices P (b : Real.Angle)).1 i - (edgeVertices P (a : Real.Angle)).1 i =
        ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
          tangentVector u i ∂surfaceAreaMeasure P) (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  classical
  obtain ⟨V, P, hP, hdist⟩ := exists_facePreserving_polygonApproximation K
    {(a : Real.Angle), (b : Real.Angle)}
  have ha (n : ℕ) : exposedEdge (P n) (a : Real.Angle) = exposedEdge K (a : Real.Angle) :=
    (hP n).2.2.2 _ (by simp)
  have hb (n : ℕ) : exposedEdge (P n) (b : Real.Angle) = exposedEdge K (b : Real.Angle) :=
    (hP n).2.2.2 _ (by simp)
  have hlim : Tendsto (fun n ↦ Metric.hausdorffDist (P n : Set Point) (K : Set Point))
      atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ Metric.hausdorffDist_nonneg)
      (Filter.eventually_atTop.2 ⟨1, fun n hn ↦ hdist n hn⟩)
    exact tendsto_one_div_atTop_nhds_zero_nat
  have hcontinuous : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hint := tendsto_integral_surfaceAreaMeasure_Ioc_of_preserves_faces
    P K hlim hab hturn ha hb (fun u ↦ tangentVector u i) hcontinuous
  have hvalue (n : ℕ) :
      (∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure (P n)) =
      (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i := by
    rw [← hpoly (P n) (V n) (hP n).2.1 i,
      edgeVertices_eq_of_exposedEdge_eq (P n) K _ (ha n),
      edgeVertices_eq_of_exposedEdge_eq (P n) K _ (hb n)]
  simp only [hvalue] at hint
  exact tendsto_nhds_unique tendsto_const_nhds hint

/-- The positive vertex increment is the tangent-coordinate surface integral over
the corresponding half-open angular interval. -/
theorem positiveVertex_sub_eq_integral
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i - (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  exact positiveVertex_sub_eq_integral_of_polygon_identity K hab hturn
    (fun P V hPV i ↦ positiveVertex_sub_eq_integral_of_eq_convexHull P V hPV hab hturn i) i

end MovingSofa
