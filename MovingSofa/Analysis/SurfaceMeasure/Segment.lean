import MovingSofa.Analysis.SurfaceMeasure.Basic
import MovingSofa.Geometry.Frame
import MovingSofa.ForMathlib.Geometry.Euclidean.Segment

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Two angular unit normals perpendicular to a nonzero planar vector are equal or antipodal. -/
theorem normalVector_eq_or_eq_add_pi_of_orthogonal
    {v : Point} (hv : v ≠ 0) {s t : Real.Angle}
    (hvs : inner ℝ v (normalVector s) = 0)
    (hvt : inner ℝ v (normalVector t) = 0) : s = t ∨ s = t + (Real.pi : Real.Angle) := by
  let o : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hnorm (a : Real.Angle) : ‖normalVector a‖ = 1 := by
    induction a using Real.Angle.induction_on with
    | _ a =>
      rw [EuclideanSpace.norm_eq]
      simp [normalVector, frame, Fin.sum_univ_two]
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal o hv (hnorm s) (hnorm t) hvs hvt with
    h | h
  · left
    induction s using Real.Angle.induction_on with
    | _ s =>
      induction t using Real.Angle.induction_on with
      | _ t =>
        apply Real.Angle.cos_sin_inj
        · exact congrFun (congrArg WithLp.ofLp h) 0
        · exact congrFun (congrArg WithLp.ofLp h) 1
  · right
    induction s using Real.Angle.induction_on with
    | _ s =>
      induction t using Real.Angle.induction_on with
      | _ t =>
        apply Real.Angle.cos_sin_inj
        · have h0 := congrFun (congrArg WithLp.ofLp h) 0
          simpa [normalVector, frame, Real.cos_add_pi] using h0
        · have h1 := congrFun (congrArg WithLp.ofLp h) 1
          simpa [normalVector, frame, Real.sin_add_pi] using h1

private theorem dirac_add_antipode_eq_of_orthogonal
    {v : Point} (hv : v ≠ 0) {s t : Real.Angle}
    (hvs : inner ℝ v (normalVector s) = 0)
    (hvt : inner ℝ v (normalVector t) = 0) :
    Measure.dirac s + Measure.dirac (s + (Real.pi : Real.Angle)) =
      Measure.dirac t + Measure.dirac (t + (Real.pi : Real.Angle)) := by
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal hv hvs hvt with h | h
  · rw [h]
  · rw [h]
    have hpi : (t + (Real.pi : Real.Angle)) + (Real.pi : Real.Angle) = t := by
      rw [add_assoc, Real.Angle.coe_pi_add_coe_pi, add_zero]
    rw [hpi, add_comm]

/-- The atomic segment measure is independent of its segment presentation. -/
theorem segmentPresentation_measure_eq (K : ConvexBody Point)
    {d c : Point × Point × Real.Angle}
    (hd : IsSegmentPresentation K d) (hc : IsSegmentPresentation K c) :
    ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) =
      ENNReal.ofReal (dist c.1 c.2.1) •
        (Measure.dirac c.2.2 + Measure.dirac (c.2.2 + (Real.pi : Real.Angle))) := by
  have hseg : segment ℝ d.1 d.2.1 = segment ℝ c.1 c.2.1 := hd.2.1.symm.trans hc.2.1
  have hlen : dist d.1 d.2.1 = dist c.1 c.2.1 := EuclideanGeometry.dist_eq_of_segment_eq hseg
  have hcn : inner ℝ (d.2.1 - d.1) (normalVector c.2.2) = 0 :=
    EuclideanGeometry.inner_direction_eq_zero_of_segment_eq hseg hc.2.2
  rw [hlen, dirac_add_antipode_eq_of_orthogonal (sub_ne_zero.mpr hd.1.symm) hd.2.2 hcn]

/-- A singleton convex body has zero surface measure. -/
theorem surfaceAreaMeasure_eq_zero_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    surfaceAreaMeasure K = 0 := by
  simp [surfaceAreaMeasure, hK]

private theorem surfaceAreaMeasure_eq_chosenSegment (K : ConvexBody Point)
    (hK : ¬(K : Set Point).Subsingleton) (hseg : ∃ d, IsSegmentPresentation K d) :
    surfaceAreaMeasure K =
      ENNReal.ofReal (dist hseg.choose.1 hseg.choose.2.1) •
        (Measure.dirac hseg.choose.2.2 +
          Measure.dirac (hseg.choose.2.2 + ((Real.pi : ℝ) : Real.Angle))) := by
  simp [surfaceAreaMeasure, hK, hseg]

/-- A nondegenerate segment presentation makes the represented convex body nonsingleton. -/
theorem not_subsingleton_of_isSegmentPresentation (K : ConvexBody Point)
    {d : Point × Point × Real.Angle} (hd : IsSegmentPresentation K d) :
    ¬(K : Set Point).Subsingleton := by
  intro hK
  apply hd.1
  apply hK
  · rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  · rw [hd.2.1]
    exact right_mem_segment ℝ _ _

/-- The surface measure of a segment is its length times the two normal atoms. -/
theorem surfaceAreaMeasure_eq_segmentPresentation (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d) :
    surfaceAreaMeasure K = ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + (Real.pi : Real.Angle))) := by
  let hseg : ∃ c, IsSegmentPresentation K c := ⟨d, hd⟩
  rw [surfaceAreaMeasure_eq_chosenSegment K
    (not_subsingleton_of_isSegmentPresentation K hd) hseg]
  exact segmentPresentation_measure_eq K hseg.choose_spec hd

/-- The surface area measure of a singleton convex body is finite. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) :
    IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  infer_instance

/-- The surface area measure of a convex body with a segment presentation is finite. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_segmentPresentation (K : ConvexBody Point)
    {d : Point × Point × Real.Angle} (hd : IsSegmentPresentation K d) :
    IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  exact (Measure.dirac d.2.2 +
    Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle))).smul_finite
      ENNReal.ofReal_ne_top

end MovingSofa
