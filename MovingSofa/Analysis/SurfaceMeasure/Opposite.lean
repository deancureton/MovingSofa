import MovingSofa.Analysis.SurfaceMeasure.Properties
import MovingSofa.Convex.Limits

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- The opposite-angle surface measure and support function. -/
def oppositeSurfaceData (K : ConvexBody Point) :
    Measure Real.Angle × (Real.Angle → ℝ) :=
  (Measure.map (fun t ↦ t - ((Real.pi : ℝ) : Real.Angle)) (surfaceAreaMeasure K),
    fun t ↦ supportValue K (t + ((Real.pi : ℝ) : Real.Angle)))

/-- The opposite surface measure is the half-turn translate of the surface measure. -/
theorem oppositeSurfaceData_fst (K : ConvexBody Point) :
    (oppositeSurfaceData K).1 =
      Measure.map (fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle))
        (surfaceAreaMeasure K) := rfl

instance isFiniteMeasure_oppositeSurfaceData (K : ConvexBody Point) :
    IsFiniteMeasure (oppositeSurfaceData K).1 := by
  rw [oppositeSurfaceData_fst]
  exact Measure.isFiniteMeasure_map _ _

/-- The opposite support function of a convex body is continuous in the normal direction. -/
theorem continuous_oppositeSurfaceData_snd (K : ConvexBody Point) :
    Continuous (oppositeSurfaceData K).2 :=
  (continuous_supportValue K).comp (continuous_id.add continuous_const)

/-- Integrating a `π`-shifted integrand against the opposite surface measure over an open angular
window is integrating the integrand itself against the surface-area measure over the `π`-translated
window.  The endpoints of the translated window are given as hypotheses so that call sites may
normalize them arithmetically. -/
theorem setIntegral_oppositeSurfaceData_angleImage_Ioo (K : ConvexBody Point) {a b a' b' : ℝ}
    (ha : a' = a + Real.pi) (hb : b' = b + Real.pi) {f : Real.Angle → ℝ} (hf : Measurable f) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        f (t + ((Real.pi : ℝ) : Real.Angle)) ∂(oppositeSurfaceData K).1) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a' b',
        f t ∂surfaceAreaMeasure K := by
  subst ha hb
  have hshift : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  have hfshift : Measurable fun t : Real.Angle ↦ f (t + ((Real.pi : ℝ) : Real.Angle)) :=
    hf.comp (continuous_id.add continuous_const).measurable
  have hE : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) :=
    (Real.Angle.isOpen_image_Ioo a b).measurableSet
  rw [oppositeSurfaceData_fst, setIntegral_map hE hfshift.aestronglyMeasurable hshift.aemeasurable,
    Real.Angle.preimage_sub_pi_image_Ioo]
  simp only [sub_add_cancel]

/-- The opposite surface measure vanishes on an open angular window whose half-turn translate
carries a single support point. -/
theorem oppositeSurfaceData_angleImage_Ioo_eq_zero_of_mem_exposedEdge (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hpa : p ∈ exposedEdge K ((a + Real.pi : ℝ) : Real.Angle))
    (hpb : p ∈ exposedEdge K ((b + Real.pi : ℝ) : Real.Angle)) :
    (oppositeSurfaceData K).1 ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  have hshift : Measurable fun t : Real.Angle ↦ t - ((Real.pi : ℝ) : Real.Angle) :=
    (continuous_id.sub continuous_const).measurable
  rw [oppositeSurfaceData_fst,
    Measure.map_apply hshift (Real.Angle.isOpen_image_Ioo a b).measurableSet,
    Real.Angle.preimage_sub_pi_image_Ioo]
  exact surfaceAreaMeasure_angleImage_Ioo_eq_zero_of_mem_exposedEdge K (by linarith) (by linarith)
    hpa hpb

end MovingSofa
