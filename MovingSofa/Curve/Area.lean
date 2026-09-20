import MovingSofa.Analysis.Stieltjes.Integral
import MovingSofa.Analysis.MeasureProducts

noncomputable section

namespace MovingSofa

/-- The constant planar path, as a continuous path of bounded variation. -/
def constBVPath (a b : ℝ) (p : Point) : ContinuousBVPaths a b :=
  ⟨fun _ ↦ p, continuous_const, fun i ↦ by
    simp [IsIntervalBoundedVariation, BoundedVariationOn, eVariationOn]⟩

def continuousBVCoordinate {a b : ℝ} (x : ContinuousBVPaths a b) (i : Fin 2) :
    RightContinuousIntervalBV a b where
  toFun t := x.val t i
  boundedVariation := x.property.2 i
  right_continuous _ :=
    ((PiLp.continuous_apply 2 _ i).comp x.property.1).continuousAt.continuousWithinAt

def curveAreaFunctional {a b : ℝ} (x : ContinuousBVPaths a b) : ℝ :=
  (intervalStieltjesIntegral (continuousBVCoordinate x 1) (fun t ↦ x.val t 0) Set.univ -
    intervalStieltjesIntegral (continuousBVCoordinate x 0) (fun t ↦ x.val t 1) Set.univ) / 2

end MovingSofa
