import MovingSofa.Analysis.Stieltjes.Smooth
import MovingSofa.Geometry.FrameCalculus

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- A coordinate of the rotating normal frame is a continuous interval-BV function whose
Stieltjes density is the corresponding tangent coordinate. -/
theorem exists_normalVector_coordinate_intervalBV {a b : ℝ} (hab : a ≤ b) (i : Fin 2) :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = normalVector (((t : ℝ) : Real.Angle)) i) ∧
      HasIntervalStieltjesDensity F
        (fun t ↦ tangentVector ((t : ℝ) : Real.Angle) i) := by
  refine exists_intervalBV_of_hasDerivAt hab
    (fun t : ℝ ↦ normalVector (t : Real.Angle) i)
    (fun t : ℝ ↦ tangentVector (t : Real.Angle) i) ?_ ?_
  · intro t
    fin_cases i
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
    · change HasDerivAt Real.sin (Real.cos t) t
      exact Real.hasDerivAt_sin t
  · fin_cases i
    · change Continuous (fun t : ℝ ↦ -Real.sin t)
      fun_prop
    · change Continuous Real.cos
      fun_prop

/-- A coordinate of the rotating tangent frame is a continuous interval-BV function whose
Stieltjes density is the negative normal coordinate. -/
theorem exists_tangentVector_coordinate_intervalBV {a b : ℝ} (hab : a ≤ b) (i : Fin 2) :
    ∃ F : RightContinuousIntervalBV a b,
      (∀ t, F.toFun t = tangentVector (((t : ℝ) : Real.Angle)) i) ∧
      HasIntervalStieltjesDensity F
        (fun t ↦ -normalVector ((t : ℝ) : Real.Angle) i) := by
  refine exists_intervalBV_of_hasDerivAt hab
    (fun t : ℝ ↦ tangentVector (t : Real.Angle) i)
    (fun t : ℝ ↦ -normalVector (t : Real.Angle) i) ?_ ?_
  · intro t
    fin_cases i
    · change HasDerivAt (fun t : ℝ ↦ -Real.sin t) (-Real.cos t) t
      convert (Real.hasDerivAt_sin t).neg using 1
    · change HasDerivAt Real.cos (-Real.sin t) t
      exact Real.hasDerivAt_cos t
  · fin_cases i
    · change Continuous (fun t : ℝ ↦ -Real.cos t)
      fun_prop
    · change Continuous (fun t : ℝ ↦ -Real.sin t)
      fun_prop

end MovingSofa
