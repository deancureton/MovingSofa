import Mathlib.Topology.ContinuousMap.Basic
import MovingSofa.Polygon.DiscreteCapData
import Mathlib.Topology.Order.ProjIcc

noncomputable section

namespace MovingSofa

def armIntegralOperator (f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), ℝ) where
  toFun x := 1 + ∫ u in (0 : ℝ)..(x : ℝ),
    magicFunctions.2 (f (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))
  continuous_toFun := by
    have hf : Continuous (fun u : ℝ ↦
        magicFunctions.2 (f (Set.projIcc 0 (Real.pi / 2) (by positivity)
          (Real.pi / 2 - u)))) := by
      unfold magicFunctions
      fun_prop
    exact continuous_const.add
      ((intervalIntegral.differentiable_integral_of_continuous hf).continuous.comp
        continuous_subtype_val)

def armLowerBoundSequence : ℕ → C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)
  | 0 => ⟨fun _ ↦ 0, continuous_const⟩
  | n + 1 =>
      ⟨fun x ↦ max (armLowerBoundSequence n x)
          (Real.toNNReal (armIntegralOperator (armLowerBoundSequence n) x)),
        (armLowerBoundSequence n).continuous.max
          (continuous_real_toNNReal.comp (armIntegralOperator (armLowerBoundSequence n)).continuous)⟩

def lowerBoundProfile (c : Set.Icc (0 : ℝ) 1) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), ℝ) where
  toFun x := max (1 - (x : ℝ)) (c : ℝ)
  continuous_toFun := (continuous_const.sub continuous_subtype_val).max continuous_const

end MovingSofa
