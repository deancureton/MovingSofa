import MovingSofa.Convex.CombinationProperties
import Mathlib.Topology.ContinuousMap.Algebra

open scoped unitInterval Pointwise

namespace MovingSofa

/-- Convex bodies form a convex domain under Minkowski interpolation. -/
theorem convexBody_isConvexDomain : IsConvexDomain.{0, 0} convexBodyCombination := by
  let e : ConvexBody Point → C(Real.Angle, ℝ) := fun K ↦
    ⟨fun t ↦ supportValue K t, (supportFunction_minkowski_embedding K K).2.2.1⟩
  have he (t : I) (K L : ConvexBody Point) :
      e (convexBodyCombination t K L) = (1 - (t : ℝ)) • e K + (t : ℝ) • e L := by
    ext u
    change supportValue (convexBodyCombination t K L) u = _
    exact supportValue_convexBodyCombination t K L u
  refine ⟨ModuleCat.of ℝ C(Real.Angle, ℝ), e, ?_, ?_, he⟩
  · intro K L h
    apply (supportFunction_minkowski_embedding K L).2.1
    intro t
    exact congrArg (fun f : C(Real.Angle, ℝ) ↦ f t) h
  · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
    refine ⟨convexBodyCombination ⟨b, hb, by linarith⟩ K L, ?_⟩
    have h : 1 - b = a := by linarith
    simpa only [h] using he ⟨b, hb, by linarith⟩ K L


end MovingSofa
