import MovingSofa.Analysis.Stieltjes.Integral
import MovingSofa.ForMathlib.BoundedVariation
import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts

noncomputable section

open scoped Topology

namespace MovingSofa

theorem intervalStieltjes_linear_combination (a b : ℝ) (hab : a ≤ b)
    (f g : RightContinuousIntervalBV a b) (r s : ℝ) :
    ∃ h : RightContinuousIntervalBV a b,
      (∀ t, h.toFun t = r * f.toFun t + s * g.toFun t) ∧
      intervalStieltjesMeasure h =
        r • intervalStieltjesMeasure f + s • intervalStieltjesMeasure g := by
  let hfun : Set.Icc a b → ℝ := fun t ↦ r * f.toFun t + s * g.toFun t
  have hBV : IsIntervalBoundedVariation a b hfun := by
    have hfr := (ContinuousLinearMap.lsmul ℝ ℝ r).lipschitzWith.comp_boundedVariationOn
      f.boundedVariation
    have hgr := (ContinuousLinearMap.lsmul ℝ ℝ s).lipschitzWith.comp_boundedVariationOn
      g.boundedVariation
    exact BoundedVariationOn.add hfr hgr
  change BoundedVariationOn hfun Set.univ at hBV
  let h : RightContinuousIntervalBV a b :=
    { toFun := hfun
      boundedVariation := hBV
      right_continuous := fun t ↦ by
        exact (f.right_continuous t).const_mul r |>.add ((g.right_continuous t).const_mul s) }
  refine ⟨h, ?_, ?_⟩
  · intro t
    rfl
  · apply MeasureTheory.VectorMeasure.ext_of_Icc
    intro x y hxy
    have hbv : BoundedVariationOn h.toFun Set.univ := h.boundedVariation
    have hleft (z : Set.Icc a b) :
        Function.leftLim h.toFun z =
          r * Function.leftLim f.toFun z + s * Function.leftLim g.toFun z := by
      rcases Filter.eq_or_neBot (𝓝[<] z) with hz | hz
      · simp [leftLim_eq_of_eq_bot _ hz, h, hfun]
      · exact tendsto_nhds_unique (hbv.tendsto_leftLim z)
          ((f.boundedVariation.tendsto_leftLim z).const_smul r |>.add
            ((g.boundedVariation.tendsto_leftLim z).const_smul s))
    have hfxy : Function.rightLim f.toFun y = f.toFun y :=
      (f.right_continuous y).rightLim_eq
    have gfxy : Function.rightLim g.toFun y = g.toFun y :=
      (g.right_continuous y).rightLim_eq
    have hxy' : Function.rightLim h.toFun y = h.toFun y :=
      (h.right_continuous y).rightLim_eq
    simp only [smul_apply, add_apply]
    rw [show intervalStieltjesMeasure h (Set.Icc x y) =
        Function.rightLim h.toFun y - Function.leftLim h.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc hbv hxy]
    rw [show intervalStieltjesMeasure f (Set.Icc x y) =
        Function.rightLim f.toFun y - Function.leftLim f.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc f.boundedVariation hxy]
    rw [show intervalStieltjesMeasure g (Set.Icc x y) =
        Function.rightLim g.toFun y - Function.leftLim g.toFun x by
          exact BoundedVariationOn.vectorMeasure_Icc g.boundedVariation hxy]
    rw [hleft x]
    rw [hxy', hfxy, gfxy]
    simp [h, hfun, sub_eq_add_neg]
    ring

end MovingSofa
