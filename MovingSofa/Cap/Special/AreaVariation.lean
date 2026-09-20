import MovingSofa.Cap.LowerNormalMeasure
import MovingSofa.Cap.Special.Domain
import MovingSofa.Convex.MixedArea

noncomputable section

open MeasureTheory

namespace MovingSofa

theorem specialCapArea_variation :
    IsQuadraticFunctional specialCapCombination
      (fun K ↦ ClassicalResults.area (K.val.val : Set Point)) ∧
    ∀ K L : SpecialCapSpace,
      convexDirectionalDerivative specialCapCombination
        (fun M ↦ ClassicalResults.area (M.val.val : Set Point)) K L =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
        (supportValue L.val.val t - supportValue K.val.val t) ∂surfaceAreaMeasure K.val.val := by
  obtain ⟨harea, hbil, -⟩ := convexBody_area_support_integral
  have hcomb := specialCap_isConvexDomain.1
  -- ### Quadraticity is the ambient bilinear form restricted to the special caps
  refine ⟨⟨fun K L ↦ (1 / 2 : ℝ) * ∫ a : Real.Angle,
      supportValue K.val.val a ∂surfaceAreaMeasure L.val.val, ⟨?_, ?_⟩,
    fun K ↦ harea K.val.val⟩, ?_⟩
  · intro K t L M
    show (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K.val.val a
        ∂surfaceAreaMeasure (specialCapCombination t L M).val.val = _
    rw [hcomb t L M]
    exact hbil.1 K.val.val t L.val.val M.val.val
  · intro M t K L
    show (1 / 2 : ℝ) * ∫ a : Real.Angle,
        supportValue (specialCapCombination t K L).val.val a
        ∂surfaceAreaMeasure M.val.val = _
    rw [hcomb t K L]
    exact hbil.2 M.val.val t K.val.val L.val.val
  intro K L
  -- ### The support difference is integrable against the finite surface area measure
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val.val) :=
    (surfaceAreaMeasure_face_union K.val.val).1
  have hint : ∀ M : ConvexBody Point,
      Integrable (supportValue M) (surfaceAreaMeasure K.val.val) := by
    intro M
    have hcont : Continuous (supportValue M) :=
      (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
    exact hcont.integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  have hdiff : Integrable (fun t ↦ supportValue L.val.val t - supportValue K.val.val t)
      (surfaceAreaMeasure K.val.val) := (hint L.val.val).sub (hint K.val.val)
  -- ### Interpolating special caps is interpolating convex bodies, so the two segment
  -- functionals are equal as functions and the mixed-area derivative transports
  have hseg : segmentFunctional specialCapCombination
        (fun M : SpecialCapSpace ↦ ClassicalResults.area (M.val.val : Set Point)) K L =
      segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point))
        K.val.val L.val.val := by
    funext t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · simp only [segmentFunctional, ht, ↓reduceDIte]
      exact congrArg (fun s : Set Point ↦ ClassicalResults.area s)
        (congrArg (fun M : ConvexBody Point ↦ (M : Set Point)) (hcomb ⟨t, ht⟩ K L))
    · simp only [segmentFunctional, ht, ↓reduceDIte]
  -- ### Both caps have vanishing base support value, so the lower normals contribute nothing
  have hzero := K.val.setIntegral_compl_image_Icc_zero_pi_eq_zero
    (fun t ↦ supportValue L.val.val t - supportValue K.val.val t)
    (by rw [K.val.property.2.2.2.2.2.1, L.val.property.2.2.2.2.2.1, sub_zero])
  have hS : MeasurableSet ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi) :=
    (isCompact_Icc.image Real.Angle.continuous_coe).isClosed.measurableSet
  rw [convexDirectionalDerivative, hseg,
    ((supportMeasure_mixedArea_symmetry K.val.val L.val.val).2).derivWithin
      (uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by norm_num)),
    ← integral_add_compl hS hdiff, hzero, add_zero]

end MovingSofa
