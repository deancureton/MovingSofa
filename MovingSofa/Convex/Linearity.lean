import MovingSofa.Convex.SupportArea

noncomputable section

open scoped unitInterval

namespace MovingSofa

theorem convexBody_maps_linear (t : I) (K L : ConvexBody Point) :
    (∀ a : Real.Angle,
      supportValue (convexBodyCombination t K L) a =
        (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a) ∧
    (∀ a : Real.Angle,
      (edgeVertices (convexBodyCombination t K L) a).1 =
        (1 - (t : ℝ)) • (edgeVertices K a).1 + (t : ℝ) • (edgeVertices L a).1 ∧
      (edgeVertices (convexBodyCombination t K L) a).2 =
        (1 - (t : ℝ)) • (edgeVertices K a).2 + (t : ℝ) • (edgeVertices L a).2) ∧
    (∀ a b : ℝ, a < b → b < a + Real.pi →
      supportingIntersection (convexBodyCombination t K L) a b =
        (1 - (t : ℝ)) • supportingIntersection K a b +
          (t : ℝ) • supportingIntersection L a b) ∧
    surfaceAreaMeasure (convexBodyCombination t K L) =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L := by
  refine ⟨supportValue_convexBodyCombination t K L, ?_, ?_,
    surfaceAreaMeasure_convexBodyCombination t K L⟩
  · exact edgeVertices_convexBodyCombination t K L
  · intro a b _hab _hba
    simp only [supportingIntersection, supportValue_convexBodyCombination]
    ext i
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

theorem convexBody_area_support_integral :
    (∀ K : ConvexBody Point, ClassicalResults.area (K : Set Point) =
      (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K a ∂surfaceAreaMeasure K) ∧
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦
        (1 / 2 : ℝ) * ∫ a : Real.Angle, supportValue K a ∂surfaceAreaMeasure L) ∧
    IsQuadraticFunctional convexBodyCombination
      (fun K : ConvexBody Point ↦ ClassicalResults.area (K : Set Point)) :=
  convexBody_area_support_integral_of_area_identity
    (convexBody_area_support_integral_of_finiteHull
      (fun P W _hW hPW ↦ convexBody_area_support_integral_of_convexHull P W hPW))

end MovingSofa
