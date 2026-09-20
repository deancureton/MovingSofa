import MovingSofa.Cap.Tail.Interpolation
import MovingSofa.Bounds.Upper.Q
import MovingSofa.Analysis.SurfaceMeasure.Opposite
import MovingSofa.Cap.InnerCornerVariation
import MovingSofa.Cap.Special.AreaVariation

/-!
# The directional derivative of the upper bound `𝒬`

`upperBoundQ` is a signed sum of six area functionals of a cap-tail triple: the cap area, the two
tail arc areas, the inner-corner curve area and the two areas of the segments joining a tail
endpoint to the corresponding cap corner.  Each summand is quadratic along the barycentric
interpolation of cap-tail triples, so each segment function is differentiable at the base point
with the summand's `convexDirectionalDerivative` as its derivative; adding those six derivatives
computes the derivative of the segment function of `𝒬` itself.

Five of the twelve endpoint contributions cancel in pairs.  The remaining two are the segment
areas at the far ends of the two tails, and they vanish because the cap-tail constraints force the
support value of both tails in the direction `3π/2` to be zero, so all four points involved lie on
the horizontal axis.  What survives is `qVariationIntegral`: the cap surface integral, the
inner-corner integral, and the two tail integrals rewritten in opposite-angle coordinates.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

def qVariationIntegral (X Y : CapTailSpace) : ℝ :=
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
    (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
      ∂surfaceAreaMeasure X.cap.val.val) -
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)),
    (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
      ∂capCornerAngleMeasure X.cap) +
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2),
    ((oppositeSurfaceData Y.rightBody).2 t - (oppositeSurfaceData X.rightBody).2 t)
      ∂(oppositeSurfaceData X.rightBody).1) +
  (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2),
    ((oppositeSurfaceData Y.leftBody).2 t - (oppositeSurfaceData X.leftBody).2 t)
      ∂(oppositeSurfaceData X.leftBody).1)

theorem upperBoundQ_variation (X Y : CapTailSpace)
    (hR : (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint =
      (distinguishedCapSides X.cap.val).1.corner)
    (hL : (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint =
      (distinguishedCapSides X.cap.val).2.corner) :
    convexDirectionalDerivative capTailCombination upperBoundQ X Y = qVariationIntegral X Y := by
  obtain ⟨hcomb, hdom⟩ := capTail_isConvexDomain
  obtain ⟨hrIoo, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  -- ### The three components of a cap-tail triple depend convex-linearly on it
  have hcap : IsConvexLinear capTailCombination specialCapCombination
      (fun Z : CapTailSpace ↦ Z.cap) := fun t Z W ↦
    Subtype.ext (Subtype.ext ((hcomb t Z W).1.trans
      (specialCap_isConvexDomain.1 t Z.cap W.cap).symm))
  have hright : IsConvexLinear capTailCombination convexBodyCombination
      (fun Z : CapTailSpace ↦ Z.rightBody) := fun t Z W ↦ (hcomb t Z W).2.1
  have hleft : IsConvexLinear capTailCombination convexBodyCombination
      (fun Z : CapTailSpace ↦ Z.leftBody) := fun t Z W ↦ (hcomb t Z W).2.2
  -- ### The two segment endpoint pairs depend convex-linearly on the triple
  have hleftPair : IsConvexLinear capTailCombination pointPairCombination
      (fun Z : CapTailSpace ↦ ((rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint,
        (distinguishedCapSides Z.cap.val).2.corner)) := by
    intro t Z W
    have hvertex : (rightLeftTailArcs (capTailCombination t Z W).rightBody
        (capTailCombination t Z W).leftBody).2.endPoint =
        (1 - (t : ℝ)) • (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint +
          (t : ℝ) • (rightLeftTailArcs W.rightBody W.leftBody).2.endPoint := by
      show (edgeVertices (capTailCombination t Z W).leftBody
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 = _
      rw [(hcomb t Z W).2.2]
      exact ((convexBody_maps_linear t Z.leftBody W.leftBody).2.1 _).2
    have hcorner : (distinguishedCapSides (capTailCombination t Z W).cap.val).2.corner =
        (1 - (t : ℝ)) • (distinguishedCapSides Z.cap.val).2.corner +
          (t : ℝ) • (distinguishedCapSides W.cap.val).2.corner :=
      capInnerCorner_of_eq_convexBodyCombination (hcomb t Z W).1 paperGerverConstants.2.2
    show ((rightLeftTailArcs (capTailCombination t Z W).rightBody
      (capTailCombination t Z W).leftBody).2.endPoint,
      (distinguishedCapSides (capTailCombination t Z W).cap.val).2.corner) = _
    rw [hvertex, hcorner]
    rfl
  have hrightPair : IsConvexLinear capTailCombination pointPairCombination
      (fun Z : CapTailSpace ↦ ((distinguishedCapSides Z.cap.val).1.corner,
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint)) := by
    intro t Z W
    have hcorner : (distinguishedCapSides (capTailCombination t Z W).cap.val).1.corner =
        (1 - (t : ℝ)) • (distinguishedCapSides Z.cap.val).1.corner +
          (t : ℝ) • (distinguishedCapSides W.cap.val).1.corner :=
      capInnerCorner_of_eq_convexBodyCombination (hcomb t Z W).1 paperGerverConstants.2.1
    have hvertex : (rightLeftTailArcs (capTailCombination t Z W).rightBody
        (capTailCombination t Z W).leftBody).1.startPoint =
        (1 - (t : ℝ)) • (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint +
          (t : ℝ) • (rightLeftTailArcs W.rightBody W.leftBody).1.startPoint := by
      show (edgeVertices (capTailCombination t Z W).rightBody
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 = _
      rw [(hcomb t Z W).2.1]
      exact ((convexBody_maps_linear t Z.rightBody W.rightBody).2.1 _).1
    show ((distinguishedCapSides (capTailCombination t Z W).cap.val).1.corner,
      (rightLeftTailArcs (capTailCombination t Z W).rightBody
        (capTailCombination t Z W).leftBody).1.startPoint) = _
    rw [hcorner, hvertex]
    rfl
  -- ### Quadraticity of the six summands of `𝒬`
  have hq1 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) :=
    specialCapArea_variation.1.comp_isConvexLinear hcap
  have hq2 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) :=
    (convexArcArea_variation _ _ (by linarith [hlIoo.1]) (by linarith [hlIoo.2])).1
      |>.comp_isConvexLinear hleft
  have hq3 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
        (distinguishedCapSides Z.cap.val).2.corner) :=
    segmentArea_variation.1.comp_isConvexLinear hleftPair
  have hq4 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) :=
    capInnerCorner_variation.2.1.comp_isConvexLinear hcap
  have hq5 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) :=
    segmentArea_variation.1.comp_isConvexLinear hrightPair
  have hq6 : IsQuadraticFunctional capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) :=
    (convexArcArea_variation _ _ (by linarith [hrIoo.2]) (by linarith [hrIoo.1])).1
      |>.comp_isConvexLinear hright
  -- ### The four summands whose derivatives contribute an integral
  have hd1 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) X Y =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi,
        (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
          ∂surfaceAreaMeasure X.cap.val.val :=
    (convexDirectionalDerivative_comp_isConvexLinear hcap
      (fun K : SpecialCapSpace ↦ ClassicalResults.area (K.val.val : Set Point)) X Y).trans
      (specialCapArea_variation.2 X.cap Y.cap)
  have hd2 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
        (supportValue Y.leftBody t - supportValue X.leftBody t)
          ∂surfaceAreaMeasure X.leftBody) +
        (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint -
          segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint) :=
    (convexDirectionalDerivative_comp_isConvexLinear hleft
      (fun M : ConvexBody Point ↦ convexArcArea M (3 * Real.pi / 2)
        (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y).trans
      ((convexArcArea_variation _ _ (by linarith [hlIoo.1]) (by linarith [hlIoo.2])).2
        X.leftBody Y.leftBody)
  have hd4 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
            Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
              (Real.pi / 2 + paperGerverConstants.2.2)),
        (supportValue Y.cap.val.val t - supportValue X.cap.val.val t)
          ∂capCornerAngleMeasure X.cap) +
        (segmentArea (distinguishedCapSides X.cap.val).2.corner
            (distinguishedCapSides Y.cap.val).2.corner -
          segmentArea (distinguishedCapSides X.cap.val).1.corner
            (distinguishedCapSides Y.cap.val).1.corner) :=
    (convexDirectionalDerivative_comp_isConvexLinear hcap
      (fun M : SpecialCapSpace ↦ curveAreaFunctional (capMiddleBV M)) X Y).trans
      (capInnerCorner_variation.2.2 X.cap Y.cap)
  have hd6 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) X Y =
      (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
        (supportValue Y.rightBody t - supportValue X.rightBody t)
          ∂surfaceAreaMeasure X.rightBody) +
        (segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint -
          segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
            (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint) :=
    (convexDirectionalDerivative_comp_isConvexLinear hright
      (fun M : ConvexBody Point ↦ convexArcArea M (Real.pi + paperGerverConstants.2.1)
        (3 * Real.pi / 2)) X Y).trans
      ((convexArcArea_variation _ _ (by linarith [hrIoo.2]) (by linarith [hrIoo.1])).2
        X.rightBody Y.rightBody)
  -- ### The two segment summands: their bulk terms vanish because the base endpoints coincide
  have hd3 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
        (distinguishedCapSides Z.cap.val).2.corner) X Y =
      segmentArea (distinguishedCapSides X.cap.val).2.corner
          (distinguishedCapSides Y.cap.val).2.corner -
        segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
          (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint := by
    have hvar := segmentArea_variation.2
      (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
      (distinguishedCapSides X.cap.val).2.corner
      (rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint
      (distinguishedCapSides Y.cap.val).2.corner
    have hbulk : (planeCrossProduct
        ((rightLeftTailArcs Y.rightBody Y.leftBody).2.endPoint +
          (distinguishedCapSides Y.cap.val).2.corner)
        ((distinguishedCapSides X.cap.val).2.corner -
          (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint) -
        2 * planeCrossProduct (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
          (distinguishedCapSides X.cap.val).2.corner) / 2 = 0 := by
      rw [← hL]
      simp only [planeCrossProduct, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
      ring
    rw [hbulk, zero_add] at hvar
    exact (convexDirectionalDerivative_comp_isConvexLinear hleftPair
      (fun x : Point × Point ↦ segmentArea x.1 x.2) X Y).trans hvar
  have hd5 : convexDirectionalDerivative capTailCombination
      (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
        (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) X Y =
      segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
          (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint -
        segmentArea (distinguishedCapSides X.cap.val).1.corner
          (distinguishedCapSides Y.cap.val).1.corner := by
    have hvar := segmentArea_variation.2
      (distinguishedCapSides X.cap.val).1.corner
      (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint
      (distinguishedCapSides Y.cap.val).1.corner
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint
    have hbulk : (planeCrossProduct
        ((distinguishedCapSides Y.cap.val).1.corner +
          (rightLeftTailArcs Y.rightBody Y.leftBody).1.startPoint)
        ((rightLeftTailArcs X.rightBody X.leftBody).1.startPoint -
          (distinguishedCapSides X.cap.val).1.corner) -
        2 * planeCrossProduct (distinguishedCapSides X.cap.val).1.corner
          (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint) / 2 = 0 := by
      rw [hR]
      simp only [planeCrossProduct, sub_self, WithLp.ofLp_zero, Pi.zero_apply, mul_zero]
      ring
    rw [hbulk, zero_add] at hvar
    exact (convexDirectionalDerivative_comp_isConvexLinear hrightPair
      (fun x : Point × Point ↦ segmentArea x.1 x.2) X Y).trans hvar
  -- ### The derivative of `𝒬` is the signed sum of the six derivatives
  have hsplit : ∀ t : ℝ, segmentFunctional capTailCombination upperBoundQ X Y t =
      segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ ClassicalResults.area (Z.cap.val.val : Set Point)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ convexArcArea Z.leftBody (3 * Real.pi / 2)
              (3 * Real.pi / 2 + paperGerverConstants.2.2)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ segmentArea
              (rightLeftTailArcs Z.rightBody Z.leftBody).2.endPoint
              (distinguishedCapSides Z.cap.val).2.corner) X Y t -
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ curveAreaFunctional (capMiddleBV Z.cap)) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ segmentArea (distinguishedCapSides Z.cap.val).1.corner
              (rightLeftTailArcs Z.rightBody Z.leftBody).1.startPoint) X Y t +
          segmentFunctional capTailCombination
            (fun Z : CapTailSpace ↦ convexArcArea Z.rightBody
              (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)) X Y t := by
    intro t
    simp only [segmentFunctional]
    split_ifs with ht
    · rfl
    · norm_num
  have hD1 := hq1.hasDerivWithinAt_segmentFunctional hdom X Y
  have hD2 := hq2.hasDerivWithinAt_segmentFunctional hdom X Y
  have hD3 := hq3.hasDerivWithinAt_segmentFunctional hdom X Y
  have hD4 := hq4.hasDerivWithinAt_segmentFunctional hdom X Y
  have hD5 := hq5.hasDerivWithinAt_segmentFunctional hdom X Y
  have hD6 := hq6.hasDerivWithinAt_segmentFunctional hdom X Y
  rw [hd1] at hD1
  rw [hd2] at hD2
  rw [hd3] at hD3
  rw [hd4] at hD4
  rw [hd5] at hD5
  rw [hd6] at hD6
  have hderiv := convexDirectionalDerivative_eq_of_hasDerivWithinAt capTailCombination
    upperBoundQ X Y ((((((hD1.add hD2).add hD3).sub hD4).add hD5).add hD6).congr
      (fun t _ ↦ hsplit t) (hsplit 0))
  -- ### The far endpoints of the two tails lie on the horizontal axis
  have hsupp : ∀ Z : CapTailSpace,
      supportValue (Z.rightBody : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 ∧
        supportValue (Z.leftBody : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    intro Z
    have hcapval :
        supportValue (Z.cap.val.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
      Z.cap.val.property.2.2.2.1
    have hr := Z.right_eq (Real.pi / 2) (by simp)
    have hl := Z.left_eq 0 (by simp)
    rw [show ((Real.pi + Real.pi / 2 : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring] at hr
    rw [show ((Real.pi / 2 + (0 : ℝ) : ℝ) : Real.Angle) =
        ((Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring,
      show ((3 * Real.pi / 2 + (0 : ℝ) : ℝ) : Real.Angle) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) from by congr 1; ring] at hl
    exact ⟨by linarith, by linarith⟩
  have hheight : ∀ K : ConvexBody Point,
      supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 →
      (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 1 = 0 ∧
        (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 1 = 0 := by
    intro K hK
    have hn : normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        -normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [show ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 + Real.pi : ℝ) : Real.Angle) from by congr 1; ring]
      exact normalVector_add_pi _
    have key : ∀ p : Point,
        inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = 0 → p 1 = 0 := by
      intro p hp
      rw [hn, inner_neg_right, inner_normalVector_real, Real.cos_pi_div_two,
        Real.sin_pi_div_two] at hp
      linarith
    have hfst : inner ℝ (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_fst_mem K _).2
    have hsnd : inner ℝ (edgeVertices K ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2
        (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) :=
      (edgeVertices_snd_mem K _).2
    exact ⟨key _ (hfst.trans hK), key _ (hsnd.trans hK)⟩
  have hzeroSegment : ∀ p q : Point, p 1 = 0 → q 1 = 0 → segmentArea p q = 0 := by
    intro p q hp hq
    simp [segmentArea, planeCrossProduct, hp, hq]
  have hrightFar : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).1.endPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).1.endPoint = 0 :=
    hzeroSegment _ _ (hheight X.rightBody (hsupp X).1).2 (hheight Y.rightBody (hsupp Y).1).2
  have hleftFar : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.startPoint
      (rightLeftTailArcs Y.rightBody Y.leftBody).2.startPoint = 0 :=
    hzeroSegment _ _ (hheight X.leftBody (hsupp X).2).1 (hheight Y.leftBody (hsupp Y).2).1
  -- ### The two tail integrals in opposite-angle coordinates
  have hrightTail : (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
        Set.Ioo (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2),
      (supportValue Y.rightBody t - supportValue X.rightBody t)
        ∂surfaceAreaMeasure X.rightBody) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo paperGerverConstants.2.1 (Real.pi / 2),
        ((oppositeSurfaceData Y.rightBody).2 t - (oppositeSurfaceData X.rightBody).2 t)
          ∂(oppositeSurfaceData X.rightBody).1 :=
    (setIntegral_oppositeSurfaceData_angleImage_Ioo X.rightBody
      (a := paperGerverConstants.2.1) (b := Real.pi / 2) (by ring) (by ring)
      (f := fun u : Real.Angle ↦ supportValue Y.rightBody u - supportValue X.rightBody u)
      ((continuous_supportValue Y.rightBody).sub
        (continuous_supportValue X.rightBody)).measurable).symm
  have hleftTail : (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
        Set.Ioo (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2),
      (supportValue Y.leftBody t - supportValue X.leftBody t)
        ∂surfaceAreaMeasure X.leftBody) =
      ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
          Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2),
        ((oppositeSurfaceData Y.leftBody).2 t - (oppositeSurfaceData X.leftBody).2 t)
          ∂(oppositeSurfaceData X.leftBody).1 :=
    (setIntegral_oppositeSurfaceData_angleImage_Ioo X.leftBody
      (a := Real.pi / 2) (b := Real.pi / 2 + paperGerverConstants.2.2) (by ring) (by ring)
      (f := fun u : Real.Angle ↦ supportValue Y.leftBody u - supportValue X.leftBody u)
      ((continuous_supportValue Y.leftBody).sub
        (continuous_supportValue X.leftBody)).measurable).symm
  -- ### Collecting the six contributions
  rw [hderiv]
  simp only [qVariationIntegral]
  linarith [hrightTail, hleftTail, hrightFar, hleftFar]

end MovingSofa
