import MovingSofa.Area.Mamikon.Middle
import MovingSofa.Area.Mamikon.Properties
import MovingSofa.Convex.TangentLinePath

/-!
# Mamikon values of tangent-line chords

For a fixed tangent normal `q`, the tangent-line parametrization of a convex body is a
continuous bounded-variation path, convex-linear in the body, each of whose values lies on the
supporting line at its own path parameter.  Mamikon convexity therefore makes the enclosed area
`straightMamikonValue` a convex quadratic functional of the body, and the terminal case `q = b`
does the same for `tangentMamikonValue`.
-/

noncomputable section

namespace MovingSofa

/-- The Mamikon value of a straight tangent-line chord is a convex quadratic functional of the
body. -/
theorem straightMamikon_quadratic_convex (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination
        (fun K ↦ straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩)) ∧
      IsConvexFunctional convexBodyCombination
        (fun K ↦ straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩)) false := by
  obtain ⟨F, hFval, hFlin⟩ := tangentLinePath_convexLinear t a b ha hb hab.le
  have hF : ∀ (K : ConvexBody Point) (s : Set.Icc a b),
      (F K).val s ∈ (supportingLineHalfPlane (K : Set Point) ((s : ℝ) : Real.Angle)).1 := by
    intro K s
    rw [hFval K]
    exact tangentLinePath_mem_supportingLine K t
      ⟨(s : ℝ), lt_of_lt_of_le ha.1 s.property.1, le_trans s.property.2 hb.2⟩
  have hval : ∀ K : ConvexBody Point,
      mamikonFunctional K a b hab hba (F K) (hF K) =
        straightMamikonValue K a b (tangentLinePath K t ⟨a, ha⟩)
          (tangentLinePath K t ⟨b, hb⟩) := by
    intro K
    have hchoose : F K = (tangentLinePath_segment_area K t a b ha hb hab.le).choose :=
      Subtype.ext ((hFval K).trans
        (tangentLinePath_segment_area K t a b ha hb hab.le).choose_spec.1.symm)
    have hstart : (F K).val ⟨a, le_rfl, hab.le⟩ = tangentLinePath K t ⟨a, ha⟩ := by
      rw [hFval K]; rfl
    have hend : (F K).val ⟨b, hab.le, le_rfl⟩ = tangentLinePath K t ⟨b, hb⟩ := by
      rw [hFval K]; rfl
    have harea : curveAreaFunctional (F K) =
        segmentArea (tangentLinePath K t ⟨a, ha⟩) (tangentLinePath K t ⟨b, hb⟩) := by
      rw [hchoose]
      exact (tangentLinePath_segment_area K t a b ha hb hab.le).choose_spec.2.2.2
    unfold mamikonFunctional straightMamikonValue
    rw [hstart, hend, harea]
  have hmain := mamikon_quadratic_convex a b hab hba F hF hFlin
  rw [funext hval] at hmain
  exact hmain

/-- The Mamikon value of a terminal tangent normal is a convex quadratic functional of the body. -/
theorem tangentMamikon_quadratic_convex (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsQuadraticFunctional convexBodyCombination (fun K ↦ tangentMamikonValue K a b) ∧
      IsConvexFunctional convexBodyCombination (fun K ↦ tangentMamikonValue K a b) false := by
  have ha : a ∈ Set.Ioc (b - Real.pi) b := ⟨by linarith, hab.le⟩
  have hb : b ∈ Set.Ioc (b - Real.pi) b := ⟨by linarith [Real.pi_pos], le_rfl⟩
  have hmain := straightMamikon_quadratic_convex b a b ha hb hab hba
  have hval : ∀ K : ConvexBody Point,
      straightMamikonValue K a b (tangentLinePath K b ⟨a, ha⟩) (tangentLinePath K b ⟨b, hb⟩) =
        tangentMamikonValue K a b := by
    intro K
    have hstart : tangentLinePath K b ⟨a, ha⟩ =
        supportingIntersection K (a : Real.Angle) (b : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left hab]
    have hend : tangentLinePath K b ⟨b, hb⟩ = (edgeVertices K (b : Real.Angle)).2 := by
      unfold tangentLinePath
      rw [ite_eq_right (lt_irrefl b)]
    have hdeg : segmentArea (edgeVertices K (b : Real.Angle)).2
        (edgeVertices K (b : Real.Angle)).2 = 0 := by
      have h := segmentArea_swap (edgeVertices K (b : Real.Angle)).2
        (edgeVertices K (b : Real.Angle)).2
      linarith
    unfold straightMamikonValue tangentMamikonValue
    rw [hstart, hend, hdeg]
    ring
  rw [funext hval] at hmain
  exact hmain

end MovingSofa
