import MovingSofa.Area.Mamikon.TangentValues
import MovingSofa.Convex.OuterCornerPath

noncomputable section

namespace MovingSofa

theorem sofaMamikon_quadratic_convex :
    IsConvexFunctional specialCapCombination middleMamikon false ∧
    IsQuadraticFunctional specialCapCombination middleMamikon ∧
    IsConvexFunctional convexBodyCombination rightTailMamikon false ∧
    IsQuadraticFunctional convexBodyCombination rightTailMamikon ∧
    IsConvexFunctional convexBodyCombination leftTailMamikon false ∧
    IsQuadraticFunctional convexBodyCombination leftTailMamikon := by
  obtain ⟨hrIoo, hlIoo, hsum⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  have hrl := paperGerverConstants_snd_fst_lt_snd_snd
  have hr0 := hrIoo.1
  have hr2 := hrIoo.2
  have hl0 := hlIoo.1
  have hl2 := hlIoo.2
  -- ### The two tail functionals are terminal tangent Mamikon values
  have htailR := tangentMamikon_quadratic_convex (Real.pi + paperGerverConstants.2.1)
    (3 * Real.pi / 2) (by linarith) (by linarith)
  have htailL := tangentMamikon_quadratic_convex (3 * Real.pi / 2)
    (3 * Real.pi / 2 + paperGerverConstants.2.2) (by linarith) (by linarith)
  -- ### The first middle summand
  have ha1 : (0 : ℝ) ∈ Set.Ioc (Real.pi / 2 - Real.pi) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hb1 : paperGerverConstants.2.1 ∈ Set.Ioc (Real.pi / 2 - Real.pi) (Real.pi / 2) :=
    ⟨by linarith, by linarith⟩
  have hmid1 := straightMamikon_quadratic_convex (Real.pi / 2) 0 paperGerverConstants.2.1
    ha1 hb1 (by linarith) (by linarith)
  -- ### The third middle summand
  have ha3 : paperGerverConstants.2.2 ∈
      Set.Ioc (Real.pi / 2 + paperGerverConstants.2.2 - Real.pi)
        (Real.pi / 2 + paperGerverConstants.2.2) := ⟨by linarith, by linarith⟩
  have hb3 : (Real.pi / 2 : ℝ) ∈
      Set.Ioc (Real.pi / 2 + paperGerverConstants.2.2 - Real.pi)
        (Real.pi / 2 + paperGerverConstants.2.2) := ⟨by linarith, by linarith⟩
  have hmid3 := straightMamikon_quadratic_convex (Real.pi / 2 + paperGerverConstants.2.2)
    paperGerverConstants.2.2 (Real.pi / 2) ha3 hb3 (by linarith) (by linarith)
  -- ### The fourth middle summand
  have hmid4 := tangentMamikon_quadratic_convex (Real.pi / 2) Real.pi (by linarith) (by linarith)
  -- ### The second middle summand, the Mamikon value of the outer-corner path
  obtain ⟨γ, hγ, hγlin⟩ := exists_outerCornerBV_convexLinear paperGerverConstants.2.1
    paperGerverConstants.2.2
  have hγmem : ∀ (B : ConvexBody Point)
      (s : Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2),
      (γ B).val s ∈ (supportingLineHalfPlane (B : Set Point) ((s : ℝ) : Real.Angle)).1 := by
    intro B s
    rw [hγ B s]
    show inner ℝ (rotatingHallwayParts (B : Set Point) ((s : ℝ) : Real.Angle)).outerCorner
      (normalVector ((s : ℝ) : Real.Angle)) = supportValue (B : Set Point) ((s : ℝ) : Real.Angle)
    rw [outerCorner_eq_support_sum B (s : ℝ), inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_normalVector_self, real_inner_comm,
      inner_normalVector_tangentVector]
    ring
  have hmid2 := mamikon_quadratic_convex paperGerverConstants.2.1 paperGerverConstants.2.2
    hrl (by linarith) γ hγmem hγlin
  -- ### The four middle summands assemble to the middle functional on all bodies
  have hquadAll := ((hmid1.1.add hmid2.1).add hmid3.1).add hmid4.1
  have hconvAll := ((hmid1.2.add hmid2.2).add hmid3.2).add hmid4.2
  have hbody : IsConvexLinear specialCapCombination convexBodyCombination
      fun K : SpecialCapSpace ↦ K.val.val := specialCap_isConvexDomain.1
  have hquad := hquadAll.comp_isConvexLinear hbody
  have hconv := hconvAll.comp_isConvexLinear hbody
  have hmideq : (fun K : SpecialCapSpace ↦
      ((straightMamikonValue K.val.val 0 paperGerverConstants.2.1
          (tangentLinePath K.val.val (Real.pi / 2) ⟨0, ha1⟩)
          (tangentLinePath K.val.val (Real.pi / 2) ⟨paperGerverConstants.2.1, hb1⟩) +
        mamikonFunctional K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 hrl
          (by linarith) (γ K.val.val) (hγmem K.val.val)) +
        straightMamikonValue K.val.val paperGerverConstants.2.2 (Real.pi / 2)
          (tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
            ⟨paperGerverConstants.2.2, ha3⟩)
          (tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
            ⟨Real.pi / 2, hb3⟩)) +
        tangentMamikonValue K.val.val (Real.pi / 2) Real.pi) = middleMamikon := by
    funext K
    have hpath1 : tangentLinePath K.val.val (Real.pi / 2) ⟨0, ha1⟩ =
        supportingIntersection K.val.val 0 ((Real.pi / 2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (show (0 : ℝ) < Real.pi / 2 by linarith), Real.Angle.coe_zero]
    have hpath2 : tangentLinePath K.val.val (Real.pi / 2)
        ⟨paperGerverConstants.2.1, hb1⟩ =
        supportingIntersection K.val.val ((paperGerverConstants.2.1 : ℝ) : Real.Angle)
          ((Real.pi / 2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left hr2]
    have hpath3 : tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
        ⟨paperGerverConstants.2.2, ha3⟩ =
        supportingIntersection K.val.val ((paperGerverConstants.2.2 : ℝ) : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (by linarith)]
    have hpath4 : tangentLinePath K.val.val (Real.pi / 2 + paperGerverConstants.2.2)
        ⟨Real.pi / 2, hb3⟩ =
        supportingIntersection K.val.val ((Real.pi / 2 : ℝ) : Real.Angle)
          ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
      unfold tangentLinePath
      rw [ite_eq_left (by linarith)]
    have hγeq : γ K.val.val = capOuterMiddleBV K :=
      Subtype.ext (funext fun s ↦ (hγ K.val.val s).trans (capOuterMiddleBV_val K s).symm)
    have hmam : mamikonFunctional K.val.val paperGerverConstants.2.1
        paperGerverConstants.2.2 hrl (by linarith) (γ K.val.val) (hγmem K.val.val) =
        segmentArea (edgeVertices K.val.val ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).1
            ((rotatingHallwayParts (K.val.val : Set Point)
              ((paperGerverConstants.2.1 : ℝ) : Real.Angle)).outerCorner) +
          curveAreaFunctional (capOuterMiddleBV K) +
          segmentArea ((rotatingHallwayParts (K.val.val : Set Point)
              ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).outerCorner)
            (edgeVertices K.val.val ((paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 -
          convexArcArea K.val.val paperGerverConstants.2.1 paperGerverConstants.2.2 := by
      unfold mamikonFunctional
      rw [hγ K.val.val ⟨paperGerverConstants.2.1, le_rfl, hrl.le⟩,
        hγ K.val.val ⟨paperGerverConstants.2.2, hrl.le, le_rfl⟩, hγeq]
    show _ = middleMamikon K
    unfold middleMamikon
    rw [hpath1, hpath2, hpath3, hpath4, hmam]
  rw [hmideq] at hquad hconv
  exact ⟨hconv, hquad, htailR.2, htailR.1, htailL.2, htailL.1⟩

end MovingSofa
