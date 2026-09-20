import MovingSofa.Cap.BalancedExistence
import MovingSofa.Cap.Injectivity
import MovingSofa.Cap.Interpolation
import MovingSofa.Convex.AreaSuperlevel
import MovingSofa.Convex.Linearity
import MovingSofa.Convex.Space
import MovingSofa.Gerver.Area
import MovingSofa.Gerver.Injectivity
import MovingSofa.Gerver.Niche.Identification
import MovingSofa.Sofa.Area

noncomputable section

open scoped unitInterval

namespace MovingSofa

def specialCapCombination (t : I) (K L : SpecialCapSpace) : SpecialCapSpace := by
  classical
  exact if h : ∃ M : SpecialCapSpace,
    M.val.val = convexBodyCombination t K.val.val L.val.val then h.choose else K

theorem specialCap_isConvexDomain :
    (∀ t K L, (specialCapCombination t K L).val.val =
      convexBodyCombination t K.val.val L.val.val) ∧
    IsConvexDomain.{0, 0} specialCapCombination ∧
    (∀ K : RightAngleCapSpace, IsBalancedMaximumCap K →
      ∃ L : SpecialCapSpace, L.val = K) ∧
    (∃ K : SpecialCapSpace,
      (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) := by
  -- ### The special class is closed under Minkowski interpolation
  have hclosed : ∀ (t : I) (K L : SpecialCapSpace), ∃ M : SpecialCapSpace,
      M.val.val = convexBodyCombination t K.val.val L.val.val := fun t K L ↦
    ⟨⟨⟨convexBodyCombination t K.val.val L.val.val,
        isCap_convexBodyCombination t K.val L.val⟩,
      satisfiesInjectivityCondition_of_eq_convexBodyCombination rfl K.property.1 L.property.1,
      convexBody_area_superlevel _ _ K.property.2 L.property.2 t⟩, rfl⟩
  have h1 : ∀ (t : I) (K L : SpecialCapSpace), (specialCapCombination t K L).val.val =
      convexBodyCombination t K.val.val L.val.val := by
    intro t K L
    have h := hclosed t K L
    rw [specialCapCombination, dite_eq_left h]
    exact h.choose_spec
  -- ### The sofa area functional is bounded by the cap area
  have hfunc : ∀ C : RightAngleCapSpace,
      capAreaFunctional C ≤ ClassicalResults.area (C.val : Set Point) := by
    intro C
    have h : (0 : ℝ) ≤ ClassicalResults.area (capNiche C) := ENNReal.toReal_nonneg
    simp only [capAreaFunctional]
    linarith
  -- ### Gerver's cap is a special cap
  obtain ⟨KG, hKGset, hKGinj⟩ := paperGerverCap_injectivity
  have hstd : IsStandardPosition paperGerverSofa (Real.pi / 2) :=
    gerver_capSupport_identification.2.1 ▸ gerver_capSupport_identification.2.2.1
  have hGfunc : capAreaFunctional KG = ClassicalResults.area paperGerverSofa :=
    capAreaFunctional_eq_sofaArea paperGerverSofa (Real.pi / 2)
      ⟨paperGerverSofa, hstd, gerver_paperNiche_identification.2.2.1.symm⟩ KG hKGset
  have hGbound : (11 : ℝ) / 5 ≤ capAreaFunctional KG := by
    rw [hGfunc, ← gerver_canonical_paper_literal.1]
    exact gerver_area_lower_bound.2
  have hGarea : (11 : ℝ) / 5 ≤ ClassicalResults.area (KG.val : Set Point) :=
    hGbound.trans (hfunc KG)
  refine ⟨h1, ?_, ?_, ⟨⟨KG, hKGinj, hGarea⟩, hKGset⟩⟩
  -- ### The convex-domain structure restricts from the ambient body domain
  · obtain ⟨V, e, hinj, -, hcomb⟩ := convexBody_isConvexDomain
    refine ⟨V, fun K ↦ e K.val.val, ?_, ?_, fun t K L ↦
      (congrArg e (h1 t K L)).trans (hcomb t K.val.val L.val.val)⟩
    · intro K L h
      exact Subtype.ext (Subtype.ext (hinj h))
    · rintro _ ⟨K, rfl⟩ _ ⟨L, rfl⟩ a b ha hb hab
      have hb1 : b ≤ 1 := by linarith
      refine ⟨specialCapCombination ⟨b, hb, hb1⟩ K L, ?_⟩
      have hba : 1 - b = a := by linarith
      simpa only [hba] using (congrArg e (h1 ⟨b, hb, hb1⟩ K L)).trans
        (hcomb ⟨b, hb, hb1⟩ K.val.val L.val.val)
  -- ### Every balanced maximum cap is special
  · intro K hK
    refine ⟨⟨K, balancedMaximumCap_injectivity K hK, ?_⟩, rfl⟩
    exact hGbound.trans ((balancedMaximumCap_maximizes_area K hK KG).trans (hfunc K))

/-- The extreme face vertices and the intersections of supporting lines of a special cap are
convex-linear along `specialCapCombination`: the underlying bodies interpolate, and both quantities
are convex-linear in the body. -/
theorem specialCap_maps_linear (t : I) (K L : SpecialCapSpace) :
    (∀ a : Real.Angle,
      (edgeVertices (specialCapCombination t K L).val.val a).1 =
          (1 - (t : ℝ)) • (edgeVertices K.val.val a).1 +
            (t : ℝ) • (edgeVertices L.val.val a).1 ∧
        (edgeVertices (specialCapCombination t K L).val.val a).2 =
          (1 - (t : ℝ)) • (edgeVertices K.val.val a).2 +
            (t : ℝ) • (edgeVertices L.val.val a).2) ∧
    ∀ a b : ℝ, a < b → b < a + Real.pi →
      supportingIntersection (specialCapCombination t K L).val.val (a : Real.Angle)
          (b : Real.Angle) =
        (1 - (t : ℝ)) • supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) +
          (t : ℝ) • supportingIntersection L.val.val (a : Real.Angle) (b : Real.Angle) := by
  obtain ⟨-, hev, hsi, -⟩ := convexBody_maps_linear t K.val.val L.val.val
  rw [specialCap_isConvexDomain.1 t K L]
  exact ⟨hev, hsi⟩

end MovingSofa
