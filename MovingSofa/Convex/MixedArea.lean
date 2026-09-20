import MovingSofa.Convex.Linearity

/-!
# The mixed area of two planar convex bodies

The mixed support integral `∫ h_K dσ_L` is symmetric in the two bodies, and the area of the
Minkowski segment `λ ↦ |(1 - λ) K + λ L|` is therefore the quadratic
`(1 - λ)² |K| + λ (1 - λ) ∫ h_L dσ_K + λ² |L|`, whose right derivative at `λ = 0` is
`∫ (h_L - h_K) dσ_K`.

The symmetry itself is `MovingSofa.supportIntegral_symm` in `MovingSofa.Convex.SupportArea`.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- Symmetry of the mixed support integral, together with the right derivative at `0` of the
area along the Minkowski segment from `K` to `L`. -/
theorem supportMeasure_mixedArea_symmetry (K L : ConvexBody Point) :
    (∫ t : Real.Angle, supportValue K t ∂surfaceAreaMeasure L) =
      (∫ t : Real.Angle, supportValue L t ∂surfaceAreaMeasure K) ∧
    HasDerivWithinAt
      (segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L)
      (∫ t : Real.Angle, supportValue L t - supportValue K t ∂surfaceAreaMeasure K)
      (Set.Icc (0 : ℝ) 1) 0 := by
  classical
  have hsymm := supportIntegral_symm K L
  refine ⟨hsymm, ?_⟩
  obtain ⟨harea, hbil, -⟩ := convexBody_area_support_integral
  have hcont (M : ConvexBody Point) : Continuous (supportValue M) :=
    (compactSet_support_continuity M M M.nonempty M.isCompact M.nonempty M.isCompact).2.2.1
  have hint : ∀ M N : ConvexBody Point, Integrable (supportValue M) (surfaceAreaMeasure N) := by
    intro M N
    let _ : IsFiniteMeasure (surfaceAreaMeasure N) := (surfaceAreaMeasure_face_union N).1
    exact (hcont M).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _))
  rw [integral_sub (hint L K) (hint K K)]
  have hfun : ∀ lam ∈ Set.Icc (0 : ℝ) 1,
      segmentFunctional convexBodyCombination
          (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L lam =
        1 / 2 * (∫ t, supportValue K t ∂surfaceAreaMeasure K) +
          ((∫ t, supportValue L t ∂surfaceAreaMeasure K) -
            ∫ t, supportValue K t ∂surfaceAreaMeasure K) * lam +
          (1 / 2 * (∫ t, supportValue K t ∂surfaceAreaMeasure K) -
            (∫ t, supportValue L t ∂surfaceAreaMeasure K) +
            1 / 2 * ∫ t, supportValue L t ∂surfaceAreaMeasure L) * lam ^ 2 := by
    intro lam hlam
    have hseg : segmentFunctional convexBodyCombination
        (fun M : ConvexBody Point ↦ ClassicalResults.area (M : Set Point)) K L lam =
        ClassicalResults.area
          ((convexBodyCombination ⟨lam, hlam⟩ K L : ConvexBody Point) : Set Point) :=
      dite_eq_left hlam
    have h2 := hbil.2 (convexBodyCombination ⟨lam, hlam⟩ K L) ⟨lam, hlam⟩ K L
    have h3 := hbil.1 K ⟨lam, hlam⟩ K L
    have h4 := hbil.1 L ⟨lam, hlam⟩ K L
    simp only [realCombination] at h2 h3 h4
    rw [hseg, harea (convexBodyCombination ⟨lam, hlam⟩ K L), h2, h3, h4, hsymm]
    ring
  have hpoly : ∀ A B C : ℝ, HasDerivAt (fun lam : ℝ ↦ A + B * lam + C * lam ^ 2) B 0 := by
    intro A B C
    have h : HasDerivAt (fun lam : ℝ ↦ A + B * lam + C * lam ^ 2)
        (0 + B * 1 + C * (2 * 0 ^ 1)) 0 :=
      HasDerivAt.add (HasDerivAt.add (hasDerivAt_const _ _)
        ((hasDerivAt_id _).const_mul _)) ((hasDerivAt_pow _ _).const_mul _)
    simpa using h
  exact HasDerivWithinAt.congr (hpoly _ _ _).hasDerivWithinAt hfun
    (hfun 0 ⟨le_rfl, zero_le_one⟩)

end MovingSofa
