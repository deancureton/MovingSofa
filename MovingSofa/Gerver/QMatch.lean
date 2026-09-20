import MovingSofa.Gerver.TailGeometry
import MovingSofa.Bounds.Upper.Q

/-!
# Gerver's cap attains the upper bound `Q`

`gerver_upperBoundQ_matches` evaluates the upper-bound functional `Q` at the cap of Gerver's
sofa together with its two canonical tails, and finds the sofa area functional `A` there.

The niche area is read off the four-piece counterclockwise traversal of the niche boundary
(`gerver_niche_orientation`): additivity of the curve area functional over that traversal
(`curveArea_concatenation`) expresses the niche area as the curve area of the middle corner
path minus the curve areas of the two inner contact curves, because the two contact pieces are
traversed backwards and the base segment lies on the line `y = 0`.  The tail geometry
(`gerver_tailGeometry`) identifies the two contact curves with the two convex tail arcs, so
their curve areas are the two `convexArcArea` terms of `Q`, and it identifies the two corners
of `Q`'s connector segments, whose signed areas therefore vanish.
-/

noncomputable section

namespace MovingSofa

/-! ## The four-piece traversal of the niche boundary -/

/-- The niche traversal is the concatenation of four pieces, each reparametrized by `[0, 1]`
through an increasing surjection: the second contact curve reversed, the inner corner path over
`[t₁, t₄]`, the fourth contact curve reversed, and the base segment.  The two reversed contact
pieces enter as bounded-variation paths `y₁`, `y₃` on `[0, 1]`, described by the two affine
parameter changes of the traversal. -/
private theorem isPathConcatenation_gerverNicheBoundary (K : SpecialCapSpace)
    (hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K.val t = paperGerverPath t)
    {Γ : ContinuousBVPaths 0 4} (hΓ : Γ.val = gerverNicheBoundary)
    {y₁ y₃ : ContinuousBVPaths 0 1}
    (hy₁ : ∀ u : Set.Icc (0 : ℝ) 1, y₁.val u =
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (u : ℝ)) 1)
    (hy₃ : ∀ u : Set.Icc (0 : ℝ) 1, y₃.val u =
      paperGerverContacts (gerverStageTimes 2 * (1 - (u : ℝ))) 3) :
    IsPathConcatenation (⟨0, 4, by norm_num, Γ⟩ : RectifiablePathData)
      ![(⟨0, 1, zero_le_one, y₁⟩ : RectifiablePathData),
        ⟨gerverStageTimes 1, gerverStageTimes 4,
          (gerverStageTimes_strictMono (show (1 : Fin 6) < 4 by decide)).le, capMiddleBV K⟩,
        ⟨0, 1, zero_le_one, y₃⟩,
        ⟨0, 1, zero_le_one, lineSegmentBVPath (paperGerverContacts 0 3)
          (paperGerverContacts (Real.pi / 2) 1)⟩] := by
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h01 : gerverStageTimes 0 < gerverStageTimes 1 :=
    gerverStageTimes_strictMono (show (0 : Fin 6) < 1 by decide)
  have h45 : gerverStageTimes 4 < gerverStageTimes 5 :=
    gerverStageTimes_strictMono (show (4 : Fin 6) < 5 by decide)
  obtain ⟨ψ₂, hψ₂c, hψ₂m, hψ₂s, hψ₂v⟩ := Set.Icc.exists_affine_monotone_surjection zero_lt_one
    (gerverStageTimes_strictMono (show (1 : Fin 6) < 4 by decide))
  refine ⟨by norm_num, ![⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨2, by norm_num⟩,
    ⟨3, by norm_num⟩, ⟨4, by norm_num⟩], ?_, rfl, rfl, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (exact absurd hij (by decide))
        | (refine Subtype.mk_le_mk.mpr ?_; norm_num)
  · intro i
    fin_cases i
    -- ### `[0, 1]`: the second contact curve, reversed
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 0 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, id, hϕc, hϕm, hϕs, continuous_id, monotone_id, Function.surjective_id,
        fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      have harg : Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (ϕ u : ℝ) =
          Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (u : ℝ) := by rw [hv]; ring
      rw [hΓ]
      refine (gerverNicheBoundary_of_le_one hmem (by rw [hv]; linarith [u.2.2])).trans ?_
      rw [harg]
      exact (hy₁ u).symm
    -- ### `[1, 2]`: the inner corner path, forwards
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (1 : ℝ) 2, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 1 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, ψ₂, hϕc, hϕm, hϕs, hψ₂c, hψ₂m, hψ₂s, fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      have hψmem : (ψ₂ u : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [(ψ₂ u).2.1], by linarith [(ψ₂ u).2.2]⟩
      have harg : gerverStageTimes 1 +
          (gerverStageTimes 4 - gerverStageTimes 1) * ((ϕ u : ℝ) - 1) = (ψ₂ u : ℝ) := by
        rw [hv, hψ₂v u]; ring
      rw [hΓ]
      refine (gerverNicheBoundary_mid hmem (by rw [hv]; linarith [u.2.1])
        (by rw [hv]; linarith [u.2.2])).trans ?_
      rw [harg]
      exact (hcorner _ hψmem).symm
    -- ### `[2, 3]`: the fourth contact curve, reversed
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (2 : ℝ) 3, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 2 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, id, hϕc, hϕm, hϕs, continuous_id, monotone_id, Function.surjective_id,
        fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      have harg : gerverStageTimes 2 * (3 - (ϕ u : ℝ)) =
          gerverStageTimes 2 * (1 - (u : ℝ)) := by rw [hv]; ring
      rw [hΓ]
      refine (gerverNicheBoundary_third hmem (by rw [hv]; linarith [u.2.1])
        (by rw [hv]; linarith [u.2.2])).trans ?_
      rw [harg]
      exact (hy₃ u).symm
    -- ### `[3, 4]`: the base segment
    · obtain ⟨ϕ, hϕc, hϕm, hϕs, hϕv⟩ :
          ∃ ϕ : Set.Icc (0 : ℝ) 1 → Set.Icc (3 : ℝ) 4, Continuous ϕ ∧ Monotone ϕ ∧
            Function.Surjective ϕ ∧ ∀ u : Set.Icc (0 : ℝ) 1, (ϕ u : ℝ) = 3 + (u : ℝ) :=
        Set.Icc.exists_translation_surjection (by norm_num)
      refine ⟨ϕ, id, hϕc, hϕm, hϕs, continuous_id, monotone_id, Function.surjective_id,
        fun u ↦ ?_⟩
      have hv := hϕv u
      have hmem : (ϕ u : ℝ) ∈ Set.Icc (0 : ℝ) 4 :=
        ⟨by rw [hv]; linarith [u.2.1], by rw [hv]; linarith [u.2.2]⟩
      rw [hΓ]
      refine (gerverNicheBoundary_base hmem (by rw [hv]; linarith [u.2.1])).trans ?_
      show _ = (lineSegmentBVPath (paperGerverContacts 0 3)
        (paperGerverContacts (Real.pi / 2) 1)).val u
      rw [lineSegmentBVPath_apply, hv, show (4 : ℝ) - (3 + (u : ℝ)) = 1 - (u : ℝ) from by ring,
        show (3 : ℝ) + (u : ℝ) - 3 = (u : ℝ) from by ring]

/-- Additivity of the curve area functional over the four-piece traversal of the niche
boundary.  The base segment contributes nothing because both of its endpoints lie on the line
`y = 0`, and the two contact pieces are traversed backwards, so their reparametrizations
contribute the negatives of their curve areas. -/
private theorem curveAreaFunctional_gerverNicheBoundary (K : SpecialCapSpace)
    (hcorner : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      capInnerCorner K.val t = paperGerverPath t)
    {Γ : ContinuousBVPaths 0 4} (hΓ : Γ.val = gerverNicheBoundary) :
    curveAreaFunctional Γ = curveAreaFunctional (capMiddleBV K) -
      curveAreaFunctional gerverRightContactBV - curveAreaFunctional gerverLeftContactBV := by
  have h0 : gerverStageTimes 0 = 0 := gerverStageTimes_zero
  have h5 : gerverStageTimes 5 = Real.pi / 2 := rfl
  have h35 : gerverStageTimes 3 < gerverStageTimes 5 :=
    gerverStageTimes_strictMono (show (3 : Fin 6) < 5 by decide)
  have h02 : gerverStageTimes 0 < gerverStageTimes 2 :=
    gerverStageTimes_strictMono (show (0 : Fin 6) < 2 by decide)
  obtain ⟨φ₁, hφ₁c, hφ₁a, hφ₁s, hφ₁v⟩ :=
    Set.Icc.exists_affine_antitone_surjection zero_lt_one h35
  obtain ⟨φ₃, hφ₃c, hφ₃a, hφ₃s, hφ₃v⟩ :=
    Set.Icc.exists_affine_antitone_surjection zero_lt_one h02
  obtain ⟨y₁, hy₁val, -, hy₁area⟩ := curveArea_reparametrization.1 _ _ 0 1 h35 zero_lt_one
    gerverRightContactBV φ₁ hφ₁c hφ₁s (Or.inr hφ₁a)
  obtain ⟨y₃, hy₃val, -, hy₃area⟩ := curveArea_reparametrization.1 _ _ 0 1 h02 zero_lt_one
    gerverLeftContactBV φ₃ hφ₃c hφ₃s (Or.inr hφ₃a)
  have hy₁ : ∀ u : Set.Icc (0 : ℝ) 1, y₁.val u =
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (u : ℝ)) 1 := by
    intro u
    rw [hy₁val]
    exact congrArg (fun r : ℝ ↦ paperGerverContacts r 1) (by rw [hφ₁v u, h5]; ring)
  have hy₃ : ∀ u : Set.Icc (0 : ℝ) 1, y₃.val u =
      paperGerverContacts (gerverStageTimes 2 * (1 - (u : ℝ))) 3 := by
    intro u
    rw [hy₃val]
    exact congrArg (fun r : ℝ ↦ paperGerverContacts r 3) (by rw [hφ₃v u, h0]; ring)
  have hsum : curveAreaFunctional Γ = curveAreaFunctional y₁ +
      curveAreaFunctional (capMiddleBV K) + curveAreaFunctional y₃ +
      curveAreaFunctional (lineSegmentBVPath (paperGerverContacts 0 3)
        (paperGerverContacts (Real.pi / 2) 1)) := by
    have h := curveArea_concatenation (⟨0, 4, by norm_num, Γ⟩ : RectifiablePathData) _
      (isPathConcatenation_gerverNicheBoundary K hcorner hΓ hy₁ hy₃)
    rw [Fin.sum_univ_four] at h
    exact h
  have hseg : curveAreaFunctional (lineSegmentBVPath (paperGerverContacts 0 3)
      (paperGerverContacts (Real.pi / 2) 1)) = 0 := by
    rw [curveAreaFunctional_lineSegmentBVPath, segmentArea, planeCrossProduct,
      gerver_niche_piece_endpoints.2.2.1, gerver_niche_piece_endpoints.2.2.2]
    ring
  rw [hsum, hseg, hy₁area hφ₁a, hy₃area hφ₃a]
  ring

/-! ## The niche area of the Gerver cap -/

/-- The niche area of the Gerver cap, in terms of the signed curve areas of the three
nondegenerate pieces of its boundary traversal: the middle corner path, and the two inner
contact curves, which the traversal runs backwards. -/
theorem gerver_capNiche_area_eq (K : SpecialCapSpace)
    (hK : (K.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2)) :
    ClassicalResults.area (capNiche K.val) =
      curveAreaFunctional (capMiddleBV K) - curveAreaFunctional gerverRightContactBV -
        curveAreaFunctional gerverLeftContactBV := by
  obtain ⟨-, hGeq, -, -, hcapeq, -, -⟩ := gerver_capSupport_identification
  have hcarrier : (K.val.val : Set Point) = gerverOuterCap := by rw [hK, hGeq, hcapeq]
  obtain ⟨K₃, hK₃set, Γ, hΓ, -, -, -, harea, -, -, -⟩ := gerver_niche_orientation
  have h3eq : K₃ = K.val := Subtype.ext (SetLike.coe_injective (hK₃set.trans hcarrier.symm))
  subst h3eq
  rw [← harea]
  exact curveAreaFunctional_gerverNicheBoundary K
    (fun _ ht ↦ capInnerCorner_eq_paperGerverPath K.val hK ht) hΓ

/-! ## The value of `Q` at Gerver's cap -/

theorem gerver_upperBoundQ_matches (X : CapTailSpace)
    (hK : (X.cap.val.val : Set Point) = capOfSofa paperGerverSofa (Real.pi / 2))
    (hB : (X.rightBody : Set Point) = (canonicalTailSets X.cap).1)
    (hD : (X.leftBody : Set Point) = (canonicalTailSets X.cap).2) :
    rightAngleAreaFunctional X.cap.val = upperBoundQ X := by
  obtain ⟨-, -, hxL, hYD, -, hparamD, hxR, hXB, -, hparamB, -, -⟩ :=
    gerver_tailGeometry X.cap X.rightBody X.leftBody hK hB hD
  obtain ⟨hltB, -, hinjB, himgB, hstartB, hendB⟩ := hparamB
  obtain ⟨hltD, -, hinjD, himgD, hstartD, hendD⟩ := hparamD
  -- ### The two tail arcs carry the curve areas of the two inner contact curves
  have hareaB : convexArcArea X.rightBody (Real.pi + paperGerverConstants.2.1)
      (3 * Real.pi / 2) = curveAreaFunctional gerverRightContactBV :=
    convexArcArea_eq_curveAreaFunctional_of_injOn gerverRightContactBV hltB
      gerverRightContactBV_apply hinjB himgB hstartB hendB
  have hareaD : convexArcArea X.leftBody (3 * Real.pi / 2)
      (3 * Real.pi / 2 + paperGerverConstants.2.2) = curveAreaFunctional gerverLeftContactBV :=
    convexArcArea_eq_curveAreaFunctional_of_injOn gerverLeftContactBV hltD
      gerverLeftContactBV_apply hinjD himgD hstartD hendD
  -- ### Both connector segments have coincident endpoints, hence vanishing signed area
  have hsegL : segmentArea (rightLeftTailArcs X.rightBody X.leftBody).2.endPoint
      (distinguishedCapSides X.cap.val).2.corner = 0 := by
    rw [hYD, hxL, segmentArea, planeCrossProduct]; ring
  have hsegR : segmentArea (distinguishedCapSides X.cap.val).1.corner
      (rightLeftTailArcs X.rightBody X.leftBody).1.startPoint = 0 := by
    rw [hxR, hXB, segmentArea, planeCrossProduct]; ring
  simp only [rightAngleAreaFunctional, capAreaFunctional, upperBoundQ]
  rw [hareaB, hareaD, hsegL, hsegR, gerver_capNiche_area_eq X.cap hK]
  ring

end MovingSofa
