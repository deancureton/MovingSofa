import MovingSofa.Convex.ArcJordan

/-!
# Area of the region between a convex arc and its supporting tangents

The loop built from a convex boundary arc and the two tangent segments meeting at the
intersection of the arc's endpoint supporting lines bounds the "Mamikon region" cut off by
those tangents.  The single result here bounds that region's signed area by the measure of any
set that receives it.
-/

noncomputable section

namespace MovingSofa

/-- The region between a convex boundary arc and its two supporting tangent segments has area
at most that of any finite-measure set that receives every point of a closed convex carrier of
the body which lies inside both endpoint supporting half-planes but outside the body. -/
theorem convexArc_tangentRegion_area_le (B : ConvexBody Point) (a b : ℝ)
    (hab : a < b) (hba : b < a + Real.pi)
    {C : Set Point} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (hBC : (B : Set Point) ⊆ C)
    (hOC : supportingIntersection B (a : Real.Angle) (b : Real.Angle) ∈ C)
    {E : Set Point} (hE : MeasureTheory.volume E ≠ ⊤)
    (hsubE : ∀ q ∈ interior ((supportingLineHalfPlane B (a : Real.Angle)).2 ∩
        (supportingLineHalfPlane B (b : Real.Angle)).2),
      q ∈ C → q ∉ (B : Set Point) → q ∈ E) :
    segmentArea (edgeVertices B (a : Real.Angle)).1
        (supportingIntersection B (a : Real.Angle) (b : Real.Angle)) +
      segmentArea (supportingIntersection B (a : Real.Angle) (b : Real.Angle))
        (edgeVertices B (b : Real.Angle)).2 -
      convexArcArea B a b ≤ ClassicalResults.area E := by
  have harea0 : (0 : ℝ) ≤ ClassicalResults.area E := ENNReal.toReal_nonneg
  by_cases hPQ : (edgeVertices B (a : Real.Angle)).1 = (edgeVertices B (b : Real.Angle)).2
  · -- coincident endpoints: the cut lemma collapses the arc and the intersection to one point
    obtain ⟨hO, hcar⟩ := (convexBoundaryArc_cut B a b hab hba _ _ _ rfl rfl rfl).1 hPQ
    obtain ⟨Δ, hΔcar, hΔstart, hΔend, hΔarea⟩ :=
      (segmentArea_jordan_and_frame (edgeVertices B (a : Real.Angle)).1
        (edgeVertices B (a : Real.Angle)).1).1
    have hreal : RealizesConvexArc B a b Δ :=
      ⟨hΔcar.trans ((segment_same ℝ _).trans hcar.symm), hΔstart, hΔend.trans hPQ⟩
    have hzero : segmentArea (edgeVertices B (a : Real.Angle)).1
        (edgeVertices B (a : Real.Angle)).1 = 0 := by
      simp only [segmentArea, planeCrossProduct]
      ring
    rw [convexArcArea_eq_jordanArcArea_of_realizes hreal, hΔarea, hO, ← hPQ, hzero]
    simpa using harea0
  · obtain ⟨A, p, γ, pieces, hA, hs0, hs1, hrev, hconcat, horient, hint, hdisj⟩ :=
      convexBoundaryArc_jordan B a b hab hba hPQ
    have hΓne : (Set.range γ.path.val).Nonempty :=
      ⟨_, ⟨⟨γ.a, le_rfl, γ.ordered⟩, rfl⟩⟩
    have hpiece0 : Set.range (pieces 0).path.val ⊆ C := by
      obtain ⟨φ, τ, -, -, hφs, -, -, -, heq⟩ := hs0
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      exact hconv (hBC (edgeVertices_fst_mem B _).1) hOC
        (by linarith [(τ s).property.2]) (τ s).property.1 (by ring)
    have hpiece1 : Set.range (pieces 1).path.val ⊆ C := by
      obtain ⟨φ, τ, -, -, hφs, -, -, -, heq⟩ := hs1
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      exact hconv hOC (hBC (edgeVertices_snd_mem B _).1)
        (by linarith [(τ s).property.2]) (τ s).property.1 (by ring)
    have hpiece2 : Set.range (pieces 2).path.val ⊆ C := by
      obtain ⟨φ, ψ, -, -, hφs, -, -, -, heq⟩ := hrev
      rintro _ ⟨u, rfl⟩
      obtain ⟨s, hs⟩ := hφs u
      rw [← hs, heq s]
      have hmem : ∀ v : Set.Icc p.a p.b, p.path.val v ∈ (B : Set Point) := by
        intro v
        have h : p.path.val v ∈ Set.range p.path.val := ⟨v, rfl⟩
        rw [p.range_eq, hA.1] at h
        exact convexBoundaryArc_subset_body B a b h
      exact hBC (hmem _)
    -- the whole loop lies in `C`, hence so does the region it encloses
    have hrangeC : Set.range γ.path.val ⊆ C := by
      refine hconcat.range_subset_iUnion.trans (Set.iUnion_subset ?_)
      intro i
      fin_cases i
      · exact hpiece0
      · exact hpiece1
      · exact hpiece2
    have hRC : jordanInterior (Set.range γ.path.val) ⊆ C :=
      jordanInterior_subset_of_subset_closed_convex hΓne hrangeC hconv hclosed
    -- `B` sits inside all of its supporting half-planes, so the region avoids `B`
    have hRnotB : ∀ q ∈ jordanInterior (Set.range γ.path.val), q ∉ (B : Set Point) := by
      intro q hq hqB
      refine Set.disjoint_left.mp hdisj hq (Set.mem_iInter₂.mpr fun t _ ↦ ?_)
      show inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue (B : Set Point) _
      exact inner_le_supportValue B hqB _
    have hRE : jordanInterior (Set.range γ.path.val) ⊆ E := fun q hq =>
      hsubE q (hint hq) (hRC hq) (hRnotB q hq)
    -- signed area of the counterclockwise loop is the area it encloses, and path additivity
    -- splits it into the two segments and the reversed arc
    have hloop : curveAreaFunctional γ.path =
        ClassicalResults.area (jordanInterior (Set.range γ.path.val)) :=
      curveArea_eq_jordanInterior_area γ.a γ.b γ.ordered _ γ.path horient
    have hparc : curveAreaFunctional p.path = convexArcArea B a b := by
      rw [convexArcArea_eq_jordanArcArea_of_realizes hA]
      show _ = curveAreaFunctional (Classical.choice A.property).path
      exact (curveArea_reparametrization.2.1 A.val A.val p
        (Classical.choice A.property) rfl).1 rfl rfl
    have hval : segmentArea (edgeVertices B (a : Real.Angle)).1
          (supportingIntersection B (a : Real.Angle) (b : Real.Angle)) +
        segmentArea (supportingIntersection B (a : Real.Angle) (b : Real.Angle))
          (edgeVertices B (b : Real.Angle)).2 - convexArcArea B a b =
        curveAreaFunctional γ.path := by
      rw [curveArea_concatenation γ pieces hconcat, Fin.sum_univ_three,
        hs0.curveAreaFunctional_eq, hs1.curveAreaFunctional_eq,
        hrev.curveAreaFunctional_eq, hparc]
      ring
    rw [hval, hloop]
    have hle : MeasureTheory.volume (jordanInterior (Set.range γ.path.val)) ≤
        MeasureTheory.volume E := MeasureTheory.measure_mono hRE
    exact (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hE hle) hE).mpr hle

end MovingSofa
