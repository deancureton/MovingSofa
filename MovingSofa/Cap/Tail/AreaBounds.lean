import MovingSofa.Convex.ArcRegionArea
import MovingSofa.Area.Mamikon.Tails

noncomputable section

namespace MovingSofa

/-- A point of a special cap above both the right inner wall at `φᴿ` and the bottom axis that
misses the right canonical tail lies in the niche, on the right side. -/
private theorem mem_capNiche_inter_right_of_notMem_canonicalTail (K : SpecialCapSpace)
    {q : Point} (hwall : q ∈ (innerWallUpperHalfPlanes K.val paperGerverConstants.2.1).1)
    (hup : q ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false)
    (hqK : q ∈ (K.1.1 : Set Point)) (hq : q ∉ (canonicalTailSets K).1) :
    q ∈ capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane := by
  obtain ⟨hrIoo, -, -⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨hmonR, -, -, -⟩ := cap_tail_monotonicity_intervals K
  have hUpEqR : (innerWallUpperHalfPlanes K.val (Real.pi / 2)).1 =
      normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
    show normalHalfPlane _ (supportValue (K.1.1 : Set Point) _ - 1) true false = _
    rw [K.1.property.2.2.2.1, sub_self]
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2),
      q ∉ (innerWallUpperHalfPlanes K.val t).1 := by
    by_contra hc
    exact hq ⟨hqK, Set.mem_iInter₂.mpr fun t ht ↦ not_not.mp fun h ↦ hc ⟨t, ht, h⟩⟩
  have htlow : paperGerverConstants.2.1 < t :=
    ht.1.lt_of_ne fun h ↦ hqt (h ▸ hwall)
  have hthigh : t < Real.pi / 2 :=
    ht.2.lt_of_ne fun h ↦ hqt (by rw [h, hUpEqR]; exact hup)
  have hmem : q ∈ (distinguishedCapSides K.val).1.upperHalfPlane ∩
      innerQuadrant (K.val.val : Set Point) t := by
    rw [(hmonR t ⟨htlow, ht.2⟩).2]
    exact ⟨hwall, hqt⟩
  exact ⟨⟨⟨hup, hup⟩,
    Set.mem_iUnion₂.mpr ⟨t, ⟨hrIoo.1.trans htlow, hthigh⟩, hmem.2⟩⟩, hwall⟩

/-- A point of a special cap above both the left inner wall at `φᴸ` and the bottom axis that
misses the left canonical tail lies in the niche, on the left side. -/
private theorem mem_capNiche_inter_left_of_notMem_canonicalTail (K : SpecialCapSpace)
    {q : Point} (hwall : q ∈ (innerWallUpperHalfPlanes K.val paperGerverConstants.2.2).2)
    (hup : q ∈ normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false)
    (hqK : q ∈ (K.1.1 : Set Point)) (hq : q ∉ (canonicalTailSets K).2) :
    q ∈ capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane := by
  obtain ⟨-, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  obtain ⟨-, hmonL, -, -⟩ := cap_tail_monotonicity_intervals K
  have hUpEqL : (innerWallUpperHalfPlanes K.val 0).2 =
      normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
    have hzero : ((((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)) =
        ((Real.pi / 2 : ℝ) : Real.Angle) := by rw [zero_add]
    show normalHalfPlane (((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue (K.1.1 : Set Point) (((0 : ℝ) + Real.pi / 2 : ℝ) : Real.Angle) - 1)
        true false = _
    rw [hzero, K.1.property.2.2.2.1, sub_self]
  obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      q ∉ (innerWallUpperHalfPlanes K.val t).2 := by
    by_contra hc
    exact hq ⟨hqK, Set.mem_iInter₂.mpr fun t ht ↦ not_not.mp fun h ↦ hc ⟨t, ht, h⟩⟩
  have htlow : 0 < t := ht.1.lt_of_ne fun h ↦ hqt (by rw [← h, hUpEqL]; exact hup)
  have hthigh : t < paperGerverConstants.2.2 := ht.2.lt_of_ne fun h ↦ hqt (h ▸ hwall)
  have hmem : q ∈ (distinguishedCapSides K.val).2.upperHalfPlane ∩
      innerQuadrant (K.val.val : Set Point) t := by
    rw [(hmonL t ⟨ht.1, hthigh⟩).2]
    exact ⟨hwall, hqt⟩
  exact ⟨⟨⟨hup, hup⟩,
    Set.mem_iUnion₂.mpr ⟨t, ⟨htlow, hthigh.trans hlIoo.2⟩, hmem.2⟩⟩, hwall⟩

theorem canonicalTail_niche_area_lower_bounds (K : SpecialCapSpace)
    (B D : ConvexBody Point)
    (hB : (B : Set Point) = (canonicalTailSets K).1)
    (hD : (D : Set Point) = (canonicalTailSets K).2) :
    segmentArea (rightLeftTailArcs B D).1.startPoint
        (distinguishedCapSides K.val).1.fanPoint -
      convexArcArea B (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2) ≤
        ClassicalResults.area
          (capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∧
    segmentArea (distinguishedCapSides K.val).2.fanPoint
        (rightLeftTailArcs B D).2.endPoint -
      convexArcArea D (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2) ≤
        ClassicalResults.area
          (capNiche K.val ∩ (distinguishedCapSides K.val).2.upperHalfPlane) := by
  obtain ⟨hrIoo, hlIoo, -⟩ := paperGerverConstants_snd_mem_Ioo
  have hpi := Real.pi_pos
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have htop : supportValue (K.1.1 : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 :=
    K.1.property.2.2.2.1
  obtain ⟨-, -, -, hBsub, -, -, -, hDsub, -, hBeq, -, -, -, hDeq, -, -⟩ :=
    canonicalTailSets_properties K
  -- endpoint support values of the two tails
  have hB1 : supportValue (B : Set Point)
      ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := hBeq paperGerverConstants.2.1 (by simp)
    rw [hB]
    linarith
  have hB2 : supportValue (B : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := hBeq (Real.pi / 2) (by simp)
    rw [hcast _ _ (show Real.pi + Real.pi / 2 = 3 * Real.pi / 2 by ring), htop] at h
    rw [hB]
    linarith
  have hD1 : supportValue (D : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    have h := hDeq 0 (by simp)
    rw [hcast _ _ (show Real.pi / 2 + (0 : ℝ) = Real.pi / 2 by ring),
      hcast _ _ (show 3 * Real.pi / 2 + (0 : ℝ) = 3 * Real.pi / 2 by ring), htop] at h
    rw [hD]
    linarith
  have hD2 : supportValue (D : Set Point)
      ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) =
      1 - supportValue (K.1.1 : Set Point)
        ((Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle) := by
    have h := hDeq paperGerverConstants.2.2 (by simp)
    rw [hD]
    linarith
  obtain ⟨hOB, hOD, hsegB, hsegD, -, -⟩ :=
    tailFanPoint_identities K.val B D hrIoo hlIoo hB1 hB2 hD1 hD2
  obtain ⟨hWmem, hZmem⟩ := specialCap_wedgeEndpoints_in_bottomEdge K
  have hnichefin : MeasureTheory.volume (capNiche K.val) ≠ ⊤ :=
    ne_of_lt (niche_uniform_bounds.1 _ K.val).2.2.1
  have hRfin : ∀ S : Set Point,
      MeasureTheory.volume (capNiche K.val ∩ S) ≠ ⊤ := fun S ↦
    ne_top_of_le_ne_top hnichefin (MeasureTheory.measure_mono Set.inter_subset_left)
  have hKconv : Convex ℝ (K.1.1 : Set Point) := K.1.1.convex
  have hKclosed : IsClosed (K.1.1 : Set Point) := K.1.1.isCompact.isClosed
  constructor
  · -- right tail
    have hHa : (supportingLineHalfPlane (B : Set Point)
        ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).2 =
        (distinguishedCapSides K.val).1.upperHalfPlane := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show Real.pi + paperGerverConstants.2.1 =
          paperGerverConstants.2.1 + Real.pi by ring), normalVector_add_pi]
      · rw [hB1]; ring
    have hHb : (supportingLineHalfPlane (B : Set Point)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
        normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring),
          normalVector_add_pi]
      · rw [hB2]; ring
    have hmain := convexArc_tangentRegion_area_le B
      (Real.pi + paperGerverConstants.2.1) (3 * Real.pi / 2)
      (by linarith [hrIoo.2]) (by linarith [hrIoo.1])
      hKconv hKclosed (by rw [hB]; exact hBsub) (by rw [hOB]; exact hWmem.1.1)
      (hRfin _) (fun q hq hqK hqB ↦ by
        have hq' := interior_subset hq
        rw [hHa, hHb] at hq'
        exact mem_capNiche_inter_right_of_notMem_canonicalTail K hq'.1 hq'.2 hqK
          (by rwa [hB] at hqB))
    rw [hOB] at hmain
    rw [show (rightLeftTailArcs B D).1.startPoint =
        (edgeVertices B ((Real.pi + paperGerverConstants.2.1 : ℝ) : Real.Angle)).1 from rfl,
      show (distinguishedCapSides K.val).1.fanPoint =
        (wedgeEndpoints K.val paperGerverConstants.2.1).1 from rfl]
    linarith [hmain, hsegB]
  · -- left tail
    have hHa : (supportingLineHalfPlane (D : Set Point)
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 =
        normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring),
          normalVector_add_pi]
      · rw [hD1]; ring
    have hHb : (supportingLineHalfPlane (D : Set Point)
        ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2 =
        (distinguishedCapSides K.val).2.upperHalfPlane := by
      refine supportingLineHalfPlane_snd_eq_normalHalfPlane ?_ ?_
      · rw [hcast _ _ (show 3 * Real.pi / 2 + paperGerverConstants.2.2 =
          (paperGerverConstants.2.2 + Real.pi / 2) + Real.pi by ring), normalVector_add_pi]
      · rw [hD2, hcast _ _ (show Real.pi / 2 + paperGerverConstants.2.2 =
          paperGerverConstants.2.2 + Real.pi / 2 by ring)]
        ring
    have hmain := convexArc_tangentRegion_area_le D
      (3 * Real.pi / 2) (3 * Real.pi / 2 + paperGerverConstants.2.2)
      (by linarith [hlIoo.1]) (by linarith [hlIoo.2])
      hKconv hKclosed (by rw [hD]; exact hDsub) (by rw [hOD]; exact hZmem.1.1)
      (hRfin _) (fun q hq hqK hqD ↦ by
        have hq' := interior_subset hq
        rw [hHa, hHb] at hq'
        exact mem_capNiche_inter_left_of_notMem_canonicalTail K hq'.2 hq'.1 hqK
          (by rwa [hD] at hqD))
    rw [hOD] at hmain
    rw [show (rightLeftTailArcs B D).2.endPoint =
        (edgeVertices D ((3 * Real.pi / 2 + paperGerverConstants.2.2 : ℝ) : Real.Angle)).2
        from rfl,
      show (distinguishedCapSides K.val).2.fanPoint =
        (wedgeEndpoints K.val paperGerverConstants.2.2).2 from rfl]
    linarith [hmain, hsegD]

end MovingSofa
