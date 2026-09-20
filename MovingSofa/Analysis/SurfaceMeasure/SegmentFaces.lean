import MovingSofa.Analysis.SurfaceMeasure.Segment
import MovingSofa.Geometry.Contacts

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem not_both_mem_short_angleArc {E : Set Real.Angle} {a b : ℝ}
    (hab : a ≤ b) (hshort : b < a + Real.pi)
    (hE : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b)
    (t : Real.Angle) : ¬(t ∈ E ∧ t + (Real.pi : Real.Angle) ∈ E) := by
  rintro ⟨ht, htpi⟩
  obtain ⟨s, hs, hst⟩ := hE ht
  obtain ⟨u, hu, hut⟩ := hE htpi
  have hang : (u : Real.Angle) = ((s + Real.pi : ℝ) : Real.Angle) := by
    calc
      (u : Real.Angle) = t + (Real.pi : Real.Angle) := hut
      _ = (s : Real.Angle) + (Real.pi : Real.Angle) := by rw [← hst]
      _ = ((s + Real.pi : ℝ) : Real.Angle) := Real.Angle.coe_add _ _ |>.symm
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp hang
  have hlow : -(2 * Real.pi) < u - (s + Real.pi) := by
    linarith [hs.1, hs.2, hu.1, hu.2]
  have hupp : u - (s + Real.pi) < 0 := by
    linarith [hs.1, hs.2, hu.1, hu.2]
  rw [hk] at hlow hupp
  have hkneg : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
  have hkgt : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
  rw [← Int.cast_zero] at hkneg
  have hcast_neg_one : (((-1 : ℤ) : ℝ)) = -1 := by norm_num
  rw [← hcast_neg_one] at hkgt
  have hkneg' : k < 0 := Int.cast_lt.mp hkneg
  have hkgt' : (-1 : ℤ) < k := Int.cast_lt.mp hkgt
  omega

/-- A normal perpendicular to a segment exposes the whole segment. -/
theorem exposedEdge_eq_segment_of_orthogonal (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (t : Real.Angle) (ht : inner ℝ (d.2.1 - d.1) (normalVector t) = 0) :
    exposedEdge K t = (K : Set Point) := by
  have hfst : d.1 ∈ K := by
    change d.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  have hconst : ∀ p ∈ (K : Set Point),
      inner ℝ p (normalVector t) = inner ℝ d.1 (normalVector t) := by
    intro p hp
    rw [hd.2.1, segment_eq_image'] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    rw [inner_add_left, inner_smul_left, ht, mul_zero, add_zero]
  have hsupport : supportValue K t = inner ℝ d.1 (normalVector t) := by
    apply le_antisymm
    · apply csSup_le (K.nonempty.image _)
      rintro _ ⟨p, hp, rfl⟩
      exact (hconst p hp).le
    · exact inner_le_supportValue K hfst t
  ext p
  constructor
  · exact fun hp ↦ hp.1
  · intro hp
    refine ⟨hp, ?_⟩
    change inner ℝ p (normalVector t) = supportValue K t
    rw [hconst p hp, hsupport]

private theorem exposedEdge_subset_endpoints_of_not_orthogonal (K : ConvexBody Point)
    (d : Point × Point × Real.Angle) (hd : IsSegmentPresentation K d)
    (t : Real.Angle) (ht : inner ℝ (d.2.1 - d.1) (normalVector t) ≠ 0) :
    exposedEdge K t ⊆ {d.1, d.2.1} := by
  have hfst : d.1 ∈ K := by
    change d.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact left_mem_segment ℝ _ _
  have hsnd : d.2.1 ∈ K := by
    change d.2.1 ∈ (K : Set Point)
    rw [hd.2.1]
    exact right_mem_segment ℝ _ _
  intro p hp
  have hpK : p ∈ segment ℝ d.1 d.2.1 := by
    rw [← hd.2.1]
    exact hp.1
  rw [segment_eq_image'] at hpK
  obtain ⟨u, hu, rfl⟩ := hpK
  have hx := inner_le_supportValue K hfst t
  have hy := inner_le_supportValue K hsnd t
  rw [← hp.2] at hx hy
  simp only [inner_add_left, inner_smul_left] at hx hy
  let c := inner ℝ (d.2.1 - d.1) (normalVector t)
  change inner ℝ d.1 (normalVector t) ≤
    inner ℝ d.1 (normalVector t) + u * c at hx
  change inner ℝ d.2.1 (normalVector t) ≤
    inner ℝ d.1 (normalVector t) + u * c at hy
  have hdiff : inner ℝ d.2.1 (normalVector t) =
      inner ℝ d.1 (normalVector t) + c := by
    dsimp only [c]
    rw [inner_sub_left]
    ring
  rw [hdiff] at hy
  have hc : c ≠ 0 := ht
  rcases lt_or_gt_of_ne hc with hcneg | hcpos
  · have hu0 : u = 0 := by
      apply le_antisymm _ hu.1
      by_contra hnot
      have hupos : 0 < u := lt_of_not_ge hnot
      nlinarith
    simp [hu0]
  · have hu1 : u = 1 := by
      apply le_antisymm hu.2
      by_contra hnot
      have hult : u < 1 := lt_of_not_ge hnot
      nlinarith
    simp [hu1]

/-- The face-union formula for a segment on an angular arc shorter than a half-turn. -/
theorem surfaceAreaMeasure_face_union_of_segmentPresentation
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) (E : Set Real.Angle) (hE : MeasurableSet E)
    {a b : ℝ} (hab : a ≤ b) (hshort : b < a + Real.pi)
    (hsubset : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) :
    surfaceAreaMeasure K E =
      Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  have hnotboth := not_both_mem_short_angleArc hab hshort hsubset d.2.2
  have hnormalPi :
      normalVector (d.2.2 + (Real.pi : Real.Angle)) = -normalVector d.2.2 := by
    induction d.2.2 using Real.Angle.induction_on with
    | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
  have hpiorth :
      inner ℝ (d.2.1 - d.1)
        (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    rw [hnormalPi, inner_neg_right, hd.2.2, neg_zero]
  by_cases hn : d.2.2 ∈ E
  · have hnpi : d.2.2 + (Real.pi : Real.Angle) ∉ E := fun hnpi ↦ hnotboth ⟨hn, hnpi⟩
    have hunion : (⋃ t ∈ E, exposedEdge K t) = (K : Set Point) := by
      apply Set.Subset.antisymm
      · intro p hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
        exact hpt.1
      · intro p hp
        exact Set.mem_iUnion₂.mpr ⟨d.2.2, hn, by
          rw [exposedEdge_eq_segment_of_orthogonal K d hd d.2.2 hd.2.2]
          exact hp⟩
    rw [surfaceAreaMeasure_eq_segmentPresentation K d hd, hunion, hd.2.1]
    simp [hE, hn, hnpi, edist_dist]
  · by_cases hnpi : d.2.2 + (Real.pi : Real.Angle) ∈ E
    · have hunion : (⋃ t ∈ E, exposedEdge K t) = (K : Set Point) := by
        apply Set.Subset.antisymm
        · intro p hp
          obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
          exact hpt.1
        · intro p hp
          exact Set.mem_iUnion₂.mpr ⟨d.2.2 + (Real.pi : Real.Angle), hnpi, by
            rw [exposedEdge_eq_segment_of_orthogonal K d hd _ hpiorth]
            exact hp⟩
      rw [surfaceAreaMeasure_eq_segmentPresentation K d hd, hunion, hd.2.1]
      simp [hE, hn, hnpi, edist_dist]
    · have hunion : (⋃ t ∈ E, exposedEdge K t) ⊆ {d.1, d.2.1} := by
        intro p hp
        obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
        have htorth : inner ℝ (d.2.1 - d.1) (normalVector t) ≠ 0 := by
          intro hortho
          rcases normalVector_eq_or_eq_add_pi_of_orthogonal
              (sub_ne_zero.mpr hd.1.symm) hortho hd.2.2 with h | h
          · exact hn (h ▸ ht)
          · exact hnpi (h ▸ ht)
        exact exposedEdge_subset_endpoints_of_not_orthogonal K d hd t htorth hpt
      rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
      have hzero : Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) = 0 := by
        let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
        exact measure_mono_null hunion
          ((Set.finite_singleton d.2.1).insert d.1 |>.measure_zero _)
      rw [hzero]
      simp [hE, hn, hnpi]

end MovingSofa
