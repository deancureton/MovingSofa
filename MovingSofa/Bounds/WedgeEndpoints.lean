import MovingSofa.Cap.Tail.Bodies
import MovingSofa.Convex.CombinationProperties

noncomputable section

namespace MovingSofa

theorem wedgeGaps_positive_lower_bound {ω : ℝ} (K : CapSpace ω)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 ω) :
    (1 - Real.sin t) / Real.cos t ≤ (wedgeGaps K t).1 ∧
    0 < (1 - Real.sin t) / Real.cos t ∧
    (1 - Real.sin (ω - t)) / Real.cos (ω - t) ≤ (wedgeGaps K t).2 ∧
    0 < (1 - Real.sin (ω - t)) / Real.cos (ω - t) := by
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩
  have hsint_lt : Real.sin t < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq t, sq_pos_of_pos hcost]
  have hcosδ : 0 < Real.cos (ω - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩
  have hsinδ_lt : Real.sin (ω - t) < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq (ω - t), sq_pos_of_pos hcosδ]
  have hbounds := K.supportValue_upper_bounds ht
  have hC := (edgeVertices_fst_mem K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)).2
  change inner ℝ (capVertices K ω).2.1
      (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  simp [normalVector, frame, Real.Angle.cos_add_pi_div_two,
    Real.Angle.sin_add_pi_div_two] at hC
  change inner ℝ (capVertices K ω).2.1 (tangentVector (ω : Real.Angle)) =
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) at hC
  have hgap₁ := wedgeGaps_fst_eq_supportValue K t
  have hgap₂ : (wedgeGaps K t).2 =
      supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) -
        (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (ω - t) := by
    simp only [wedgeGaps, wedgeEndpoints, inner_sub_left,
      real_inner_smul_left, hC]
    rw [inner_tangentVector_self]
    ring
  rw [hgap₁, hgap₂]
  refine ⟨?_, div_pos (sub_pos.mpr hsint_lt) hcost, ?_,
    div_pos (sub_pos.mpr hsinδ_lt) hcosδ⟩
  · apply (div_le_iff₀ hcost).2
    rw [sub_mul, div_mul_cancel₀ _ hcost.ne']
    nlinarith [hbounds.1]
  · apply (div_le_iff₀ hcosδ).2
    rw [sub_mul, div_mul_cancel₀ _ hcosδ.ne']
    nlinarith [hbounds.2]

/-- Base points between the horizontal extrema of a right-angle cap lie in the cap. -/
private theorem smul_normalVector_zero_mem_of_rightAngleCap (K : RightAngleCapSpace) {x : ℝ}
    (hlo : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤ x)
    (hhi : x ≤ supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle)) :
    x • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) := by
  obtain ⟨A, hA, hAeq⟩ := exists_mem_inner_eq_supportValue K.val ((0 : ℝ) : Real.Angle)
  obtain ⟨C, hC, hCeq⟩ := exists_mem_inner_eq_supportValue K.val ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_zero] at hAeq
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hCeq
  have hzero : inner ℝ (x • normalVector (0 : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_smul_normalVector_zero, Real.cos_pi_div_two, mul_zero]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨le_of_eq hzero.symm, le_of_eq hzero.symm⟩ ?_
  intro t ht
  have htI : 0 ≤ t ∧ t ≤ Real.pi := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith only [h.2, Real.pi_pos]⟩
    · exact ⟨by linarith only [h.1, Real.pi_pos], by linarith only [h.2]⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1 htI.2
  rw [inner_smul_normalVector_zero]
  rcases le_or_gt 0 (Real.cos t) with hcos | hcos
  · have h := inner_le_supportValue K.val hA (t : Real.Angle)
    rw [inner_normalVector_real] at h
    have hy := (K.mem_horizontalStrip hA).1
    nlinarith only [h, hAeq, hhi, hcos, mul_nonneg hsin hy]
  · have h := inner_le_supportValue K.val hC (t : Real.Angle)
    rw [inner_normalVector_real] at h
    have hy := (K.mem_horizontalStrip hC).1
    nlinarith only [h, hCeq, hlo, hcos, mul_nonneg hsin hy]

/-- The bottom right cap vertex is the horizontal maximum on the base line. -/
private theorem capVertices_zero_snd_eq (K : RightAngleCapSpace) :
    (capVertices K 0).1.2 =
      supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) •
        normalVector (0 : Real.Angle) := by
  set R := supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) with hRdef
  have hS : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤ R := by
    obtain ⟨p, hp⟩ := K.val.nonempty
    have h0 := inner_le_supportValue K.val hp ((0 : ℝ) : Real.Angle)
    have hpi := inner_le_supportValue K.val hp ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_zero] at h0
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hpi
    rw [hRdef]
    linarith
  have hmem : R • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) :=
    smul_normalVector_zero_mem_of_rightAngleCap K hS le_rfl
  have hedge : R • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((0 : ℝ) : Real.Angle) := by
    refine ⟨hmem, ?_⟩
    change inner ℝ (R • normalVector (0 : Real.Angle))
      (normalVector ((0 : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, Real.cos_zero, mul_one]
  show (edgeVertices K.val ((0 : ℝ) : Real.Angle)).2 = _
  refine edgeVertices_snd_eq_of_tangent_isLeast K.val ((0 : ℝ) : Real.Angle) hedge ?_
  intro q hq
  have hq1 : 0 ≤ q 1 := (K.mem_horizontalStrip hq.1).1
  have hp1 : inner ℝ (R • normalVector (0 : Real.Angle))
      (tangentVector ((0 : ℝ) : Real.Angle)) = 0 := by
    rw [real_inner_smul_left, show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) from rfl,
      inner_normalVector_tangentVector, mul_zero]
  rw [hp1, inner_tangentVector_zero]
  exact hq1

/-- The bottom left cap vertex is the horizontal minimum on the base line. -/
private theorem capVertices_pi_div_two_fst_eq (K : RightAngleCapSpace) :
    (capVertices K (Real.pi / 2)).2.1 =
      (-supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) •
        normalVector (0 : Real.Angle) := by
  set S := supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) with hSdef
  have hR : -S ≤ supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle) := by
    obtain ⟨p, hp⟩ := K.val.nonempty
    have h0 := inner_le_supportValue K.val hp ((0 : ℝ) : Real.Angle)
    have hpi := inner_le_supportValue K.val hp ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_zero] at h0
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hpi
    rw [hSdef]
    linarith
  have hmem : (-S) • normalVector (0 : Real.Angle) ∈ (K.val : Set Point) :=
    smul_normalVector_zero_mem_of_rightAngleCap K le_rfl hR
  have hang : ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi : ℝ) : Real.Angle) := by
    congr 1
    ring
  have hedge : (-S) • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((Real.pi : ℝ) : Real.Angle) := by
    refine ⟨hmem, ?_⟩
    change inner ℝ ((-S) • normalVector (0 : Real.Angle))
      (normalVector ((Real.pi : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, Real.cos_pi]
    ring
  show (edgeVertices K.val ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 = _
  rw [hang]
  refine edgeVertices_fst_eq_of_tangent_isGreatest K.val ((Real.pi : ℝ) : Real.Angle) hedge ?_
  intro q hq
  have hq1 : 0 ≤ q 1 := (K.mem_horizontalStrip hq.1).1
  have hp1 : inner ℝ ((-S) • normalVector (0 : Real.Angle))
      (tangentVector ((Real.pi : ℝ) : Real.Angle)) = 0 := by
    rw [real_inner_smul_left, inner_tangentVector_pi]
    simp [normalVector, frame]
  rw [hp1, inner_tangentVector_pi]
  linarith

/-- Horizontal coordinates strictly inside the cap width give interior bottom-edge points. -/
private theorem smul_normalVector_zero_mem_bottomEdge (K : RightAngleCapSpace) {x : ℝ}
    (hlo : -supportValue (K.val : Set Point) ((Real.pi : ℝ) : Real.Angle) < x)
    (hhi : x < supportValue (K.val : Set Point) ((0 : ℝ) : Real.Angle)) :
    x • normalVector (0 : Real.Angle) ∈
      exposedEdge K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K 0).1.2, (capVertices K (Real.pi / 2)).2.1} := by
  have hinj : ∀ a b : ℝ, a • normalVector (0 : Real.Angle) =
      b • normalVector (0 : Real.Angle) → a = b := by
    intro a b h
    have h' := congrArg (fun p : Point ↦ inner ℝ p (normalVector ((0 : ℝ) : Real.Angle))) h
    simpa only [inner_smul_normalVector_zero, Real.cos_zero, mul_one] using h'
  have hcos : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show (3 * Real.pi / 2 : ℝ) = Real.pi + Real.pi / 2 by ring, Real.cos_add,
      Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_pi, Real.sin_pi]
    ring
  refine ⟨⟨smul_normalVector_zero_mem_of_rightAngleCap K hlo.le hhi.le, ?_⟩, ?_⟩
  · change inner ℝ (x • normalVector (0 : Real.Angle))
      (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [inner_smul_normalVector_zero, hcos, mul_zero, K.property.2.2.2.2.2.1]
  · rintro (h | h)
    · rw [capVertices_zero_snd_eq K] at h
      exact absurd (hinj _ _ h) (ne_of_lt hhi)
    · rw [capVertices_pi_div_two_fst_eq K] at h
      exact absurd (hinj _ _ h) (ne_of_gt hlo)

theorem specialCap_wedgeEndpoints_in_bottomEdge (K : SpecialCapSpace) :
    (distinguishedCapSides K.val).1.fanPoint ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K.val 0).1.2, (capVertices K.val (Real.pi / 2)).2.1} ∧
    (distinguishedCapSides K.val).2.fanPoint ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        {(capVertices K.val 0).1.2, (capVertices K.val (Real.pi / 2)).2.1} := by
  obtain ⟨hrIoo, hlIoo, hrl⟩ := paperGerverConstants_snd_mem_Ioo
  -- the certified parameter bound `0 < varphi ≤ 1/25` and its trigonometric consequences
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, q, hqbox, hqeq, -⟩ := gerver_parameter_identification
    exact (hall q hqbox hqeq).2.2.2.2.2.2.2.1
  have hcosr : (1249 : ℝ) / 1250 ≤ Real.cos paperGerverConstants.2.1 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := paperGerverConstants.2.1)
    nlinarith only [h, hphi, hrIoo.1]
  have hcpos : (0 : ℝ) < Real.cos paperGerverConstants.2.1 := by linarith
  have hsinr : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.1 :=
    (Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [hrIoo.2, Real.pi_pos])).le
  have hsinl : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.2 :=
    (Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [hlIoo.2, Real.pi_pos])).le
  have hcosl : (0 : ℝ) ≤ Real.cos paperGerverConstants.2.2 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hlIoo.1, Real.pi_pos], hlIoo.2⟩).le
  have hcosdiff : Real.pi / 2 - paperGerverConstants.2.2 = paperGerverConstants.2.1 := by
    linarith
  have hsinleq : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [show paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 by linarith,
      Real.sin_pi_div_two_sub]
  have hinvc : (1 : ℝ) / Real.cos paperGerverConstants.2.1 ≤ 1250 / 1249 := by
    rw [div_le_div_iff₀ hcpos (by norm_num)]
    linarith
  -- the cap is wide, by rectangle area monotonicity and the special-cap area threshold
  have hwidth : (11 : ℝ) / 5 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) := by
    have h := K.property.2.trans K.val.area_le_horizontalWidth
    rwa [supportValue_zero_eq_horizontalMax, supportValue_pi_eq_neg_horizontalMin,
      ← sub_eq_add_neg]
  -- support lower bounds at the two distinguished angles
  have hlowR : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinr hcpos.le).1
    rwa [← supportValue_zero_eq_horizontalMax] at h
  have hlowL : Real.cos paperGerverConstants.2.1 *
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) := by
    have h := (CapSpace.horizontal_le_supportValue K.val hsinl hcosl).2
    rw [supportValue_pi_eq_neg_horizontalMin, ← hsinleq, mul_neg, ← neg_mul]
    exact h
  -- the two positive wedge gaps
  have hgap₁ := wedgeGaps_positive_lower_bound K.val paperGerverConstants.2.1 hrIoo
  have hgap₂ := wedgeGaps_positive_lower_bound K.val paperGerverConstants.2.2 hlIoo
  rw [wedgeGaps_fst_eq_supportValue] at hgap₁
  rw [wedgeGaps_snd_eq_supportValue,
    show ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) by
      congr 1; ring, hcosdiff] at hgap₂
  have hgap₁' : (1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1 ≤
      supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) -
        (supportValue (K.val.val : Set Point)
          ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 := hgap₁.1
  have hgap₂' : (1 - Real.sin paperGerverConstants.2.1) / Real.cos paperGerverConstants.2.1 ≤
      supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) -
        (supportValue (K.val.val : Set Point)
          ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos paperGerverConstants.2.1 := hgap₂.2.2.1
  -- the reciprocal-cosine lower bounds for the two inner-wall coordinates
  have hRc : supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point) ((paperGerverConstants.2.1 : ℝ) : Real.Angle) /
        Real.cos paperGerverConstants.2.1 := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hSc : supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) ≤
      supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) /
        Real.cos paperGerverConstants.2.1 := by
    rw [le_div_iff₀ hcpos]
    linarith
  have hRc' : supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) -
      1 / Real.cos paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1 := by
    rw [sub_div]
    linarith
  have hSc' : supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle) -
      1 / Real.cos paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1 := by
    rw [sub_div]
    linarith
  -- the two fan points as multiples of the horizontal normal
  have htv : tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (0 : Real.Angle) := by
    have h := tangentVector_add_pi_div_two 0
    rwa [zero_add, Real.Angle.coe_zero] at h
  constructor
  · show ((supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1) /
        Real.cos paperGerverConstants.2.1) • normalVector (0 : Real.Angle) ∈ _
    refine smul_normalVector_zero_mem_bottomEdge K.val ?_ ?_
    · linarith
    · have hpos : 0 < (1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1 := hgap₁.2.1
      linarith
  · show ((supportValue (K.val.val : Set Point)
        ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
        Real.cos (Real.pi / 2 - paperGerverConstants.2.2)) •
        tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ _
    rw [hcosdiff, htv, smul_neg, ← neg_smul]
    refine smul_normalVector_zero_mem_bottomEdge K.val ?_ ?_
    · have hpos : 0 < (1 - Real.sin paperGerverConstants.2.1) /
          Real.cos paperGerverConstants.2.1 := hgap₂.2.2.2
      linarith
    · linarith

end MovingSofa
