import MovingSofa.Cap.Tail.Bodies

noncomputable section

namespace MovingSofa

/-- A point above both distinguished inner walls of a special cap lies above mid-height. -/
private theorem lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes (K : SpecialCapSpace)
    {q : Point} (h₁ : q ∈ (distinguishedCapSides K.val).1.upperHalfPlane)
    (h₂ : q ∈ (distinguishedCapSides K.val).2.upperHalfPlane) :
    (horizontalMax K.val.val - horizontalMin K.val.val) / 2 < q 1 := by
  obtain ⟨hrIoo, hlIoo, hrl⟩ := paperGerverConstants_snd_mem_Ioo
  have hphi : paperGerverConstants.2.1 ≤ (40 : ℝ) / 1000 := by
    obtain ⟨hall, p, hpbox, hpeq, -⟩ := gerver_parameter_identification
    exact (hall p hpbox hpeq).2.2.2.2.2.2.2.1
  have hcosr : (1249 : ℝ) / 1250 ≤ Real.cos paperGerverConstants.2.1 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := paperGerverConstants.2.1)
    nlinarith only [h, hphi, hrIoo.1]
  have hsinle : Real.sin paperGerverConstants.2.1 ≤ paperGerverConstants.2.1 :=
    Real.sin_le hrIoo.1.le
  have hcpos : (0 : ℝ) < Real.cos paperGerverConstants.2.1 := by linarith
  have hsinr : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.1 :=
    (Real.sin_pos_of_pos_of_lt_pi hrIoo.1 (by linarith [hrIoo.2, Real.pi_pos])).le
  have hsinl : (0 : ℝ) ≤ Real.sin paperGerverConstants.2.2 :=
    (Real.sin_pos_of_pos_of_lt_pi hlIoo.1 (by linarith [hlIoo.2, Real.pi_pos])).le
  have hcosl : (0 : ℝ) ≤ Real.cos paperGerverConstants.2.2 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hlIoo.1, Real.pi_pos], hlIoo.2⟩).le
  have hleq : paperGerverConstants.2.2 = Real.pi / 2 - paperGerverConstants.2.1 := by linarith
  have hsinleq : Real.sin paperGerverConstants.2.2 = Real.cos paperGerverConstants.2.1 := by
    rw [hleq, Real.sin_pi_div_two_sub]
  have hcosleq : Real.cos paperGerverConstants.2.2 = Real.sin paperGerverConstants.2.1 := by
    rw [hleq, Real.cos_pi_div_two_sub]
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
  -- the two defining support inequalities of the closed tail half-planes
  have h₁' : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.1 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ q (normalVector ((paperGerverConstants.2.1 : ℝ) : Real.Angle)) := h₁
  have h₂' : supportValue (K.val.val : Set Point)
      ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      inner ℝ q
        (normalVector ((paperGerverConstants.2.2 + Real.pi / 2 : ℝ) : Real.Angle)) := h₂
  rw [inner_normalVector_real] at h₁'
  rw [inner_normalVector_real, Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, hsinleq, hcosleq] at h₂'
  -- the strict product bound of the informal proof
  rw [← supportValue_zero_eq_horizontalMax, sub_eq_add_neg,
    ← supportValue_pi_eq_neg_horizontalMin]
  by_contra hcon
  rw [not_lt] at hcon
  have hcs : (1199 : ℝ) / 1250 ≤
      Real.cos paperGerverConstants.2.1 - Real.sin paperGerverConstants.2.1 := by linarith
  have hprod : (2 : ℝ) < (Real.cos paperGerverConstants.2.1 -
      Real.sin paperGerverConstants.2.1) *
      (supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) := by
    have h := mul_le_mul hcs hwidth (by norm_num) (by linarith)
    linarith
  have hmul : q 1 * Real.sin paperGerverConstants.2.1 ≤
      (supportValue (K.val.val : Set Point) ((0 : ℝ) : Real.Angle) +
        supportValue (K.val.val : Set Point) ((Real.pi : ℝ) : Real.Angle)) / 2 *
        Real.sin paperGerverConstants.2.1 :=
    mul_le_mul_of_nonneg_right hcon hsinr
  nlinarith only [h₁', h₂', hlowR, hlowL, hmul, hprod]

theorem cap_and_niche_tail_separation (K : SpecialCapSpace) :
    ((K.val.val : Set Point) ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∩
        (distinguishedCapSides K.val).2.upperHalfPlane = ∅ ∧
    (capNiche K.val ∩ (distinguishedCapSides K.val).1.upperHalfPlane) ∩
        (distinguishedCapSides K.val).2.upperHalfPlane = ∅ := by
  have hwidth : (11 : ℝ) / 5 ≤ horizontalMax K.val.val - horizontalMin K.val.val :=
    K.property.2.trans K.val.area_le_horizontalWidth
  constructor
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨⟨hqK, h₁⟩, h₂⟩
    have hmid := lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes K h₁ h₂
    have hq := (K.val.mem_horizontalStrip hqK).2
    linarith
  · refine Set.eq_empty_iff_forall_notMem.mpr ?_
    rintro q ⟨⟨hqN, h₁⟩, h₂⟩
    have hmid := lt_coordinate_of_mem_distinguishedCapSides_upperHalfPlanes K h₁ h₂
    have hq := (capNiche_subset_rectangle K.val hqN).2.2.2
    linarith

end MovingSofa
