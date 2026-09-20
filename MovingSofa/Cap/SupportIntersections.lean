import MovingSofa.Cap.HalfPlanes

noncomputable section

open Set MeasureTheory

namespace MovingSofa

private theorem supportingIntersection_le_supportValue_of_mem_Icc_left
    (K : ConvexBody Point) {a b r : ℝ} (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hr : r ∈ Set.Icc (a - Real.pi) a) :
    inner ℝ (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
        (normalVector (r : Real.Angle)) ≤ supportValue K (r : Real.Angle) := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let q := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hqmem := edgeVertices_fst_mem K (a : Real.Angle)
  have hqa : inner ℝ q (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := hqmem.2
  have hqb : inner ℝ q (normalVector (b : Real.Angle)) ≤
      supportValue K (b : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnormal : inner ℝ (p - q) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, hpa, hqa, sub_self]
  have htangent : 0 ≤ inner ℝ (p - q) (tangentVector (a : Real.Angle)) := by
    have hdiff : 0 ≤ inner ℝ (p - q) (normalVector (b : Real.Angle)) := by
      rw [inner_sub_left, hpb]
      linarith
    have hnb : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    rw [hnb, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hdiff
    nlinarith
  have hqr : inner ℝ q (normalVector (r : Real.Angle)) ≤
      supportValue K (r : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnr : normalVector (r : Real.Angle) =
      Real.cos (r - a) • normalVector (a : Real.Angle) +
        Real.sin (r - a) • tangentVector (a : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real a (r - a)
  have hsinr : Real.sin (r - a) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith [hr.2]) (by linarith [hr.1])
  have hdiff : inner ℝ (p - q) (normalVector (r : Real.Angle)) ≤ 0 := by
    rw [hnr, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add]
    exact mul_nonpos_of_nonpos_of_nonneg hsinr htangent
  rw [inner_sub_left] at hdiff
  linarith

private theorem supportingIntersection_le_supportValue_of_mem_Icc_right
    (K : ConvexBody Point) {a b r : ℝ} (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hr : r ∈ Set.Icc b (b + Real.pi)) :
    inner ℝ (supportingIntersection K (a : Real.Angle) (b : Real.Angle))
        (normalVector (r : Real.Angle)) ≤ supportValue K (r : Real.Angle) := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let q := (edgeVertices K (b : Real.Angle)).2
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hsina : Real.sin (a - b) < 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_neg_of_pos hsin
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hqmem := edgeVertices_snd_mem K (b : Real.Angle)
  have hqb : inner ℝ q (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) := hqmem.2
  have hqa : inner ℝ q (normalVector (a : Real.Angle)) ≤
      supportValue K (a : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnormal : inner ℝ (p - q) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, hpb, hqb, sub_self]
  have htangent : inner ℝ (p - q) (tangentVector (b : Real.Angle)) ≤ 0 := by
    have hdiff : 0 ≤ inner ℝ (p - q) (normalVector (a : Real.Angle)) := by
      rw [inner_sub_left, hpa]
      linarith
    have hna : normalVector (a : Real.Angle) =
        Real.cos (a - b) • normalVector (b : Real.Angle) +
          Real.sin (a - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
    rw [hna, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add] at hdiff
    nlinarith
  have hqr : inner ℝ q (normalVector (r : Real.Angle)) ≤
      supportValue K (r : Real.Angle) := inner_le_supportValue K hqmem.1 _
  have hnr : normalVector (r : Real.Angle) =
      Real.cos (r - b) • normalVector (b : Real.Angle) +
        Real.sin (r - b) • tangentVector (b : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real b (r - b)
  have hsinr : 0 ≤ Real.sin (r - b) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1]) (by linarith [hr.2])
  have hdiff : inner ℝ (p - q) (normalVector (r : Real.Angle)) ≤ 0 := by
    rw [hnr, inner_add_right, inner_smul_right, inner_smul_right, hnormal,
      mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos hsinr htangent
  rw [inner_sub_left] at hdiff
  linarith

/-- Adjacent allowed support normals meet in the represented convex body. -/
theorem HasHalfPlaneRepresentation.supportingIntersection_mem_of_gap
    (K : ConvexBody Point) (R : Set ℝ) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hK : HasHalfPlaneRepresentation K ((fun r : ℝ ↦ (r : Real.Angle)) '' R))
    (hR : ∀ r ∈ R, r ∈ Set.Icc (a - Real.pi) a ∨ r ∈ Set.Icc b (b + Real.pi)) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K := by
  change supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ (K : Set Point)
  rw [hK.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro u hu
  obtain ⟨r, hr, rfl⟩ := hu
  rcases hR r hr with hr | hr
  · exact supportingIntersection_le_supportValue_of_mem_Icc_left K hab hpi hr
  · exact supportingIntersection_le_supportValue_of_mem_Icc_right K hab hpi hr


end MovingSofa
