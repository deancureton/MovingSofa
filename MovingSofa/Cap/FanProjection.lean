import MovingSofa.Cap.Contacts
import MovingSofa.Cap.HalfPlanes

noncomputable section

namespace MovingSofa

/-- Support values in the upper angular range of a non-right cap are nonnegative. -/
theorem supportValue_nonneg_of_mem_capUpperAngles {ω : ℝ} (K : CapSpace ω)
    (hω : ω < Real.pi / 2) {φ : ℝ} (hφ : φ ∈ capUpperAngles ω) :
    0 ≤ supportValue K.val (φ : Real.Angle) := by
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩
  rcases hφ with hφ | hφ
  · obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hpFan := K.subset_capFan hpK
    have hpy : p 1 = 0 := by
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) at hpnormal
      rw [K.property.2.2.2.2.2.1] at hpnormal
      have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
          (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
        congr 1
        ring
      rw [hang, normalVector_add_pi, inner_neg_right] at hpnormal
      simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
    have hpx : 0 ≤ p 0 := by
      have hpω := hpFan.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      simp [normalVector, frame, PiLp.inner_apply, hpy] at hpω
      by_contra hneg
      have := mul_neg_of_pos_of_neg hcosω (lt_of_not_ge hneg)
      linarith
    have hcosφ : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc
      ⟨(neg_nonpos.mpr (by positivity : 0 ≤ Real.pi / 2)).trans hφ.1,
        hφ.2.trans hω.le⟩
    have hinner : 0 ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      simp [normalVector, frame, PiLp.inner_apply, hpy]
      exact mul_nonneg hcosφ hpx
    exact hinner.trans (inner_le_supportValue K.val hpK (φ : Real.Angle))

  · obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
      ((ω + Real.pi : ℝ) : Real.Angle)
    have hpFan := K.subset_capFan hpK
    have hpu : inner ℝ p (normalVector (ω : Real.Angle)) = 0 := by
      change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) =
        supportValue K.val ((ω + Real.pi : ℝ) : Real.Angle) at hpnormal
      rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hpnormal
      linarith
    let μ := inner ℝ p (tangentVector (ω : Real.Angle))
    have hp : μ • tangentVector (ω : Real.Angle) = p := by
      have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
        p (ω : Real.Angle)
      rw [hpu, zero_smul, zero_add] at hframe
      exact hframe
    have hμ : 0 ≤ μ := by
      have hpy := hpFan.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpy
      have hp1 := congrArg (fun q : Point ↦ q 1) hp
      change μ * Real.cos ω = p 1 at hp1
      have hpy' : 0 ≤ p 1 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hpy
      rw [← hp1] at hpy'
      by_contra hneg
      have := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hcosω
      linarith
    have hsin : 0 ≤ Real.sin (φ - ω) := Real.sin_nonneg_of_nonneg_of_le_pi
      (by linarith [hφ.1]) (by linarith [hφ.2, Real.pi_pos])
    have hinner : 0 ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      have htv : inner ℝ (tangentVector (ω : Real.Angle))
          (normalVector (φ : Real.Angle)) = Real.sin (φ - ω) := by
        simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.sin_sub]
        ring
      have heq : inner ℝ p (normalVector (φ : Real.Angle)) = μ * Real.sin (φ - ω) := by
        rw [← hp, real_inner_smul_left, htv]
      rw [heq]
      exact mul_nonneg hμ hsin
    exact hinner.trans (inner_le_supportValue K.val hpK (φ : Real.Angle))

/-- The origin belongs to every cap of angle strictly below a right angle. -/
theorem zero_mem_cap_of_lt {ω : ℝ} (K : CapSpace ω)
    (hω : ω < Real.pi / 2) : (0 : Point) ∈ (K.val : Set Point) := by
  apply K.mem_of_mem_capFan_of_le_supportValue
  · simp [capFan, normalHalfPlane]
  · intro φ hφ
    simpa using supportValue_nonneg_of_mem_capUpperAngles K hω hφ

/-- The normal projection of the zero-angle support value belongs to the cap. -/
theorem supportValue_zero_smul_normalVector_mem {ω : ℝ} (K : CapSpace ω) :
    supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) ∈
      (K.val : Set Point) := by
  obtain ⟨p, hpK, hpnormal⟩ :=
    exists_mem_inner_eq_supportValue K.val (0 : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpx : p 0 = supportValue K.val (0 : Real.Angle) := by
    change inner ℝ p (normalVector (0 : Real.Angle)) = supportValue K.val (0 : Real.Angle)
      at hpnormal
    simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
  have hpy : 0 ≤ p 1 := by
    have := hpFan.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
    simpa [normalVector, frame, PiLp.inner_apply] using this
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (supportValue K.val (0 : Real.Angle) •
          normalVector (0 : Real.Angle)) (normalVector (ω : Real.Angle))
      by_cases hω : ω = Real.pi / 2
      · simp [normalVector, frame, PiLp.inner_apply, hω]
      · have hωlt : ω < Real.pi / 2 := K.property.2.1.lt_of_ne hω
        have hs : 0 ≤ supportValue K.val (0 : Real.Angle) :=
          supportValue_nonneg_of_mem_capUpperAngles K hωlt
            (Or.inl ⟨le_rfl, K.property.1.le⟩)
        simp only [real_inner_smul_left]
        simp [normalVector, frame, PiLp.inner_apply]
        exact mul_nonneg hs (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [K.property.1, Real.pi_pos], K.property.2.1⟩)
    · change 0 ≤ inner ℝ (supportValue K.val (0 : Real.Angle) •
          normalVector (0 : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [normalVector, frame, PiLp.inner_apply]
  · intro φ hφ
    have hφI : φ ∈ Set.Icc 0 Real.pi := by
      rcases hφ with hφ | hφ
      · exact ⟨hφ.1, hφ.2.trans
          (K.property.2.1.trans (by linarith [Real.pi_pos]))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hφ.1,
          hφ.2.trans (by linarith [K.property.2.1, Real.pi_pos])⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφI
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ
        (supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      simp [normalVector, frame, PiLp.inner_apply, hpx]
      exact mul_nonneg hsinφ hpy
    exact hinner.trans hbound

/-- At a right angle, the opposite normal projection belongs to the cap. -/
theorem supportValue_pi_smul_normalVector_mem_of_eq {ω : ℝ} (K : CapSpace ω)
    (hω : ω = Real.pi / 2) :
    supportValue K.val (Real.pi : Real.Angle) • normalVector (Real.pi : Real.Angle) ∈
      (K.val : Set Point) := by
  obtain ⟨p, hpK, hpnormal⟩ :=
    exists_mem_inner_eq_supportValue K.val (Real.pi : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpx : -p 0 = supportValue K.val (Real.pi : Real.Angle) := by
    change inner ℝ p (normalVector (Real.pi : Real.Angle)) =
      supportValue K.val (Real.pi : Real.Angle) at hpnormal
    simpa [normalVector, frame, PiLp.inner_apply] using hpnormal
  have hpy : 0 ≤ p 1 := by
    have := hpFan.2
    change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at this
    simpa [normalVector, frame, PiLp.inner_apply] using this
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor <;>
      simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, hω]
  · intro φ hφ
    have hφI : φ ∈ Set.Icc 0 Real.pi := by
      rcases hφ with hφ | hφ
      · exact ⟨hφ.1, hφ.2.trans (by rw [hω]; linarith [Real.pi_pos])⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hφ.1,
          hφ.2.trans (by rw [hω]; linarith)⟩
    have hsinφ : 0 ≤ Real.sin φ := Real.sin_nonneg_of_mem_Icc hφI
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ
        (supportValue K.val (Real.pi : Real.Angle) • normalVector (Real.pi : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      rw [← hpx]
      simp [normalVector, frame, PiLp.inner_apply]
      exact mul_nonneg hsinφ hpy
    exact hinner.trans hbound

/-- For a non-right cap, the terminal tangent projection belongs to the cap. -/
theorem supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt {ω : ℝ}
    (K : CapSpace ω) (hω : ω < Real.pi / 2) :
    supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) •
        tangentVector (ω : Real.Angle) ∈ (K.val : Set Point) := by
  have hcosω : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩
  let L := supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle)
  obtain ⟨p, hpK, hpnormal⟩ := exists_mem_inner_eq_supportValue K.val
    ((ω + Real.pi / 2 : ℝ) : Real.Angle)
  have hpFan := K.subset_capFan hpK
  have hpv : inner ℝ p (tangentVector (ω : Real.Angle)) = L := by
    change inner ℝ p (normalVector ((ω + Real.pi / 2 : ℝ) : Real.Angle)) = L at hpnormal
    rw [show ((ω + Real.pi / 2 : ℝ) : Real.Angle) =
      (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hpnormal
    exact hpnormal
  let a := inner ℝ p (normalVector (ω : Real.Angle))
  have ha : 0 ≤ a := hpFan.1
  have hp : a • normalVector (ω : Real.Angle) + L • tangentVector (ω : Real.Angle) = p := by
    simpa only [a, hpv] using
      inner_normalVector_smul_add_inner_tangentVector_smul p (ω : Real.Angle)
  have hL : 0 ≤ L := supportValue_nonneg_of_mem_capUpperAngles K hω
    (Or.inr ⟨by linarith [K.property.1, Real.pi_pos], le_rfl⟩)
  apply K.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector (ω : Real.Angle))
      rw [real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
      simp
    · change 0 ≤ inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [tangentVector, normalVector, frame, PiLp.inner_apply]
      exact mul_nonneg hL hcosω.le
  · intro φ hφ
    have hdiff : φ - ω ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rcases hφ with hφ | hφ
      · exact ⟨by linarith [hφ.1, K.property.2.1],
          by linarith [hφ.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hφ.1, K.property.2.1, Real.pi_pos],
          by linarith [hφ.2]⟩
    have hcos : 0 ≤ Real.cos (φ - ω) := Real.cos_nonneg_of_mem_Icc hdiff
    have hnu : inner ℝ (normalVector (ω : Real.Angle))
        (normalVector (φ : Real.Angle)) = Real.cos (φ - ω) := by
      rw [inner_normalVector_normalVector]
      rw [show ω - φ = -(φ - ω) by ring, Real.cos_neg]
    have hbound := inner_le_supportValue K.val hpK (φ : Real.Angle)
    have hinner : inner ℝ (L • tangentVector (ω : Real.Angle))
        (normalVector (φ : Real.Angle)) ≤ inner ℝ p (normalVector (φ : Real.Angle)) := by
      rw [← hp, inner_add_left, real_inner_smul_left, real_inner_smul_left, hnu]
      exact le_add_of_nonneg_left (mul_nonneg ha hcos)
    exact hinner.trans hbound


end MovingSofa
