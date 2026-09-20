import MovingSofa.Cap.HalfPlanes
import MovingSofa.ForMathlib.Analysis.SpecialFunctions.Trigonometric

noncomputable section

namespace MovingSofa

/-- Every polygon cap of angle less than pi/2 contains the top parallelogram corner. -/
theorem stripParallelogram_top_mem_of_angle_lt (Θ : AngleSet)
    (hΘ : Θ.angle < Real.pi / 2) (K : PolygonCapSpace Θ) :
    (stripParallelogram Θ.angle).2.2 ∈ (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  have hc : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  obtain ⟨pω, hpω, hpωeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image (fun p ↦ inner ℝ p (normalVector (Θ.angle : Real.Angle))))
  obtain ⟨pT, hpT, hpTeq⟩ := (K.val.val.isCompact.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).sSup_mem
      (K.val.val.nonempty.image
        (fun p ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))))
  have hpω' : inner ℝ pω (normalVector (Θ.angle : Real.Angle)) = 1 := by
    change inner ℝ pω (normalVector (Θ.angle : Real.Angle)) =
      supportValue K.val.val (Θ.angle : Real.Angle) at hpωeq
    simpa only [K.val.property.2.2.1] using hpωeq
  have hpT' : inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    change inner ℝ pT (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Real.pi / 2 : ℝ) : Real.Angle) at hpTeq
    simpa only [K.val.property.2.2.2.1] using hpTeq
  have hpωT : inner ℝ pω (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
    exact (inner_le_supportValue K.val.val hpω _).trans_eq K.val.property.2.2.2.1
  have hpTω : inner ℝ pT (normalVector (Θ.angle : Real.Angle)) ≤ 1 := by
    exact (inner_le_supportValue K.val.val hpT _).trans_eq K.val.property.2.2.1
  have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 := by
    have hgap : Real.tan (Real.pi / 4 - Θ.angle / 2) =
        (Real.cos Θ.angle)⁻¹ - Real.tan Θ.angle := by
      simpa [show Real.pi / 4 - Θ.angle / 2 =
          (Real.pi / 2 - Θ.angle) / 2 by ring]
        using Real.tan_pi_div_two_sub_div_two Θ.angle ⟨Θ.angle_pos.le, hΘ⟩
    have htan := Real.tan_eq_sin_div_cos Θ.angle
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
    field_simp [hc.ne']
    ring
  have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
  rw [K.property.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  change inner ℝ o (normalVector a) ≤ supportValue K.val.val a
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · have htupper : t ∈ capUpperAngles Θ.angle := by
      rcases ht with (ht | ⟨s, hs, rfl⟩) | ht
      · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
      · exact Or.inr ⟨by dsimp; linarith [(Θ.interior s hs).1],
          by dsimp; linarith [(Θ.interior s hs).2]⟩
      · rcases ht with rfl | rfl
        · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
        · exact Or.inr ⟨le_rfl, by linarith [Θ.angle_pos]⟩
    rcases htupper with ht | ht
    · let c := Real.cos t / Real.cos Θ.angle
      let s := Real.sin (Θ.angle - t) / Real.cos Θ.angle
      have hc0 : 0 ≤ c := div_nonneg
        (Real.cos_nonneg_of_mem_Icc
          ⟨(neg_nonpos.mpr (by positivity)).trans ht.1, ht.2.trans Θ.angle_le⟩) hc.le
      have hs0 : 0 ≤ s := div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr ht.2)
          (by linarith [ht.1, Θ.angle_le, Real.pi_pos])) hc.le
      have hdecomp : normalVector (t : Real.Angle) =
          c • normalVector (Θ.angle : Real.Angle) -
            s • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) := by
        ext i
        fin_cases i
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
          ring
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoω, hoT]
      apply (inner_le_supportValue K.val.val hpω (t : Real.Angle)).trans'
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpω']
      simpa only [mul_one] using
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpωT hs0) c
    · let c := Real.sin (t - Θ.angle) / Real.cos Θ.angle
      let s := -Real.cos t / Real.cos Θ.angle
      have hc0 : 0 ≤ c := div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1, Θ.angle_le])
          (by linarith [ht.2, Θ.angle_pos, Real.pi_pos])) hc.le
      have hs0 : 0 ≤ s := div_nonneg
        (neg_nonneg.mpr (Real.cos_nonpos_of_pi_div_two_le_of_le ht.1
          (by linarith [ht.2, Θ.angle_le, Real.pi_pos]))) hc.le
      have hdecomp : normalVector (t : Real.Angle) =
          c • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) -
            s • normalVector (Θ.angle : Real.Angle) := by
        ext i
        fin_cases i
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
        · simp [c, s, normalVector, frame, Real.sin_sub]
          field_simp [hc.ne']
          ring
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hoT, hoω]
      apply (inner_le_supportValue K.val.val hpT (t : Real.Angle)).trans'
      rw [hdecomp, inner_sub_right, inner_smul_right, inner_smul_right, hpT']
      simpa only [mul_one] using
        sub_le_sub_left (mul_le_mul_of_nonneg_left hpTω hs0) c
  · rcases ha with rfl | rfl
    · rw [normalVector_add_pi, inner_neg_right, hoω, K.val.property.2.2.2.2.1]
      norm_num
    · rw [inner_normalVector_three_pi_div_two, K.val.property.2.2.2.2.2.1]
      simp [o, stripParallelogram]

end MovingSofa
