import MovingSofa.ForMathlib.Convex.Function
import MovingSofa.Geometry.Hallway

noncomputable section

namespace MovingSofa

abbrev RotationCalculationAngle := Set.Ico (Real.arccos (5 / 11 : ℝ)) (Real.pi / 2)

def rotationCalculationMinimum (ω : RotationCalculationAngle) : ℝ :=
  if ω.val < Real.arctan (11 / 5 : ℝ) then 5 / 4 else 11 / 10

def rotationCalculationValues (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val)) :
    ℝ × ℝ × Point × Point :=
  let r := 1 - d.val * (Real.cos ω.val / Real.sin ω.val)
  let g := Real.sqrt (1 - r ^ 2)
  let o := (stripParallelogram ω.val).2.2
  (r, g, o - tangentVector 0 + d.val • normalVector 0, o - g • normalVector 0)

theorem rotationCalculation_convex (d : ℝ) (hd : 1 ≤ d) :
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2))
      (fun t ↦ (1 - d * (Real.cos t / Real.sin t)) ^ 2) ∧
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2))
      (fun t ↦ Real.cos t ^ 2) := by
  let D := Set.Icc (Real.pi / 4) (Real.pi / 2)
  have hsin (t : ℝ) (ht : t ∈ D) : Real.sin t ≠ 0 := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have ht0 : 0 < t := lt_of_lt_of_le (by positivity : 0 < Real.pi / 4) ht.1
    have htpi : t < Real.pi := lt_of_le_of_lt ht.2 (by linarith)
    exact (Real.sin_pos_of_pos_of_lt_pi ht0 htpi).ne'
  have hfirst (t : ℝ) (ht : t ∈ D) : HasDerivAt
      (fun s ↦ (1 - d * (Real.cos s / Real.sin s)) ^ 2)
      (2 * d * (1 - d * (Real.cos t / Real.sin t)) / Real.sin t ^ 2) t := by
    have htrig : -(Real.sin t * Real.sin t) - Real.cos t * Real.cos t = -1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    convert (((hasDerivAt_const t 1).sub
      ((hasDerivAt_const t d).mul ((Real.hasDerivAt_cos t).div
        (Real.hasDerivAt_sin t) (hsin t ht)))).pow 2) using 1
    all_goals simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply]
    all_goals norm_num
    all_goals simp only [htrig]
    all_goals field_simp [hsin t ht]
  have hsecond (t : ℝ) (ht : t ∈ D) : HasDerivAt
      (fun s ↦ 2 * d * (1 - d * (Real.cos s / Real.sin s)) / Real.sin s ^ 2)
      (2 * d / Real.sin t ^ 4 *
        (d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t)) t := by
    have hs := hsin t ht
    have htrig : -(Real.sin t * Real.sin t) - Real.cos t * Real.cos t = -1 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    convert (((hasDerivAt_const t (2 * d)).mul
      ((hasDerivAt_const t 1).sub
        ((hasDerivAt_const t d).mul ((Real.hasDerivAt_cos t).div
          (Real.hasDerivAt_sin t) hs)))).div
      ((Real.hasDerivAt_sin t).pow 2) (pow_ne_zero 2 hs)) using 1
    all_goals simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, Pi.pow_apply]
    all_goals norm_num
    all_goals simp only [htrig]
    all_goals field_simp [hs]
    all_goals ring
  constructor
  · apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t ↦ 2 * d * (1 - d * (Real.cos t / Real.sin t)) / Real.sin t ^ 2)
      (f'' := fun t ↦ 2 * d / Real.sin t ^ 4 *
        (d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t)) (convex_Icc _ _)
    · fun_prop
    · intro t ht
      exact (hfirst t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      exact (hsecond t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have hc : 2 * Real.sin t * Real.cos t ≤ 1 := by
        nlinarith [sq_nonneg (Real.sin t - Real.cos t), Real.sin_sq_add_cos_sq t]
      have : 0 ≤ d + 2 * d * Real.cos t ^ 2 - 2 * Real.sin t * Real.cos t := by
        nlinarith [sq_nonneg (Real.cos t)]
      positivity
  · apply convexOn_of_hasDerivWithinAt2_nonneg
      (f' := fun t ↦ -2 * Real.sin t * Real.cos t)
      (f'' := fun t ↦ -2 * Real.cos (2 * t)) (convex_Icc _ _)
    · fun_prop
    · intro t ht
      convert ((Real.hasDerivAt_cos t).mul (Real.hasDerivAt_cos t)).hasDerivWithinAt using 1 <;>
        first | funext s; simp [Pi.mul_apply]; ring | ring
    · intro t ht
      convert (((Real.hasDerivAt_sin t).mul (Real.hasDerivAt_cos t)).const_mul (-2))
        |>.hasDerivWithinAt using 1 <;>
          first | funext s; simp [Pi.mul_apply]; ring |
            rw [Real.cos_two_mul, ← Real.sin_sq_add_cos_sq t]; ring
    · intro t ht
      have htD := interior_subset ht
      change t ∈ Set.Icc (Real.pi / 4) (Real.pi / 2) at htD
      have h1 : Real.pi / 2 ≤ 2 * t := by
        calc
          Real.pi / 2 = 2 * (Real.pi / 4) := by ring
          _ ≤ 2 * t := mul_le_mul_of_nonneg_left htD.1 (by norm_num)
      have h2 : 2 * t ≤ Real.pi + Real.pi / 2 := by
        calc
          2 * t ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left htD.2 (by norm_num)
          _ ≤ Real.pi + Real.pi / 2 := by linarith [Real.pi_pos]
      exact mul_nonneg_of_nonpos_of_nonpos (by norm_num)
        (Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2)


private def rotationBound (d t : ℝ) : ℝ :=
  (1 - d * (Real.cos t / Real.sin t)) ^ 2 + 4 * Real.cos t ^ 2

private theorem rotationBound_convex (d : ℝ) (hd : 1 ≤ d) :
    ConvexOn ℝ (Set.Icc (Real.pi / 4) (Real.pi / 2)) (rotationBound d) := by
  obtain ⟨h₁, h₂⟩ := rotationCalculation_convex d hd
  exact h₁.add (h₂.smul (by norm_num : (0 : ℝ) ≤ 4))

private theorem rotationBound_arccos :
    rotationBound (5 / 4) (Real.arccos (5 / 11)) < 1 := by
  have hs : Real.sin (Real.arccos (5 / 11)) = Real.sqrt 96 / 11 := by
    rw [Real.sin_arccos]
    norm_num
  have hsq : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
  have hlo : 97 / 10 < Real.sqrt 96 := by
    nlinarith [Real.sqrt_nonneg 96]
  have hhi : Real.sqrt 96 < 49 / 5 := by
    nlinarith [Real.sqrt_nonneg 96]
  unfold rotationBound
  rw [Real.cos_arccos (by norm_num) (by norm_num), hs]
  have hpos : 0 < Real.sqrt 96 := by positivity
  field_simp
  nlinarith

private theorem rotationBound_arctan_left :
    rotationBound (5 / 4) (Real.arctan (11 / 5)) < 1 := by
  unfold rotationBound
  rw [Real.cos_arctan, Real.sin_arctan]
  norm_num
  have hs : Real.sqrt (146 : ℝ) ^ 2 = 146 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (146 : ℝ) := by positivity
  field_simp
  nlinarith

private theorem rotationBound_arctan_right :
    rotationBound (11 / 10) (Real.arctan (11 / 5)) < 1 := by
  unfold rotationBound
  rw [Real.cos_arctan, Real.sin_arctan]
  norm_num
  have hs : Real.sqrt (146 : ℝ) ^ 2 = 146 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (146 : ℝ) := by positivity
  field_simp
  nlinarith

private theorem rotationBound_pi_div_two (d : ℝ) : rotationBound d (Real.pi / 2) = 1 := by
  simp [rotationBound]

/-- The three landmark angles of the rotation calculation are strictly ordered:
`π / 4 < arccos (5 / 11) < arctan (11 / 5) < π / 2`. -/
theorem rotationCalculation_angle_bounds :
    Real.pi / 4 < Real.arccos (5 / 11 : ℝ) ∧
    Real.arccos (5 / 11 : ℝ) < Real.arctan (11 / 5 : ℝ) ∧
    Real.arctan (11 / 5 : ℝ) < Real.pi / 2 := by
  have ha : Real.arccos (5 / 11 : ℝ) = Real.arctan (Real.sqrt 96 / 5) := by
    rw [Real.arccos_eq_arctan (by norm_num)]
    norm_num
    ring
  have hs : Real.sqrt 96 ^ 2 = 96 := Real.sq_sqrt (by norm_num)
  have hpos := Real.sqrt_nonneg 96
  refine ⟨?_, ?_, Real.arctan_lt_pi_div_two _⟩
  · rw [ha, ← Real.arctan_one]
    apply Real.arctan_strictMono
    nlinarith
  · rw [ha]
    apply Real.arctan_strictMono
    nlinarith

private theorem rotationBound_lt_one (ω : RotationCalculationAngle) :
    rotationBound (rotationCalculationMinimum ω) ω.val < 1 := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hdom₁ : Set.Icc (Real.arccos (5 / 11 : ℝ)) (Real.arctan (11 / 5 : ℝ)) ⊆
      Set.Icc (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    exact ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hdom₂ : Set.Icc (Real.arctan (11 / 5 : ℝ)) (Real.pi / 2) ⊆
      Set.Icc (Real.pi / 4) (Real.pi / 2) := by
    intro t ht
    exact ⟨(ha.le.trans hab.le).trans ht.1, ht.2⟩
  unfold rotationCalculationMinimum
  split_ifs with h
  · exact ConvexOn.lt_on_Ico_of_lt_of_le
      ((rotationBound_convex (5 / 4) (by norm_num)).subset hdom₁ (convex_Icc _ _))
      rotationBound_arccos rotationBound_arctan_left.le ω.property.1 h
  · exact ConvexOn.lt_on_Ico_of_lt_of_le
      ((rotationBound_convex (11 / 10) (by norm_num)).subset hdom₂ (convex_Icc _ _))
      rotationBound_arctan_right (rotationBound_pi_div_two _).le (le_of_not_gt h) ω.property.2

private theorem rotationCalculation_sin_bound (ω : RotationCalculationAngle) :
    1 < rotationCalculationMinimum ω * Real.sin ω.val := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hsinmono := Real.strictMonoOn_sin.monotoneOn
  unfold rotationCalculationMinimum
  split_ifs with h
  · have hs := hsinmono
      (show Real.arccos (5 / 11 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show ω.val ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ω.property.1, ω.property.2, Real.pi_pos]) ω.property.1
    rw [Real.sin_arccos] at hs
    norm_num at hs
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 96)
    have hp := Real.sqrt_nonneg 96
    have : 44 / 5 < Real.sqrt 96 := by nlinarith
    nlinarith
  · have hs := hsinmono
      (show Real.arctan (11 / 5 : ℝ) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [Real.pi_pos])
      (show ω.val ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) by
        constructor <;> linarith [ω.property.1, ω.property.2, Real.pi_pos]) (le_of_not_gt h)
    rw [Real.sin_arctan] at hs
    norm_num at hs
    have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 146)
    have hp : 0 < Real.sqrt 146 := by positivity
    have hupper : Real.sqrt 146 < 121 / 10 := by nlinarith
    have hbase : 10 / 11 < 11 / Real.sqrt 146 := (lt_div_iff₀ hp).2 (by nlinarith)
    nlinarith

private theorem rotationCalculation_g_bound (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val))
    (hr : 0 ≤ (rotationCalculationValues ω d).1) :
    2 * Real.cos ω.val < (rotationCalculationValues ω d).2.1 := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hw0 : 0 < ω.val := by linarith [ω.property.1, Real.pi_pos]
  have hsin : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hcos : 0 < Real.cos ω.val := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hcot : 0 ≤ Real.cos ω.val / Real.sin ω.val := le_of_lt (div_pos hcos hsin)
  have hmin : 0 ≤ rotationCalculationMinimum ω := by
    unfold rotationCalculationMinimum
    split_ifs <;> norm_num
  have hdd := mul_le_mul_of_nonneg_right d.property.1 hcot
  change 0 ≤ 1 - d.val * (Real.cos ω.val / Real.sin ω.val) at hr
  have hf := rotationBound_lt_one ω
  unfold rotationBound at hf
  have hrle : 1 - d.val * (Real.cos ω.val / Real.sin ω.val) ≤
      1 - rotationCalculationMinimum ω * (Real.cos ω.val / Real.sin ω.val) := by linarith
  have hr0 : 0 ≤ 1 - rotationCalculationMinimum ω * (Real.cos ω.val / Real.sin ω.val) := by linarith
  have hsquares := sq_le_sq₀ hr hr0 |>.2 hrle
  have hrad : 0 ≤ 1 - (1 - d.val * (Real.cos ω.val / Real.sin ω.val)) ^ 2 := by nlinarith [sq_nonneg (Real.cos ω.val)]
  have hsqrt := Real.sq_sqrt hrad
  have hnonneg := Real.sqrt_nonneg (1 - (1 - d.val * (Real.cos ω.val / Real.sin ω.val)) ^ 2)
  change 2 * Real.cos ω.val < Real.sqrt _
  nlinarith

theorem rotationCalculation_inequalities (ω : RotationCalculationAngle)
    (d : Set.Icc (rotationCalculationMinimum ω) (Real.tan ω.val))
    (hr : 0 ≤ (rotationCalculationValues ω d).1) :
    1 < inner ℝ
      ((rotationCalculationValues ω d).2.2.1 -
        ((stripParallelogram ω.val).2.2 - tangentVector 0))
      (normalVector ((Real.pi / 2 - ω.val : ℝ) : Real.Angle)) ∧
    1 < inner ℝ
      ((rotationCalculationValues ω d).2.2.2 -
        ((stripParallelogram ω.val).2.2 - normalVector (ω.val : Real.Angle)))
      (tangentVector ((Real.pi / 2 - ω.val : ℝ) : Real.Angle)) := by
  obtain ⟨ha, hab, hb⟩ := rotationCalculation_angle_bounds
  have hw0 : 0 < ω.val := by linarith [ω.property.1, Real.pi_pos]
  have hsin : 0 < Real.sin ω.val :=
    Real.sin_pos_of_pos_of_lt_pi hw0 (by linarith [ω.property.2, Real.pi_pos])
  have hcos : 0 < Real.cos ω.val :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ω.property.2⟩
  have hg := rotationCalculation_g_bound ω d hr
  have hd := mul_le_mul_of_nonneg_right d.property.1 hsin.le
  have hds := rotationCalculation_sin_bound ω
  constructor
  · simp [rotationCalculationValues, inner_smul_left,
      normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
    linarith
  · have hvec : (rotationCalculationValues ω d).2.2.2 -
        ((stripParallelogram ω.val).2.2 - normalVector (ω.val : Real.Angle)) =
        normalVector (ω.val : Real.Angle) - (rotationCalculationValues ω d).2.1 • normalVector 0 := by
      simp only [rotationCalculationValues]
      abel
    rw [hvec]
    simp only [inner_sub_left, inner_smul_left]
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
      Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, -Real.Angle.coe_sub]
    have hm := mul_lt_mul_of_pos_right hg hcos
    nlinarith [Real.sin_sq_add_cos_sq ω.val]

end MovingSofa
