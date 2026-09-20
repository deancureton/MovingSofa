import MovingSofa.Geometry.Reflection
import MovingSofa.Cap.Clipped.Estimates
import MovingSofa.Classical.Area
import MovingSofa.ForMathlib.MeasureTheory.RegionBetween
import MovingSofa.Geometry.ParallelogramGap

noncomputable section

namespace MovingSofa

open MeasureTheory Set

def clippedCap (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    normalHalfPlane 0 (d + Real.tan ((Real.pi / 2 - ω) / 2)) false false ∩
    normalHalfPlane ((ω + Real.pi / 2 : ℝ) : Real.Angle)
      (d + Real.tan ((Real.pi / 2 - ω) / 2)) false false

theorem mem_clippedCap_iff (ω d : ℝ) (p : Point) :
    p ∈ clippedCap ω d ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
        Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1) ∧
      p 0 ≤ d + Real.tan ((Real.pi / 2 - ω) / 2) ∧
      -Real.sin ω * p 0 + Real.cos ω * p 1 ≤
        d + Real.tan ((Real.pi / 2 - ω) / 2) := by
  simp only [clippedCap, Set.mem_inter_iff, mem_stripParallelogram_iff]
  simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.cos_add, Real.sin_add, -Real.Angle.coe_add, and_assoc, mul_comm]

theorem clippedCap_removed_pieces_disjoint {C S c d : ℝ}
    (hC : 0 < C) (hS : 0 ≤ S) (hd : 0 ≤ d) (hc : c * (1 + S) = C) :
    Disjoint {p : Point | p 1 ≤ 1 ∧ c + d < p 0}
      {p : Point | c + d < -S * p 0 + C * p 1} := by
  rw [Set.disjoint_left]
  intro p hp hq
  change p 1 ≤ 1 ∧ c + d < p 0 at hp
  change c + d < -S * p 0 + C * p 1 at hq
  have hmul := mul_le_mul_of_nonneg_left hp.1 hC.le
  have hmul' := mul_le_mul_of_nonneg_left (le_of_lt hp.2) hS
  have hprod := mul_nonneg hd (by linarith : 0 ≤ 1 + S)
  nlinarith

private theorem mem_stripParallelogram_coordinates (ω : ℝ) (p : Point) :
    p ∈ (stripParallelogram ω).1 ↔
      (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
      (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
        Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1) := by
  rw [mem_stripParallelogram_iff]
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]

private theorem capReflection_rotatedCoordinate (ω : ℝ) (p : Point) :
    Real.cos ω * capReflection ω p 0 +
        Real.sin ω * capReflection ω p 1 = p 1 := by
  rw [capReflection_apply_zero, capReflection_apply_one]
  calc
    _ = (Real.sin ω ^ 2 + Real.cos ω ^ 2) * p 1 := by ring
    _ = p 1 := by rw [Real.sin_sq_add_cos_sq]; ring

private def rightRemovedTriangle (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    {p | d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0}

private def leftRemovedTriangle (ω d : ℝ) : Set Point :=
  (stripParallelogram ω).1 ∩
    {p | d + Real.tan ((Real.pi / 2 - ω) / 2) <
      -Real.sin ω * p 0 + Real.cos ω * p 1}

private theorem leftRemovedTriangle_eq_preimage (ω d : ℝ) :
    leftRemovedTriangle ω d =
      capReflection ω ⁻¹' rightRemovedTriangle ω d := by
  ext p
  simp only [leftRemovedTriangle, rightRemovedTriangle, Set.mem_inter_iff,
    Set.mem_ofPred_eq, Set.mem_preimage]
  rw [mem_stripParallelogram_coordinates,
    mem_stripParallelogram_coordinates,
    capReflection_rotatedCoordinate, capReflection_apply_zero,
    capReflection_apply_one]
  tauto

private theorem volume_stripParallelogram (ω : ℝ) (hC : 0 < Real.cos ω) :
    volume (stripParallelogram ω).1 = ENNReal.ofReal (1 / Real.cos ω) := by
  let f : ℝ → ℝ := fun y ↦ (-Real.sin ω * y) / Real.cos ω
  let g : ℝ → ℝ := fun y ↦ (1 - Real.sin ω * y) / Real.cos ω
  have hf : Measurable f := by fun_prop
  have hg : Measurable g := by fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous f).intervalIntegrable 0 1)
  have hgi : IntegrableOn g (Icc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      ((by fun_prop : Continuous g).intervalIntegrable 0 1)
  have hfg : ∀ y ∈ Icc (0 : ℝ) 1, f y ≤ g y := by
    intro y _
    dsimp [f, g]
    rw [div_le_div_iff_of_pos_right hC]
    linarith
  have hset : (stripParallelogram ω).1 =
      {p : Point | p 1 ∈ Icc (0 : ℝ) 1 ∧ p 0 ∈ Icc (f (p 1)) (g (p 1))} := by
    ext p
    rw [mem_stripParallelogram_coordinates]
    simp only [Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨hy, ?_, ?_⟩
      · dsimp [f]
        apply (div_le_iff₀ hC).2
        linarith [hz.1]
      · dsimp [g]
        apply (le_div_iff₀ hC).2
        linarith [hz.2]
    · rintro ⟨hy, hx0, hx1⟩
      refine ⟨hy, ?_, ?_⟩
      · dsimp [f] at hx0
        have := (div_le_iff₀ hC).1 hx0
        linarith
      · dsimp [g] at hx1
        have := (le_div_iff₀ hC).1 hx1
        linarith
  rw [hset, volume_horizontalIcc hf hg measurableSet_Icc hfi hgi hfg]
  have hdiff : g - f = fun _ ↦ 1 / Real.cos ω := by
    funext y
    dsimp [f, g]
    field_simp [hC.ne']
    ring
  rw [hdiff, setIntegral_const]
  simp

private theorem volume_rightRemovedTriangle (ω d : ℝ)
    (hω : ω ∈ Ioo 0 (Real.pi / 2)) (hd0 : 0 ≤ d) (hdt : d ≤ Real.tan ω) :
    volume (rightRemovedTriangle ω d) =
      ENNReal.ofReal ((Real.tan ω - d) ^ 2 *
        (Real.cos ω / Real.sin ω) / 2) := by
  let C := Real.cos ω
  let S := Real.sin ω
  let c := Real.tan ((Real.pi / 2 - ω) / 2)
  let A := c + d
  let b := Real.tan ω - d
  let H := b * C / S
  let f : ℝ → ℝ := fun _ ↦ A
  let g : ℝ → ℝ := fun y ↦ (1 - S * y) / C
  have hC : 0 < C :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hω.1
    (by linarith [hω.2, Real.pi_pos])
  have hcircle : S ^ 2 + C ^ 2 = 1 := Real.sin_sq_add_cos_sq ω
  have hgap : c = C⁻¹ - Real.tan ω :=
    (parallelogram_gap ω ⟨hω.1.le, hω.2⟩).2.2.2.2
  have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
  have hcC : c * C = 1 - S := by
    rw [hgap, htan]
    field_simp [hC.ne']
  have hS1 : S < 1 := by nlinarith [sq_pos_of_pos hC]
  have hc0 : 0 < c := by
    have hcdiv : c = (1 - S) / C := by
      apply (eq_div_iff hC.ne').2
      exact hcC
    rw [hcdiv]
    exact div_pos (sub_pos.mpr hS1) hC
  have hb0 : 0 ≤ b := by dsimp [b]; linarith
  have hbC : b * C = S - d * C := by
    dsimp [b]
    rw [htan]
    field_simp [hC.ne']
  have hAC : A * C = 1 - b * C := by
    dsimp [A]
    nlinarith [hcC, hbC]
  have hH0 : 0 ≤ H := by positivity
  have hH1 : H ≤ 1 := by
    dsimp [H, b]
    apply (div_le_iff₀ hS).2
    dsimp [b] at hbC
    nlinarith
  have hf : Measurable f := measurable_const
  have hg : Measurable g := by fun_prop
  have hfi : IntegrableOn f (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).mp
      ((by fun_prop : Continuous f).intervalIntegrable 0 H)
  have hgi : IntegrableOn g (Icc (0 : ℝ) H) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).mp
      ((by fun_prop : Continuous g).intervalIntegrable 0 H)
  have hfg : ∀ y ∈ Icc (0 : ℝ) H, f y ≤ g y := by
    intro y hy
    dsimp [f, g, A]
    apply (le_div_iff₀ hC).2
    dsimp [H, b] at hy
    dsimp [b] at hbC hAC
    have hy' := (le_div_iff₀ hS).1 hy.2
    nlinarith
  have hset : rightRemovedTriangle ω d =
      {p : Point | p 1 ∈ Icc (0 : ℝ) H ∧ p 0 ∈ Ioc (f (p 1)) (g (p 1))} := by
    ext p
    simp only [rightRemovedTriangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_Icc, Set.mem_Ioc]
    rw [mem_stripParallelogram_coordinates]
    constructor
    · rintro ⟨⟨hy, hz⟩, hxA⟩
      refine ⟨⟨hy.1, ?_⟩, ?_, ?_⟩
      · dsimp [H, b]
        have hu : C * A + S * p 1 < 1 := by
          dsimp [A]
          nlinarith [mul_lt_mul_of_pos_left hxA hC]
        apply (le_div_iff₀ hS).2
        nlinarith [hAC]
      · simpa [f, A, add_comm]
      · dsimp [g]
        apply (le_div_iff₀ hC).2
        linarith [hz.2]
    · rintro ⟨hy, hxA, hxU⟩
      refine ⟨⟨⟨hy.1, hy.2.trans hH1⟩, ?_, ?_⟩, ?_⟩
      · have hA0 : 0 < A := by dsimp [A]; linarith
        dsimp [f, A] at hxA
        nlinarith [mul_pos hC (lt_trans hA0 hxA)]
      · dsimp [g] at hxU
        have := (le_div_iff₀ hC).1 hxU
        linarith
      · simpa [f, A, add_comm] using hxA
  rw [hset, volume_horizontalIoc hf hg measurableSet_Icc hfi hgi hfg]
  have hdiff : g - f = fun y ↦ b - S / C * y := by
    funext y
    dsimp [f, g, A, b]
    rw [hgap, htan]
    field_simp [hC.ne']
    ring
  rw [hdiff, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hH0]
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ b) volume 0 H :=
    continuous_const.intervalIntegrable 0 H
  have hlinear : IntervalIntegrable (fun y : ℝ ↦ S / C * y) volume 0 H :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 H
  rw [intervalIntegral.integral_sub hconst hlinear,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_id]
  simp only [sub_zero, smul_eq_mul]
  congr 1
  norm_num
  change H * b - S / C * (H ^ 2 / 2) = b ^ 2 * (C / S) / 2
  dsimp [H]
  field_simp [hC.ne', hS.ne']
  ring

private theorem measurableSet_stripParallelogram (ω : ℝ) :
    MeasurableSet (stripParallelogram ω).1 := by
  rw [show (stripParallelogram ω).1 =
      {p : Point |
        (0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (0 ≤ Real.cos ω * p 0 + Real.sin ω * p 1 ∧
          Real.cos ω * p 0 + Real.sin ω * p 1 ≤ 1)} by
    ext p
    exact mem_stripParallelogram_coordinates ω p]
  measurability

private theorem measurableSet_rightRemovedTriangle (ω d : ℝ) :
    MeasurableSet (rightRemovedTriangle ω d) := by
  unfold rightRemovedTriangle
  apply (measurableSet_stripParallelogram ω).inter
  measurability

private theorem measurableSet_leftRemovedTriangle (ω d : ℝ) :
    MeasurableSet (leftRemovedTriangle ω d) := by
  unfold leftRemovedTriangle
  apply (measurableSet_stripParallelogram ω).inter
  measurability

private theorem volume_leftRemovedTriangle_eq_right (ω d : ℝ) :
    volume (leftRemovedTriangle ω d) = volume (rightRemovedTriangle ω d) := by
  rw [leftRemovedTriangle_eq_preimage]
  exact (LinearIsometryEquiv.measurePreserving (capReflection ω)).measure_preimage
    (measurableSet_rightRemovedTriangle ω d).nullMeasurableSet

private theorem stripParallelogram_decomposition (ω d : ℝ) :
    (stripParallelogram ω).1 =
      (clippedCap ω d ∪ rightRemovedTriangle ω d) ∪ leftRemovedTriangle ω d := by
  ext p
  simp only [Set.mem_union]
  constructor
  · intro hp
    by_cases hx : p 0 ≤ d + Real.tan ((Real.pi / 2 - ω) / 2)
    · by_cases hz : -Real.sin ω * p 0 + Real.cos ω * p 1 ≤
          d + Real.tan ((Real.pi / 2 - ω) / 2)
      · exact Or.inl (Or.inl ((mem_clippedCap_iff ω d p).2
          ⟨((mem_stripParallelogram_coordinates ω p).1 hp).1,
            ((mem_stripParallelogram_coordinates ω p).1 hp).2, hx, hz⟩))
      · exact Or.inr ⟨hp, by
          change d + Real.tan ((Real.pi / 2 - ω) / 2) <
            -Real.sin ω * p 0 + Real.cos ω * p 1
          exact lt_of_not_ge hz⟩
    · exact Or.inl (Or.inr ⟨hp, by
        change d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0
        exact lt_of_not_ge hx⟩)
  · rintro (hp | hp)
    · rcases hp with hp | hp
      · exact (mem_stripParallelogram_coordinates ω p).2
          ⟨((mem_clippedCap_iff ω d p).1 hp).1,
            ((mem_clippedCap_iff ω d p).1 hp).2.1⟩
      · exact hp.1
    · exact hp.1

private theorem clippedCap_disjoint_rightRemovedTriangle (ω d : ℝ) :
    Disjoint (clippedCap ω d) (rightRemovedTriangle ω d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := ((mem_clippedCap_iff ω d p).1 hp).2.2.1
  exact (not_lt_of_ge hp') hq.2

private theorem clippedCap_disjoint_leftRemovedTriangle (ω d : ℝ) :
    Disjoint (clippedCap ω d) (leftRemovedTriangle ω d) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have hp' := ((mem_clippedCap_iff ω d p).1 hp).2.2.2
  exact (not_lt_of_ge hp') hq.2

private theorem rightRemovedTriangle_disjoint_leftRemovedTriangle
    {ω d : ℝ} (hC : 0 < Real.cos ω) (hS : 0 ≤ Real.sin ω) (hd : 0 ≤ d)
    (hc : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) = Real.cos ω) :
    Disjoint (rightRemovedTriangle ω d) (leftRemovedTriangle ω d) := by
  apply (clippedCap_removed_pieces_disjoint hC hS hd hc).mono
  · rintro p ⟨hp, hright⟩
    change d + Real.tan ((Real.pi / 2 - ω) / 2) < p 0 at hright
    exact ⟨((mem_stripParallelogram_coordinates ω p).1 hp).1.2,
      by simpa [add_comm] using hright⟩
  · rintro p ⟨_, hleft⟩
    change d + Real.tan ((Real.pi / 2 - ω) / 2) <
      -Real.sin ω * p 0 + Real.cos ω * p 1 at hleft
    simpa [add_comm] using hleft

theorem clippedCap_area_formula (ω d : ℝ)
    (hω : ω ∈ Ioo 0 (Real.pi / 2)) (hd0 : 0 ≤ d) (hdt : d ≤ Real.tan ω) :
    ClassicalResults.area (clippedCap ω d) =
      1 / Real.cos ω - (Real.tan ω - d) ^ 2 *
        (Real.cos ω / Real.sin ω) := by
  let C := Real.cos ω
  let S := Real.sin ω
  let c := Real.tan ((Real.pi / 2 - ω) / 2)
  let T := (Real.tan ω - d) ^ 2 * (C / S) / 2
  have hC : 0 < C :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hS : 0 < S := Real.sin_pos_of_pos_of_lt_pi hω.1
    (by linarith [hω.2, Real.pi_pos])
  have hgap : c = C⁻¹ - Real.tan ω :=
    (parallelogram_gap ω ⟨hω.1.le, hω.2⟩).2.2.2.2
  have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
  have hcC : c * C = 1 - S := by
    rw [hgap, htan]
    field_simp [hC.ne']
  have hc : c * (1 + S) = C := by
    apply (mul_right_cancel₀ hC.ne')
    nlinarith [hcC, Real.sin_sq_add_cos_sq ω]
  have hP := volume_stripParallelogram ω hC
  have hR := volume_rightRemovedTriangle ω d hω hd0 hdt
  have hL : volume (leftRemovedTriangle ω d) = ENNReal.ofReal T := by
    rw [volume_leftRemovedTriangle_eq_right, hR]
  have hR' : volume (rightRemovedTriangle ω d) = ENNReal.ofReal T := by
    simpa [T, C, S] using hR
  have hCR := clippedCap_disjoint_rightRemovedTriangle ω d
  have hCL := clippedCap_disjoint_leftRemovedTriangle ω d
  have hRL := rightRemovedTriangle_disjoint_leftRemovedTriangle hC hS.le hd0 hc
  have hdecomp : volume (stripParallelogram ω).1 =
      (volume (clippedCap ω d) + volume (rightRemovedTriangle ω d)) +
        volume (leftRemovedTriangle ω d) := by
    rw [stripParallelogram_decomposition,
      measure_union (hCL.union_left hRL) (measurableSet_leftRemovedTriangle ω d),
      measure_union hCR (measurableSet_rightRemovedTriangle ω d)]
  rw [hP, hR', hL] at hdecomp
  have hclip_subset : clippedCap ω d ⊆ (stripParallelogram ω).1 := by
    intro p hp
    exact (mem_stripParallelogram_coordinates ω p).2
      ⟨((mem_clippedCap_iff ω d p).1 hp).1,
        ((mem_clippedCap_iff ω d p).1 hp).2.1⟩
  have hclip_ne : volume (clippedCap ω d) ≠ ⊤ := by
    apply ne_of_lt
    refine lt_of_le_of_lt (measure_mono hclip_subset) ?_
    rw [hP]
    exact ENNReal.ofReal_lt_top
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hTne : ENNReal.ofReal T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsum_ne : volume (clippedCap ω d) + ENNReal.ofReal T ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hclip_ne, hTne⟩
  have hreal := congrArg ENNReal.toReal hdecomp
  rw [ENNReal.toReal_add hsum_ne hTne,
    ENNReal.toReal_add hclip_ne hTne,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / Real.cos ω),
    ENNReal.toReal_ofReal hT0] at hreal
  unfold ClassicalResults.area
  dsimp [T, C, S] at hreal ⊢
  linarith

theorem clippedCap_minimum_area (ω : RotationCalculationAngle) :
    ClassicalResults.area (clippedCap ω.val (rotationCalculationMinimum ω)) < 11 / 5 := by
  have hω0 : 0 < ω.val :=
    (Real.arccos_pos.mpr (by norm_num : (5 / 11 : ℝ) < 1)).trans_le ω.property.1
  calc
    ClassicalResults.area (clippedCap ω.val (rotationCalculationMinimum ω)) =
        1 / Real.cos ω.val -
          (Real.tan ω.val - rotationCalculationMinimum ω) ^ 2 *
            (Real.cos ω.val / Real.sin ω.val) :=
      clippedCap_area_formula ω.val (rotationCalculationMinimum ω)
        ⟨hω0, ω.property.2⟩ (rotationCalculationMinimum_pos ω).le
        (rotationCalculationMinimum_lt_tan ω).le
    _ < 11 / 5 := rotationCalculation_area_estimate ω

end MovingSofa
