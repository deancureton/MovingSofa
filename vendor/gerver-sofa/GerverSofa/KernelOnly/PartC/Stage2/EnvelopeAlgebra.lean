import GerverSofa.KernelOnly.PartC.Stage2.MeshFacts

/-!
# Part C Stage 2 redesign: exact envelope algebra

The first 64x64 contact-box attempt was intentionally fail-closed but too
coarse at contact/equality cells: interval dependency destroys exact
cancellation.  This module switches to the analytic envelope coefficients.

For the outer `u`-contact curve `A`, the phasewise velocity is a nonnegative
scalar multiple of `v`; for the outer `v`-contact curve `C`, the velocity is a
nonpositive scalar multiple of `u`.  The scalar coefficients below are the
five exact algebraic pieces.  No numerical root is recomputed here.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

/-- Phasewise scalar multiplying `v(t)` in the derivative of `A`. -/
def rhoA (t : ℝ) : ℝ :=
  if t ≤ params.phi then 0
  else if t ≤ params.theta then
    -(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2
  else if t ≤ eta then
    1 + params.c1 - t
  else if t ≤ tau then
    params.d1 - t / 2
  else
    1 / 2

/-- Phasewise nonnegative scalar for `C'(t) = -rhoC(t) * u(t)`. -/
def rhoC (t : ℝ) : ℝ :=
  if t ≤ params.phi then 1 / 2
  else if t ≤ params.theta then
    t / 2 - params.b1
  else if t ≤ eta then
    1 + params.c2 + t
  else if t ≤ tau then
    -(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2
  else
    0

private theorem b1_lower : (-53 / 100 : ℝ) ≤ params.b1 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((-52762459802678462416060380937 : ℝ) /
        100000000000000000000000000000) ≤ params.b1 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem b1_upper : params.b1 ≤ (-1 / 2 : ℝ) := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h : params.b1 ≤
      ((-52762459802678462416040380937 : ℝ) /
        100000000000000000000000000000) := by
    aesop
  norm_num at h ⊢
  linarith

private theorem b2_lower : (9 / 10 : ℝ) ≤ params.b2 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((92025838516063762289360579501 : ℝ) /
        100000000000000000000000000000) ≤ params.b2 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem c1_lower : (3 / 5 : ℝ) ≤ params.c1 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((313022761424232933776114655193 : ℝ) /
        500000000000000000000000000000) ≤ params.c1 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem c2_lower : (-1 : ℝ) ≤ params.c2 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((-151160128631428920268654781 : ℝ) /
        160000000000000000000000000) ≤ params.c2 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem d1_lower : (13 / 10 : ℝ) ≤ params.d1 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((1641278451780291167220080819 : ℝ) /
        1250000000000000000000000000) ≤ params.d1 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem d2_lower : (-53 / 100 : ℝ) ≤ params.d2 := by
  have hp := params_mem
  dsimp [Romik.box, qR] at hp
  have h :
      ((-105076534082910887440587258861 : ℝ) /
        200000000000000000000000000000) ≤ params.d2 := by
    aesop
  norm_num at h ⊢
  linarith

private theorem theta_lower_crude : (2 / 3 : ℝ) ≤ params.theta := by
  have h := theta_bounds.1
  norm_num at h ⊢
  linarith

private theorem theta_upper_crude : params.theta ≤ (7 / 10 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem T_lt_two : T < 2 := by
  have hpi := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hpi.2
  have hfour : (ExactReplay.piI.hi : ℝ) < 4 := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem three_halves_lt_T : (3 / 2 : ℝ) < T := by
  have hpi := ExactReplay.piI_contains_pi
  have hlo : (ExactReplay.piI.lo : ℝ) ≤ Real.pi := hpi.1
  have hthree : (3 : ℝ) < (ExactReplay.piI.lo : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem eta_lt_four_thirds : eta < (4 / 3 : ℝ) := by
  dsimp [eta]
  nlinarith [T_lt_two, theta_lower_crude]

private theorem four_fifths_lt_eta : (4 / 5 : ℝ) < eta := by
  dsimp [eta]
  nlinarith [three_halves_lt_T, theta_upper_crude]

private theorem rhoA_phase2_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) (htθ : t ≤ params.theta) :
    0 ≤ -(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2 := by
  have ht07 : t ≤ (7 / 10 : ℝ) := le_trans htθ theta_upper_crude
  have ht1 : t ≤ 1 := by linarith
  have hbt : (-53 / 100 : ℝ) * t ≤ params.b1 * t :=
    mul_le_mul_of_nonneg_right b1_lower ht0
  have hquad : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  nlinarith [b2_lower]

private theorem rhoA_phase3_nonneg
    {t : ℝ} (_ht0 : 0 ≤ t) (htη : t ≤ eta) :
    0 ≤ 1 + params.c1 - t := by
  have ht : t < (4 / 3 : ℝ) := lt_of_le_of_lt htη eta_lt_four_thirds
  nlinarith [c1_lower]

private theorem rhoA_phase4_nonneg
    {t : ℝ} (_ht0 : 0 ≤ t) (htτ : t ≤ tau) :
    0 ≤ params.d1 - t / 2 := by
  have htT : t ≤ T := le_trans htτ tau_le_T
  have ht2 : t < 2 := lt_of_le_of_lt htT T_lt_two
  nlinarith [d1_lower]

private theorem rhoC_phase2_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ t / 2 - params.b1 := by
  nlinarith [b1_upper]

private theorem rhoC_phase3_nonneg
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ 1 + params.c2 + t := by
  nlinarith [c2_lower]

private theorem rhoC_phase4_nonneg
    {t : ℝ} (hηt : eta ≤ t) (htτ : t ≤ tau) :
    0 ≤ -(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2 := by
  have ht0 : 0 ≤ t := by
    have : (0 : ℝ) < eta := lt_trans (by norm_num) four_fifths_lt_eta
    linarith
  have htT : t ≤ T := le_trans htτ tau_le_T
  have ht2 : t < 2 := lt_of_le_of_lt htT T_lt_two
  have hmul : (13 / 10 : ℝ) * t ≤ params.d1 * t :=
    mul_le_mul_of_nonneg_right d1_lower ht0
  have hquad : 0 ≤ t * (2 - t) := mul_nonneg ht0 (by linarith)
  nlinarith [d2_lower, four_fifths_lt_eta]

/-- The `A` envelope coefficient is nonnegative on the full physical range. -/
theorem rhoA_nonneg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 ≤ rhoA t := by
  unfold rhoA
  split_ifs with hφ hθ hη hτ
  · norm_num
  · exact rhoA_phase2_nonneg ht.1 hθ
  · exact rhoA_phase3_nonneg ht.1 hη
  · exact rhoA_phase4_nonneg ht.1 hτ
  · norm_num

/-- The reflected `C` envelope coefficient is nonnegative on the full physical range. -/
theorem rhoC_nonneg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 ≤ rhoC t := by
  unfold rhoC
  split_ifs with hφ hθ hη hτ
  · norm_num
  · exact rhoC_phase2_nonneg ht.1
  · exact rhoC_phase3_nonneg ht.1
  · have hηt : eta ≤ t := le_of_lt (lt_of_not_ge hη)
    exact rhoC_phase4_nonneg hηt hτ
  · norm_num

/-- The first outer contact starts at the exact fan endpoint `(1,0)`. -/
theorem A_zero_eq_anchor : A 0 = anchor := by
  have hφ : (0 : ℝ) ≤ params.phi := le_of_lt (Romik.phi_pos_of_mem_box params_mem)
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  have halpha0 : alpha 0 = 0 := by
    unfold alpha alphaBetaAt
    simp [hφ, Romik.alphaBeta1, ha2] <;> norm_num
  simp [A, anchor, pathZero, halpha0, u, v]

/-- The second outer contact ends exactly on the fan boundary. -/
theorem C_T_snd_zero : (C T).2 = 0 := by
  have hφpos : 0 < params.phi := Romik.phi_pos_of_mem_box params_mem
  have hτT : tau < T := by
    dsimp [tau]
    linarith
  have hητ : eta ≤ tau := switchOrder.eta_le_tau
  have hθη : params.theta ≤ eta := switchOrder.theta_le_eta
  have hφθ : params.phi ≤ params.theta := switchOrder.phi_le_theta
  have hφT : params.phi < T := lt_of_le_of_lt (le_trans hφθ (le_trans hθη hητ)) hτT
  have hθT : params.theta < T := lt_of_le_of_lt (le_trans hθη hητ) hτT
  have hηT : eta < T := lt_of_le_of_lt hητ hτT
  have he2 := Romik.e2_eq_quarter_of_equations params_equations
  have hABT : alphaBetaAt T = Romik.alphaBeta5 params T := by
    unfold alphaBetaAt
    rw [if_neg (not_le.mpr hφT)]
    rw [if_neg (not_le.mpr hθT)]
    rw [if_neg (not_le.mpr hηT)]
    rw [if_neg (not_le.mpr hτT)]
  have hbetaT : beta T = 0 := by
    rw [beta, hABT]
    simp [Romik.alphaBeta5, T, he2] <;> norm_num
  change (Romik.path params T).2 - beta T * (u T).2 + (v T).2 = 0
  rw [pathEndYZero, hbetaT]
  simp [u, v, T]

end Stage2
end PartC
end GerverSofa
