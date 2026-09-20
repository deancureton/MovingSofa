import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenSignFacts

/-!
# Part C Stage 4: positive turning determinant on phases 2--5

The determinant is the signed turning numerator of the nonzero path velocity.
These phasewise facts are the analytic input for the remaining one-turn chord
argument; they do not assert the no-hidden conclusion by themselves.
-/

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

noncomputable section

private theorem b1_upper_neg_half_turn : params.b1 ≤ (-1 / 2 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem d1_lower_thirteen_tenths_turn : (13 / 10 : ℝ) ≤ params.d1 := by
  have h := PartB.d1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem T_lt_eight_fifths_turn : T < (8 / 5 : ℝ) := by
  have hp := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hp.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

/-! The next six statements expose the coefficient-derivative signs used in
the manuscript's tangent-angle argument.  They are deliberately stated for
the explicit smooth-phase formulae; no derivative is assigned at a switch. -/

theorem phase2_betaPrime_neg {r : ℝ}
    (hr : r ∈ Ioo params.phi params.theta) :
    -(1 / 2 : ℝ) * r + params.b1 < 0 := by
  have hr0 : 0 ≤ r := le_trans phi_nonneg hr.1.le
  nlinarith [b1_upper_neg_half_turn]

theorem phase4_alphaPrime_neg {r : ℝ} (hr : r ∈ Ioo eta tau) :
    (1 / 2 : ℝ) * r - params.d1 < 0 := by
  have hrT : r < T := lt_trans hr.2 tau_lt_T
  nlinarith [d1_lower_thirteen_tenths_turn, T_lt_eight_fifths_turn]

private theorem a1_lower_six_fifths_turn : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem phi_upper_twentieth_turn : params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem alpha1_prime_nonpos_small_turn {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    -2 * params.a1 * Real.cos s - 2 * params.a2 * Real.sin s ≤ 0 := by
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths_turn]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  rw [ha2]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  nlinarith [hsinUpper, hcosLower, hmul, hquad]

private theorem beta1_prime_nonpos_small_turn {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    -2 * params.a1 * Real.sin s + 2 * params.a2 * Real.cos s ≤ 0 := by
  have hpi : s ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have ha1 : 0 ≤ params.a1 := le_trans (by norm_num : (0 : ℝ) ≤ 6 / 5)
    a1_lower_six_fifths_turn
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  rw [ha2]
  nlinarith [mul_nonneg ha1 hsin0, hcos0]

private theorem phase5_derivative_signs_turn {t : ℝ}
    (ht : t ∈ Ioo tau T) :
    (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t ≤ 0) ∧
    (-2 * params.e1 * Real.sin t + 2 * params.e2 * Real.cos t ≤ 0) := by
  let s : ℝ := T - t
  have hs0 : 0 ≤ s := by dsimp [s]; linarith [ht.2]
  have hsphi : s ≤ params.phi := by
    have hTtau : T - tau = params.phi := by
      dsimp [tau]
      ring
    dsimp [s]
    rw [← hTtau]
    linarith [ht.1]
  have hs20 : s ≤ (1 / 20 : ℝ) := le_trans hsphi phi_upper_twentieth_turn
  have hap1 := alpha1_prime_nonpos_small_turn hs0 hs20
  have hbp1 := beta1_prime_nonpos_small_turn hs0 hs20
  have he1 := Romik.e1_eq_a1_of_equations params_equations
  have he2 := Romik.e2_eq_neg_a2_of_equations params_equations
  have hsin := Real.sin_pi_div_two_sub s
  have hcos := Real.cos_pi_div_two_sub s
  have hts : t = T - s := by dsimp [s]; ring
  constructor
  · rw [hts]
    dsimp [T]
    rw [he1, he2, hcos, hsin]
    simpa [mul_add, add_mul] using hbp1
  · rw [hts]
    dsimp [T]
    rw [he1, he2, hsin, hcos]
    simpa [mul_add, add_mul] using hap1

/-- Phase-five coefficient derivatives are nonpositive.  This is the exact
formula-level input used below; strict turning follows from the strict
nonvanishing of the first coefficient. -/
theorem phase5_coefficientPrime_nonpos {t : ℝ}
    (ht : t ∈ Ioo tau T) :
    (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t ≤ 0) ∧
    (-2 * params.e1 * Real.sin t + 2 * params.e2 * Real.cos t ≤ 0) :=
  phase5_derivative_signs_turn ht

end

end Stage4
end PartC
end GerverSofa
