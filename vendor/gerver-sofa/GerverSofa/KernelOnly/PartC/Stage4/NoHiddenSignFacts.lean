import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenMatchFacts

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

noncomputable section

private theorem phi_upper_twentieth : params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_six_fifths : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem b1_upper_neg_half : params.b1 ≤ (-1 / 2 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem d1_lower_thirteen_tenths : (13 / 10 : ℝ) ≤ params.d1 := by
  have h := PartB.d1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem T_lt_eight_fifths : T < (8 / 5 : ℝ) := by
  have hp := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hp.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem alphaBeta1_fst_nonpos_small {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (Romik.alphaBeta1 params s).1 ≤ 0 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinLower := Real.sin_ge_sub_cube hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcube : 0 ≤ s ^ 2 * ((1 / 20 : ℝ) - s) :=
    mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths]
  have hmul : (12 / 5 : ℝ) * Real.sin s ≤ 2 * params.a1 * Real.sin s :=
    mul_le_mul_of_nonneg_right hcoef hsin0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinLower, hcosLower, hquad, hcube, hmul]

private theorem alphaBeta1_snd_nonneg_small {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    0 ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤ 2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hcosLower, hquad, hmul]

private theorem alphaBeta5_fst_nonpos_tail {t : ℝ}
    (ht : t ∈ Icc tau T) :
    (Romik.alphaBeta5 params t).1 ≤ 0 := by
  let s : ℝ := T - t
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith [ht.2]
  have hsphi : s ≤ params.phi := by
    have hTtau : T - tau = params.phi := by
      dsimp [tau]
      ring
    dsimp [s]
    rw [← hTtau]
    linarith [ht.1]
  have hs20 : s ≤ (1 / 20 : ℝ) := le_trans hsphi phi_upper_twentieth
  have hb := alphaBeta1_snd_nonneg_small hs0 hs20
  have href := congrArg Prod.fst (alphaBeta5_reflect1_direct s)
  have hTs : T - s = t := by
    dsimp [s]
    ring
  rw [hTs] at href
  have heq : (Romik.alphaBeta5 params t).1 = -(Romik.alphaBeta1 params s).2 := by
    simpa [noHiddenReflAB] using href
  rw [heq]
  exact neg_nonpos.mpr hb

private theorem alphaBeta5_snd_nonneg_tail {t : ℝ}
    (ht : t ∈ Icc tau T) :
    0 ≤ (Romik.alphaBeta5 params t).2 := by
  let s : ℝ := T - t
  have hs0 : 0 ≤ s := by
    dsimp [s]
    linarith [ht.2]
  have hsphi : s ≤ params.phi := by
    have hTtau : T - tau = params.phi := by
      dsimp [tau]
      ring
    dsimp [s]
    rw [← hTtau]
    linarith [ht.1]
  have hs20 : s ≤ (1 / 20 : ℝ) := le_trans hsphi phi_upper_twentieth
  have ha := alphaBeta1_fst_nonpos_small hs0 hs20
  have href := congrArg Prod.snd (alphaBeta5_reflect1_direct s)
  have hTs : T - s = t := by
    dsimp [s]
    ring
  rw [hTs] at href
  have heq : (Romik.alphaBeta5 params t).2 = -(Romik.alphaBeta1 params s).1 := by
    simpa [noHiddenReflAB] using href
  rw [heq]
  exact neg_nonneg.mpr ha

/-- The `u_t` coefficient of the Gerver velocity is nonpositive on the
entire no-hidden `U` domain. -/
theorem alpha_nonpos {t : ℝ} (ht : t ∈ Icc params.phi T) :
    alpha t ≤ 0 := by
  have htPhysical : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_nonneg ht.1, ht.2⟩
  by_cases hphi : t ≤ params.phi
  · have heq : t = params.phi := le_antisymm hphi ht.1
    subst t
    have h := alphaBeta1_fst_nonpos_small phi_nonneg phi_upper_twentieth
    simpa [alpha, alphaBetaAt] using h
  · by_cases htheta : t ≤ params.theta
    · simp only [alpha, alphaBetaAt, if_neg hphi, if_pos htheta]
      dsimp [Romik.alphaBeta2]
      have ht0 : 0 ≤ t := le_trans phi_nonneg ht.1
      have hb : 1 + 2 * params.b1 ≤ 0 := by
        nlinarith [b1_upper_neg_half]
      nlinarith
    · by_cases heta : t ≤ eta
      · have hrho := Stage2.rhoC_nonneg htPhysical
        unfold Stage2.rhoC at hrho
        rw [if_neg hphi, if_neg htheta, if_pos heta] at hrho
        simp only [alpha, alphaBetaAt, if_neg hphi, if_neg htheta, if_pos heta]
        dsimp [Romik.alphaBeta3]
        nlinarith
      · by_cases htau : t ≤ tau
        · have hrho := Stage2.rhoC_nonneg htPhysical
          unfold Stage2.rhoC at hrho
          rw [if_neg hphi, if_neg htheta, if_neg heta, if_pos htau] at hrho
          simp only [alpha, alphaBetaAt, if_neg hphi, if_neg htheta, if_neg heta, if_pos htau]
          dsimp [Romik.alphaBeta4]
          nlinarith
        · have ht5 : t ∈ Icc tau T := ⟨le_of_lt (lt_of_not_ge htau), ht.2⟩
          have h5 := alphaBeta5_fst_nonpos_tail ht5
          simpa [alpha, alphaBetaAt, hphi, htheta, heta, htau] using h5

/-- The `v_t` coefficient of the Gerver velocity is nonnegative on the
entire no-hidden `U` domain. -/
theorem beta_nonneg {t : ℝ} (ht : t ∈ Icc params.phi T) :
    0 ≤ beta t := by
  have htPhysical : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_nonneg ht.1, ht.2⟩
  by_cases hphi : t ≤ params.phi
  · have heq : t = params.phi := le_antisymm hphi ht.1
    subst t
    have h := alphaBeta1_snd_nonneg_small phi_nonneg phi_upper_twentieth
    simpa [beta, alphaBetaAt] using h
  · by_cases htheta : t ≤ params.theta
    · have hrho := Stage2.rhoA_nonneg htPhysical
      unfold Stage2.rhoA at hrho
      rw [if_neg hphi, if_pos htheta] at hrho
      simp only [beta, alphaBetaAt, if_neg hphi, if_pos htheta]
      dsimp [Romik.alphaBeta2]
      exact hrho
    · by_cases heta : t ≤ eta
      · have hrho := Stage2.rhoA_nonneg htPhysical
        unfold Stage2.rhoA at hrho
        rw [if_neg hphi, if_neg htheta, if_pos heta] at hrho
        simp only [beta, alphaBetaAt, if_neg hphi, if_neg htheta, if_pos heta]
        dsimp [Romik.alphaBeta3]
        exact hrho
      · by_cases htau : t ≤ tau
        · simp only [beta, alphaBetaAt, if_neg hphi, if_neg htheta, if_neg heta, if_pos htau]
          dsimp [Romik.alphaBeta4]
          nlinarith [d1_lower_thirteen_tenths, T_lt_eight_fifths, ht.2]
        · have ht5 : t ∈ Icc tau T := ⟨le_of_lt (lt_of_not_ge htau), ht.2⟩
          have h5 := alphaBeta5_snd_nonneg_tail ht5
          simpa [beta, alphaBetaAt, hphi, htheta, heta, htau] using h5

end

end Stage4
end PartC
end GerverSofa
