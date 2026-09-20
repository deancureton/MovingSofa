import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenDirect
import GerverSofa.KernelOnly.PartC.Stage4.WallGraphs

/-!
# Part C Stage 4: direct membership of the certified vertical fills

These are the three concrete reverse-inclusion facts needed to identify the
literal niche with its certified vertical-fill region.  They are proved from
the literal open-quadrant definition, not assumed through a Stage 2 API.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

private theorem sin_pos_physical {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1
    (lt_trans ht.2 (by dsimp [T]; linarith [Real.pi_pos]))

private theorem cos_pos_physical {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩

private theorem phi_upper_twentieth_membership :
    params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_six_fifths_membership :
    (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem alphaBeta1_snd_nonneg_early {s : ℝ}
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
    nlinarith [a1_lower_six_fifths_membership]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤
      2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hcosLower, hquad, hmul]

private theorem beta_nonneg_early {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.theta) : 0 ≤ beta t := by
  by_cases hphi : t ≤ params.phi
  · have hs20 : t ≤ (1 / 20 : ℝ) :=
      le_trans hphi phi_upper_twentieth_membership
    have h := alphaBeta1_snd_nonneg_early ht.1 hs20
    simpa [beta, alphaBetaAt, hphi] using h
  · have htPhysical : t ∈ Icc (0 : ℝ) T :=
      ⟨ht.1, le_trans ht.2 (le_trans theta_lt_eta.le
        (le_trans eta_lt_tau.le tau_le_T))⟩
    have hrho := Stage2.rhoA_nonneg htPhysical
    unfold Stage2.rhoA at hrho
    rw [if_neg hphi, if_pos ht.2] at hrho
    simp only [beta, alphaBetaAt, if_neg hphi, if_pos ht.2]
    dsimp [Romik.alphaBeta2]
    exact hrho

private theorem B_bRoof_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    bRoof t (B t).1 = (B t).2 := by
  have hs0 : Real.sin t ≠ 0 := ne_of_gt (sin_pos_physical ht)
  have hcontact := B_inner_u_identity t
  unfold bRoof
  apply (div_eq_iff hs0).2
  dsimp [dot, u] at hcontact ⊢
  nlinarith

private theorem B_le_dRoof {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (htPhi : t ∈ Icc params.phi T) :
    (B t).2 ≤ dRoof t (B t).1 := by
  have hc := cos_pos_physical ht
  have ha := alpha_nonpos htPhi
  have hv : dot (B t - Romik.path params t) (v t) = alpha t := by
    simp only [B, dot, v]
    simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold dRoof
  apply (le_div_iff₀ hc).2
  dsimp [dot, v] at hv ⊢
  nlinarith

private theorem D_dRoof_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    dRoof t (D t).1 = (D t).2 := by
  have hc0 : Real.cos t ≠ 0 := ne_of_gt (cos_pos_physical ht)
  have hcontact := D_inner_v_identity t
  unfold dRoof
  apply (div_eq_iff hc0).2
  dsimp [dot, v] at hcontact ⊢
  nlinarith

private theorem D_le_bRoof {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (htTheta : t ∈ Icc (0 : ℝ) params.theta) :
    (D t).2 ≤ bRoof t (D t).1 := by
  have hs := sin_pos_physical ht
  have hb := beta_nonneg_early htTheta
  have hu : dot (D t - Romik.path params t) (u t) = -beta t := by
    simp only [D, dot, u]
    simp
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold bRoof
  apply (le_div_iff₀ hs).2
  dsimp [dot, u] at hu ⊢
  nlinarith

/-- Every strict vertical point below a core-path point belongs to the literal
niche. -/
theorem vertical_below_path_mem_niche {r Y : ℝ}
    (hr : r ∈ Icc params.phi tau) (hY0 : 0 ≤ Y)
    (hY : Y < (Romik.path params r).2) :
    ((Romik.path params r).1, Y) ∈ Romik.niche params := by
  have hrIoo : r ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le phi_pos hr.1,
      lt_of_le_of_lt hr.2 tau_lt_T⟩
  refine ⟨by simpa [capFan] using hY0, ⟨r, hrIoo, ?_⟩⟩
  apply (mem_innerQuadrant_iff_roofs hrIoo).2
  have hroof := roofs_at_path r hrIoo
  rw [hroof.1, hroof.2]
  exact ⟨hY, hY⟩

/-- Every strict vertical point below the late `B` contact belongs to the
literal niche. -/
theorem vertical_below_B_mem_niche {r Y : ℝ}
    (hr : r ∈ Icc eta T) (hY0 : 0 ≤ Y) (hY : Y < (B r).2) :
    ((B r).1, Y) ∈ Romik.niche params := by
  have hrlt : r < T := by
    by_contra hnot
    have hrT : r = T := le_antisymm hr.2 (le_of_not_gt hnot)
    subst r
    rw [B_T_y_zero] at hY
    linarith
  have hrIoo : r ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le (lt_trans theta_pos theta_lt_eta) hr.1, hrlt⟩
  have hrPhi : r ∈ Icc params.phi T :=
    ⟨le_trans (le_trans phi_lt_theta.le theta_lt_eta.le) hr.1, hr.2⟩
  refine ⟨by simpa [capFan] using hY0, ⟨r, hrIoo, ?_⟩⟩
  apply (mem_innerQuadrant_iff_roofs hrIoo).2
  refine ⟨?_, ?_⟩
  · rw [B_bRoof_eq hrIoo]
    exact hY
  · exact lt_of_lt_of_le hY (B_le_dRoof hrIoo hrPhi)

/-- Every strict vertical point below the early `D` contact belongs to the
literal niche. -/
theorem vertical_below_D_mem_niche {r Y : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta) (hY0 : 0 ≤ Y)
    (hY : Y < (D r).2) :
    ((D r).1, Y) ∈ Romik.niche params := by
  have hrpos : 0 < r := by
    by_contra hnot
    have hr0 : r = 0 := le_antisymm (le_of_not_gt hnot) hr.1
    subst r
    rw [D_zero_y_zero] at hY
    linarith
  have hrIoo : r ∈ Ioo (0 : ℝ) T :=
    ⟨hrpos, lt_of_le_of_lt hr.2 theta_lt_T⟩
  refine ⟨by simpa [capFan] using hY0, ⟨r, hrIoo, ?_⟩⟩
  apply (mem_innerQuadrant_iff_roofs hrIoo).2
  refine ⟨?_, ?_⟩
  · exact lt_of_lt_of_le hY (D_le_bRoof hrIoo hr)
  · rw [D_dRoof_eq hrIoo]
    exact hY

end Stage4
end PartC
end GerverSofa
