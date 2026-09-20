import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenDirect

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

private theorem phi_le_one_twentieth_diag :
    params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_diag : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem a1_upper_diag : params.a1 ≤ (5 / 4 : ℝ) := by
  have h := PartB.a1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem phase1_alpha_lower {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (-1 / 8 : ℝ) ≤ (Romik.alphaBeta1 params s).1 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosUpper := Real.cos_le_one s
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  have hmul : 2 * params.a1 * Real.sin s ≤ (1 / 8 : ℝ) := by
    have h1 : 2 * params.a1 ≤ (5 / 2 : ℝ) := by
      nlinarith [a1_upper_diag]
    have h2 : Real.sin s ≤ (1 / 20 : ℝ) :=
      le_trans hsinUpper hs20
    nlinarith [mul_nonneg hsin0 (sub_nonneg.mpr h1),
      mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ (5 / 2 : ℝ) by norm_num)]
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith

private theorem phase1_alpha_nonpos_diag {s : ℝ}
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
    nlinarith [a1_lower_diag]
  have hmul : (12 / 5 : ℝ) * Real.sin s ≤
      2 * params.a1 * Real.sin s :=
    mul_le_mul_of_nonneg_right hcoef hsin0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinLower, hcosLower, hquad, hcube, hmul]

private theorem phase1_beta_lower {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (13 / 10 : ℝ) ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcosCrude : (799 / 800 : ℝ) ≤ Real.cos s := by
    nlinarith [hcosLower, sq_nonneg s,
      mul_nonneg hs0 (sub_nonneg.mpr hs20)]
  have hcos0 : 0 ≤ Real.cos s := by linarith
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_diag]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤
      2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hmul]

private theorem dot_rot_phase1_diag (s t : ℝ) :
    dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t) =
      (Romik.alphaBeta1 params s).1 *
          (Real.cos (s - t) + Real.sin (s - t)) +
      (Romik.alphaBeta1 params s).2 *
          (Real.cos (s - t) - Real.sin (s - t)) := by
  simp [dot, Romik.rot, u, v, Real.cos_sub, Real.sin_sub]
  ring

private theorem phase1_diag_deriv_nonneg {t s : ℝ}
    (ht0 : 0 ≤ t) (hts : t ≤ s) (hsphi : s ≤ params.phi) :
    0 ≤ dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t) := by
  have hs0 : 0 ≤ s := le_trans ht0 hts
  have hs20 : s ≤ (1 / 20 : ℝ) :=
    le_trans hsphi phi_le_one_twentieth_diag
  have hd0 : 0 ≤ s - t := sub_nonneg.mpr hts
  have hd20 : s - t ≤ (1 / 20 : ℝ) := by linarith
  have hdpi : s - t ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin (s - t) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd0 hdpi
  have hsinUpper := Real.sin_le hd0
  have hcosLower : 1 - (s - t) ^ 2 / 2 ≤ Real.cos (s - t) :=
    Real.one_sub_sq_div_two_le_cos
  have hcosUpper := Real.cos_le_one (s - t)
  have hdiff : (9 / 10 : ℝ) ≤
      Real.cos (s - t) - Real.sin (s - t) := by
    nlinarith [hcosLower, hsinUpper, sq_nonneg (s - t),
      mul_nonneg hd0 (sub_nonneg.mpr hd20)]
  have hsum0 : 0 ≤ Real.cos (s - t) + Real.sin (s - t) := by
    nlinarith
  have hsumUpper : Real.cos (s - t) + Real.sin (s - t) ≤ (21 / 20 : ℝ) := by
    nlinarith
  have haLo := phase1_alpha_lower hs0 hs20
  have haHi := phase1_alpha_nonpos_diag hs0 hs20
  have hbLo := phase1_beta_lower hs0 hs20
  have haProd : (-21 / 160 : ℝ) ≤
      (Romik.alphaBeta1 params s).1 *
        (Real.cos (s - t) + Real.sin (s - t)) := by
    have hmul1 := mul_le_mul_of_nonpos_left hsumUpper haHi
    have hmul2 := mul_le_mul_of_nonneg_right haLo
      (show 0 ≤ (21 / 20 : ℝ) by norm_num)
    nlinarith
  have hbProd : (117 / 100 : ℝ) ≤
      (Romik.alphaBeta1 params s).2 *
        (Real.cos (s - t) - Real.sin (s - t)) := by
    have hdiff0 : 0 ≤ Real.cos (s - t) - Real.sin (s - t) := by linarith
    have hb0 : 0 ≤ (Romik.alphaBeta1 params s).2 := by linarith
    nlinarith [mul_nonneg
      ((show 0 ≤ (Romik.alphaBeta1 params s).2 - 13 / 10 by linarith)) hdiff0,
      mul_nonneg (show 0 ≤ (13 / 10 : ℝ) by norm_num)
        (show 0 ≤ Real.cos (s - t) - Real.sin (s - t) - 9 / 10 by linarith)]
  rw [dot_rot_phase1_diag]
  linarith

private theorem dot_path1_diag_hasDerivAt (t s : ℝ) :
    HasDerivAt (fun r => dot (Romik.path1 params r) (u t + v t))
      (dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t)) s := by
  have h := path1_hasDerivAt_public s
  have h1 := HasDerivAt.const_mul (u t + v t).1 h.fst
  have h2 := HasDerivAt.const_mul (u t + v t).2 h.snd
  simpa [dot, mul_comm] using h1.fun_add h2

theorem early_endpoint_diagonal_nonneg {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    0 ≤ dot (Romik.path params params.phi - Romik.path params t) (u t + v t) := by
  have hmono : MonotoneOn
      (fun s => dot (Romik.path1 params s) (u t + v t))
      (Icc t params.phi) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun s => dot (Romik.rot s (Romik.alphaBeta1 params s)) (u t + v t))
      (convex_Icc t params.phi) ?_ ?_ ?_
    · intro s hs
      exact (dot_path1_diag_hasDerivAt t s).continuousAt.continuousWithinAt
    · intro s hs
      exact (dot_path1_diag_hasDerivAt t s).hasDerivWithinAt
    · intro s hs
      have hi : s ∈ Ioo t params.phi := by
        simpa only [interior_Icc] using hs
      exact phase1_diag_deriv_nonneg ht.1 hi.1.le hi.2.le
  have hle := hmono
    (show t ∈ Icc t params.phi from ⟨le_rfl, ht.2⟩)
    (show params.phi ∈ Icc t params.phi from ⟨ht.2, le_rfl⟩) ht.2
  have hpathT : Romik.path params t = Romik.path1 params t := by
    simp only [Romik.path, if_pos ht.2]
  have hpathPhi : Romik.path params params.phi =
      Romik.path1 params params.phi := by
    simp only [Romik.path, if_pos le_rfl]
  rw [hpathT, hpathPhi]
  unfold dot at hle ⊢
  dsimp at hle ⊢
  linarith

private def diagPhaseB4 (r : ℝ) : Point :=
  Stage2.phaseA4 r - u r

private def diagPhaseB5 (r : ℝ) : Point :=
  Stage2.phaseA5 r - u r

private theorem u_hasDerivAt_diag (r : ℝ) : HasDerivAt u (v r) r := by
  change HasDerivAt (fun s : ℝ => (Real.cos s, Real.sin s))
    (-Real.sin r, Real.cos r) r
  exact (Real.hasDerivAt_cos r).prodMk (Real.hasDerivAt_sin r)

private theorem diagPhaseB4_hasDerivAt (r : ℝ) :
    HasDerivAt diagPhaseB4 ((params.d1 - r / 2 - 1) • v r) r := by
  have h := (Stage2.A4_hasDerivAt_public r).fun_sub (u_hasDerivAt_diag r)
  refine h.congr_deriv ?_
  apply Prod.ext <;> simp [v] <;> ring

private theorem diagPhaseB5_hasDerivAt (r : ℝ) :
    HasDerivAt diagPhaseB5 ((-(1 / 2 : ℝ)) • v r) r := by
  have h := (Stage2.A5_hasDerivAt_public r).fun_sub (u_hasDerivAt_diag r)
  refine h.congr_deriv ?_
  apply Prod.ext <;> simp [v] <;> ring

private theorem diagPhaseB4_eq_B {r : ℝ} (hr : r ∈ Icc eta tau) :
    diagPhaseB4 r = B r := by
  rcases hr.1.eq_or_lt with h | h
  · subst r
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    have hdiag : diagPhaseB4 eta =
        Romik.path4 params eta +
          (Romik.alphaBeta4 params eta).1 • v eta := by
      apply Prod.ext <;> simp [diagPhaseB4, Stage2.phaseA4]
    have hetaRaw : eta ≤ Real.pi / 2 - params.theta := by rfl
    have hB : B eta = Romik.path3 params eta +
        (Romik.alphaBeta3 params eta).1 • v eta := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr phi_lt_eta, not_le.mpr theta_lt_eta, hetaRaw]
    calc
      diagPhaseB4 eta = Romik.path4 params eta +
          (Romik.alphaBeta4 params eta).1 • v eta := hdiag
      _ = Romik.path3 params eta +
          (Romik.alphaBeta3 params eta).1 • v eta := by
            rw [hm, alphaBeta_match34_direct]
      _ = B eta := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < r := by
      simpa [eta, T] using h
    have htauRaw : r ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using hr.2
    apply Prod.ext <;>
      simp [diagPhaseB4, Stage2.phaseA4, B, alpha, alphaBetaAt,
        Romik.path, not_le.mpr (lt_trans phi_lt_eta h),
        not_le.mpr (lt_trans theta_lt_eta h), not_le.mpr h, hr.2,
        not_le.mpr hetaRaw, htauRaw, eta, tau, T]

private theorem diagPhaseB5_eq_B {r : ℝ} (hr : r ∈ Icc tau T) :
    diagPhaseB5 r = B r := by
  rcases hr.1.eq_or_lt with h | h
  · subst r
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    have hdiag : diagPhaseB5 tau =
        Romik.path5 params tau +
          (Romik.alphaBeta5 params tau).1 • v tau := by
      apply Prod.ext <;> simp [diagPhaseB5, Stage2.phaseA5]
    have htauRaw : tau ≤ Real.pi / 2 - params.phi := by rfl
    have hetaRaw : ¬ tau ≤ Real.pi / 2 - params.theta := by
      exact not_le.mpr (by simpa [eta, T] using eta_lt_tau)
    have hB : B tau = Romik.path4 params tau +
        (Romik.alphaBeta4 params tau).1 • v tau := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr (lt_trans phi_lt_eta eta_lt_tau),
          not_le.mpr (lt_trans theta_lt_eta eta_lt_tau),
          not_le.mpr eta_lt_tau, hetaRaw, htauRaw]
    calc
      diagPhaseB5 tau = Romik.path5 params tau +
          (Romik.alphaBeta5 params tau).1 • v tau := hdiag
      _ = Romik.path4 params tau +
          (Romik.alphaBeta4 params tau).1 • v tau := by
            rw [hm, alphaBeta_match45_direct]
      _ = B tau := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < r := by
      simpa [eta, T] using lt_trans eta_lt_tau h
    have htauRaw : Real.pi / 2 - params.phi < r := by
      simpa [tau, T] using h
    apply Prod.ext <;>
      simp [diagPhaseB5, Stage2.phaseA5, B, alpha, alphaBetaAt,
        Romik.path,
        not_le.mpr (lt_trans (lt_trans phi_lt_eta eta_lt_tau) h),
        not_le.mpr (lt_trans (lt_trans theta_lt_eta eta_lt_tau) h),
        not_le.mpr (lt_trans eta_lt_tau h), not_le.mpr h,
        not_le.mpr hetaRaw, not_le.mpr htauRaw, eta, tau, T]

private theorem theta_upper_diag : params.theta ≤ (689 / 1000 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem halfT_le_eta_sub_phi : T / 2 ≤ eta - params.phi := by
  have hp : (157 / 50 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2
    norm_num at h ⊢
    exact h
  dsimp [eta, T]
  nlinarith [theta_upper_diag, phi_le_one_twentieth_diag]

private theorem d1_upper_diag : params.d1 ≤ (33 / 25 : ℝ) := by
  have h := PartB.d1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem eta_lower_diag : (4 / 5 : ℝ) ≤ eta := by
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three, theta_upper_diag]

private theorem phaseB4_coeff_nonpos_diag {r : ℝ} (hr : eta ≤ r) :
    params.d1 - r / 2 - 1 ≤ 0 := by
  nlinarith [d1_upper_diag, eta_lower_diag]

private theorem late_cos_sub_sin_nonpos {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    Real.cos (r - t) - Real.sin (r - t) ≤ 0 := by
  have hhalf : T / 2 ≤ r - t := by
    nlinarith [halfT_le_eta_sub_phi, ht.2, hr.1]
  have hdeltaT : r - t ≤ T := by linarith [hr.2, ht.1]
  have hlo : -(Real.pi / 2) ≤ T - (r - t) := by
    dsimp [T] at hdeltaT ⊢
    nlinarith [Real.pi_pos]
  have hhi : r - t ≤ Real.pi / 2 := by simpa [T] using hdeltaT
  have horder : T - (r - t) ≤ r - t := by linarith
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two hlo hhi horder
  have htrig : Real.sin (T - (r - t)) = Real.cos (r - t) := by
    change Real.sin (Real.pi / 2 - (r - t)) = Real.cos (r - t)
    exact Real.sin_pi_div_two_sub (r - t)
  rw [htrig] at hs
  linarith

private theorem dot_fixed_hasDerivAt_diag
    {f : ℝ → Point} {df w : Point} {r : ℝ}
    (h : HasDerivAt f df r) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) r := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  simpa [dot, mul_comm] using h1.fun_add h2

private theorem phaseB4_diag_monotone (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    MonotoneOn (fun r => dot (diagPhaseB4 r) (u t + v t)) (Icc eta tau) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun r => dot ((params.d1 - r / 2 - 1) • v r) (u t + v t))
    (convex_Icc eta tau) ?_ ?_ ?_
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB4_hasDerivAt r)).continuousAt.continuousWithinAt
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB4_hasDerivAt r)).hasDerivWithinAt
  · intro r hr
    have hi : r ∈ Ioo eta tau := by simpa only [interior_Icc] using hr
    have hcoef := phaseB4_coeff_nonpos_diag hi.1.le
    have htrig := late_cos_sub_sin_nonpos ht
      ⟨hi.1.le, le_trans hi.2.le tau_lt_T.le⟩
    have heq :
        dot ((params.d1 - r / 2 - 1) • v r) (u t + v t) =
          (params.d1 - r / 2 - 1) *
            (Real.cos (r - t) - Real.sin (r - t)) := by
      simp [dot, u, v, Real.cos_sub, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos hcoef htrig

private theorem phaseB5_diag_monotone (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    MonotoneOn (fun r => dot (diagPhaseB5 r) (u t + v t)) (Icc tau T) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun r => dot ((-(1 / 2 : ℝ)) • v r) (u t + v t))
    (convex_Icc tau T) ?_ ?_ ?_
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB5_hasDerivAt r)).continuousAt.continuousWithinAt
  · intro r hr
    exact (dot_fixed_hasDerivAt_diag (w := u t + v t)
      (diagPhaseB5_hasDerivAt r)).hasDerivWithinAt
  · intro r hr
    have hi : r ∈ Ioo tau T := by simpa only [interior_Icc] using hr
    have htrig := late_cos_sub_sin_nonpos ht
      ⟨le_trans eta_lt_tau.le hi.1.le, hi.2.le⟩
    have heq : dot ((-(1 / 2 : ℝ)) • v r) (u t + v t) =
        (-(1 / 2 : ℝ)) *
          (Real.cos (r - t) - Real.sin (r - t)) := by
      simp [dot, u, v, Real.cos_sub, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos (by norm_num) htrig

private theorem B_diag_mono_from_eta {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    dot (B eta) (u t + v t) ≤ dot (B r) (u t + v t) := by
  by_cases hrtau : r ≤ tau
  · have hm := phaseB4_diag_monotone t ht
    have heta : eta ∈ Icc eta tau := ⟨le_rfl, eta_lt_tau.le⟩
    have hrr : r ∈ Icc eta tau := ⟨hr.1, hrtau⟩
    have h := hm heta hrr hr.1
    change dot (diagPhaseB4 eta) (u t + v t) ≤
      dot (diagPhaseB4 r) (u t + v t) at h
    rw [diagPhaseB4_eq_B heta, diagPhaseB4_eq_B hrr] at h
    exact h
  · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
    have heta : eta ∈ Icc eta tau := ⟨le_rfl, eta_lt_tau.le⟩
    have htau4 : tau ∈ Icc eta tau := ⟨eta_lt_tau.le, le_rfl⟩
    have htau5 : tau ∈ Icc tau T := ⟨le_rfl, tau_lt_T.le⟩
    have hrr : r ∈ Icc tau T := ⟨htaur, hr.2⟩
    have h4 := phaseB4_diag_monotone t ht heta htau4 eta_lt_tau.le
    have h5 := phaseB5_diag_monotone t ht htau5 hrr htaur
    change dot (diagPhaseB4 eta) (u t + v t) ≤
      dot (diagPhaseB4 tau) (u t + v t) at h4
    change dot (diagPhaseB5 tau) (u t + v t) ≤
      dot (diagPhaseB5 r) (u t + v t) at h5
    rw [diagPhaseB4_eq_B heta, diagPhaseB4_eq_B htau4] at h4
    rw [diagPhaseB5_eq_B htau5, diagPhaseB5_eq_B hrr] at h5
    exact le_trans h4 h5

theorem B_early_diagonal_nonneg {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t + v t) := by
  have hstart := early_endpoint_diagonal_nonneg ht
  have hmono := B_diag_mono_from_eta ht hr
  rw [B_eta_eq_path_phi] at hmono
  unfold dot at hstart hmono ⊢
  dsimp at hstart hmono ⊢
  linarith

theorem B_early_boundary_outside {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t) ∨
      0 ≤ dot (B r - Romik.path params t) (v t) := by
  have hdiag := B_early_diagonal_nonneg ht hr
  by_contra h
  push_neg at h
  have hadd :
      dot (B r - Romik.path params t) (u t + v t) =
        dot (B r - Romik.path params t) (u t) +
          dot (B r - Romik.path params t) (v t) := by
    unfold dot
    dsimp [u, v]
    ring
  rw [hadd] at hdiag
  linarith

private theorem T_le_pi_diag : T ≤ Real.pi := by
  dsimp [T]
  nlinarith [Real.pi_pos]

private theorem contact_u_mono_after
    {F : ℝ → Point} {c : ℝ → ℝ} {a b t : ℝ}
    (hder : ∀ q, HasDerivAt F ((c q) • v q) q)
    (hc : ∀ q ∈ Ioo a b, c q ≤ 0)
    (ht0 : 0 ≤ t) (hta : t ≤ a) (hbT : b ≤ T) :
    MonotoneOn (fun q => dot (F q) (u t)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun q => dot ((c q) • v q) (u t))
    (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).continuousAt.continuousWithinAt
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hsin : Real.sin (t - q) ≤ 0 := by
      apply Real.sin_nonpos_of_nonpos_of_neg_pi_le
      · linarith [hta, hi.1]
      · have hqT : q ≤ T := le_trans hi.2.le hbT
        have : q - t ≤ T := by linarith
        nlinarith [T_le_pi_diag]
    have heq : dot ((c q) • v q) (u t) = c q * Real.sin (t - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg_of_nonpos_of_nonpos (hc q hi) hsin

private theorem contact_u_anti_before
    {F : ℝ → Point} {c : ℝ → ℝ} {a b t : ℝ}
    (hder : ∀ q, HasDerivAt F ((c q) • v q) q)
    (hc : ∀ q ∈ Ioo a b, c q ≤ 0)
    (ha0 : 0 ≤ a) (hbt : b ≤ t) (htT : t ≤ T) :
    AntitoneOn (fun q => dot (F q) (u t)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun q => dot ((c q) • v q) (u t))
    (convex_Icc a b) ?_ ?_ ?_
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).continuousAt.continuousWithinAt
  · intro q hq
    exact (dot_fixed_hasDerivAt_diag (w := u t) (hder q)).hasDerivWithinAt
  · intro q hq
    have hi : q ∈ Ioo a b := by simpa only [interior_Icc] using hq
    have hsin : 0 ≤ Real.sin (t - q) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · linarith [hi.2, hbt]
      · have hq0 : 0 ≤ q := le_trans ha0 hi.1.le
        have : t - q ≤ T := by linarith
        exact le_trans this T_le_pi_diag
    have heq : dot ((c q) • v q) (u t) = c q * Real.sin (t - q) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonpos_of_nonneg (hc q hi) hsin

private theorem phase4_u_mono_after {a b t : ℝ}
    (ha : eta ≤ a) (hb : b ≤ tau) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    MonotoneOn (fun q => dot (diagPhaseB4 q) (u t)) (Icc a b) := by
  exact contact_u_mono_after
    (F := diagPhaseB4) (c := fun q => params.d1 - q / 2 - 1)
    diagPhaseB4_hasDerivAt
    (by intro q hq; exact phaseB4_coeff_nonpos_diag (le_trans ha hq.1.le))
    ht0 hta (le_trans hb tau_lt_T.le)

private theorem phase4_u_anti_before {a b t : ℝ}
    (ha : eta ≤ a) (hb : b ≤ tau) (hbt : b ≤ t) (htT : t ≤ T) :
    AntitoneOn (fun q => dot (diagPhaseB4 q) (u t)) (Icc a b) := by
  exact contact_u_anti_before
    (F := diagPhaseB4) (c := fun q => params.d1 - q / 2 - 1)
    diagPhaseB4_hasDerivAt
    (by intro q hq; exact phaseB4_coeff_nonpos_diag (le_trans ha hq.1.le))
    (le_trans (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (le_trans eta_lower_diag ha)) hbt htT

private theorem phase5_u_mono_after {a b t : ℝ}
    (ha : tau ≤ a) (hb : b ≤ T) (ht0 : 0 ≤ t) (hta : t ≤ a) :
    MonotoneOn (fun q => dot (diagPhaseB5 q) (u t)) (Icc a b) := by
  exact contact_u_mono_after
    (F := diagPhaseB5) (c := fun _ => (-(1 / 2 : ℝ)))
    diagPhaseB5_hasDerivAt (by intro q hq; norm_num)
    ht0 hta hb

private theorem phase5_u_anti_before {a b t : ℝ}
    (ha : tau ≤ a) (hb : b ≤ T) (hbt : b ≤ t) (htT : t ≤ T) :
    AntitoneOn (fun q => dot (diagPhaseB5 q) (u t)) (Icc a b) := by
  exact contact_u_anti_before
    (F := diagPhaseB5) (c := fun _ => (-(1 / 2 : ℝ)))
    diagPhaseB5_hasDerivAt (by intro q hq; norm_num)
    (le_trans (by norm_num : (0 : ℝ) ≤ 4 / 5)
      (le_trans eta_lower_diag (le_trans eta_lt_tau.le ha))) hbt htT

private theorem B_u_ge_eta {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) eta) (hr : r ∈ Icc eta T) :
    dot (B eta) (u t) ≤ dot (B r) (u t) := by
  by_cases hrtau : r ≤ tau
  · have heta : eta ∈ Icc eta r := ⟨le_rfl, hr.1⟩
    have hrr : r ∈ Icc eta r := ⟨hr.1, le_rfl⟩
    have hm := phase4_u_mono_after (a := eta) (b := r) (t := t)
      le_rfl hrtau ht.1 ht.2
    have h := hm heta hrr hr.1
    change dot (diagPhaseB4 eta) (u t) ≤ dot (diagPhaseB4 r) (u t) at h
    rw [diagPhaseB4_eq_B ⟨le_rfl, eta_lt_tau.le⟩,
      diagPhaseB4_eq_B ⟨hr.1, hrtau⟩] at h
    exact h
  · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
    have heta4 : eta ∈ Icc eta tau := ⟨le_rfl, eta_lt_tau.le⟩
    have htau4 : tau ∈ Icc eta tau := ⟨eta_lt_tau.le, le_rfl⟩
    have htau5 : tau ∈ Icc tau r := ⟨le_rfl, htaur⟩
    have hrr5 : r ∈ Icc tau r := ⟨htaur, le_rfl⟩
    have h4 := (phase4_u_mono_after (a := eta) (b := tau) (t := t)
      le_rfl le_rfl ht.1 ht.2)
      heta4 htau4 eta_lt_tau.le
    have h5 := (phase5_u_mono_after (a := tau) (b := r) (t := t)
      le_rfl hr.2 ht.1 (le_trans ht.2 eta_lt_tau.le))
      htau5 hrr5 htaur
    change dot (diagPhaseB4 eta) (u t) ≤ dot (diagPhaseB4 tau) (u t) at h4
    change dot (diagPhaseB5 tau) (u t) ≤ dot (diagPhaseB5 r) (u t) at h5
    rw [diagPhaseB4_eq_B heta4, diagPhaseB4_eq_B htau4] at h4
    rw [diagPhaseB5_eq_B ⟨le_rfl, tau_lt_T.le⟩,
      diagPhaseB5_eq_B ⟨htaur, hr.2⟩] at h5
    exact le_trans h4 h5

private theorem B_u_global_min {t r : ℝ}
    (ht : t ∈ Icc eta T) (hr : r ∈ Icc eta T) :
    dot (B t) (u t) ≤ dot (B r) (u t) := by
  have ht0 : 0 ≤ t := by nlinarith [eta_lower_diag, ht.1]
  by_cases httau : t ≤ tau
  · have ht4 : t ∈ Icc eta tau := ⟨ht.1, httau⟩
    by_cases hrtau : r ≤ tau
    · have hr4 : r ∈ Icc eta tau := ⟨hr.1, hrtau⟩
      by_cases hrt : r ≤ t
      · have hrr : r ∈ Icc r t := ⟨le_rfl, hrt⟩
        have htt : t ∈ Icc r t := ⟨hrt, le_rfl⟩
        have ha := phase4_u_anti_before (a := r) (b := t) (t := t)
          hr.1 httau le_rfl ht.2
        have h := ha hrr htt hrt
        change dot (diagPhaseB4 t) (u t) ≤ dot (diagPhaseB4 r) (u t) at h
        rw [diagPhaseB4_eq_B hr4, diagPhaseB4_eq_B ht4] at h
        exact h
      · have htr : t ≤ r := le_of_lt (lt_of_not_ge hrt)
        have htt : t ∈ Icc t r := ⟨le_rfl, htr⟩
        have hrr : r ∈ Icc t r := ⟨htr, le_rfl⟩
        have hm := phase4_u_mono_after (a := t) (b := r) (t := t)
          ht.1 hrtau ht0 le_rfl
        have h := hm htt hrr htr
        change dot (diagPhaseB4 t) (u t) ≤ dot (diagPhaseB4 r) (u t) at h
        rw [diagPhaseB4_eq_B ht4, diagPhaseB4_eq_B hr4] at h
        exact h
    · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
      have htt4 : t ∈ Icc t tau := ⟨le_rfl, httau⟩
      have htau4' : tau ∈ Icc t tau := ⟨httau, le_rfl⟩
      have h4 := (phase4_u_mono_after (a := t) (b := tau) (t := t)
        ht.1 le_rfl ht0 le_rfl)
        htt4 htau4' httau
      have htau5' : tau ∈ Icc tau r := ⟨le_rfl, htaur⟩
      have hrr5 : r ∈ Icc tau r := ⟨htaur, le_rfl⟩
      have h5 := (phase5_u_mono_after (a := tau) (b := r) (t := t)
        le_rfl hr.2 ht0 httau)
        htau5' hrr5 htaur
      change dot (diagPhaseB4 t) (u t) ≤ dot (diagPhaseB4 tau) (u t) at h4
      change dot (diagPhaseB5 tau) (u t) ≤ dot (diagPhaseB5 r) (u t) at h5
      rw [diagPhaseB4_eq_B ht4,
        diagPhaseB4_eq_B ⟨eta_lt_tau.le, le_rfl⟩] at h4
      rw [diagPhaseB5_eq_B ⟨le_rfl, tau_lt_T.le⟩,
        diagPhaseB5_eq_B ⟨htaur, hr.2⟩] at h5
      exact le_trans h4 h5
  · have htaut : tau ≤ t := le_of_lt (lt_of_not_ge httau)
    have ht5 : t ∈ Icc tau T := ⟨htaut, ht.2⟩
    by_cases hrtau : r ≤ tau
    · have hr4 : r ∈ Icc eta tau := ⟨hr.1, hrtau⟩
      have hrr4 : r ∈ Icc r tau := ⟨le_rfl, hrtau⟩
      have htau4' : tau ∈ Icc r tau := ⟨hrtau, le_rfl⟩
      have h4 := (phase4_u_anti_before (a := r) (b := tau) (t := t)
        hr.1 le_rfl htaut ht.2) hrr4 htau4' hrtau
      have htau5' : tau ∈ Icc tau t := ⟨le_rfl, htaut⟩
      have htt5 : t ∈ Icc tau t := ⟨htaut, le_rfl⟩
      have h5 := (phase5_u_anti_before (a := tau) (b := t) (t := t)
        le_rfl ht.2 le_rfl ht.2) htau5' htt5 htaut
      change dot (diagPhaseB4 tau) (u t) ≤ dot (diagPhaseB4 r) (u t) at h4
      change dot (diagPhaseB5 t) (u t) ≤ dot (diagPhaseB5 tau) (u t) at h5
      rw [diagPhaseB4_eq_B hr4,
        diagPhaseB4_eq_B ⟨eta_lt_tau.le, le_rfl⟩] at h4
      rw [diagPhaseB5_eq_B ⟨le_rfl, tau_lt_T.le⟩,
        diagPhaseB5_eq_B ht5] at h5
      exact le_trans h5 h4
    · have htaur : tau ≤ r := le_of_lt (lt_of_not_ge hrtau)
      have hr5 : r ∈ Icc tau T := ⟨htaur, hr.2⟩
      by_cases hrt : r ≤ t
      · have hrr : r ∈ Icc r t := ⟨le_rfl, hrt⟩
        have htt : t ∈ Icc r t := ⟨hrt, le_rfl⟩
        have ha := phase5_u_anti_before (a := r) (b := t) (t := t)
          htaur ht.2 le_rfl ht.2
        have h := ha hrr htt hrt
        change dot (diagPhaseB5 t) (u t) ≤ dot (diagPhaseB5 r) (u t) at h
        rw [diagPhaseB5_eq_B hr5, diagPhaseB5_eq_B ht5] at h
        exact h
      · have htr : t ≤ r := le_of_lt (lt_of_not_ge hrt)
        have htt : t ∈ Icc t r := ⟨le_rfl, htr⟩
        have hrr : r ∈ Icc t r := ⟨htr, le_rfl⟩
        have hm := phase5_u_mono_after (a := t) (b := r) (t := t)
          htaut hr.2 ht0 le_rfl
        have h := hm htt hrr htr
        change dot (diagPhaseB5 t) (u t) ≤ dot (diagPhaseB5 r) (u t) at h
        rw [diagPhaseB5_eq_B ht5, diagPhaseB5_eq_B hr5] at h
        exact h

theorem B_late_u_nonneg {t r : ℝ}
    (ht : t ∈ Icc params.phi T) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t) := by
  by_cases hteta : t ≤ eta
  · have hstart := U_phi_nonneg ht
    have hmono := B_u_ge_eta
      (show t ∈ Icc (0 : ℝ) eta from ⟨le_trans phi_pos.le ht.1, hteta⟩) hr
    rw [B_eta_eq_path_phi] at hmono
    unfold Stage2.UValue at hstart
    unfold dot at hstart hmono ⊢
    dsimp at hstart hmono ⊢
    linarith
  · have heta : eta ≤ t := le_of_lt (lt_of_not_ge hteta)
    have hmin := B_u_global_min (show t ∈ Icc eta T from ⟨heta, ht.2⟩) hr
    have hcontact := B_inner_u_identity t
    unfold dot at hmin hcontact ⊢
    dsimp at hmin hcontact ⊢
    linarith

theorem B_boundary_outside {t r : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (hr : r ∈ Icc eta T) :
    0 ≤ dot (B r - Romik.path params t) (u t) ∨
      0 ≤ dot (B r - Romik.path params t) (v t) := by
  by_cases htphi : t ≤ params.phi
  · exact B_early_boundary_outside ⟨ht.1.le, htphi⟩ hr
  · exact Or.inl (B_late_u_nonneg
      ⟨le_of_lt (lt_of_not_ge htphi), ht.2.le⟩ hr)

private theorem phase1_beta_upper {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    (Romik.alphaBeta1 params s).2 ≤ (3 / 2 : ℝ) := by
  have hpi : s ≤ Real.pi := by nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hcosUpper := Real.cos_le_one s
  have hcos0 : 0 ≤ Real.cos s := by
    have hlow := Real.one_sub_sq_div_two_le_cos (x := s)
    nlinarith [hlow, sq_nonneg s, mul_nonneg hs0 (sub_nonneg.mpr hs20)]
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  have hmul : 2 * params.a1 * Real.cos s ≤ (5 / 2 : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hcosUpper
      (show 0 ≤ 2 * params.a1 by nlinarith [a1_lower_diag])
    have ha : 2 * params.a1 ≤ (5 / 2 : ℝ) := by nlinarith [a1_upper_diag]
    nlinarith
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith

private theorem path1_fst_antitone :
    AntitoneOn (fun s => (Romik.path1 params s).1)
      (Icc (0 : ℝ) params.phi) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun s => (Romik.rot s (Romik.alphaBeta1 params s)).1)
    (convex_Icc (0 : ℝ) params.phi) ?_ ?_ ?_
  · intro s hs
    have h := dot_fixed_hasDerivAt_diag (w := ((1 : ℝ), 0))
      (path1_hasDerivAt_public s)
    simpa [dot] using h.continuousAt.continuousWithinAt
  · intro s hs
    have h := dot_fixed_hasDerivAt_diag (w := ((1 : ℝ), 0))
      (path1_hasDerivAt_public s)
    simpa [dot] using h.hasDerivWithinAt
  · intro s hs
    have hi : s ∈ Ioo (0 : ℝ) params.phi := by
      simpa only [interior_Icc] using hs
    have hs20 := le_trans hi.2.le phi_le_one_twentieth_diag
    have ha := phase1_alpha_nonpos_diag hi.1.le hs20
    have hb := phase1_beta_lower hi.1.le hs20
    have hsin : 0 ≤ Real.sin s := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi hi.1.le
        (by nlinarith [Real.pi_gt_three, hs20])
    have hcos : 0 ≤ Real.cos s := by
      have hlow := Real.one_sub_sq_div_two_le_cos (x := s)
      nlinarith [hlow, sq_nonneg s,
        mul_nonneg hi.1.le (sub_nonneg.mpr hs20)]
    dsimp [Romik.rot]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg ha hcos,
      mul_nonneg (show 0 ≤ (Romik.alphaBeta1 params s).2 by linarith) hsin]

private theorem path1_snd_slope_upper :
    AntitoneOn (fun s => (Romik.path1 params s).2 - (3 / 2 : ℝ) * s)
      (Icc (0 : ℝ) params.phi) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun s => (Romik.rot s (Romik.alphaBeta1 params s)).2 - 3 / 2)
    (convex_Icc (0 : ℝ) params.phi) ?_ ?_ ?_
  · intro s hs
    have hp := dot_fixed_hasDerivAt_diag (w := ((0 : ℝ), 1))
      (path1_hasDerivAt_public s)
    have h := hp.fun_sub
      (HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_id s))
    simpa [dot] using h.continuousAt.continuousWithinAt
  · intro s hs
    have hp := dot_fixed_hasDerivAt_diag (w := ((0 : ℝ), 1))
      (path1_hasDerivAt_public s)
    have h := hp.fun_sub
      (HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_id s))
    simpa [dot] using h.hasDerivWithinAt
  · intro s hs
    have hi : s ∈ Ioo (0 : ℝ) params.phi := by
      simpa only [interior_Icc] using hs
    have hs20 := le_trans hi.2.le phi_le_one_twentieth_diag
    have ha := phase1_alpha_nonpos_diag hi.1.le hs20
    have hbLo := phase1_beta_lower hi.1.le hs20
    have hbHi := phase1_beta_upper hi.1.le hs20
    have hsin : 0 ≤ Real.sin s := by
      exact Real.sin_nonneg_of_nonneg_of_le_pi hi.1.le
        (by nlinarith [Real.pi_gt_three, hs20])
    have hcos0 : 0 ≤ Real.cos s := by
      have hlow := Real.one_sub_sq_div_two_le_cos (x := s)
      nlinarith [hlow, sq_nonneg s,
        mul_nonneg hi.1.le (sub_nonneg.mpr hs20)]
    have hcos1 := Real.cos_le_one s
    dsimp [Romik.rot]
    have haSin := mul_nonpos_of_nonpos_of_nonneg ha hsin
    have hbCos : (Romik.alphaBeta1 params s).2 * Real.cos s ≤ 3 / 2 := by
      have h1 := mul_le_mul_of_nonneg_right hbHi hcos0
      have h2 := mul_le_mul_of_nonneg_left hcos1
        (show 0 ≤ (3 / 2 : ℝ) by norm_num)
      nlinarith
    nlinarith

private theorem phase1_path_x_nonpos {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    (Romik.path params t).1 ≤ 0 := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) params.phi := ⟨le_rfl, phi_pos.le⟩
  have h := path1_fst_antitone h0 ht ht.1
  have hp0 := congrArg Prod.fst pathZero
  have hpt : Romik.path params t = Romik.path1 params t := by
    simp [Romik.path, ht.2]
  have hzero : Romik.path params 0 = Romik.path1 params 0 := by
    simp [Romik.path, phi_pos.le]
  change (Romik.path1 params t).1 ≤ (Romik.path1 params 0).1 at h
  rw [← congrArg Prod.fst hzero, ← congrArg Prod.fst hpt] at h
  simpa [hp0] using h

private theorem phase1_path_y_upper {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    (Romik.path params t).2 ≤ (3 / 40 : ℝ) := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) params.phi := ⟨le_rfl, phi_pos.le⟩
  have h := path1_snd_slope_upper h0 ht ht.1
  have hp0 := congrArg Prod.snd pathZero
  have hpt : Romik.path params t = Romik.path1 params t := by
    simp [Romik.path, ht.2]
  have hzero : Romik.path params 0 = Romik.path1 params 0 := by
    simp [Romik.path, phi_pos.le]
  change (Romik.path1 params t).2 - 3 / 2 * t ≤
    (Romik.path1 params 0).2 - 3 / 2 * 0 at h
  rw [← congrArg Prod.snd hzero, ← congrArg Prod.snd hpt] at h
  nlinarith [phi_le_one_twentieth_diag, ht.2, hp0]

private theorem B_T_x_formula : (B T).1 = params.k51 + params.e1 := by
  have hetaRaw : ¬ T ≤ Real.pi / 2 - params.theta := by
    exact not_le.mpr (by simpa [eta, T] using eta_lt_T)
  have htauRaw : ¬ T ≤ Real.pi / 2 - params.phi := by
    exact not_le.mpr (by simpa [tau, T] using tau_lt_T)
  have hpath : Romik.path params T = Romik.path5 params T := by
    simp only [Romik.path, if_neg (not_le.mpr phi_lt_T),
      if_neg (not_le.mpr theta_lt_T), if_neg hetaRaw, if_neg htauRaw]
  have halpha : alpha T = (Romik.alphaBeta5 params T).1 := by
    simp only [alpha, alphaBetaAt, if_neg (not_le.mpr phi_lt_T),
      if_neg (not_le.mpr theta_lt_T), if_neg (not_le.mpr eta_lt_T),
      if_neg (not_le.mpr tau_lt_T)]
  rw [B, hpath, halpha]
  simp [Romik.path5, Romik.alphaBeta5, Romik.rot, Romik.addK,
    u, v, T]
  ring

private theorem B_T_x_lower : (19 / 100 : ℝ) ≤ (B T).1 := by
  have hk := PartB.k51_contains.1
  have he := PartB.e1_contains.1
  rw [B_T_x_formula]
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at hk he ⊢
  linarith

theorem B_T_u_nonneg_early {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.phi) :
    0 ≤ dot (B T - Romik.path params t) (u t) := by
  have hx := phase1_path_x_nonpos ht
  have hy := phase1_path_y_upper ht
  have hBTx := B_T_x_lower
  have hBTy := B_T_y_zero
  have ht20 := le_trans ht.2 phi_le_one_twentieth_diag
  have hsin0 : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi
    ht.1 (by nlinarith [Real.pi_gt_three, ht20])
  have hsin1 := Real.sin_le ht.1
  have hcosLower : (799 / 800 : ℝ) ≤ Real.cos t := by
    have h := Real.one_sub_sq_div_two_le_cos (x := t)
    nlinarith [h, sq_nonneg t, mul_nonneg ht.1 (sub_nonneg.mpr ht20)]
  have hcos0 : 0 ≤ Real.cos t := by linarith
  have hdx : (19 / 100 : ℝ) ≤ (B T).1 - (Romik.path params t).1 := by
    linarith
  have hdxCos : (19 / 100 : ℝ) * (799 / 800) ≤
      ((B T).1 - (Romik.path params t).1) * Real.cos t := by
    have h1 := mul_le_mul_of_nonneg_right hdx hcos0
    have h2 := mul_le_mul_of_nonneg_left hcosLower
      (show 0 ≤ (19 / 100 : ℝ) by norm_num)
    exact le_trans h2 h1
  have hySin : (Romik.path params t).2 * Real.sin t ≤
      (3 / 40 : ℝ) * (1 / 20) := by
    have h1 := mul_le_mul_of_nonneg_right hy hsin0
    have h2 : (3 / 40 : ℝ) * Real.sin t ≤ (3 / 40) * (1 / 20) := by
      apply mul_le_mul_of_nonneg_left
      · exact le_trans hsin1 ht20
      · norm_num
    exact le_trans h1 h2
  unfold dot
  dsimp [u]
  rw [hBTy]
  nlinarith

theorem B_T_u_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ dot (B T - Romik.path params t) (u t) := by
  by_cases htphi : t ≤ params.phi
  · exact B_T_u_nonneg_early ⟨ht.1.le, htphi⟩
  · exact B_late_u_nonneg
      ⟨le_of_lt (lt_of_not_ge htphi), ht.2.le⟩
      ⟨eta_lt_T.le, le_rfl⟩

/-! ## Exact reflected forms

Only the early half of the coefficient reflection is needed here.  Its image
under `r ↦ T-r` is exactly the late `B` interval.  Keeping the endpoint cases
explicit avoids relying on definitional reduction across the four switching
equalities of `alphaBetaAt`.
-/

private theorem alpha_reflect_beta_early {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta) :
    alpha (T - r) = -beta r := by
  by_cases hrphi : r < params.phi
  · have hsphi : ¬ T - r ≤ params.phi := by
      have hphiTau := lt_trans phi_lt_eta eta_lt_tau
      exact not_le.mpr (by
        dsimp [T, tau] at hphiTau ⊢
        nlinarith [hrphi])
    have hstheta : ¬ T - r ≤ params.theta := by
      exact not_le.mpr (lt_trans theta_lt_tau (by dsimp [tau]; linarith))
    have hseta : ¬ T - r ≤ eta := by
      exact not_le.mpr (by dsimp [eta]; linarith [hrphi, phi_lt_theta])
    have hstau : ¬ T - r ≤ tau := by
      exact not_le.mpr (by dsimp [tau]; linarith)
    have href := congrArg Prod.fst (alphaBeta5_reflect1_direct r)
    simpa [alpha, beta, alphaBetaAt, noHiddenReflAB, hrphi.le,
      hsphi, hstheta, hseta, hstau] using href
  · have hphir : params.phi ≤ r := le_of_not_gt hrphi
    by_cases hre : r = params.phi
    · subst r
      have href := congrArg Prod.fst
        (alphaBeta4_reflect2_direct params.phi)
      have hmatch := congrArg Prod.snd alphaBeta_match12_direct
      have hTphi : T - params.phi = tau := by
        rfl
      rw [hTphi] at href
      rw [hTphi]
      simp only [alpha, beta, alphaBetaAt,
        if_pos le_rfl,
        if_neg (not_le.mpr (lt_trans phi_lt_eta eta_lt_tau)),
        if_neg (not_le.mpr theta_lt_tau),
        if_neg (not_le.mpr eta_lt_tau),
        if_pos le_rfl]
      dsimp [noHiddenReflAB] at href
      rw [hmatch]
      exact href
    · have hphir' : params.phi < r := lt_of_le_of_ne hphir (Ne.symm hre)
      by_cases hretheta : r = params.theta
      · subst r
        have href := congrArg Prod.fst
          (alphaBeta3_reflect_direct params.theta)
        have hmatch := congrArg Prod.snd alphaBeta_match23_direct
        simp only [alpha, beta, alphaBetaAt,
          if_neg (not_le.mpr phi_lt_theta), if_pos le_rfl,
          show T - params.theta = eta by rfl,
          if_neg (not_le.mpr phi_lt_eta),
          if_neg (not_le.mpr theta_lt_eta), if_pos le_rfl]
        dsimp [eta] at href ⊢
        dsimp [noHiddenReflAB] at href
        rw [hmatch]
        exact href
      · have hrtheta : r < params.theta :=
          lt_of_le_of_ne hr.2 hretheta
        have hsphi : ¬ T - r ≤ params.phi := by
          have hthetaTau := theta_lt_tau
          exact not_le.mpr (by
            dsimp [T, tau] at hthetaTau ⊢
            linarith [hrtheta])
        have hstheta : ¬ T - r ≤ params.theta := by
          have hthetaEta := theta_lt_eta
          exact not_le.mpr (by
            dsimp [T, eta] at hthetaEta ⊢
            linarith [hrtheta])
        have hseta : ¬ T - r ≤ eta := by
          exact not_le.mpr (by dsimp [eta]; linarith)
        have hstau : T - r ≤ tau := by
          dsimp [tau]
          linarith
        have href := congrArg Prod.fst (alphaBeta4_reflect2_direct r)
        simpa [alpha, beta, alphaBetaAt, noHiddenReflAB,
          not_le.mpr hphir', hrtheta.le,
          hsphi, hstheta, hseta, hstau] using href

/-- The late `B` contact arc is the exact horizontal reflection of the early
`D` contact arc. -/
theorem B_reflect_D {r : ℝ} (hr : r ∈ Icc (0 : ℝ) params.theta) :
    B (T - r) = noHiddenHReflect (D r) := by
  have hp := path_reflect_noHidden
    (show r ∈ Icc (0 : ℝ) T from
      ⟨hr.1, le_trans hr.2 theta_lt_T.le⟩)
  have ha := alpha_reflect_beta_early hr
  rw [B, D, hp, ha]
  apply Prod.ext
  · dsimp [noHiddenHReflect, u, v, T]
    rw [Real.sin_pi_div_two_sub]
    ring
  · dsimp [noHiddenHReflect, u, v, T]
    rw [Real.cos_pi_div_two_sub]
    ring

private theorem B_reflect_u_dot_eq_D_v {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta)
    (ht : t ∈ Icc (0 : ℝ) T) :
    dot (B (T - r) - Romik.path params (T - t)) (u (T - t)) =
      dot (D r - Romik.path params t) (v t) := by
  rw [B_reflect_D hr, path_reflect_noHidden ht]
  dsimp [dot, noHiddenHReflect, u, v, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

private theorem B_reflect_v_dot_eq_D_u {r t : ℝ}
    (hr : r ∈ Icc (0 : ℝ) params.theta)
    (ht : t ∈ Icc (0 : ℝ) T) :
    dot (B (T - r) - Romik.path params (T - t)) (v (T - t)) =
      dot (D r - Romik.path params t) (u t) := by
  rw [B_reflect_D hr, path_reflect_noHidden ht]
  dsimp [dot, noHiddenHReflect, u, v, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

/-- Every point of the early `D` contact arc lies outside at least one of the
two moving inner walls. -/
theorem D_boundary_outside {t r : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hr : r ∈ Icc (0 : ℝ) params.theta) :
    0 ≤ dot (D r - Romik.path params t) (u t) ∨
      0 ≤ dot (D r - Romik.path params t) (v t) := by
  have htRef : T - t ∈ Ioo (0 : ℝ) T := by
    have ht0 := ht.1
    have htT := ht.2
    constructor <;> dsimp [T] at ht0 htT ⊢ <;> linarith
  have hrRef : T - r ∈ Icc eta T := by
    constructor
    · dsimp [eta]
      linarith [hr.2]
    · linarith [hr.1]
  have htClosed : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  rcases B_boundary_outside htRef hrRef with hu | hv
  · right
    rw [B_reflect_u_dot_eq_D_v hr htClosed] at hu
    exact hu
  · left
    rw [B_reflect_v_dot_eq_D_u hr htClosed] at hv
    exact hv

/-- Reflected endpoint separator used for the strict lower horizontal range of
the niche. -/
theorem D_zero_v_nonneg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 ≤ dot (D 0 - Romik.path params t) (v t) := by
  have htRef : T - t ∈ Ioo (0 : ℝ) T := by
    have ht0 := ht.1
    have htT := ht.2
    constructor <;> dsimp [T] at ht0 htT ⊢ <;> linarith
  have h := B_T_u_nonneg htRef
  have htransport := B_reflect_u_dot_eq_D_v
    (t := t) (r := 0)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) params.theta from
      ⟨le_rfl, theta_pos.le⟩)
    (show t ∈ Icc (0 : ℝ) T from ⟨ht.1.le, ht.2.le⟩)
  have htransport' :
      dot (B T - Romik.path params (T - t)) (u (T - t)) =
        dot (D 0 - Romik.path params t) (v t) := by
    simpa using htransport
  rw [htransport'] at h
  exact h

end Stage4
end PartC
end GerverSofa
