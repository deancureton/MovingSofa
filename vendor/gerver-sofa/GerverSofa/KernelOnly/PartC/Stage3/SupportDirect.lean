import GerverSofa.KernelOnly.PartC.Stage2.SupportPhaseDerivatives
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Direct outer-support closure for Part C

This proof uses the five source-clean phase derivative identities and glues
monotonicity across the four certified switching times.  It does not require a
globally differentiable contact parametrisation at the speed-change junctions.
-/

noncomputable section

open Set

namespace GerverSofa
namespace PartC
namespace Stage3

open Stage2

private theorem T_nonneg : (0 : ℝ) ≤ T := by
  dsimp [T]
  positivity

private theorem T_le_pi : T ≤ Real.pi := by
  dsimp [T]
  nlinarith [Real.pi_pos]

private theorem cos_nonneg_physical {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) T) (hy : y ∈ Icc (0 : ℝ) T) :
    0 ≤ Real.cos (x - y) := by
  rcases hx with ⟨hx0, hxT⟩
  rcases hy with ⟨hy0, hyT⟩
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · dsimp [T] at hxT hyT ⊢
    linarith
  · dsimp [T] at hxT hyT ⊢
    linarith

private theorem sin_nonneg_diff {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) T) (hy : y ∈ Icc (0 : ℝ) T) (hxy : x ≤ y) :
    0 ≤ Real.sin (y - x) := by
  rcases hx with ⟨hx0, hxT⟩
  rcases hy with ⟨hy0, hyT⟩
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · linarith
  · have hT : y - x ≤ T := by linarith
    exact le_trans hT T_le_pi

private theorem dot_hasDerivAt_fixed {f : ℝ → Point} {df : Point} {t : ℝ}
    (h : HasDerivAt f df t) (w : Point) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) t := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  have hs := h1.fun_add h2
  simpa [dot, mul_comm] using hs

private theorem glue_mono {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : MonotoneOn f (Icc a b)) (h2 : MonotoneOn f (Icc b c)) :
    MonotoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y ≤ b
  · exact h1 ⟨hx.1, le_trans hxy hyb⟩ ⟨hy.1, hyb⟩ hxy
  by_cases hbx : b ≤ x
  · exact h2 ⟨hbx, le_trans hxy hy.2⟩ ⟨le_trans hbx hxy, hy.2⟩ hxy
  · have hxb : x ≤ b := le_of_not_ge hbx
    have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
    exact le_trans
      (h1 ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb)
      (h2 ⟨le_rfl, hbc⟩ ⟨hby, hy.2⟩ hby)

private theorem glue_anti {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (h1 : AntitoneOn f (Icc a b)) (h2 : AntitoneOn f (Icc b c)) :
    AntitoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y ≤ b
  · exact h1 ⟨hx.1, le_trans hxy hyb⟩ ⟨hy.1, hyb⟩ hxy
  by_cases hbx : b ≤ x
  · exact h2 ⟨hbx, le_trans hxy hy.2⟩ ⟨le_trans hbx hxy, hy.2⟩ hxy
  · have hxb : x ≤ b := le_of_not_ge hbx
    have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
    exact le_trans
      (h2 ⟨le_rfl, hbc⟩ ⟨hby, hy.2⟩ hby)
      (h1 ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb)

private theorem restrict_mono {f : ℝ → ℝ} {a b c d : ℝ}
    (h : MonotoneOn f (Icc a b)) (hac : a ≤ c) (hdb : d ≤ b) :
    MonotoneOn f (Icc c d) := by
  intro x hx y hy hxy
  exact h ⟨le_trans hac hx.1, le_trans hx.2 hdb⟩
    ⟨le_trans hac hy.1, le_trans hy.2 hdb⟩ hxy

private def a1c (_t : ℝ) : ℝ := 0
private def a2c (t : ℝ) : ℝ := -(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2
private def a3c (t : ℝ) : ℝ := 1 + params.c1 - t
private def a4c (t : ℝ) : ℝ := params.d1 - t / 2
private def a5c (_t : ℝ) : ℝ := 1 / 2

private def c1c (_t : ℝ) : ℝ := 1 / 2
private def c2c (t : ℝ) : ℝ := t / 2 - params.b1
private def c3c (t : ℝ) : ℝ := 1 + params.c2 + t
private def c4c (t : ℝ) : ℝ := -(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2
private def c5c (_t : ℝ) : ℝ := 0

private theorem a1_nonneg (t : ℝ) : 0 ≤ a1c t := by simp [a1c]
private theorem a2_nonneg {t : ℝ} (ht : t ∈ Ioo params.phi params.theta) : 0 ≤ a2c t := by
  have hp : t ∈ Icc (0 : ℝ) T := by
    exact ⟨le_trans phi_nonneg (le_of_lt ht.1),
      le_trans (le_of_lt ht.2) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))⟩
  have h := rhoA_nonneg hp
  simpa [rhoA, a2c, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem a3_nonneg {t : ℝ} (ht : t ∈ Ioo params.theta eta) : 0 ≤ a3c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans zero_le_theta (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) (le_trans eta_le_tau tau_le_T)⟩
  have h := rhoA_nonneg hp
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta ht.1
  simpa [rhoA, a3c, not_le.mpr hphi, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem a4_nonneg {t : ℝ} (ht : t ∈ Ioo eta tau) : 0 ≤ a4c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans (le_trans zero_le_theta theta_le_eta) (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) tau_le_T⟩
  have h := rhoA_nonneg hp
  have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta ht.1
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
  simpa [rhoA, a4c, not_le.mpr hphi, not_le.mpr htheta, not_le.mpr ht.1,
    le_of_lt ht.2] using h
private theorem a5_nonneg (t : ℝ) : 0 ≤ a5c t := by norm_num [a5c]

private theorem c1_nonneg (t : ℝ) : 0 ≤ c1c t := by norm_num [c1c]
private theorem c2_nonneg {t : ℝ} (ht : t ∈ Ioo params.phi params.theta) : 0 ≤ c2c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans phi_nonneg (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))⟩
  have h := rhoC_nonneg hp
  simpa [rhoC, c2c, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem c3_nonneg {t : ℝ} (ht : t ∈ Ioo params.theta eta) : 0 ≤ c3c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans zero_le_theta (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) (le_trans eta_le_tau tau_le_T)⟩
  have h := rhoC_nonneg hp
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta ht.1
  simpa [rhoC, c3c, not_le.mpr hphi, not_le.mpr ht.1, le_of_lt ht.2] using h
private theorem c4_nonneg {t : ℝ} (ht : t ∈ Ioo eta tau) : 0 ≤ c4c t := by
  have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans (le_trans zero_le_theta theta_le_eta) (le_of_lt ht.1),
    le_trans (le_of_lt ht.2) tau_le_T⟩
  have h := rhoC_nonneg hp
  have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta ht.1
  have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
  simpa [rhoC, c4c, not_le.mpr hphi, not_le.mpr htheta, not_le.mpr ht.1,
    le_of_lt ht.2] using h
private theorem c5_nonneg (t : ℝ) : 0 ≤ c5c t := by simp [c5c]

private theorem rot_dot_u (t : ℝ) (z : Point) : dot (Romik.rot t z) (u t) = z.1 := by
  dsimp [dot, Romik.rot, u]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * Real.cos t +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.sin t
        = z.1 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.1 := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem rot_dot_v (t : ℝ) (z : Point) : dot (Romik.rot t z) (v t) = z.2 := by
  dsimp [dot, Romik.rot, v]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * (-Real.sin t) +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.cos t
        = z.2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.2 := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem rot_injective (t : ℝ) : Function.Injective (Romik.rot t) := by
  intro x y h
  have hu := congrArg (fun z => dot z (u t)) h
  have hv := congrArg (fun z => dot z (v t)) h
  rw [rot_dot_u, rot_dot_u] at hu
  rw [rot_dot_v, rot_dot_v] at hv
  exact Prod.ext hu hv

private theorem pathPrime1_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime1 p t = Romik.rot t (Romik.alphaBeta1 p t) := rfl
private theorem pathPrime2_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime2 p t = Romik.rot t (Romik.alphaBeta2 p t) := rfl
private theorem pathPrime3_eq_rot (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime3 p t = Romik.rot t (Romik.alphaBeta3 p t) := rfl

private theorem matchPrime12 : Romik.pathPrime1 params params.phi = Romik.pathPrime2 params params.phi := by
  have h10 := congrFun params_equations (10 : Fin 22)
  have h11 := congrFun params_equations (11 : Fin 22)
  simp [Romik.Equations, Romik.system] at h10 h11
  apply Prod.ext <;> linarith
private theorem matchPrime23 : Romik.pathPrime2 params params.theta = Romik.pathPrime3 params params.theta := by
  have h14 := congrFun params_equations (14 : Fin 22)
  have h15 := congrFun params_equations (15 : Fin 22)
  simp [Romik.Equations, Romik.system] at h14 h15
  apply Prod.ext <;> linarith
private theorem matchAB12 : Romik.alphaBeta1 params params.phi = Romik.alphaBeta2 params params.phi := by
  apply rot_injective params.phi
  simpa [pathPrime1_eq_rot, pathPrime2_eq_rot] using matchPrime12
private theorem matchAB23 : Romik.alphaBeta2 params params.theta = Romik.alphaBeta3 params params.theta := by
  apply rot_injective params.theta
  simpa [pathPrime2_eq_rot, pathPrime3_eq_rot] using matchPrime23

private def reflAB (z : Point) : Point := (-z.2, -z.1)
private theorem ab4_reflect_ab2 (t : ℝ) : Romik.alphaBeta4 params (T - t) = reflAB (Romik.alphaBeta2 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta4, Romik.alphaBeta2]
  rw [Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations]
  ring
private theorem ab3_reflect (t : ℝ) : Romik.alphaBeta3 params (T - t) = reflAB (Romik.alphaBeta3 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta3]
  rw [Romik.c2_eq_c1_sub_halfPi_of_equations params_equations]
  ring
private theorem ab5_reflect_ab1 (t : ℝ) : Romik.alphaBeta5 params (T - t) = reflAB (Romik.alphaBeta1 params t) := by
  dsimp [T, reflAB, Romik.alphaBeta5, Romik.alphaBeta1]
  rw [Romik.e1_eq_a1_of_equations params_equations,
      Romik.e2_eq_neg_a2_of_equations params_equations]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring
private theorem matchAB34 : Romik.alphaBeta3 params eta = Romik.alphaBeta4 params eta := by
  have h3 := ab3_reflect params.theta
  have h4 := ab4_reflect_ab2 params.theta
  have hm := congrArg reflAB matchAB23
  simpa [eta] using h3.trans (hm.symm.trans h4.symm)
private theorem matchAB45 : Romik.alphaBeta4 params tau = Romik.alphaBeta5 params tau := by
  have h4 := ab4_reflect_ab2 params.phi
  have h5 := ab5_reflect_ab1 params.phi
  have hm := congrArg reflAB matchAB12
  simpa [tau] using h4.trans (hm.symm.trans h5.symm)

private theorem A_eq_phase1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.phi) : A t = phaseA1 t := by
  apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA1, ht.2]

private theorem A_eq_phase2 {t : ℝ} (ht : t ∈ Icc params.phi params.theta) : A t = phaseA2 t := by
  by_cases h : t = params.phi
  · subst t
    calc
      A params.phi = phaseA1 params.phi := A_eq_phase1 ⟨phi_nonneg, le_rfl⟩
      _ = phaseA2 params.phi := by
        unfold phaseA1 phaseA2
        rw [PartB.match12, matchAB12]
  · have hp : params.phi < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA2, not_le.mpr hp, ht.2]

private theorem A_eq_phase3 {t : ℝ} (ht : t ∈ Icc params.theta eta) : A t = phaseA3 t := by
  by_cases h : t = params.theta
  · subst t
    calc
      A params.theta = phaseA2 params.theta := A_eq_phase2 ⟨switchOrder.phi_le_theta, le_rfl⟩
      _ = phaseA3 params.theta := by
        unfold phaseA2 phaseA3
        rw [PartB.match23, matchAB23]
  · have htheta : params.theta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : t ≤ Real.pi / 2 - params.theta := by
      simpa [eta, T] using ht.2
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA3, not_le.mpr hphi,
      not_le.mpr htheta, hηraw, ht.2, eta, T]

private theorem A_eq_phase4 {t : ℝ} (ht : t ∈ Icc eta tau) : A t = phaseA4 t := by
  by_cases h : t = eta
  · subst t
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    calc
      A eta = phaseA3 eta := A_eq_phase3 ⟨theta_le_eta, le_rfl⟩
      _ = phaseA4 eta := by
        unfold phaseA3 phaseA4
        rw [hm, matchAB34]
  · have he : eta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta he
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using he
    have hτraw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA4, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, hτraw, not_le.mpr he, ht.2, eta, tau, T]

private theorem A_eq_phase5 {t : ℝ} (ht : t ∈ Icc tau T) : A t = phaseA5 t := by
  by_cases h : t = tau
  · subst t
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    calc
      A tau = phaseA4 tau := A_eq_phase4 ⟨eta_le_tau, le_rfl⟩
      _ = phaseA5 tau := by
        unfold phaseA4 phaseA5
        rw [hm, matchAB45]
  · have htau : tau < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have heta : eta < t := lt_of_le_of_lt eta_le_tau htau
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta heta
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using heta
    have hτraw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using htau
    apply Prod.ext <;> simp [A, alpha, alphaBetaAt, Romik.path, phaseA5, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, not_le.mpr hτraw, not_le.mpr heta, not_le.mpr htau, eta, tau, T]

private theorem C_eq_phase1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.phi) : C t = phaseC1 t := by
  apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC1, ht.2]

private theorem C_eq_phase2 {t : ℝ} (ht : t ∈ Icc params.phi params.theta) : C t = phaseC2 t := by
  by_cases h : t = params.phi
  · subst t
    calc
      C params.phi = phaseC1 params.phi := C_eq_phase1 ⟨phi_nonneg, le_rfl⟩
      _ = phaseC2 params.phi := by
        unfold phaseC1 phaseC2
        rw [PartB.match12, matchAB12]
  · have hp : params.phi < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC2, not_le.mpr hp, ht.2]

private theorem C_eq_phase3 {t : ℝ} (ht : t ∈ Icc params.theta eta) : C t = phaseC3 t := by
  by_cases h : t = params.theta
  · subst t
    calc
      C params.theta = phaseC2 params.theta := C_eq_phase2 ⟨switchOrder.phi_le_theta, le_rfl⟩
      _ = phaseC3 params.theta := by
        unfold phaseC2 phaseC3
        rw [PartB.match23, matchAB23]
  · have htheta : params.theta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : t ≤ Real.pi / 2 - params.theta := by
      simpa [eta, T] using ht.2
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC3, not_le.mpr hphi,
      not_le.mpr htheta, hηraw, ht.2, eta, T]

private theorem C_eq_phase4 {t : ℝ} (ht : t ∈ Icc eta tau) : C t = phaseC4 t := by
  by_cases h : t = eta
  · subst t
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    calc
      C eta = phaseC3 eta := C_eq_phase3 ⟨theta_le_eta, le_rfl⟩
      _ = phaseC4 eta := by
        unfold phaseC3 phaseC4
        rw [hm, matchAB34]
  · have he : eta < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta he
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using he
    have hτraw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC4, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, hτraw, not_le.mpr he, ht.2, eta, tau, T]

private theorem C_eq_phase5 {t : ℝ} (ht : t ∈ Icc tau T) : C t = phaseC5 t := by
  by_cases h : t = tau
  · subst t
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    calc
      C tau = phaseC4 tau := C_eq_phase4 ⟨eta_le_tau, le_rfl⟩
      _ = phaseC5 tau := by
        unfold phaseC4 phaseC5
        rw [hm, matchAB45]
  · have htau : tau < t := lt_of_le_of_ne ht.1 (Ne.symm h)
    have heta : eta < t := lt_of_le_of_lt eta_le_tau htau
    have htheta : params.theta < t := lt_of_le_of_lt theta_le_eta heta
    have hphi : params.phi < t := lt_of_le_of_lt switchOrder.phi_le_theta htheta
    have hηraw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using heta
    have hτraw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using htau
    apply Prod.ext <;> simp [C, beta, alphaBetaAt, Romik.path, phaseC5, not_le.mpr hphi,
      not_le.mpr htheta, not_le.mpr hηraw, not_le.mpr hτraw, not_le.mpr heta, not_le.mpr htau, eta, tau, T]

private theorem C5_hasDerivAt_coeff (t : ℝ) :
    HasDerivAt phaseC5 ((-(c5c t)) • u t) t := by
  simpa [c5c] using C5_hasDerivAt_public t

private theorem transfer_mono_A {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, A t = F t)
    (hm : MonotoneOn (fun t => dot (F t) w) (Icc a b)) :
    MonotoneOn (fun t => dot (A t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy
private theorem transfer_anti_A {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, A t = F t)
    (hm : AntitoneOn (fun t => dot (F t) w) (Icc a b)) :
    AntitoneOn (fun t => dot (A t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy
private theorem transfer_mono_C {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, C t = F t)
    (hm : MonotoneOn (fun t => dot (F t) w) (Icc a b)) :
    MonotoneOn (fun t => dot (C t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy
private theorem transfer_anti_C {F : ℝ → Point} {a b : ℝ} {w : Point}
    (heq : ∀ t ∈ Icc a b, C t = F t)
    (hm : AntitoneOn (fun t => dot (F t) w) (Icc a b)) :
    AntitoneOn (fun t => dot (C t) w) (Icc a b) := by
  intro x hx y hy hxy
  simpa [heq x hx, heq y hy] using hm hx hy hxy

private theorem phase_A_own_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbs : b ≤ s) (hsT : s ≤ T) :
    MonotoneOn (fun t => dot (F t) (u s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => dot ((r t) • v t) (u s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have hsin := sin_nonneg_diff ⟨ht0, le_trans (le_of_lt hi.2) (le_trans hbs hsT)⟩
      ⟨le_trans ht0 (le_trans (le_of_lt hi.2) hbs), hsT⟩ (le_trans (le_of_lt hi.2) hbs)
    have heq : dot ((r t) • v t) (u s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg hrt hsin

private theorem phase_A_own_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) (hbT : b ≤ T) :
    AntitoneOn (fun t => dot (F t) (u s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => dot ((r t) • v t) (u s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have htT : t ≤ T := le_trans (le_of_lt hi.2) hbT
    have hsin0 : Real.sin (s - t) ≤ 0 := by
      have hnon : s - t ≤ 0 := by linarith [hsa, hi.1]
      have hnegpi : -Real.pi ≤ s - t := by
        have : t - s ≤ T := by linarith
        nlinarith [T_le_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hnon hnegpi
    have heq : dot ((r t) • v t) (u s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos hrt hsin0

private theorem phase_C_own_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbs : b ≤ s) (hsT : s ≤ T) :
    MonotoneOn (fun t => dot (F t) (v s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => dot ((-(r t)) • u t) (v s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have hsin := sin_nonneg_diff ⟨ht0, le_trans (le_of_lt hi.2) (le_trans hbs hsT)⟩
      ⟨le_trans ht0 (le_trans (le_of_lt hi.2) hbs), hsT⟩ (le_trans (le_of_lt hi.2) hbs)
    have heq : dot ((-(r t)) • u t) (v s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonneg hrt hsin

private theorem phase_C_own_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (hs0 : 0 ≤ s) (hsa : s ≤ a) (hbT : b ≤ T) :
    AntitoneOn (fun t => dot (F t) (v s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => dot ((-(r t)) • u t) (v s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hrt := hr t hi
    have hsin0 : Real.sin (s - t) ≤ 0 := by
      have hnon : s - t ≤ 0 := by linarith [hsa, hi.1]
      have hnegpi : -Real.pi ≤ s - t := by
        have : t - s ≤ T := by linarith [hbT, hi.2, hs0]
        nlinarith [T_le_pi]
      exact Real.sin_nonpos_of_nonpos_of_neg_pi_le hnon hnegpi
    have heq : dot ((-(r t)) • u t) (v s) = r t * Real.sin (s - t) := by
      simp [dot, u, v, Real.sin_sub]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos hrt hsin0

private theorem phase_A_cross_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (F t) (v s)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => dot ((r t) • v t) (v s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (v s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans ha0 (le_of_lt hi.1), le_trans (le_of_lt hi.2) hbT⟩
    have hc := cos_nonneg_physical hp hs
    have heq : dot ((r t) • v t) (v s) = r t * Real.cos (t - s) := by
      simp [dot, v, Real.cos_sub]
      ring
    rw [heq]
    exact mul_nonneg (hr t hi) hc

private theorem phase_C_cross_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b s : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (F t) (u s)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => dot ((-(r t)) • u t) (u s))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).continuousAt.continuousWithinAt
  · intro t ht; exact (dot_hasDerivAt_fixed (hder t) (u s)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have hp : t ∈ Icc (0 : ℝ) T := ⟨le_trans ha0 (le_of_lt hi.1), le_trans (le_of_lt hi.2) hbT⟩
    have hc := cos_nonneg_physical hp hs
    have heq : dot ((-(r t)) • u t) (u s) = -(r t * Real.cos (t - s)) := by
      simp [dot, u, Real.cos_sub]
      ring
    rw [heq]
    exact neg_nonpos.mpr (mul_nonneg (hr t hi) hc)

private theorem phase_A_y_mono {F : ℝ → Point} {r : ℝ → ℝ} {a b : ℝ}
    (hder : ∀ t, HasDerivAt F ((r t) • v t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    MonotoneOn (fun t => dot (F t) (0, 1)) (Icc a b) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun t => dot ((r t) • v t) (0, 1))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have htT : t ≤ T := le_trans (le_of_lt hi.2) hbT
    have hc : 0 ≤ Real.cos t := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · nlinarith [Real.pi_pos, ht0]
      · simpa [T] using htT
    have heq : dot ((r t) • v t) (0, 1) = r t * Real.cos t := by
      simp [dot, v]
    rw [heq]
    exact mul_nonneg (hr t hi) hc

private theorem phase_C_y_anti {F : ℝ → Point} {r : ℝ → ℝ} {a b : ℝ}
    (hder : ∀ t, HasDerivAt F ((-(r t)) • u t) t)
    (hr : ∀ t ∈ Ioo a b, 0 ≤ r t)
    (ha0 : 0 ≤ a) (hbT : b ≤ T) :
    AntitoneOn (fun t => dot (F t) (0, 1)) (Icc a b) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => dot ((-(r t)) • u t) (0, 1))
    (convex_Icc a b) ?_ ?_ ?_
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).continuousAt.continuousWithinAt
  · intro t ht
    exact (dot_hasDerivAt_fixed (hder t) (0, 1)).hasDerivWithinAt
  · intro t ht
    have hi : t ∈ Ioo a b := by simpa only [interior_Icc] using ht
    have ht0 : 0 ≤ t := le_trans ha0 (le_of_lt hi.1)
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht0
        (le_trans (le_trans (le_of_lt hi.2) hbT) T_le_pi)
    have heq : dot ((-(r t)) • u t) (0, 1) = -(r t * Real.sin t) := by
      simp [dot, u]
    rw [heq]
    exact neg_nonpos.mpr (mul_nonneg (hr t hi) hsin)

-- Full physical-phase monotonicities for cross supports and vertical coordinates.
private theorem A_v_global_mono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (A t) (v s)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase1 ht)
    (phase_A_cross_mono (r:=a1c) A1_hasDerivAt_public (fun t ht => a1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))) hs)
  have h2 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase2 ht)
    (phase_A_cross_mono (r:=a2c) A2_hasDerivAt_public (fun t ht => a2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)) hs)
  have h3 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase3 ht)
    (phase_A_cross_mono (r:=a3c) A3_hasDerivAt_public (fun t ht => a3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T) hs)
  have h4 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase4 ht)
    (phase_A_cross_mono (r:=a4c) A4_hasDerivAt_public (fun t ht => a4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T hs)
  have h5 := transfer_mono_A (w:=v s) (fun t ht => A_eq_phase5 ht)
    (phase_A_cross_mono (r:=a5c) A5_hasDerivAt_public (fun t ht => a5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl) hs)
  have h12 := glue_mono phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_mono zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_mono
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem C_u_global_anti (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (C t) (u s)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase1 ht)
    (phase_C_cross_anti (r:=c1c) C1_hasDerivAt_public (fun t ht => c1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))) hs)
  have h2 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase2 ht)
    (phase_C_cross_anti (r:=c2c) C2_hasDerivAt_public (fun t ht => c2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)) hs)
  have h3 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase3 ht)
    (phase_C_cross_anti (r:=c3c) C3_hasDerivAt_public (fun t ht => c3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T) hs)
  have h4 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase4 ht)
    (phase_C_cross_anti (r:=c4c) C4_hasDerivAt_public (fun t ht => c4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T hs)
  have h5 := transfer_anti_C (w:=u s) (fun t ht => C_eq_phase5 ht)
    (phase_C_cross_anti (r:=c5c) C5_hasDerivAt_coeff (fun t ht => c5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl) hs)
  have h12 := glue_anti phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_anti zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_anti (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_anti
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem A_y_global_mono :
    MonotoneOn (fun t => dot (A t) (0, 1)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase1 ht)
    (phase_A_y_mono (r:=a1c) A1_hasDerivAt_public (fun t ht => a1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))))
  have h2 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase2 ht)
    (phase_A_y_mono (r:=a2c) A2_hasDerivAt_public (fun t ht => a2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
  have h3 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase3 ht)
    (phase_A_y_mono (r:=a3c) A3_hasDerivAt_public (fun t ht => a3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T))
  have h4 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase4 ht)
    (phase_A_y_mono (r:=a4c) A4_hasDerivAt_public (fun t ht => a4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T)
  have h5 := transfer_mono_A (w:=(0,1)) (fun t ht => A_eq_phase5 ht)
    (phase_A_y_mono (r:=a5c) A5_hasDerivAt_public (fun t ht => a5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl))
  have h12 := glue_mono phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_mono zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_mono
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem C_y_global_anti :
    AntitoneOn (fun t => dot (C t) (0, 1)) (Icc (0 : ℝ) T) := by
  have h1 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase1 ht)
    (phase_C_y_anti (r:=c1c) C1_hasDerivAt_public (fun t ht => c1_nonneg t)
      (by rfl) (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))))
  have h2 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase2 ht)
    (phase_C_y_anti (r:=c2c) C2_hasDerivAt_public (fun t ht => c2_nonneg ht)
      phi_nonneg (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
  have h3 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase3 ht)
    (phase_C_y_anti (r:=c3c) C3_hasDerivAt_public (fun t ht => c3_nonneg ht)
      zero_le_theta (le_trans eta_le_tau tau_le_T))
  have h4 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase4 ht)
    (phase_C_y_anti (r:=c4c) C4_hasDerivAt_public (fun t ht => c4_nonneg ht)
      (le_trans zero_le_theta theta_le_eta) tau_le_T)
  have h5 := transfer_anti_C (w:=(0,1)) (fun t ht => C_eq_phase5 ht)
    (phase_C_y_anti (r:=c5c) C5_hasDerivAt_coeff (fun t ht => c5_nonneg t)
      (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) (by rfl))
  have h12 := glue_anti phi_nonneg switchOrder.phi_le_theta h1 h2
  have h123 := glue_anti zero_le_theta theta_le_eta h12 h3
  have h1234 := glue_anti (le_trans zero_le_theta theta_le_eta) eta_le_tau h123 h4
  exact glue_anti
    (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) tau_le_T h1234 h5

private theorem A_u_left_mono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) s) := by
  by_cases h1 : s ≤ params.phi
  · apply transfer_mono_A (w := u s)
    · intro t ht
      exact A_eq_phase1 ⟨ht.1, le_trans ht.2 h1⟩
    · exact phase_A_own_mono (r := a1c) A1_hasDerivAt_public
        (fun t _ => a1_nonneg t) (by rfl) (by rfl) hs.2
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m1 : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) params.phi) :=
      transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
        (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) (by rfl) hphi hs.2)
    have m2 : MonotoneOn (fun t => dot (A t) (u s)) (Icc params.phi s) := by
      apply transfer_mono_A (w := u s)
      · intro t ht
        exact A_eq_phase2 ⟨ht.1, le_trans ht.2 h2⟩
      · exact phase_A_own_mono (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h2⟩)
          phi_nonneg (by rfl) hs.2
    exact glue_mono phi_nonneg hphi m1 m2
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m12 : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) params.theta) := by
      have m1 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
        (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) (by rfl) (le_trans switchOrder.phi_le_theta htheta) hs.2)
      have m2 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase2 ht)
        (phase_A_own_mono (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ht) phi_nonneg htheta hs.2)
      exact glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m3 : MonotoneOn (fun t => dot (A t) (u s)) (Icc params.theta s) := by
      apply transfer_mono_A (w := u s)
      · intro t ht
        exact A_eq_phase3 ⟨ht.1, le_trans ht.2 h3⟩
      · exact phase_A_own_mono (r := a3c) A3_hasDerivAt_public
          (fun t ht => a3_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h3⟩)
          zero_le_theta (by rfl) hs.2
    exact glue_mono zero_le_theta htheta m12 m3
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m123 : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) eta) := by
      have m1 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
        (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta heta)) hs.2)
      have m2 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase2 ht)
        (phase_A_own_mono (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ht) phi_nonneg (le_trans theta_le_eta heta) hs.2)
      have m3 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase3 ht)
        (phase_A_own_mono (r := a3c) A3_hasDerivAt_public
          (fun t ht => a3_nonneg ht) zero_le_theta heta hs.2)
      have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
      exact glue_mono zero_le_theta theta_le_eta m12 m3
    have m4 : MonotoneOn (fun t => dot (A t) (u s)) (Icc eta s) := by
      apply transfer_mono_A (w := u s)
      · intro t ht
        exact A_eq_phase4 ⟨ht.1, le_trans ht.2 h4⟩
      · exact phase_A_own_mono (r := a4c) A4_hasDerivAt_public
          (fun t ht => a4_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h4⟩)
          (le_trans zero_le_theta theta_le_eta) (by rfl) hs.2
    exact glue_mono (le_trans zero_le_theta theta_le_eta) heta m123 m4
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  have mpre : MonotoneOn (fun t => dot (A t) (u s)) (Icc (0 : ℝ) tau) := by
    have m1 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase1 ht)
      (phase_A_own_mono (r := a1c) A1_hasDerivAt_public
        (fun t _ => a1_nonneg t) (by rfl)
        (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau htau))) hs.2)
    have m2 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase2 ht)
      (phase_A_own_mono (r := a2c) A2_hasDerivAt_public
        (fun t ht => a2_nonneg ht) phi_nonneg
        (le_trans theta_le_eta (le_trans eta_le_tau htau)) hs.2)
    have m3 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase3 ht)
      (phase_A_own_mono (r := a3c) A3_hasDerivAt_public
        (fun t ht => a3_nonneg ht) zero_le_theta (le_trans eta_le_tau htau) hs.2)
    have m4 := transfer_mono_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_mono (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) (le_trans zero_le_theta theta_le_eta) htau hs.2)
    have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m123 := glue_mono zero_le_theta theta_le_eta m12 m3
    exact glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau m123 m4
  have m5 : MonotoneOn (fun t => dot (A t) (u s)) (Icc tau s) := by
    apply transfer_mono_A (w := u s)
    · intro t ht
      exact A_eq_phase5 ⟨ht.1, le_trans ht.2 hs.2⟩
    · exact phase_A_own_mono (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau)
        (by rfl) hs.2
  exact glue_mono (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) htau mpre m5

private theorem A_u_right_anti (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (A t) (u s)) (Icc s T) := by
  by_cases h1 : s ≤ params.phi
  · have m1 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s params.phi) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase1 ⟨le_trans hs.1 ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a1c) A1_hasDerivAt_public
          (fun t _ => a1_nonneg t) hs.1 (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m2 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase2 ht)
      (phase_A_own_anti (r := a2c) A2_hasDerivAt_public
        (fun t ht => a2_nonneg ht) hs.1 h1
        (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m3 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase3 ht)
      (phase_A_own_anti (r := a3c) A3_hasDerivAt_public
        (fun t ht => a3_nonneg ht) hs.1 (le_trans h1 switchOrder.phi_le_theta)
        (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_anti (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) hs.1
        (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) tau_le_T)
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1
        (le_trans (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) eta_le_tau)
        (by rfl))
    have m23 := glue_anti switchOrder.phi_le_theta theta_le_eta m2 m3
    have m234 := glue_anti (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau m23 m4
    have m2345 := glue_anti
      (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T m234 m5
    exact glue_anti h1
      (le_trans (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T)
      m1 m2345
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m2 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s params.theta) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase2 ⟨le_trans hphi ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a2c) A2_hasDerivAt_public
          (fun t ht => a2_nonneg ⟨lt_of_le_of_lt hphi ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))
    have m3 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase3 ht)
      (phase_A_own_anti (r := a3c) A3_hasDerivAt_public
        (fun t ht => a3_nonneg ht) hs.1 h2 (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_anti (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) hs.1 (le_trans h2 theta_le_eta) tau_le_T)
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1 (le_trans (le_trans h2 theta_le_eta) eta_le_tau) (by rfl))
    have m34 := glue_anti theta_le_eta eta_le_tau m3 m4
    have m345 := glue_anti (le_trans theta_le_eta eta_le_tau) tau_le_T m34 m5
    exact glue_anti h2
      (le_trans (le_trans theta_le_eta eta_le_tau) tau_le_T) m2 m345
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m3 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s eta) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase3 ⟨le_trans htheta ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a3c) A3_hasDerivAt_public
          (fun t ht => a3_nonneg ⟨lt_of_le_of_lt htheta ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans eta_le_tau tau_le_T)
    have m4 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase4 ht)
      (phase_A_own_anti (r := a4c) A4_hasDerivAt_public
        (fun t ht => a4_nonneg ht) hs.1 h3 tau_le_T)
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1 (le_trans h3 eta_le_tau) (by rfl))
    have m45 := glue_anti eta_le_tau tau_le_T m4 m5
    exact glue_anti h3 (le_trans eta_le_tau tau_le_T) m3 m45
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m4 : AntitoneOn (fun t => dot (A t) (u s)) (Icc s tau) := by
      apply transfer_anti_A (w := u s)
      · intro t ht
        exact A_eq_phase4 ⟨le_trans heta ht.1, ht.2⟩
      · exact phase_A_own_anti (r := a4c) A4_hasDerivAt_public
          (fun t ht => a4_nonneg ⟨lt_of_le_of_lt heta ht.1, ht.2⟩)
          hs.1 (by rfl) tau_le_T
    have m5 := transfer_anti_A (w := u s) (fun t ht => A_eq_phase5 ht)
      (phase_A_own_anti (r := a5c) A5_hasDerivAt_public
        (fun t _ => a5_nonneg t) hs.1 h4 (by rfl))
    exact glue_anti h4 tau_le_T m4 m5
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  apply transfer_anti_A (w := u s)
  · intro t ht
    exact A_eq_phase5 ⟨le_trans htau ht.1, ht.2⟩
  · exact phase_A_own_anti (r := a5c) A5_hasDerivAt_public
      (fun t _ => a5_nonneg t) hs.1 (by rfl) (by rfl)

private theorem C_v_left_mono (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) s) := by
  by_cases h1 : s ≤ params.phi
  · apply transfer_mono_C (w := v s)
    · intro t ht
      exact C_eq_phase1 ⟨ht.1, le_trans ht.2 h1⟩
    · exact phase_C_own_mono (r := c1c) C1_hasDerivAt_public
        (fun t _ => c1_nonneg t) (by rfl) (by rfl) hs.2
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
      (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
        (fun t _ => c1_nonneg t) (by rfl) hphi hs.2)
    have m2 : MonotoneOn (fun t => dot (C t) (v s)) (Icc params.phi s) := by
      apply transfer_mono_C (w := v s)
      · intro t ht
        exact C_eq_phase2 ⟨ht.1, le_trans ht.2 h2⟩
      · exact phase_C_own_mono (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h2⟩)
          phi_nonneg (by rfl) hs.2
    exact glue_mono phi_nonneg hphi m1 m2
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m12 : MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) params.theta) := by
      have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
        (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
          (fun t _ => c1_nonneg t) (by rfl) (le_trans switchOrder.phi_le_theta htheta) hs.2)
      have m2 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase2 ht)
        (phase_C_own_mono (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ht) phi_nonneg htheta hs.2)
      exact glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m3 : MonotoneOn (fun t => dot (C t) (v s)) (Icc params.theta s) := by
      apply transfer_mono_C (w := v s)
      · intro t ht
        exact C_eq_phase3 ⟨ht.1, le_trans ht.2 h3⟩
      · exact phase_C_own_mono (r := c3c) C3_hasDerivAt_public
          (fun t ht => c3_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h3⟩)
          zero_le_theta (by rfl) hs.2
    exact glue_mono zero_le_theta htheta m12 m3
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m123 : MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) eta) := by
      have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
        (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
          (fun t _ => c1_nonneg t) (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta heta)) hs.2)
      have m2 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase2 ht)
        (phase_C_own_mono (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ht) phi_nonneg (le_trans theta_le_eta heta) hs.2)
      have m3 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase3 ht)
        (phase_C_own_mono (r := c3c) C3_hasDerivAt_public
          (fun t ht => c3_nonneg ht) zero_le_theta heta hs.2)
      have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
      exact glue_mono zero_le_theta theta_le_eta m12 m3
    have m4 : MonotoneOn (fun t => dot (C t) (v s)) (Icc eta s) := by
      apply transfer_mono_C (w := v s)
      · intro t ht
        exact C_eq_phase4 ⟨ht.1, le_trans ht.2 h4⟩
      · exact phase_C_own_mono (r := c4c) C4_hasDerivAt_public
          (fun t ht => c4_nonneg ⟨ht.1, lt_of_lt_of_le ht.2 h4⟩)
          (le_trans zero_le_theta theta_le_eta) (by rfl) hs.2
    exact glue_mono (le_trans zero_le_theta theta_le_eta) heta m123 m4
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  have mpre : MonotoneOn (fun t => dot (C t) (v s)) (Icc (0 : ℝ) tau) := by
    have m1 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase1 ht)
      (phase_C_own_mono (r := c1c) C1_hasDerivAt_public
        (fun t _ => c1_nonneg t) (by rfl)
        (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau htau))) hs.2)
    have m2 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase2 ht)
      (phase_C_own_mono (r := c2c) C2_hasDerivAt_public
        (fun t ht => c2_nonneg ht) phi_nonneg
        (le_trans theta_le_eta (le_trans eta_le_tau htau)) hs.2)
    have m3 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase3 ht)
      (phase_C_own_mono (r := c3c) C3_hasDerivAt_public
        (fun t ht => c3_nonneg ht) zero_le_theta (le_trans eta_le_tau htau) hs.2)
    have m4 := transfer_mono_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_mono (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) (le_trans zero_le_theta theta_le_eta) htau hs.2)
    have m12 := glue_mono phi_nonneg switchOrder.phi_le_theta m1 m2
    have m123 := glue_mono zero_le_theta theta_le_eta m12 m3
    exact glue_mono (le_trans zero_le_theta theta_le_eta) eta_le_tau m123 m4
  have m5 : MonotoneOn (fun t => dot (C t) (v s)) (Icc tau s) := by
    apply transfer_mono_C (w := v s)
    · intro t ht
      exact C_eq_phase5 ⟨ht.1, le_trans ht.2 hs.2⟩
    · exact phase_C_own_mono (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau)
        (by rfl) hs.2
  exact glue_mono (le_trans (le_trans zero_le_theta theta_le_eta) eta_le_tau) htau mpre m5

private theorem C_v_right_anti (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    AntitoneOn (fun t => dot (C t) (v s)) (Icc s T) := by
  by_cases h1 : s ≤ params.phi
  · have m1 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s params.phi) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase1 ⟨le_trans hs.1 ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c1c) C1_hasDerivAt_public
          (fun t _ => c1_nonneg t) hs.1 (by rfl)
          (le_trans switchOrder.phi_le_theta (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m2 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase2 ht)
      (phase_C_own_anti (r := c2c) C2_hasDerivAt_public
        (fun t ht => c2_nonneg ht) hs.1 h1
        (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T)))
    have m3 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase3 ht)
      (phase_C_own_anti (r := c3c) C3_hasDerivAt_public
        (fun t ht => c3_nonneg ht) hs.1 (le_trans h1 switchOrder.phi_le_theta)
        (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_anti (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) hs.1
        (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) tau_le_T)
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1
        (le_trans (le_trans (le_trans h1 switchOrder.phi_le_theta) theta_le_eta) eta_le_tau)
        (by rfl))
    have m23 := glue_anti switchOrder.phi_le_theta theta_le_eta m2 m3
    have m234 := glue_anti (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau m23 m4
    have m2345 := glue_anti
      (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T m234 m5
    exact glue_anti h1
      (le_trans (le_trans (le_trans switchOrder.phi_le_theta theta_le_eta) eta_le_tau) tau_le_T)
      m1 m2345
  have hphi : params.phi ≤ s := le_of_lt (lt_of_not_ge h1)
  by_cases h2 : s ≤ params.theta
  · have m2 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s params.theta) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase2 ⟨le_trans hphi ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c2c) C2_hasDerivAt_public
          (fun t ht => c2_nonneg ⟨lt_of_le_of_lt hphi ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans theta_le_eta (le_trans eta_le_tau tau_le_T))
    have m3 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase3 ht)
      (phase_C_own_anti (r := c3c) C3_hasDerivAt_public
        (fun t ht => c3_nonneg ht) hs.1 h2 (le_trans eta_le_tau tau_le_T))
    have m4 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_anti (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) hs.1 (le_trans h2 theta_le_eta) tau_le_T)
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1 (le_trans (le_trans h2 theta_le_eta) eta_le_tau) (by rfl))
    have m34 := glue_anti theta_le_eta eta_le_tau m3 m4
    have m345 := glue_anti (le_trans theta_le_eta eta_le_tau) tau_le_T m34 m5
    exact glue_anti h2
      (le_trans (le_trans theta_le_eta eta_le_tau) tau_le_T) m2 m345
  have htheta : params.theta ≤ s := le_of_lt (lt_of_not_ge h2)
  by_cases h3 : s ≤ eta
  · have m3 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s eta) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase3 ⟨le_trans htheta ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c3c) C3_hasDerivAt_public
          (fun t ht => c3_nonneg ⟨lt_of_le_of_lt htheta ht.1, ht.2⟩)
          hs.1 (by rfl) (le_trans eta_le_tau tau_le_T)
    have m4 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase4 ht)
      (phase_C_own_anti (r := c4c) C4_hasDerivAt_public
        (fun t ht => c4_nonneg ht) hs.1 h3 tau_le_T)
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1 (le_trans h3 eta_le_tau) (by rfl))
    have m45 := glue_anti eta_le_tau tau_le_T m4 m5
    exact glue_anti h3 (le_trans eta_le_tau tau_le_T) m3 m45
  have heta : eta ≤ s := le_of_lt (lt_of_not_ge h3)
  by_cases h4 : s ≤ tau
  · have m4 : AntitoneOn (fun t => dot (C t) (v s)) (Icc s tau) := by
      apply transfer_anti_C (w := v s)
      · intro t ht
        exact C_eq_phase4 ⟨le_trans heta ht.1, ht.2⟩
      · exact phase_C_own_anti (r := c4c) C4_hasDerivAt_public
          (fun t ht => c4_nonneg ⟨lt_of_le_of_lt heta ht.1, ht.2⟩)
          hs.1 (by rfl) tau_le_T
    have m5 := transfer_anti_C (w := v s) (fun t ht => C_eq_phase5 ht)
      (phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
        (fun t _ => c5_nonneg t) hs.1 h4 (by rfl))
    exact glue_anti h4 tau_le_T m4 m5
  have htau : tau ≤ s := le_of_lt (lt_of_not_ge h4)
  apply transfer_anti_C (w := v s)
  · intro t ht
    exact C_eq_phase5 ⟨le_trans htau ht.1, ht.2⟩
  · exact phase_C_own_anti (r := c5c) C5_hasDerivAt_coeff
      (fun t _ => c5_nonneg t) hs.1 (by rfl) (by rfl)

theorem A_own_max (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    ∀ t ∈ Icc (0 : ℝ) T, dot (A t) (u s) ≤ dot (A s) (u s) := by
  intro t ht
  by_cases hts : t ≤ s
  · exact A_u_left_mono s hs ⟨ht.1, hts⟩ ⟨hs.1, le_rfl⟩ hts
  · have hst : s ≤ t := le_of_lt (lt_of_not_ge hts)
    exact A_u_right_anti s hs ⟨le_rfl, hs.2⟩ ⟨hst, ht.2⟩ hst

theorem C_own_max (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    ∀ t ∈ Icc (0 : ℝ) T, dot (C t) (v s) ≤ dot (C s) (v s) := by
  intro t ht
  by_cases hts : t ≤ s
  · exact C_v_left_mono s hs ⟨ht.1, hts⟩ ⟨hs.1, le_rfl⟩ hts
  · have hst : s ≤ t := le_of_lt (lt_of_not_ge hts)
    exact C_v_right_anti s hs ⟨le_rfl, hs.2⟩ ⟨hst, ht.2⟩ hst

private theorem a1_lower : (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem k51_lower : (-11 / 10 : ℝ) ≤ params.k51 := by
  have hp := params_mem
  dsimp [Romik.box] at hp
  have hlo :
      qR (-20344080735756291713874857283) 20000000000000000000000000000 ≤ params.k51 := by
    aesop
  norm_num [qR] at hlo ⊢
  linarith

private theorem endpointGap_nonneg : 0 ≤ 3 * params.a1 + params.k51 - 1 := by
  nlinarith [a1_lower, k51_lower]

private theorem path5_fst_formula (p : Romik.Params) (t : ℝ) :
    (Romik.path5 p t).1 =
      Real.cos t * (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2) -
        Real.sin t * (-p.e2 * Real.cos t + p.e1 * Real.sin t - 1) + p.k51 := by
  rfl

private theorem C_zero_formula : C 0 = (1 - 2 * params.a1, 1) := by
  have hphi : (0 : ℝ) ≤ params.phi := phi_nonneg
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  change
    ((Romik.path params 0).1 - beta 0 * (u 0).1 + (v 0).1,
     (Romik.path params 0).2 - beta 0 * (u 0).2 + (v 0).2) =
      (1 - 2 * params.a1, 1)
  rw [pathZero]
  apply Prod.ext <;> simp [beta, alphaBetaAt, hphi, Romik.alphaBeta1, u, v, ha2] <;> ring

private theorem A_T_formula : A T = (params.a1 + params.k51, 1) := by
  have he1 := Romik.e1_eq_a1_of_equations params_equations
  have he2 := Romik.e2_eq_quarter_of_equations params_equations
  have hphase : A T = phaseA5 T := A_eq_phase5 ⟨tau_le_T, le_rfl⟩
  rw [hphase]
  apply Prod.ext
  · simp [phaseA5, path5_fst_formula, Romik.alphaBeta5, u, v, T, he1, he2] <;> ring
  · have hpath : Romik.path params T = Romik.path5 params T := by
      simpa [T] using Romik.path_halfPi_eq_path5_of_mem_box params_mem
    have hy : (Romik.path5 params T).2 = 0 := by
      rw [← hpath]
      exact pathEndYZero
    have hyHalfPi : (Romik.path5 params (Real.pi / 2)).2 = 0 := by
      simpa [T] using hy
    simp [phaseA5, hyHalfPi, Romik.alphaBeta5, u, v, T, he1, he2]

private theorem endpoint_relation : A T = C 0 + (3 * params.a1 + params.k51 - 1) • (1, 0) := by
  rw [A_T_formula, C_zero_formula]
  apply Prod.ext <;> simp <;> ring

private theorem A_T_v_le_C_zero_v (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    dot (A T) (v s) ≤ dot (C 0) (v s) := by
  rw [endpoint_relation]
  have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (le_trans hs.2 T_le_pi)
  simp [dot, v]
  nlinarith [endpointGap_nonneg]

private theorem C_zero_u_le_A_T_u (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
    dot (C 0) (u s) ≤ dot (A T) (u s) := by
  rw [endpoint_relation]
  rcases hs with ⟨hs0, hsT⟩
  have hc : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    · dsimp [T] at hsT ⊢
      nlinarith [Real.pi_pos]
    · simpa [T] using hsT
  simp [dot, u]
  nlinarith [endpointGap_nonneg]

theorem A_base_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ (A t).2 := by
  intro t ht
  have hm := A_y_global_mono ⟨le_rfl, T_nonneg⟩ ht ht.1
  have h0 : dot (A 0) (0, 1) = 0 := by
    rw [A_zero_eq_anchor]
    simp [dot, anchor]
  have ht' : dot (A t) (0, 1) = (A t).2 := by simp [dot]
  change dot (A 0) (0, 1) ≤ dot (A t) (0, 1) at hm
  rw [h0, ht'] at hm
  exact hm

theorem C_base_nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ (C t).2 := by
  intro t ht
  have hm := C_y_global_anti ht ⟨T_nonneg, le_rfl⟩ ht.2
  have hT : dot (C T) (0, 1) = 0 := by
    simp [dot, C_T_snd_zero]
  have ht' : dot (C t) (0, 1) = (C t).2 := by simp [dot]
  change dot (C T) (0, 1) ≤ dot (C t) (0, 1) at hm
  rw [hT, ht'] at hm
  exact hm

theorem supportA_direct : ∀ t ∈ Icc (0 : ℝ) T, A t ∈ K := by
  intro t ht
  rw [Romik.mem_K0]
  refine ⟨A_base_nonneg t ht, ?_⟩
  intro s hs
  have hsT : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  constructor
  · change dot (A t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    have hmax := A_own_max s hsT t ht
    rw [A_support_identity] at hmax
    exact hmax
  · change dot (A t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    have hmono := A_v_global_mono s hsT ht ⟨T_nonneg, le_rfl⟩ ht.2
    have hsep := A_T_v_le_C_zero_v s hsT
    have hmax := C_own_max s hsT 0 ⟨le_rfl, T_nonneg⟩
    have hid := C_support_identity s
    linarith

theorem supportC_direct : ∀ t ∈ Icc (0 : ℝ) T, C t ∈ K := by
  intro t ht
  rw [Romik.mem_K0]
  refine ⟨C_base_nonneg t ht, ?_⟩
  intro s hs
  have hsT : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  constructor
  · change dot (C t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    have hanti := C_u_global_anti s hsT ⟨le_rfl, T_nonneg⟩ ht ht.1
    have hsep := C_zero_u_le_A_T_u s hsT
    have hmax := A_own_max s hsT T ⟨T_nonneg, le_rfl⟩
    have hid := A_support_identity s
    linarith
  · change dot (C t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    have hmax := C_own_max s hsT t ht
    rw [C_support_identity] at hmax
    exact hmax

end Stage3
end PartC
end GerverSofa
