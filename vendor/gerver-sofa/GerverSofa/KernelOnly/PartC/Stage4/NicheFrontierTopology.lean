import GerverSofa.KernelOnly.PartC.Stage4.VerticalFillTopology
import GerverSofa.KernelOnly.PartC.Stage4.NicheMembershipFacts
import GerverSofa.KernelOnly.PartC.Stage4.NicheEnvelopeSupport
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Separation.Hausdorff

/-!
# Part C Stage 4: frontier of a strict vertical subgraph

This file contains the topological calculation used by the concrete Gerver
niche.  The generic lemma is intentionally independent of the old Stage 2
topology sketches: it computes the closure and the interior of a strict
vertical subgraph directly.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-! ## The three Gerver roof arcs are graphs over horizontal position -/

private theorem u_hasDerivAt_frontier (t : ℝ) : HasDerivAt u (v t) t := by
  change HasDerivAt (fun s : ℝ => (Real.cos s, Real.sin s))
    (-Real.sin t, Real.cos t) t
  exact (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)

private theorem v_hasDerivAt_frontier (t : ℝ) : HasDerivAt v (-u t) t := by
  change HasDerivAt (fun s : ℝ => (-Real.sin s, Real.cos s))
    (-Real.cos t, -Real.sin t) t
  exact (Real.hasDerivAt_sin t).fun_neg.prodMk (Real.hasDerivAt_cos t)

private theorem square_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
  simpa only [id_eq, one_mul, mul_one] using
    (hasDerivAt_id t).fun_mul (hasDerivAt_id t)

private theorem beta1_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta1 params s).2)
      (-2 * params.a1 * Real.sin t + 2 * params.a2 * Real.cos t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.a1) (Real.hasDerivAt_cos t)
  have h2 := HasDerivAt.const_mul (2 * params.a2) (Real.hasDerivAt_sin t)
  have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
  refine h.congr_deriv ?_
  ring

private theorem beta2_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).2)
      (-(1 / 2 : ℝ) * t + params.b1) t := by
  have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ))
    (square_hasDerivAt_frontier t)
  have h2 := HasDerivAt.const_mul params.b1 (hasDerivAt_id t)
  have hraw := ((h1.fun_add h2).fun_add (hasDerivAt_const t params.b2)).fun_add
    (hasDerivAt_const t (1 / 2 : ℝ))
  have h := hraw.congr_deriv (show
      (-(1 / 4 : ℝ) * (t + t) + params.b1 * 1 + 0 + 0) =
        (-(1 / 2 : ℝ) * t + params.b1) by ring)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with s
  dsimp [Romik.alphaBeta2]
  ring

private theorem alpha4_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).1)
      ((1 / 2 : ℝ) * t - params.d1) t := by
  have h1 := HasDerivAt.const_mul (1 / 4 : ℝ)
    (square_hasDerivAt_frontier t)
  have h2 := HasDerivAt.const_mul params.d1 (hasDerivAt_id t)
  have hraw := (((h1.fun_sub h2).fun_sub (hasDerivAt_const t params.d2)).fun_sub
    (hasDerivAt_const t (1 / 2 : ℝ)))
  have h := hraw.congr_deriv (show
      ((1 / 4 : ℝ) * (t + t) - params.d1 * 1 - 0 - 0) =
        ((1 / 2 : ℝ) * t - params.d1) by ring)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with s
  dsimp [Romik.alphaBeta4]
  ring

private theorem alpha5_hasDerivAt_frontier (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).1)
      (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.e1) (Real.hasDerivAt_sin t)
  have h2 := HasDerivAt.const_mul (2 * params.e2) (Real.hasDerivAt_cos t)
  have h := ((hasDerivAt_const t (1 : ℝ)).fun_sub h1).fun_add h2
  refine h.congr_deriv ?_
  ring

private theorem contactD_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {bp : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (hb : HasDerivAt (fun s => (ab s).2) bp t) :
    HasDerivAt (fun s => x s - (ab s).2 • u s)
      (((ab t).1 - bp) • u t) t := by
  have h := hx.fun_sub (hb.fun_smul (u_hasDerivAt_frontier t))
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v] <;> ring

private theorem contactB_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {ap : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (ha : HasDerivAt (fun s => (ab s).1) ap t) :
    HasDerivAt (fun s => x s + (ab s).1 • v s)
      (((ab t).2 + ap) • v t) t := by
  have h := hx.fun_add (ha.fun_smul (v_hasDerivAt_frontier t))
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v] <;> ring

private def phaseD1 (t : ℝ) : Point :=
  Romik.path1 params t - (Romik.alphaBeta1 params t).2 • u t

private def phaseD2 (t : ℝ) : Point :=
  Romik.path2 params t - (Romik.alphaBeta2 params t).2 • u t

private def phaseB4 (t : ℝ) : Point :=
  Romik.path4 params t + (Romik.alphaBeta4 params t).1 • v t

private def phaseB5 (t : ℝ) : Point :=
  Romik.path5 params t + (Romik.alphaBeta5 params t).1 • v t

private theorem phaseD1_hasDerivAt (t : ℝ) :
    HasDerivAt phaseD1 ((1 / 2 : ℝ) • u t) t := by
  have h := contactD_hasDerivAt t (path1_hasDerivAt_public t)
    (beta1_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • u t)
    dsimp [Romik.alphaBeta1]
    ring)

private theorem phaseD2_hasDerivAt (t : ℝ) :
    HasDerivAt phaseD2 ((1 + params.b1 - t / 2) • u t) t := by
  have h := contactD_hasDerivAt t (path2_hasDerivAt_public t)
    (beta2_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • u t)
    dsimp [Romik.alphaBeta2]
    ring)

private theorem phaseB4_hasDerivAt (t : ℝ) :
    HasDerivAt phaseB4 ((params.d1 - 1 - t / 2) • v t) t := by
  have h := contactB_hasDerivAt t (path4_hasDerivAt_public t)
    (alpha4_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • v t)
    dsimp [Romik.alphaBeta4]
    ring)

private theorem phaseB5_hasDerivAt (t : ℝ) :
    HasDerivAt phaseB5 ((-(1 / 2 : ℝ)) • v t) t := by
  have h := contactB_hasDerivAt t (path5_hasDerivAt_public t)
    (alpha5_hasDerivAt_frontier t)
  exact h.congr_deriv (by
    apply congrArg (fun c : ℝ => c • v t)
    dsimp [Romik.alphaBeta5]
    ring)

private theorem phaseD1_continuous : Continuous phaseD1 := by
  exact continuous_iff_continuousAt.2 fun t => (phaseD1_hasDerivAt t).continuousAt

private theorem phaseD2_continuous : Continuous phaseD2 := by
  exact continuous_iff_continuousAt.2 fun t => (phaseD2_hasDerivAt t).continuousAt

private theorem phaseB4_continuous : Continuous phaseB4 := by
  exact continuous_iff_continuousAt.2 fun t => (phaseB4_hasDerivAt t).continuousAt

private theorem phaseB5_continuous : Continuous phaseB5 := by
  exact continuous_iff_continuousAt.2 fun t => (phaseB5_hasDerivAt t).continuousAt

private theorem dot_fixed_hasDerivAt_frontier
    {f : ℝ → Point} {df w : Point} {t : ℝ}
    (h : HasDerivAt f df t) :
    HasDerivAt (fun s => dot (f s) w) (dot df w) t := by
  have h1 := HasDerivAt.const_mul w.1 h.fst
  have h2 := HasDerivAt.const_mul w.2 h.snd
  simpa [dot, mul_comm] using h1.fun_add h2

private theorem b1_lower_frontier : (-53 / 100 : ℝ) ≤ params.b1 := by
  have h := PartB.b1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem theta_upper_frontier : params.theta ≤ (689 / 1000 : ℝ) := by
  have h := theta_bounds.2
  norm_num at h ⊢
  linarith

private theorem d1_lower_frontier : (13 / 10 : ℝ) ≤ params.d1 := by
  have h := PartB.d1_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem d1_upper_frontier : params.d1 ≤ (33 / 25 : ℝ) := by
  have h := PartB.d1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem eta_lower_frontier : (4 / 5 : ℝ) ≤ eta := by
  dsimp [eta, T]
  nlinarith [Real.pi_gt_three, theta_upper_frontier]

private theorem T_upper_frontier : T < (8 / 5 : ℝ) := by
  have hp := ExactReplay.piI_contains_pi
  have hhi : Real.pi ≤ (ExactReplay.piI.hi : ℝ) := hp.2
  have h32 : (ExactReplay.piI.hi : ℝ) < (16 / 5 : ℝ) := by
    norm_num [ExactReplay.piI, ExactReplay.q]
  dsimp [T]
  linarith

private theorem phaseD1_fst_strictMono :
    StrictMonoOn (fun t => (phaseD1 t).1) (Icc (0 : ℝ) params.phi) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseD1_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseD1 s).1)
      (((1 / 2 : ℝ) • u t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseD1_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], by
      have htT : t < T := lt_trans ht.2 phi_lt_T
      simpa [T] using htT⟩
  simpa [u] using mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hc

private theorem phaseD2_fst_strictMono :
    StrictMonoOn (fun t => (phaseD2 t).1) (Icc params.phi params.theta) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseD2_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseD2 s).1)
      (((1 + params.b1 - t / 2) • u t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseD2_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hcoef : 0 < 1 + params.b1 - t / 2 := by
    nlinarith [b1_lower_frontier, theta_upper_frontier, ht.2]
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, phi_pos, ht.1], by
      have htT : t < T := lt_trans ht.2 theta_lt_T
      simpa [T] using htT⟩
  simpa [u] using mul_pos hcoef hc

private theorem phaseB4_fst_strictMono :
    StrictMonoOn (fun t => (phaseB4 t).1) (Icc eta tau) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseB4_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseB4 s).1)
      (((params.d1 - 1 - t / 2) • v t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseB4_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hcoef : params.d1 - 1 - t / 2 < 0 := by
    nlinarith [d1_upper_frontier, eta_lower_frontier, ht.1]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (lt_trans theta_pos theta_lt_eta) ht.1)
    (lt_trans (lt_trans ht.2 tau_lt_T) (by
      dsimp [T]; nlinarith [Real.pi_pos]))
  have hm : 0 < (params.d1 - 1 - t / 2) * (-Real.sin t) :=
    mul_pos_of_neg_of_neg hcoef (neg_neg_of_pos hs)
  simpa [v] using hm

private theorem phaseB5_fst_strictMono :
    StrictMonoOn (fun t => (phaseB5 t).1) (Icc tau T) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) phaseB5_continuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  have hder : HasDerivAt (fun s => (phaseB5 s).1)
      (((-(1 / 2 : ℝ)) • v t).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (phaseB5_hasDerivAt t)
    simpa [dot] using h
  rw [hder.deriv]
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans (lt_trans (lt_trans theta_pos theta_lt_eta) eta_lt_tau) ht.1)
    (lt_trans ht.2 (by dsimp [T]; nlinarith [Real.pi_pos]))
  simpa [v] using mul_pos_of_neg_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0)
    (neg_neg_of_pos hs)

private theorem phaseD1_eq_D {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.phi) :
    phaseD1 t = D t := by
  apply Prod.ext <;>
    simp [phaseD1, D, beta, alphaBetaAt, Romik.path, ht.2]

private theorem phaseD2_eq_D {t : ℝ} (ht : t ∈ Icc params.phi params.theta) :
    phaseD2 t = D t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    apply Prod.ext <;>
      simp [phaseD2, D, beta, alphaBetaAt, Romik.path, phi_lt_theta.le,
        PartB.match12, alphaBeta_match12_direct]
  · apply Prod.ext <;>
      simp [phaseD2, D, beta, alphaBetaAt, Romik.path, not_le.mpr h, ht.2]

private theorem phaseB4_eq_B {t : ℝ} (ht : t ∈ Icc eta tau) :
    phaseB4 t = B t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    have hm : Romik.path3 params eta = Romik.path4 params eta := by
      simpa [eta, T] using PartB.match34
    have hphase : phaseB4 eta = Romik.path4 params eta +
        (Romik.alphaBeta4 params eta).1 • v eta := by
      rfl
    have hetaRaw : eta ≤ Real.pi / 2 - params.theta := by rfl
    have hB : B eta = Romik.path3 params eta +
        (Romik.alphaBeta3 params eta).1 • v eta := by
      apply Prod.ext <;>
        simp [B, alpha, alphaBetaAt, Romik.path,
          not_le.mpr phi_lt_eta, not_le.mpr theta_lt_eta, hetaRaw]
    calc
      phaseB4 eta = Romik.path4 params eta +
          (Romik.alphaBeta4 params eta).1 • v eta := hphase
      _ = Romik.path3 params eta +
          (Romik.alphaBeta3 params eta).1 • v eta := by
            rw [hm, alphaBeta_match34_direct]
      _ = B eta := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using h
    have htauRaw : t ≤ Real.pi / 2 - params.phi := by
      simpa [tau, T] using ht.2
    apply Prod.ext <;>
      simp [phaseB4, B, alpha, alphaBetaAt, Romik.path,
        not_le.mpr (lt_trans phi_lt_eta h),
        not_le.mpr (lt_trans theta_lt_eta h), not_le.mpr h, ht.2,
        not_le.mpr hetaRaw, htauRaw, eta, tau, T]

private theorem phaseB5_eq_B {t : ℝ} (ht : t ∈ Icc tau T) :
    phaseB5 t = B t := by
  rcases ht.1.eq_or_lt with h | h
  · subst t
    have hm : Romik.path4 params tau = Romik.path5 params tau := by
      simpa [tau, T] using PartB.match45
    have hphase : phaseB5 tau = Romik.path5 params tau +
        (Romik.alphaBeta5 params tau).1 • v tau := by
      rfl
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
      phaseB5 tau = Romik.path5 params tau +
          (Romik.alphaBeta5 params tau).1 • v tau := hphase
      _ = Romik.path4 params tau +
          (Romik.alphaBeta4 params tau).1 • v tau := by
            rw [hm, alphaBeta_match45_direct]
      _ = B tau := hB.symm
  · have hetaRaw : Real.pi / 2 - params.theta < t := by
      simpa [eta, T] using lt_trans eta_lt_tau h
    have htauRaw : Real.pi / 2 - params.phi < t := by
      simpa [tau, T] using h
    apply Prod.ext <;>
      simp [phaseB5, B, alpha, alphaBetaAt, Romik.path,
        not_le.mpr (lt_trans (lt_trans phi_lt_eta eta_lt_tau) h),
        not_le.mpr (lt_trans (lt_trans theta_lt_eta eta_lt_tau) h),
        not_le.mpr (lt_trans eta_lt_tau h), not_le.mpr h,
        not_le.mpr hetaRaw, not_le.mpr htauRaw, eta, tau, T]

/-- The early contact arc has strictly increasing horizontal projection. -/
theorem D_fst_strictMono :
    StrictMonoOn (fun t => (D t).1) (Icc (0 : ℝ) params.theta) := by
  intro x hx y hy hxy
  by_cases hyphi : y ≤ params.phi
  · have hxphi : x ∈ Icc (0 : ℝ) params.phi :=
      ⟨hx.1, le_trans hxy.le hyphi⟩
    have hyphi' : y ∈ Icc (0 : ℝ) params.phi := ⟨hy.1, hyphi⟩
    simpa [phaseD1_eq_D hxphi, phaseD1_eq_D hyphi'] using
      phaseD1_fst_strictMono hxphi hyphi' hxy
  · have hphiy : params.phi < y := lt_of_not_ge hyphi
    by_cases hxphi : x ≤ params.phi
    · have hx1 : x ∈ Icc (0 : ℝ) params.phi := ⟨hx.1, hxphi⟩
      have hphi1 : params.phi ∈ Icc (0 : ℝ) params.phi :=
        ⟨phi_pos.le, le_rfl⟩
      have hphi2 : params.phi ∈ Icc params.phi params.theta :=
        ⟨le_rfl, phi_lt_theta.le⟩
      have hy2 : y ∈ Icc params.phi params.theta :=
        ⟨hphiy.le, hy.2⟩
      have hleft := phaseD1_fst_strictMono.monotoneOn hx1 hphi1 hxphi
      have hright := phaseD2_fst_strictMono hphi2 hy2 hphiy
      calc
        (D x).1 = (phaseD1 x).1 := congrArg Prod.fst (phaseD1_eq_D hx1).symm
        _ ≤ (phaseD1 params.phi).1 := hleft
        _ = (D params.phi).1 := congrArg Prod.fst (phaseD1_eq_D hphi1)
        _ = (phaseD2 params.phi).1 := congrArg Prod.fst (phaseD2_eq_D hphi2).symm
        _ < (phaseD2 y).1 := hright
        _ = (D y).1 := congrArg Prod.fst (phaseD2_eq_D hy2)
    · have hphix : params.phi < x := lt_of_not_ge hxphi
      have hx2 : x ∈ Icc params.phi params.theta := ⟨hphix.le, hx.2⟩
      have hy2 : y ∈ Icc params.phi params.theta := ⟨hphiy.le, hy.2⟩
      simpa [phaseD2_eq_D hx2, phaseD2_eq_D hy2] using
        phaseD2_fst_strictMono hx2 hy2 hxy

/-- The late contact arc has strictly increasing horizontal projection. -/
theorem B_fst_strictMono :
    StrictMonoOn (fun t => (B t).1) (Icc eta T) := by
  intro x hx y hy hxy
  by_cases hytau : y ≤ tau
  · have hx4 : x ∈ Icc eta tau := ⟨hx.1, le_trans hxy.le hytau⟩
    have hy4 : y ∈ Icc eta tau := ⟨hy.1, hytau⟩
    simpa [phaseB4_eq_B hx4, phaseB4_eq_B hy4] using
      phaseB4_fst_strictMono hx4 hy4 hxy
  · have htauy : tau < y := lt_of_not_ge hytau
    by_cases hxtau : x ≤ tau
    · have hx4 : x ∈ Icc eta tau := ⟨hx.1, hxtau⟩
      have htau4 : tau ∈ Icc eta tau := ⟨eta_lt_tau.le, le_rfl⟩
      have htau5 : tau ∈ Icc tau T := ⟨le_rfl, tau_lt_T.le⟩
      have hy5 : y ∈ Icc tau T := ⟨htauy.le, hy.2⟩
      have hleft := phaseB4_fst_strictMono.monotoneOn hx4 htau4 hxtau
      have hright := phaseB5_fst_strictMono htau5 hy5 htauy
      calc
        (B x).1 = (phaseB4 x).1 := congrArg Prod.fst (phaseB4_eq_B hx4).symm
        _ ≤ (phaseB4 tau).1 := hleft
        _ = (B tau).1 := congrArg Prod.fst (phaseB4_eq_B htau4)
        _ = (phaseB5 tau).1 := congrArg Prod.fst (phaseB5_eq_B htau5).symm
        _ < (phaseB5 y).1 := hright
        _ = (B y).1 := congrArg Prod.fst (phaseB5_eq_B hy5)
    · have htaux : tau < x := lt_of_not_ge hxtau
      have hx5 : x ∈ Icc tau T := ⟨htaux.le, hx.2⟩
      have hy5 : y ∈ Icc tau T := ⟨htauy.le, hy.2⟩
      simpa [phaseB5_eq_B hx5, phaseB5_eq_B hy5] using
        phaseB5_fst_strictMono hx5 hy5 hxy

private theorem b1_upper_frontier : params.b1 ≤ (-527 / 1000 : ℝ) := by
  have h := PartB.b1_contains.2
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem c2_lower_frontier : (-1 : ℝ) ≤ params.c2 := by
  have h := PartB.c2_contains.1
  norm_num [RatInterval.Contains, ExactReplay.fullInputBox, ExactReplay.getI,
    CertificateManifest.z22, CertificateManifest.q] at h ⊢
  linarith

private theorem path_fst_deriv_neg {t : ℝ} (ht : t ∈ Ioo params.phi tau) :
    deriv (fun s => (Romik.path params s).1) t < 0 := by
  have hder : HasDerivAt (fun s => (Romik.path params s).1)
      ((Romik.rot t (alphaBetaAt t)).1) t := by
    have h := dot_fixed_hasDerivAt_frontier (w := ((1 : ℝ), 0))
      (path_hasDerivAt_noHidden t)
    simpa [dot] using h
  rw [hder.deriv]
  have htPhys : t ∈ Icc params.phi T := ⟨ht.1.le, le_trans ht.2.le tau_lt_T.le⟩
  have ha := alpha_nonpos htPhys
  have hb := beta_nonneg htPhys
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (lt_trans phi_pos ht.1) (lt_trans (lt_trans ht.2 tau_lt_T)
      (by dsimp [T]; nlinarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, phi_pos, ht.1], by
      have htT := lt_trans ht.2 tau_lt_T
      simpa [T] using htT⟩
  by_cases htheta : t ≤ params.theta
  · have hphi : ¬ t ≤ params.phi := not_le.mpr ht.1
    have has : alpha t < 0 := by
      simp only [alpha, alphaBetaAt, if_neg hphi, if_pos htheta]
      dsimp [Romik.alphaBeta2]
      nlinarith [b1_upper_frontier, ht.1, phi_pos]
    dsimp [Romik.rot]
    change Real.cos t * alpha t - Real.sin t * beta t < 0
    nlinarith [mul_neg_of_neg_of_pos has hc, mul_nonneg hb hs.le]
  · by_cases heta : t ≤ eta
    · have hphi : ¬ t ≤ params.phi := not_le.mpr ht.1
      have has : alpha t < 0 := by
        simp only [alpha, alphaBetaAt, if_neg hphi, if_neg htheta, if_pos heta]
        dsimp [Romik.alphaBeta3]
        nlinarith [c2_lower_frontier, theta_pos, lt_of_not_ge htheta]
      dsimp [Romik.rot]
      change Real.cos t * alpha t - Real.sin t * beta t < 0
      nlinarith [mul_neg_of_neg_of_pos has hc, mul_nonneg hb hs.le]
    · have hphi : ¬ t ≤ params.phi := not_le.mpr ht.1
      have hbp : 0 < beta t := by
        simp only [beta, alphaBetaAt, if_neg hphi, if_neg htheta, if_neg heta,
          if_pos ht.2.le]
        dsimp [Romik.alphaBeta4]
        nlinarith [d1_lower_frontier, T_upper_frontier,
          lt_trans ht.2 tau_lt_T]
      dsimp [Romik.rot]
      change Real.cos t * alpha t - Real.sin t * beta t < 0
      nlinarith [mul_nonpos_of_nonpos_of_nonneg ha hc.le,
        mul_pos hbp hs]

/-- The core path runs strictly from right to left in horizontal projection. -/
theorem core_path_fst_strictAnti :
    StrictAntiOn (fun t => (Romik.path params t).1) (Icc params.phi tau) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) pathContinuous.fst.continuousOn
  intro t ht
  rw [interior_Icc] at ht
  exact path_fst_deriv_neg ht

/-! ## A single left-to-right parametrization of the three roof arcs -/

/-- The affine reversal which runs through the core path from `tau` to `phi`
while the auxiliary parameter runs from `theta` to `eta`. -/
def coreReverseTime (s : ℝ) : ℝ :=
  tau - ((tau - params.phi) / (eta - params.theta)) *
    (s - params.theta)

private theorem coreReverseTime_theta :
    coreReverseTime params.theta = tau := by
  simp [coreReverseTime]

private theorem coreReverseTime_eta : coreReverseTime eta = params.phi := by
  have hne : eta - params.theta ≠ 0 := sub_ne_zero.mpr theta_lt_eta.ne'
  dsimp [coreReverseTime]
  field_simp [hne]
  ring

private theorem coreReverseTime_strictAnti : StrictAnti coreReverseTime := by
  intro x y hxy
  have hc : 0 < (tau - params.phi) / (eta - params.theta) :=
    div_pos (sub_pos.mpr (lt_trans phi_lt_theta
      (lt_trans theta_lt_eta eta_lt_tau))) (sub_pos.mpr theta_lt_eta)
  have hprod := mul_pos hc (sub_pos.mpr hxy)
  dsimp [coreReverseTime]
  nlinarith [hprod]

private theorem coreReverseTime_mem {s : ℝ}
    (hs : s ∈ Icc params.theta eta) :
    coreReverseTime s ∈ Icc params.phi tau := by
  constructor
  · rw [← coreReverseTime_eta]
    exact coreReverseTime_strictAnti.antitone hs.2
  · rw [← coreReverseTime_theta]
    exact coreReverseTime_strictAnti.antitone hs.1

private theorem coreReverseTime_continuous : Continuous coreReverseTime := by
  unfold coreReverseTime
  fun_prop

/-- A single continuous parametrization of the complete upper niche arc. -/
def nicheTopArc (s : ℝ) : Point :=
  if s ≤ params.theta then D s
  else if s ≤ eta then Romik.path params (coreReverseTime s)
  else B s

private theorem nicheTopArc_of_le_theta {s : ℝ} (hs : s ≤ params.theta) :
    nicheTopArc s = D s := by
  simp [nicheTopArc, hs]

private theorem nicheTopArc_of_middle {s : ℝ}
    (hθ : params.theta < s) (hη : s ≤ eta) :
    nicheTopArc s = Romik.path params (coreReverseTime s) := by
  simp [nicheTopArc, not_le.mpr hθ, hη]

private theorem nicheTopArc_of_late {s : ℝ} (hη : eta < s) :
    nicheTopArc s = B s := by
  simp [nicheTopArc, not_le.mpr (lt_trans theta_lt_eta hη),
    not_le.mpr hη]

theorem nicheTopArc_continuous : Continuous nicheTopArc := by
  have hcore : Continuous
      (fun s : ℝ => Romik.path params (coreReverseTime s)) :=
    pathContinuous.comp coreReverseTime_continuous
  have hcoreB : Continuous (fun s : ℝ =>
      if s ≤ eta then Romik.path params (coreReverseTime s) else B s) := by
    exact hcore.if_le B_continuous continuous_id continuous_const (by
      intro s hs
      subst s
      rw [coreReverseTime_eta]
      exact B_eta_eq_path_phi.symm)
  exact D_continuous.if_le hcoreB continuous_id continuous_const (by
    intro s hs
    subst s
    rw [if_pos theta_lt_eta.le, coreReverseTime_theta]
    exact D_theta_eq_path_tau)

/-- Horizontal projection of the complete upper arc is strictly increasing. -/
theorem nicheTopArc_fst_strictMono :
    StrictMonoOn (fun s => (nicheTopArc s).1) (Icc (0 : ℝ) T) := by
  intro x hx y hy hxy
  change (nicheTopArc x).1 < (nicheTopArc y).1
  by_cases hyθ : y ≤ params.theta
  · have hxD : x ∈ Icc (0 : ℝ) params.theta :=
      ⟨hx.1, le_trans hxy.le hyθ⟩
    have hyD : y ∈ Icc (0 : ℝ) params.theta := ⟨hy.1, hyθ⟩
    rw [nicheTopArc_of_le_theta hxD.2, nicheTopArc_of_le_theta hyθ]
    exact D_fst_strictMono hxD hyD hxy
  · have hθy : params.theta < y := lt_of_not_ge hyθ
    by_cases hxθ : x ≤ params.theta
    · have hxD : x ∈ Icc (0 : ℝ) params.theta := ⟨hx.1, hxθ⟩
      have hθD : params.theta ∈ Icc (0 : ℝ) params.theta :=
        ⟨theta_pos.le, le_rfl⟩
      have hleft := D_fst_strictMono.monotoneOn hxD hθD hxθ
      rw [nicheTopArc_of_le_theta hxθ]
      by_cases hyη : y ≤ eta
      · have hyM : y ∈ Icc params.theta eta := ⟨hθy.le, hyη⟩
        have hcy := coreReverseTime_mem hyM
        have hcytau : coreReverseTime y < tau := by
          rw [← coreReverseTime_theta]
          exact coreReverseTime_strictAnti hθy
        have hright := core_path_fst_strictAnti hcy
          (right_mem_Icc.2 (lt_trans phi_lt_theta
            (lt_trans theta_lt_eta eta_lt_tau)).le) hcytau
        rw [nicheTopArc_of_middle hθy hyη]
        calc
          (D x).1 ≤ (D params.theta).1 := hleft
          _ = (Romik.path params tau).1 := congrArg Prod.fst D_theta_eq_path_tau
          _ < (Romik.path params (coreReverseTime y)).1 := hright
      · have hηy : eta < y := lt_of_not_ge hyη
        have hyB : y ∈ Icc eta T := ⟨hηy.le, hy.2⟩
        have hηB : eta ∈ Icc eta T := ⟨le_rfl, eta_lt_T.le⟩
        have hB := B_fst_strictMono hηB hyB hηy
        have hcore := core_path_fst_strictAnti
          (left_mem_Icc.2 (lt_trans phi_lt_theta
            (lt_trans theta_lt_eta eta_lt_tau)).le)
          (right_mem_Icc.2 (lt_trans phi_lt_theta
            (lt_trans theta_lt_eta eta_lt_tau)).le)
          (lt_trans phi_lt_theta (lt_trans theta_lt_eta eta_lt_tau))
        rw [nicheTopArc_of_late hηy]
        calc
          (D x).1 ≤ (D params.theta).1 := hleft
          _ = (Romik.path params tau).1 := congrArg Prod.fst D_theta_eq_path_tau
          _ < (Romik.path params params.phi).1 := hcore
          _ = (B eta).1 := congrArg Prod.fst B_eta_eq_path_phi.symm
          _ < (B y).1 := hB
    · have hθx : params.theta < x := lt_of_not_ge hxθ
      by_cases hyη : y ≤ eta
      · have hxM : x ∈ Icc params.theta eta :=
          ⟨hθx.le, le_trans hxy.le hyη⟩
        have hyM : y ∈ Icc params.theta eta := ⟨hθy.le, hyη⟩
        have hcyx : coreReverseTime y < coreReverseTime x :=
          coreReverseTime_strictAnti hxy
        rw [nicheTopArc_of_middle hθx hxM.2,
          nicheTopArc_of_middle hθy hyη]
        exact core_path_fst_strictAnti (coreReverseTime_mem hyM)
          (coreReverseTime_mem hxM) hcyx
      · have hηy : eta < y := lt_of_not_ge hyη
        rw [nicheTopArc_of_late hηy]
        by_cases hxη : x ≤ eta
        · have hxM : x ∈ Icc params.theta eta := ⟨hθx.le, hxη⟩
          have hcx := coreReverseTime_mem hxM
          have hpath : (Romik.path params (coreReverseTime x)).1 ≤
              (Romik.path params params.phi).1 :=
            core_path_fst_strictAnti.antitoneOn
              (left_mem_Icc.2 (lt_trans phi_lt_theta
                (lt_trans theta_lt_eta eta_lt_tau)).le)
              hcx hcx.1
          have hyB : y ∈ Icc eta T := ⟨hηy.le, hy.2⟩
          have hB := B_fst_strictMono
            (left_mem_Icc.2 eta_lt_T.le) hyB hηy
          rw [nicheTopArc_of_middle hθx hxη]
          calc
            (Romik.path params (coreReverseTime x)).1 ≤
                (Romik.path params params.phi).1 := hpath
            _ = (B eta).1 := congrArg Prod.fst B_eta_eq_path_phi.symm
            _ < (B y).1 := hB
        · have hηx : eta < x := lt_of_not_ge hxη
          have hxB : x ∈ Icc eta T := ⟨hηx.le, hx.2⟩
          have hyB : y ∈ Icc eta T := ⟨hηy.le, hy.2⟩
          rw [nicheTopArc_of_late hηx]
          exact B_fst_strictMono hxB hyB hxy

theorem nicheTopArc_y_nonneg {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    0 ≤ (nicheTopArc s).2 := by
  by_cases hθ : s ≤ params.theta
  · rw [nicheTopArc_of_le_theta hθ]
    exact D_y_nonneg ⟨hs.1, hθ⟩
  · have hθs : params.theta < s := lt_of_not_ge hθ
    by_cases hη : s ≤ eta
    · rw [nicheTopArc_of_middle hθs hη]
      exact path_core_y_nonneg (coreReverseTime_mem ⟨hθs.le, hη⟩)
    · have hηs : eta < s := lt_of_not_ge hη
      rw [nicheTopArc_of_late hηs]
      exact B_y_nonneg ⟨hηs.le, hs.2⟩

theorem nicheTopArc_y_pos {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) T) :
    0 < (nicheTopArc s).2 := by
  by_cases hθ : s ≤ params.theta
  · rw [nicheTopArc_of_le_theta hθ]
    exact D_y_pos ⟨hs.1, hθ⟩
  · have hθs : params.theta < s := lt_of_not_ge hθ
    by_cases hη : s ≤ eta
    · rw [nicheTopArc_of_middle hθs hη]
      exact path_core_y_pos (coreReverseTime_mem ⟨hθs.le, hη⟩)
    · have hηs : eta < s := lt_of_not_ge hη
      rw [nicheTopArc_of_late hηs]
      exact B_y_pos ⟨hηs.le, hs.2⟩

theorem nicheTopArc_zero : nicheTopArc 0 = D 0 := by
  exact nicheTopArc_of_le_theta theta_pos.le

theorem nicheTopArc_T : nicheTopArc T = B T := by
  exact nicheTopArc_of_late eta_lt_T

theorem coreReverseTime_image :
    coreReverseTime '' Icc params.theta eta = Icc params.phi tau := by
  simpa [coreReverseTime_theta, coreReverseTime_eta] using
    coreReverseTime_continuous.continuousOn.image_Icc_of_antitoneOn
      theta_lt_eta.le
      (coreReverseTime_strictAnti.antitone.antitoneOn (Icc params.theta eta))

/-- The glued arc has exactly the three curve images, with no additional
points introduced by the reparametrization. -/
theorem nicheTopArc_image :
    curveImage nicheTopArc (Icc (0 : ℝ) T) =
      curveImage D (Icc (0 : ℝ) params.theta) ∪
      curveImage (Romik.path params) (Icc params.phi tau) ∪
      curveImage B (Icc eta T) := by
  classical
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    by_cases hθ : s ≤ params.theta
    · left; left
      exact ⟨s, ⟨hs.1, hθ⟩, (nicheTopArc_of_le_theta hθ).symm⟩
    · have hθs : params.theta < s := lt_of_not_ge hθ
      by_cases hη : s ≤ eta
      · left; right
        exact ⟨coreReverseTime s, coreReverseTime_mem ⟨hθs.le, hη⟩,
          (nicheTopArc_of_middle hθs hη).symm⟩
      · right
        have hηs : eta < s := lt_of_not_ge hη
        exact ⟨s, ⟨hηs.le, hs.2⟩, (nicheTopArc_of_late hηs).symm⟩
  · rintro ((⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩) | ⟨s, hs, rfl⟩)
    · exact ⟨s, ⟨hs.1, le_trans hs.2 theta_lt_T.le⟩,
        nicheTopArc_of_le_theta hs.2⟩
    · rw [← coreReverseTime_image] at ht
      rcases ht with ⟨s, hs, rfl⟩
      by_cases hst : s = params.theta
      · subst s
        refine ⟨params.theta, ⟨theta_pos.le, theta_lt_T.le⟩, ?_⟩
        rw [nicheTopArc_of_le_theta le_rfl, coreReverseTime_theta]
        exact D_theta_eq_path_tau
      · have hθs : params.theta < s := lt_of_le_of_ne hs.1 (Ne.symm hst)
        exact ⟨s, ⟨le_trans theta_pos.le hs.1,
          le_trans hs.2 eta_lt_T.le⟩,
          nicheTopArc_of_middle hθs hs.2⟩
    · by_cases hse : s = eta
      · subst s
        refine ⟨eta, ⟨le_trans theta_pos.le theta_lt_eta.le, eta_lt_T.le⟩, ?_⟩
        rw [nicheTopArc_of_middle theta_lt_eta le_rfl, coreReverseTime_eta]
        exact B_eta_eq_path_phi.symm
      · have hηs : eta < s := lt_of_le_of_ne hs.1 (Ne.symm hse)
        exact ⟨s, ⟨le_trans (le_trans theta_pos.le theta_lt_eta.le) hs.1, hs.2⟩,
          nicheTopArc_of_late hηs⟩



/-- A vertically filled strict subgraph over a compact interval. -/
def strictSubgraphRegion (a b : ℝ) (H : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 < H p.1}

/-- The closed vertical fill associated with `strictSubgraphRegion`. -/
def closedSubgraphRegion (a b : ℝ) (H : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ 0 ≤ p.2 ∧ p.2 ≤ H p.1}

/-- The base together with the graph of the roof. -/
def strictSubgraphBoundary (a b : ℝ) (H : ℝ → ℝ) : Set Point :=
  {p | p.1 ∈ Icc a b ∧ (p.2 = 0 ∨ p.2 = H p.1)}

private theorem strictSubgraphRegion_as_image
    {a b : ℝ} {H : ℝ → ℝ} (hab : a < b)
    (hHpos : ∀ x ∈ Ioo a b, 0 < H x)
    (ha : H a = 0) (hb : H b = 0) :
    (fun z : ℝ × ℝ => (z.1, z.2 * H z.1)) ''
        (Ioo a b ×ˢ Ico (0 : ℝ) 1) =
      strictSubgraphRegion a b H := by
  classical
  ext p
  constructor
  · rintro ⟨z, ⟨hzx, hzs⟩, rfl⟩
    have htop := hHpos z.1 hzx
    refine ⟨⟨hzx.1.le, hzx.2.le⟩, ?_, ?_⟩
    · exact mul_nonneg hzs.1 htop.le
    · exact mul_lt_of_lt_one_left htop hzs.2
  · rintro ⟨hx, hy0, hy⟩
    have hxa : a < p.1 := by
      rcases hx.1.eq_or_lt with h | h
      · rw [← h, ha] at hy
        linarith
      · exact h
    have hxb : p.1 < b := by
      rcases hx.2.eq_or_lt with h | h
      · rw [h, hb] at hy
        linarith
      · exact h
    have htop := hHpos p.1 ⟨hxa, hxb⟩
    let s : ℝ := p.2 / H p.1
    have hs : s ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg hy0 htop.le
      · exact (div_lt_one htop).2 hy
    refine ⟨(p.1, s), ⟨⟨hxa, hxb⟩, hs⟩, ?_⟩
    apply Prod.ext
    · rfl
    · dsimp [s]
      field_simp [ne_of_gt htop]

private theorem closedSubgraphRegion_as_image
    {a b : ℝ} {H : ℝ → ℝ}
    (hHnonneg : ∀ x ∈ Icc a b, 0 ≤ H x) :
    (fun z : ℝ × ℝ => (z.1, z.2 * H z.1)) ''
        (Icc a b ×ˢ Icc (0 : ℝ) 1) =
      closedSubgraphRegion a b H := by
  classical
  ext p
  constructor
  · rintro ⟨z, ⟨hzx, hzs⟩, rfl⟩
    have htop := hHnonneg z.1 hzx
    refine ⟨hzx, mul_nonneg hzs.1 htop, ?_⟩
    exact mul_le_of_le_one_left htop hzs.2
  · rintro ⟨hx, hy0, hy⟩
    have htop := hHnonneg p.1 hx
    by_cases hzero : H p.1 = 0
    · have hpy : p.2 = 0 := by linarith
      refine ⟨(p.1, 0), ⟨hx, by norm_num⟩, ?_⟩
      apply Prod.ext
      · rfl
      · simpa only [zero_mul] using hpy.symm
    · have htop' : 0 < H p.1 := lt_of_le_of_ne htop (Ne.symm hzero)
      let s : ℝ := p.2 / H p.1
      have hs : s ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg hy0 htop'.le
        · exact (div_le_one htop').2 hy
      refine ⟨(p.1, s), ⟨hx, hs⟩, ?_⟩
      apply Prod.ext
      · rfl
      · dsimp [s]
        field_simp [hzero]

theorem closure_strictSubgraphRegion
    {a b : ℝ} {H : ℝ → ℝ} (hab : a < b)
    (hH : Continuous H)
    (hHnonneg : ∀ x ∈ Icc a b, 0 ≤ H x)
    (hHpos : ∀ x ∈ Ioo a b, 0 < H x)
    (ha : H a = 0) (hb : H b = 0) :
    closure (strictSubgraphRegion a b H) = closedSubgraphRegion a b H := by
  let P : Set (ℝ × ℝ) := Ioo a b ×ˢ Ico (0 : ℝ) 1
  let Q : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (0 : ℝ) 1
  let F : ℝ × ℝ → Point := fun z => (z.1, z.2 * H z.1)
  have hclP : closure P = Q := by
    simp only [P, Q, closure_prod_eq, closure_Ioo hab.ne,
      closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
  have hQcompact : IsCompact Q := by
    exact isCompact_Icc.prod isCompact_Icc
  have hF : Continuous F := by
    dsimp [F]
    exact continuous_fst.prodMk (continuous_snd.mul (hH.comp continuous_fst))
  have hPcompact : IsCompact (closure P) := by
    rw [hclP]
    exact hQcompact
  calc
    closure (strictSubgraphRegion a b H) = closure (F '' P) := by
      rw [strictSubgraphRegion_as_image hab hHpos ha hb]
    _ = F '' closure P :=
      (image_closure_of_isCompact hPcompact hF.continuousOn).symm
    _ = F '' Q := by rw [hclP]
    _ = closedSubgraphRegion a b H :=
      closedSubgraphRegion_as_image hHnonneg

theorem interior_strictSubgraphRegion
    {a b : ℝ} {H : ℝ → ℝ} (hH : Continuous H) :
    interior (strictSubgraphRegion a b H) =
      {p | p.1 ∈ Ioo a b ∧ 0 < p.2 ∧ p.2 < H p.1} := by
  let O : Set Point := {p | p.1 ∈ Ioo a b ∧ 0 < p.2 ∧ p.2 < H p.1}
  have hOopen : IsOpen O := by
    dsimp [O]
    exact (isOpen_Ioo.preimage continuous_fst).inter
      ((isOpen_Ioi.preimage continuous_snd).inter
        (isOpen_lt continuous_snd (hH.comp continuous_fst)))
  apply Set.Subset.antisymm
  · intro p hp
    have hpS := interior_subset hp
    have hxmono : strictSubgraphRegion a b H ⊆ Icc a b ×ˢ (Set.univ : Set ℝ) := by
      intro q hq
      exact ⟨hq.1, Set.mem_univ _⟩
    have hymono : strictSubgraphRegion a b H ⊆ (Set.univ : Set ℝ) ×ˢ Ici 0 := by
      intro q hq
      exact ⟨Set.mem_univ _, hq.2.1⟩
    have hx := interior_mono hxmono hp
    have hy := interior_mono hymono hp
    rw [interior_prod_eq, interior_Icc, interior_univ] at hx
    rw [interior_prod_eq, interior_univ, interior_Ici] at hy
    exact ⟨hx.1, hy.2, hpS.2.2⟩
  · apply interior_maximal
    · intro p hp
      exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, hp.2.1.le, hp.2.2⟩
    · exact hOopen

/-- The frontier of a positive strict vertical subgraph consists exactly of
its roof and its base. -/
theorem frontier_strictSubgraphRegion
    {a b : ℝ} {H : ℝ → ℝ} (hab : a < b)
    (hH : Continuous H)
    (hHnonneg : ∀ x ∈ Icc a b, 0 ≤ H x)
    (hHpos : ∀ x ∈ Ioo a b, 0 < H x)
    (ha : H a = 0) (hb : H b = 0) :
    frontier (strictSubgraphRegion a b H) = strictSubgraphBoundary a b H := by
  rw [frontier, closure_strictSubgraphRegion hab hH hHnonneg hHpos ha hb,
    interior_strictSubgraphRegion hH]
  ext p
  simp only [Set.mem_diff, closedSubgraphRegion, strictSubgraphBoundary,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨hx, hy0, hyH⟩, hnot⟩
    refine ⟨hx, ?_⟩
    by_cases hya : p.2 = 0
    · exact Or.inl hya
    right
    by_contra hyne
    apply hnot
    refine ⟨?_, lt_of_le_of_ne hy0 (Ne.symm hya), lt_of_le_of_ne hyH hyne⟩
    constructor
    · apply lt_of_le_of_ne hx.1
      intro heq
      have hp0 : p.2 = 0 := by
        rw [← heq, ha] at hyH
        linarith
      exact hya hp0
    · apply lt_of_le_of_ne hx.2
      intro heq
      have hp0 : p.2 = 0 := by
        rw [heq, hb] at hyH
        linarith
      exact hya hp0
  · rintro ⟨hx, hbase | hroof⟩
    · refine ⟨⟨hx, ?_, ?_⟩, ?_⟩
      · simpa [hbase]
      · simpa [hbase] using hHnonneg p.1 hx
      · intro hstrict
        rw [hbase] at hstrict
        exact (lt_irrefl (0 : ℝ)) hstrict.2.1
    · refine ⟨⟨hx, ?_, hroof.le⟩, ?_⟩
      · rw [hroof]
        exact hHnonneg p.1 hx
      · intro hstrict
        exact (lt_irrefl (H p.1)) (hroof ▸ hstrict.2.2)

/-! ## Turning a monotone roof arc into a global continuous graph -/

noncomputable def horizontalOrderIso
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Icc a b ≃o Icc (γ a).1 (γ b).1 := by
  have himage :
      (fun t ↦ (γ t).1) '' Icc a b = Icc (γ a).1 (γ b).1 :=
    hγ.fst.image_Icc_of_monotoneOn hab.le hx.monotoneOn
  exact
    (StrictMonoOn.orderIso (fun t ↦ (γ t).1) (Icc a b) hx).trans
      (OrderIso.setCongr _ _ himage)

@[simp]
theorem horizontalOrderIso_apply_val
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b))
    (t : Icc a b) :
    ((horizontalOrderIso γ hab hγ hx t : Icc (γ a).1 (γ b).1) : ℝ) =
      (γ t.1).1 := by
  rfl

noncomputable def roofOnHorizontalRange
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Icc (γ a).1 (γ b).1 → ℝ :=
  fun X ↦ (γ ((horizontalOrderIso γ hab hγ hx).symm X).1).2

theorem continuous_roofOnHorizontalRange
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Continuous (roofOnHorizontalRange γ hab hγ hx) := by
  exact continuous_snd.comp
    (hγ.domRestrict.comp (horizontalOrderIso γ hab hγ hx).symm.continuous)

private theorem horizontal_endpoints_le
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    (γ a).1 ≤ (γ b).1 :=
  (hx (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab).le

noncomputable def monotoneCurveRoof
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) : ℝ → ℝ :=
  Set.IccExtend (horizontal_endpoints_le γ hab hx)
    (roofOnHorizontalRange γ hab hγ hx)

theorem continuous_monotoneCurveRoof
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    Continuous (monotoneCurveRoof γ hab hγ hx) := by
  exact (continuous_roofOnHorizontalRange γ hab hγ hx).Icc_extend'

private theorem horizontal_mem_range
    (γ : ℝ → Point) {a b t : ℝ} (hab : a < b)
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b))
    (ht : t ∈ Icc a b) :
    (γ t).1 ∈ Icc (γ a).1 (γ b).1 := by
  exact ⟨hx.monotoneOn (left_mem_Icc.2 hab.le) ht ht.1,
    hx.monotoneOn ht (right_mem_Icc.2 hab.le) ht.2⟩

theorem monotoneCurveRoof_at
    (γ : ℝ → Point) {a b t : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b))
    (ht : t ∈ Icc a b) :
    monotoneCurveRoof γ hab hγ hx (γ t).1 = (γ t).2 := by
  let e := horizontalOrderIso γ hab hγ hx
  have htr := horizontal_mem_range γ hab hx ht
  have heq : e ⟨t, ht⟩ = ⟨(γ t).1, htr⟩ := by
    apply Subtype.ext
    rfl
  have hinv : e.symm ⟨(γ t).1, htr⟩ = ⟨t, ht⟩ := by
    rw [← heq, e.symm_apply_apply]
  rw [monotoneCurveRoof, Set.IccExtend_of_mem _ _ htr]
  change (γ (e.symm ⟨(γ t).1, htr⟩).1).2 = (γ t).2
  rw [hinv]

theorem verticalFill_eq_strictSubgraphRegion
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    verticalFill γ (Icc a b) =
      strictSubgraphRegion (γ a).1 (γ b).1
        (monotoneCurveRoof γ hab hγ hx) := by
  ext p
  constructor
  · rintro ⟨t, ht, hxt, hy0, hy⟩
    have htr := horizontal_mem_range γ hab hx ht
    refine ⟨?_, hy0, ?_⟩
    · simpa [hxt] using htr
    · rw [hxt, monotoneCurveRoof_at γ hab hγ hx ht]
      exact hy
  · rintro ⟨hpx, hy0, hy⟩
    let e := horizontalOrderIso γ hab hγ hx
    let ts : Icc a b := e.symm ⟨p.1, hpx⟩
    have heval := congrArg Subtype.val
      ((horizontalOrderIso γ hab hγ hx).apply_symm_apply ⟨p.1, hpx⟩)
    have hxt : (γ ts.1).1 = p.1 := by
      change
        (γ ((horizontalOrderIso γ hab hγ hx).symm ⟨p.1, hpx⟩).1).1 = p.1
      simpa only [horizontalOrderIso_apply_val] using heval
    refine ⟨ts.1, ts.2, hxt.symm, hy0, ?_⟩
    rw [← hxt, monotoneCurveRoof_at γ hab hγ hx ts.2] at hy
    exact hy

theorem curveImage_eq_roofGraph
    (γ : ℝ → Point) {a b : ℝ} (hab : a < b)
    (hγ : ContinuousOn γ (Icc a b))
    (hx : StrictMonoOn (fun t ↦ (γ t).1) (Icc a b)) :
    curveImage γ (Icc a b) =
      {p | p.1 ∈ Icc (γ a).1 (γ b).1 ∧
        p.2 = monotoneCurveRoof γ hab hγ hx p.1} := by
  ext p
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨horizontal_mem_range γ hab hx ht,
      (monotoneCurveRoof_at γ hab hγ hx ht).symm⟩
  · rintro ⟨hpx, hpy⟩
    let e := horizontalOrderIso γ hab hγ hx
    let ts : Icc a b := e.symm ⟨p.1, hpx⟩
    have heval := congrArg Subtype.val
      ((horizontalOrderIso γ hab hγ hx).apply_symm_apply ⟨p.1, hpx⟩)
    have hxt : (γ ts.1).1 = p.1 := by
      change
        (γ ((horizontalOrderIso γ hab hγ hx).symm ⟨p.1, hpx⟩).1).1 = p.1
      simpa only [horizontalOrderIso_apply_val] using heval
    refine ⟨ts.1, ts.2, ?_⟩
    apply Prod.ext
    · exact hxt
    · calc
        (γ ts.1).2 = monotoneCurveRoof γ hab hγ hx (γ ts.1).1 :=
          (monotoneCurveRoof_at γ hab hγ hx ts.2).symm
        _ = monotoneCurveRoof γ hab hγ hx p.1 := by rw [hxt]
        _ = p.2 := hpy.symm

private theorem T_pos_frontier : 0 < T := by
  dsimp [T]
  nlinarith [Real.pi_pos]

/-- The continuous roof function determined by the complete niche top arc. -/
noncomputable def nicheRoof : ℝ → ℝ :=
  monotoneCurveRoof nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono

theorem nicheRoof_continuous : Continuous nicheRoof :=
  continuous_monotoneCurveRoof nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono

theorem nicheRoof_at_topArc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    nicheRoof (nicheTopArc s).1 = (nicheTopArc s).2 :=
  monotoneCurveRoof_at nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono hs

theorem nicheRoof_nonneg {X : ℝ}
    (hX : X ∈ Icc (D 0).1 (B T).1) : 0 ≤ nicheRoof X := by
  have hends : Icc (D 0).1 (B T).1 =
      Icc (nicheTopArc 0).1 (nicheTopArc T).1 := by
    rw [nicheTopArc_zero, nicheTopArc_T]
  rw [hends] at hX
  let e := horizontalOrderIso nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  let s : Icc (0 : ℝ) T := e.symm ⟨X, hX⟩
  have heval := congrArg Subtype.val
    ((horizontalOrderIso nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn
      nicheTopArc_fst_strictMono).apply_symm_apply ⟨X, hX⟩)
  have hxarc : (nicheTopArc s.1).1 = X := by
    change
      (nicheTopArc ((horizontalOrderIso nicheTopArc T_pos_frontier
        nicheTopArc_continuous.continuousOn
        nicheTopArc_fst_strictMono).symm ⟨X, hX⟩).1).1 = X
    simpa only [horizontalOrderIso_apply_val] using heval
  rw [← hxarc, nicheRoof_at_topArc s.2]
  exact nicheTopArc_y_nonneg s.2

theorem nicheRoof_pos {X : ℝ}
    (hX : X ∈ Ioo (D 0).1 (B T).1) : 0 < nicheRoof X := by
  have hends : Ioo (D 0).1 (B T).1 =
      Ioo (nicheTopArc 0).1 (nicheTopArc T).1 := by
    rw [nicheTopArc_zero, nicheTopArc_T]
  rw [hends] at hX
  let e := horizontalOrderIso nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  have hXcc : X ∈ Icc (nicheTopArc 0).1 (nicheTopArc T).1 :=
    ⟨hX.1.le, hX.2.le⟩
  let s : Icc (0 : ℝ) T := e.symm ⟨X, hXcc⟩
  have heval := congrArg Subtype.val
    ((horizontalOrderIso nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn
      nicheTopArc_fst_strictMono).apply_symm_apply ⟨X, hXcc⟩)
  have hxarc : (nicheTopArc s.1).1 = X := by
    change
      (nicheTopArc ((horizontalOrderIso nicheTopArc T_pos_frontier
        nicheTopArc_continuous.continuousOn
        nicheTopArc_fst_strictMono).symm ⟨X, hXcc⟩).1).1 = X
    simpa only [horizontalOrderIso_apply_val] using heval
  have hs0 : 0 < s.1 := by
    by_contra hn
    have hszero : s.1 = 0 := le_antisymm (le_of_not_gt hn) s.2.1
    have hxzero : (nicheTopArc 0).1 = X := by
      simpa [hszero] using hxarc
    exact (ne_of_lt hX.1) hxzero
  have hsT : s.1 < T := by
    by_contra hn
    have hsT' : s.1 = T := le_antisymm s.2.2 (le_of_not_gt hn)
    have hxT : (nicheTopArc T).1 = X := by
      simpa [hsT'] using hxarc
    exact (ne_of_gt hX.2) hxT
  rw [← hxarc, nicheRoof_at_topArc s.2]
  exact nicheTopArc_y_pos ⟨hs0, hsT⟩

theorem nicheRoof_left : nicheRoof (D 0).1 = 0 := by
  rw [← nicheTopArc_zero, nicheRoof_at_topArc (left_mem_Icc.2 T_pos_frontier.le),
    nicheTopArc_zero]
  exact D_zero_y_zero

theorem nicheRoof_right : nicheRoof (B T).1 = 0 := by
  rw [← nicheTopArc_T, nicheRoof_at_topArc (right_mem_Icc.2 T_pos_frontier.le),
    nicheTopArc_T]
  exact B_T_y_zero

private theorem nicheTopArc_verticalFill :
    verticalFill nicheTopArc (Icc (0 : ℝ) T) = certifiedNicheRegion := by
  classical
  ext q
  constructor
  · rintro ⟨s, hs, hx, hy0, hy⟩
    have htop : nicheTopArc s ∈
        curveImage D (Icc (0 : ℝ) params.theta) ∪
        curveImage (Romik.path params) (Icc params.phi tau) ∪
        curveImage B (Icc eta T) := by
      rw [← nicheTopArc_image]
      exact ⟨s, hs, rfl⟩
    rcases htop with (⟨r, hr, her⟩ | ⟨r, hr, her⟩) | ⟨r, hr, her⟩
    · exact Or.inl (Or.inl ⟨r, hr, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩)
    · exact Or.inl (Or.inr ⟨r, hr, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩)
    · exact Or.inr ⟨r, hr, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩
  · intro hq
    rcases hq with (⟨r, hr, hx, hy0, hy⟩ | ⟨r, hr, hx, hy0, hy⟩) |
      ⟨r, hr, hx, hy0, hy⟩
    · have htop : D r ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [nicheTopArc_image]
        exact Or.inl (Or.inl ⟨r, hr, rfl⟩)
      rcases htop with ⟨s, hs, her⟩
      exact ⟨s, hs, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩
    · have htop : Romik.path params r ∈
          curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [nicheTopArc_image]
        exact Or.inl (Or.inr ⟨r, hr, rfl⟩)
      rcases htop with ⟨s, hs, her⟩
      exact ⟨s, hs, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩
    · have htop : B r ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [nicheTopArc_image]
        exact Or.inr ⟨r, hr, rfl⟩
      rcases htop with ⟨s, hs, her⟩
      exact ⟨s, hs, by simpa [her] using hx,
        hy0, by simpa [her] using hy⟩

/-- The three certified fills form one strict subgraph. -/
theorem certifiedNicheRegion_eq_strictSubgraph :
    certifiedNicheRegion =
      strictSubgraphRegion (D 0).1 (B T).1 nicheRoof := by
  rw [← nicheTopArc_verticalFill,
    verticalFill_eq_strictSubgraphRegion nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono,
    nicheTopArc_zero, nicheTopArc_T]
  rfl

private theorem lineSegment_horizontal
    {a b : Point} (hab : a.1 < b.1) (ha : a.2 = 0) (hb : b.2 = 0) :
    lineSegment a b = {p | p.1 ∈ Icc a.1 b.1 ∧ p.2 = 0} := by
  classical
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    constructor
    · have hba : 0 ≤ b.1 - a.1 := sub_nonneg.mpr hab.le
      constructor
      · have hmul : 0 ≤ r * (b.1 - a.1) := mul_nonneg hr.1 hba
        nlinarith [hmul]
      · have hmul : 0 ≤ (1 - r) * (b.1 - a.1) :=
          mul_nonneg (sub_nonneg.mpr hr.2) hba
        nlinarith [hmul]
    · simp [ha, hb]
  · rintro ⟨hx, hy⟩
    let r : ℝ := (p.1 - a.1) / (b.1 - a.1)
    have hden : 0 < b.1 - a.1 := sub_pos.mpr hab
    have hr : r ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
      · exact (div_le_one hden).2 (by linarith [hx.2])
    refine ⟨r, hr, ?_⟩
    apply Prod.ext
    · dsimp [r]
      field_simp [ne_of_gt hden]
      ring
    · simp [ha, hb, hy]

private theorem niche_horizontal_endpoints : (D 0).1 < (B T).1 := by
  have h := nicheTopArc_fst_strictMono
    (left_mem_Icc.2 T_pos_frontier.le)
    (right_mem_Icc.2 T_pos_frontier.le) T_pos_frontier
  simpa [nicheTopArc_zero, nicheTopArc_T] using h

theorem claimedNicheBoundary_eq_subgraphBoundary :
    claimedNicheBoundary =
      strictSubgraphBoundary (D 0).1 (B T).1 nicheRoof := by
  have hbase := lineSegment_horizontal niche_horizontal_endpoints
    D_zero_y_zero B_T_y_zero
  have hroof := curveImage_eq_roofGraph nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  rw [nicheTopArc_zero, nicheTopArc_T] at hroof
  ext p
  constructor
  · intro hp
    change p ∈ lineSegment (D 0) (B T) ∪
      curveImage B (Icc eta T) ∪
      curveImage (Romik.path params) (Icc params.phi tau) ∪
      curveImage D (Icc 0 params.theta) at hp
    have hp' : p ∈ lineSegment (D 0) (B T) ∨
        p ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
      rw [nicheTopArc_image]
      rcases hp with ((hb | hB) | hpath) | hD
      · exact Or.inl hb
      · exact Or.inr (Or.inr hB)
      · exact Or.inr (Or.inl (Or.inr hpath))
      · exact Or.inr (Or.inl (Or.inl hD))
    rcases hp' with hb | hr
    · rw [hbase] at hb
      exact ⟨hb.1, Or.inl hb.2⟩
    · rw [hroof] at hr
      exact ⟨hr.1, Or.inr hr.2⟩
  · rintro ⟨hx, hbase' | hroof'⟩
    · have hb : p ∈ lineSegment (D 0) (B T) := by
        rw [hbase]
        exact ⟨hx, hbase'⟩
      change p ∈ lineSegment (D 0) (B T) ∪
        curveImage B (Icc eta T) ∪
        curveImage (Romik.path params) (Icc params.phi tau) ∪
        curveImage D (Icc 0 params.theta)
      exact Or.inl (Or.inl (Or.inl hb))
    · have hr : p ∈ curveImage nicheTopArc (Icc (0 : ℝ) T) := by
        rw [hroof]
        exact ⟨hx, hroof'⟩
      rw [nicheTopArc_image] at hr
      change p ∈ lineSegment (D 0) (B T) ∪
        curveImage B (Icc eta T) ∪
        curveImage (Romik.path params) (Icc params.phi tau) ∪
        curveImage D (Icc 0 params.theta)
      rcases hr with (hD | hpath) | hB
      · exact Or.inr hD
      · exact Or.inl (Or.inr hpath)
      · exact Or.inl (Or.inl (Or.inr hB))

/-- Direct frontier calculation for the certified three-fill region. -/
theorem frontier_certifiedNicheRegion :
    frontier certifiedNicheRegion = claimedNicheBoundary := by
  rw [certifiedNicheRegion_eq_strictSubgraph,
    frontier_strictSubgraphRegion niche_horizontal_endpoints nicheRoof_continuous
      (by intro X hX; exact nicheRoof_nonneg hX)
      (by intro X hX; exact nicheRoof_pos hX)
      nicheRoof_left nicheRoof_right,
    ← claimedNicheBoundary_eq_subgraphBoundary]

/-! ## Literal instantaneous wedges lie below the certified graph -/

private theorem sin_pos_frontier {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.sin t :=
  Real.sin_pos_of_pos_of_lt_pi ht.1
    (lt_trans ht.2 (by dsimp [T]; nlinarith [Real.pi_pos]))

private theorem cos_pos_frontier {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    0 < Real.cos t :=
  Real.cos_pos_of_mem_Ioo
    ⟨by nlinarith [Real.pi_pos, ht.1], by simpa [T] using ht.2⟩

private theorem instantRoof_le_of_u_outside {t X Y : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hu : 0 ≤ dot ((X, Y) - Romik.path params t) (u t)) :
    instantRoof t X ≤ Y := by
  apply le_trans (min_le_left _ _)
  unfold bRoof
  apply (div_le_iff₀ (sin_pos_frontier ht)).2
  dsimp [dot, u] at hu ⊢
  nlinarith

private theorem instantRoof_le_of_v_outside {t X Y : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T)
    (hv : 0 ≤ dot ((X, Y) - Romik.path params t) (v t)) :
    instantRoof t X ≤ Y := by
  apply le_trans (min_le_right _ _)
  unfold dRoof
  apply (div_le_iff₀ (cos_pos_frontier ht)).2
  dsimp [dot, v] at hv ⊢
  nlinarith

/-- A core path point dominates every instantaneous roof at its horizontal
coordinate.  This is the exact geometric content of the two no-hidden
inequalities. -/
theorem core_is_upper_envelope {r : ℝ} (hr : r ∈ Icc params.phi tau) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      instantRoof t (Romik.path params r).1 ≤ (Romik.path params r).2 := by
  intro t ht
  by_cases htr : r ≤ t
  · have hU : 0 ≤ dot (Romik.path params r - Romik.path params t) (u t) :=
      noHiddenU_direct r ⟨hr.1, le_trans hr.2 tau_lt_T.le⟩ t
        ⟨htr, ht.2.le⟩
    exact instantRoof_le_of_u_outside ht hU
  · have htr' : t ≤ r := le_of_not_ge htr
    have hV : 0 ≤ dot (Romik.path params r - Romik.path params t) (v t) :=
      noHiddenV_direct t ⟨ht.1.le, le_trans htr' hr.2⟩ r ⟨htr', hr.2⟩
    exact instantRoof_le_of_v_outside ht hV

/-- Every point of the glued certified roof dominates every instantaneous
wall roof at its horizontal coordinate. -/
theorem nicheTopArc_is_upper_envelope {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Ioo (0 : ℝ) T) :
    instantRoof t (nicheTopArc s).1 ≤ (nicheTopArc s).2 := by
  by_cases hθ : s ≤ params.theta
  · rw [nicheTopArc_of_le_theta hθ]
    rcases D_boundary_outside ht ⟨hs.1, hθ⟩ with hu | hv
    · exact instantRoof_le_of_u_outside ht hu
    · exact instantRoof_le_of_v_outside ht hv
  · have hθs : params.theta < s := lt_of_not_ge hθ
    by_cases hη : s ≤ eta
    · rw [nicheTopArc_of_middle hθs hη]
      exact core_is_upper_envelope (coreReverseTime_mem ⟨hθs.le, hη⟩) t ht
    · have hηs : eta < s := lt_of_not_ge hη
      rw [nicheTopArc_of_late hηs]
      rcases B_boundary_outside ht ⟨hηs.le, hs.2⟩ with hu | hv
      · exact instantRoof_le_of_u_outside ht hu
      · exact instantRoof_le_of_v_outside ht hv

private theorem niche_point_horizontal_range {q : Point}
    (hq : q ∈ Romik.niche params) : q.1 ∈ Ioo (D 0).1 (B T).1 := by
  rcases hq with ⟨hqFan, t, ht, hquad⟩
  have hq0 : 0 ≤ q.2 := by simpa [capFan] using hqFan
  have hwalls := hquad
  change
    dot (q - Romik.path params t) (u t) < 0 ∧
      dot (q - Romik.path params t) (v t) < 0 at hwalls
  have hBT := B_T_u_nonneg ht
  have hqBT : dot (q - B T) (u t) < 0 := by
    unfold dot at hwalls hBT ⊢
    dsimp [u] at hwalls hBT ⊢
    linarith
  have hright : q.1 < (B T).1 := by
    by_contra hn
    have hdx : 0 ≤ q.1 - (B T).1 := sub_nonneg.mpr (le_of_not_gt hn)
    have hxterm : 0 ≤ (q.1 - (B T).1) * Real.cos t :=
      mul_nonneg hdx (cos_pos_frontier ht).le
    have hyterm : 0 ≤ (q.2 - (B T).2) * Real.sin t := by
      rw [B_T_y_zero]
      simpa using mul_nonneg hq0 (sin_pos_frontier ht).le
    dsimp [dot, u] at hqBT
    linarith
  have hD := D_zero_v_nonneg ht
  have hqD : dot (q - D 0) (v t) < 0 := by
    unfold dot at hwalls hD ⊢
    dsimp [v] at hwalls hD ⊢
    linarith
  have hleft : (D 0).1 < q.1 := by
    by_contra hn
    have hdx : q.1 - (D 0).1 ≤ 0 := sub_nonpos.mpr (le_of_not_gt hn)
    have hxterm : 0 ≤ (q.1 - (D 0).1) * (-Real.sin t) :=
      mul_nonneg_of_nonpos_of_nonpos hdx (neg_nonpos.mpr (sin_pos_frontier ht).le)
    have hyterm : 0 ≤ (q.2 - (D 0).2) * Real.cos t := by
      rw [D_zero_y_zero]
      simpa using mul_nonneg hq0 (cos_pos_frontier ht).le
    dsimp [dot, v] at hqD
    linarith
  exact ⟨hleft, hright⟩

private theorem niche_subset_certifiedNicheRegion :
    Romik.niche params ⊆ certifiedNicheRegion := by
  intro q hq
  rcases hq with ⟨hqFan, t, ht, hquad⟩
  have hqAll : q ∈ Romik.niche params := ⟨hqFan, t, ht, hquad⟩
  have hXopen := niche_point_horizontal_range hqAll
  have hX : q.1 ∈ Icc (nicheTopArc 0).1 (nicheTopArc T).1 := by
    simpa [nicheTopArc_zero, nicheTopArc_T] using
      (show q.1 ∈ Icc (D 0).1 (B T).1 from ⟨hXopen.1.le, hXopen.2.le⟩)
  let e := horizontalOrderIso nicheTopArc T_pos_frontier
    nicheTopArc_continuous.continuousOn nicheTopArc_fst_strictMono
  let s : Icc (0 : ℝ) T := e.symm ⟨q.1, hX⟩
  have heval := congrArg Subtype.val
    ((horizontalOrderIso nicheTopArc T_pos_frontier
      nicheTopArc_continuous.continuousOn
      nicheTopArc_fst_strictMono).apply_symm_apply ⟨q.1, hX⟩)
  have hxarc : (nicheTopArc s.1).1 = q.1 := by
    change
      (nicheTopArc ((horizontalOrderIso nicheTopArc T_pos_frontier
        nicheTopArc_continuous.continuousOn
        nicheTopArc_fst_strictMono).symm ⟨q.1, hX⟩).1).1 = q.1
    simpa only [horizontalOrderIso_apply_val] using heval
  have hinstant : q.2 < instantRoof t q.1 := by
    have hw := (mem_innerQuadrant_iff_roofs ht).1 hquad
    simpa [instantRoof, lt_min_iff] using hw
  have hupper := nicheTopArc_is_upper_envelope s.2 ht
  have hroofAt := nicheRoof_at_topArc s.2
  have hq0 : 0 ≤ q.2 := by simpa [capFan] using hqFan
  rw [certifiedNicheRegion_eq_strictSubgraph]
  refine ⟨by simpa [nicheTopArc_zero, nicheTopArc_T] using hX, hq0, ?_⟩
  calc
    q.2 < instantRoof t q.1 := hinstant
    _ ≤ (nicheTopArc s.1).2 := by simpa [hxarc] using hupper
    _ = nicheRoof q.1 := by rw [← hroofAt, hxarc]

private theorem certifiedNicheRegion_subset_niche :
    certifiedNicheRegion ⊆ Romik.niche params := by
  intro q hq
  rcases hq with (⟨r, hr, hx, hy0, hy⟩ | ⟨r, hr, hx, hy0, hy⟩) |
    ⟨r, hr, hx, hy0, hy⟩
  · have hmem := vertical_below_D_mem_niche hr hy0 hy
    have heq : q = ((D r).1, q.2) := by
      apply Prod.ext
      · exact hx
      · rfl
    rw [heq]
    exact hmem
  · have hmem := vertical_below_path_mem_niche hr hy0 hy
    have heq : q = ((Romik.path params r).1, q.2) := by
      apply Prod.ext
      · exact hx
      · rfl
    rw [heq]
    exact hmem
  · have hmem := vertical_below_B_mem_niche hr hy0 hy
    have heq : q = ((B r).1, q.2) := by
      apply Prod.ext
      · exact hx
      · rfl
    rw [heq]
    exact hmem

/-- Literal niche equals the three concrete strict vertical fills. -/
theorem niche_eq_certifiedNicheRegion :
    Romik.niche params = certifiedNicheRegion :=
  Set.Subset.antisymm niche_subset_certifiedNicheRegion
    certifiedNicheRegion_subset_niche

/-- Final exact set-valued boundary equality required by Part C. -/
theorem niche_frontier_direct :
    frontier (Romik.niche params) = claimedNicheBoundary := by
  rw [niche_eq_certifiedNicheRegion]
  exact frontier_certifiedNicheRegion

end Stage4
end PartC
end GerverSofa
