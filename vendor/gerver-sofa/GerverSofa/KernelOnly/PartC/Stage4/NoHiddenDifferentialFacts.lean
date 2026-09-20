import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenTurningFacts
import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenContinuityFacts
import Mathlib.Analysis.Convex.Deriv

/-!
# Part C Stage 4: global path derivative and one-turn velocity monotonicity

The path derivative is glued across the four switches using equality of both
the path values and the body-frame velocity coefficients.  The coefficient
derivatives themselves need not match at a switch.  Consequently the fixed
projection is proved antitone phase by phase and then glued order-theoretically.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

private theorem hasDerivAt_if_le_point
    {f g f' g' : ℝ → Point} {c x : ℝ}
    (hf : HasDerivAt f (f' x) x)
    (hg : HasDerivAt g (g' x) x)
    (hvalue : f c = g c)
    (hderiv : f' c = g' c) :
    HasDerivAt (fun y => if y ≤ c then f y else g y)
      (if x ≤ c then f' x else g' x) x := by
  rcases lt_trichotomy x c with hxc | hxc | hxc
  · rw [if_pos hxc.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxc] with y hy
    have hyc : y < c := show y < c from hy
    simp [hyc.le]
  · subst x
    rw [if_pos le_rfl]
    have hleft : HasDerivWithinAt
        (fun y => if y ≤ c then f y else g y) (f' c) (Iic c) c := by
      exact hf.hasDerivWithinAt.congr
        (by
          intro y hy
          have hyc : y ≤ c := show y ≤ c from hy
          simp [hyc])
        (by simp)
    have hright : HasDerivWithinAt
        (fun y => if y ≤ c then f y else g y) (f' c) (Ici c) c := by
      have hg' : HasDerivWithinAt g (f' c) (Ici c) c :=
        hg.hasDerivWithinAt.congr_deriv hderiv.symm
      exact hg'.congr
        (by
          intro y hy
          have hcy : c ≤ y := show c ≤ y from hy
          rcases hcy.eq_or_lt with h | h
          · subst y
            simpa using hvalue
          · simp [not_le.mpr h])
        (by simpa using hvalue)
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using
      hleft.union hright
  · rw [if_neg (not_le.mpr hxc)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxc] with y hy
    have hcy : c < y := show c < y from hy
    simp [not_le.mpr hcy]

/-- The literal five-piece Gerver path is differentiable at the switches as
well as in the phase interiors. -/
theorem path_hasDerivAt_noHidden (x : ℝ) :
    HasDerivAt (Romik.path params)
      (Romik.rot x (alphaBetaAt x)) x := by
  let p45 : ℝ → Point := fun y =>
    if y ≤ tau then Romik.path4 params y else Romik.path5 params y
  let d45 : ℝ → Point := fun y =>
    if y ≤ tau then Romik.rot y (Romik.alphaBeta4 params y)
    else Romik.rot y (Romik.alphaBeta5 params y)
  have hp45 (y : ℝ) : HasDerivAt p45 (d45 y) y := by
    apply hasDerivAt_if_le_point
      (path4_hasDerivAt_public y) (path5_hasDerivAt_public y)
    · simpa [tau, T] using PartB.match45
    · exact congrArg (Romik.rot tau) alphaBeta_match45_direct

  let p345 : ℝ → Point := fun y =>
    if y ≤ eta then Romik.path3 params y else p45 y
  let d345 : ℝ → Point := fun y =>
    if y ≤ eta then Romik.rot y (Romik.alphaBeta3 params y) else d45 y
  have hp345 (y : ℝ) : HasDerivAt p345 (d345 y) y := by
    apply hasDerivAt_if_le_point (path3_hasDerivAt_public y) (hp45 y)
    · simp only [p45, if_pos eta_lt_tau.le]
      simpa [eta, T] using PartB.match34
    · simp only [d45, if_pos eta_lt_tau.le]
      exact congrArg (Romik.rot eta) alphaBeta_match34_direct

  let p2345 : ℝ → Point := fun y =>
    if y ≤ params.theta then Romik.path2 params y else p345 y
  let d2345 : ℝ → Point := fun y =>
    if y ≤ params.theta then Romik.rot y (Romik.alphaBeta2 params y)
    else d345 y
  have hp2345 (y : ℝ) : HasDerivAt p2345 (d2345 y) y := by
    apply hasDerivAt_if_le_point (path2_hasDerivAt_public y) (hp345 y)
    · simp only [p345, if_pos theta_lt_eta.le]
      exact PartB.match23
    · simp only [d345, if_pos theta_lt_eta.le]
      exact congrArg (Romik.rot params.theta) alphaBeta_match23_direct

  let p12345 : ℝ → Point := fun y =>
    if y ≤ params.phi then Romik.path1 params y else p2345 y
  let d12345 : ℝ → Point := fun y =>
    if y ≤ params.phi then Romik.rot y (Romik.alphaBeta1 params y)
    else d2345 y
  have hp12345 : HasDerivAt p12345 (d12345 x) x := by
    apply hasDerivAt_if_le_point (path1_hasDerivAt_public x) (hp2345 x)
    · simp only [p2345, if_pos phi_lt_theta.le]
      exact PartB.match12
    · simp only [d2345, if_pos phi_lt_theta.le]
      exact congrArg (Romik.rot params.phi) alphaBeta_match12_direct

  have hpEq : p12345 = Romik.path params := by
    funext y
    simp only [p45, p345, p2345, p12345, Romik.path, eta, tau, T]
    rfl
  have hdEq : d12345 x = Romik.rot x (alphaBetaAt x) := by
    simp only [d45, d345, d2345, d12345, alphaBetaAt]
    by_cases h1 : x ≤ params.phi
    · simp only [if_pos h1]
    · by_cases h2 : x ≤ params.theta
      · simp only [if_neg h1, if_pos h2]
      · by_cases h3 : x ≤ eta
        · simp only [if_neg h1, if_neg h2, if_pos h3]
        · by_cases h4 : x ≤ tau
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_pos h4]
          · simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4]
  rw [hpEq] at hp12345
  exact hp12345.congr_deriv hdEq

/-- Scalar projection of the corner velocity on the fixed vector `u(t)`. -/
def uVelocity (t r : ℝ) : ℝ :=
  alpha r * Real.cos (t - r) + beta r * Real.sin (t - r)

private def uVelocityPiece (ab : ℝ → Point) (t r : ℝ) : ℝ :=
  (ab r).1 * Real.cos (t - r) + (ab r).2 * Real.sin (t - r)

private theorem square_hasDerivAt_noHidden (r : ℝ) :
    HasDerivAt (fun s : ℝ => s * s) (r + r) r := by
  simpa only [id_eq, one_mul, mul_one] using
    (hasDerivAt_id r).fun_mul (hasDerivAt_id r)

private theorem alpha2_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).1) (-1) r := by
  dsimp [Romik.alphaBeta2]
  have h := (hasDerivAt_const r (1 + 2 * params.b1)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem beta2_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).2)
      (-(1 / 2 : ℝ) * r + params.b1) r := by
  dsimp [Romik.alphaBeta2]
  have hsq := HasDerivAt.const_mul (-(1 / 4 : ℝ))
    (square_hasDerivAt_noHidden r)
  have hlin := HasDerivAt.const_mul params.b1 (hasDerivAt_id r)
  have hraw := (((hsq.fun_add hlin).fun_add (hasDerivAt_const r params.b2)).fun_add
    (hasDerivAt_const r (1 / 2 : ℝ)))
  simpa only [id_eq, mul_assoc] using hraw.congr_deriv (by ring)

private theorem alpha3_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).1) (-1) r := by
  dsimp [Romik.alphaBeta3]
  have h := (hasDerivAt_const r (-1 - params.c2)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem beta3_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).2) (-1) r := by
  dsimp [Romik.alphaBeta3]
  have h := (hasDerivAt_const r (1 + params.c1)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem alpha4_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).1)
      ((1 / 2 : ℝ) * r - params.d1) r := by
  dsimp [Romik.alphaBeta4]
  have hsq := HasDerivAt.const_mul (1 / 4 : ℝ)
    (square_hasDerivAt_noHidden r)
  have hlin := HasDerivAt.const_mul params.d1 (hasDerivAt_id r)
  have hraw := (((hsq.fun_sub hlin).fun_sub (hasDerivAt_const r params.d2)).fun_sub
    (hasDerivAt_const r (1 / 2 : ℝ)))
  simpa only [id_eq, mul_assoc] using hraw.congr_deriv (by ring)

private theorem beta4_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).2) (-1) r := by
  dsimp [Romik.alphaBeta4]
  have h := (hasDerivAt_const r (2 * params.d1 - 1)).fun_sub
    (hasDerivAt_id r)
  exact h.congr_deriv (by ring)

private theorem alpha5_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).1)
      (-2 * params.e1 * Real.cos r - 2 * params.e2 * Real.sin r) r := by
  dsimp [Romik.alphaBeta5]
  have hsin := HasDerivAt.const_mul (2 * params.e1)
    (Real.hasDerivAt_sin r)
  have hcos := HasDerivAt.const_mul (2 * params.e2)
    (Real.hasDerivAt_cos r)
  have hraw := ((hasDerivAt_const r (1 : ℝ)).fun_sub hsin).fun_add hcos
  exact hraw.congr_deriv (by ring)

private theorem beta5_hasDerivAt (r : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).2)
      (-2 * params.e1 * Real.sin r + 2 * params.e2 * Real.cos r) r := by
  dsimp [Romik.alphaBeta5]
  have hcos := HasDerivAt.const_mul (2 * params.e1)
    (Real.hasDerivAt_cos r)
  have hsin := HasDerivAt.const_mul (2 * params.e2)
    (Real.hasDerivAt_sin r)
  have hraw := (hcos.fun_add hsin).fun_sub
    (hasDerivAt_const r (1 / 2 : ℝ))
  exact hraw.congr_deriv (by ring)

private theorem alphaBetaAt_eq_piece2 {r : ℝ}
    (hr : r ∈ Icc params.phi params.theta) :
    alphaBetaAt r = Romik.alphaBeta2 params r := by
  by_cases hphi : r ≤ params.phi
  · have hrphi : r = params.phi := le_antisymm hphi hr.1
    subst r
    simpa [alphaBetaAt] using alphaBeta_match12_direct
  · simp [alphaBetaAt, hphi, hr.2]

private theorem alphaBetaAt_eq_piece3 {r : ℝ}
    (hr : r ∈ Icc params.theta eta) :
    alphaBetaAt r = Romik.alphaBeta3 params r := by
  by_cases htheta : r ≤ params.theta
  · have hrtheta : r = params.theta := le_antisymm htheta hr.1
    subst r
    simp only [alphaBetaAt, if_neg (not_le.mpr phi_lt_theta), if_pos le_rfl]
    exact alphaBeta_match23_direct
  · have hphi : ¬ r ≤ params.phi :=
      not_le.mpr (lt_trans phi_lt_theta (lt_of_not_ge htheta))
    simp [alphaBetaAt, hphi, htheta, hr.2]

private theorem alphaBetaAt_eq_piece4 {r : ℝ}
    (hr : r ∈ Icc eta tau) :
    alphaBetaAt r = Romik.alphaBeta4 params r := by
  by_cases heta : r ≤ eta
  · have hreta : r = eta := le_antisymm heta hr.1
    subst r
    simp only [alphaBetaAt, if_neg (not_le.mpr phi_lt_eta),
      if_neg (not_le.mpr theta_lt_eta), if_pos le_rfl]
    exact alphaBeta_match34_direct
  · have htheta : ¬ r ≤ params.theta :=
      not_le.mpr (lt_trans theta_lt_eta (lt_of_not_ge heta))
    have hphi : ¬ r ≤ params.phi :=
      not_le.mpr (lt_trans phi_lt_theta (lt_of_not_ge htheta))
    simp [alphaBetaAt, hphi, htheta, heta, hr.2]

private theorem alphaBetaAt_eq_piece5 {r : ℝ}
    (hr : r ∈ Icc tau T) :
    alphaBetaAt r = Romik.alphaBeta5 params r := by
  by_cases htau : r ≤ tau
  · have hrtau : r = tau := le_antisymm htau hr.1
    subst r
    simp only [alphaBetaAt, if_neg (not_le.mpr
      (lt_trans phi_lt_theta (lt_trans theta_lt_eta eta_lt_tau))),
      if_neg (not_le.mpr (lt_trans theta_lt_eta eta_lt_tau)),
      if_neg (not_le.mpr eta_lt_tau), if_pos le_rfl]
    exact alphaBeta_match45_direct
  · have heta : ¬ r ≤ eta :=
      not_le.mpr (lt_trans eta_lt_tau (lt_of_not_ge htau))
    have htheta : ¬ r ≤ params.theta :=
      not_le.mpr (lt_trans theta_lt_eta (lt_of_not_ge heta))
    have hphi : ¬ r ≤ params.phi :=
      not_le.mpr (lt_trans phi_lt_theta (lt_of_not_ge htheta))
    simp [alphaBetaAt, hphi, htheta, heta, htau]

private theorem uVelocityPiece_hasDerivAt
    {a b : ℝ → ℝ} {ap bp t r : ℝ}
    (ha : HasDerivAt a ap r) (hb : HasDerivAt b bp r) :
    HasDerivAt
      (fun s => a s * Real.cos (t - s) + b s * Real.sin (t - s))
      ((ap - b r) * Real.cos (t - r) +
        (a r + bp) * Real.sin (t - r)) r := by
  have hsub : HasDerivAt (fun s : ℝ => t - s) (-1) r :=
    by simpa only [id_eq, zero_sub] using
      ((hasDerivAt_const r t).fun_sub (hasDerivAt_id r))
  have hcos : HasDerivAt (fun s : ℝ => Real.cos (t - s))
      (Real.sin (t - r)) r := by
    have h := (Real.hasDerivAt_cos (t - r)).comp r hsub
    exact h.congr_deriv (by ring)
  have hsin : HasDerivAt (fun s : ℝ => Real.sin (t - s))
      (-Real.cos (t - r)) r := by
    have h := (Real.hasDerivAt_sin (t - r)).comp r hsub
    exact h.congr_deriv (by ring)
  have h := (ha.fun_mul hcos).fun_add (hb.fun_mul hsin)
  exact h.congr_deriv (by ring)

private theorem uVelocity_eq_piece2 {t r : ℝ}
    (hr : r ∈ Icc params.phi params.theta) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta2 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece2 hr
  simp only [alpha, beta, h]

private theorem uVelocity_eq_piece3 {t r : ℝ}
    (hr : r ∈ Icc params.theta eta) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta3 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece3 hr
  simp only [alpha, beta, h]

private theorem uVelocity_eq_piece4 {t r : ℝ}
    (hr : r ∈ Icc eta tau) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta4 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece4 hr
  simp only [alpha, beta, h]

private theorem uVelocity_eq_piece5 {t r : ℝ}
    (hr : r ∈ Icc tau T) :
    uVelocity t r = uVelocityPiece (Romik.alphaBeta5 params) t r := by
  unfold uVelocity uVelocityPiece
  have h := alphaBetaAt_eq_piece5 hr
  simp only [alpha, beta, h]

private theorem piece_signs
    {ab : ℝ → Point} {r : ℝ} (hrT : r ∈ Icc params.phi T)
    (heq : alphaBetaAt r = ab r) :
    (ab r).1 ≤ 0 ∧ 0 ≤ (ab r).2 := by
  have ha := alpha_nonpos hrT
  have hb := beta_nonneg hrT
  change (alphaBetaAt r).1 ≤ 0 at ha
  change 0 ≤ (alphaBetaAt r).2 at hb
  rw [heq] at ha hb
  exact ⟨ha, hb⟩

private theorem uVelocity_continuous (t : ℝ) : Continuous (uVelocity t) := by
  unfold uVelocity
  have hsub : Continuous (fun r : ℝ => t - r) :=
    continuous_const.sub continuous_id
  have ha : Continuous alpha := alpha_continuous
  have hb : Continuous beta := beta_continuous
  exact (ha.mul (Real.continuous_cos.comp hsub)).add
    (hb.mul (Real.continuous_sin.comp hsub))

private theorem uVelocity_hasDerivAt_phase2 {t r : ℝ}
    (hr : r ∈ Ioo params.phi params.theta) :
    HasDerivAt (uVelocity t)
      (((-1 : ℝ) - (Romik.alphaBeta2 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta2 params r).1 +
        (-(1/2 : ℝ) * r + params.b1)) * Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha2_hasDerivAt r) (beta2_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece2 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_hasDerivAt_phase3 {t r : ℝ}
    (hr : r ∈ Ioo params.theta eta) :
    HasDerivAt (uVelocity t)
      (((-1 : ℝ) - (Romik.alphaBeta3 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta3 params r).1 - 1) * Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha3_hasDerivAt r) (beta3_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece3 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_hasDerivAt_phase4 {t r : ℝ}
    (hr : r ∈ Ioo eta tau) :
    HasDerivAt (uVelocity t)
      ((((1/2 : ℝ) * r - params.d1) -
        (Romik.alphaBeta4 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta4 params r).1 - 1) * Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha4_hasDerivAt r) (beta4_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece4 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_hasDerivAt_phase5 {t r : ℝ}
    (hr : r ∈ Ioo tau T) :
    HasDerivAt (uVelocity t)
      (((-2 * params.e1 * Real.cos r - 2 * params.e2 * Real.sin r) -
          (Romik.alphaBeta5 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta5 params r).1 +
          (-2 * params.e1 * Real.sin r + 2 * params.e2 * Real.cos r)) *
        Real.sin (t-r)) r := by
  have hd := uVelocityPiece_hasDerivAt (t := t)
    (alpha5_hasDerivAt r) (beta5_hasDerivAt r)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact uVelocity_eq_piece5 (t := t) ⟨hs.1.le, hs.2.le⟩

private theorem uVelocity_phase2_anti {t hi : ℝ}
    (hhi : hi ∈ Icc params.phi params.theta) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc params.phi hi) := by
  let f' : ℝ → ℝ := fun r =>
    (((-1 : ℝ) - (Romik.alphaBeta2 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta2 params r).1 +
        (-(1/2 : ℝ) * r + params.b1)) * Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc params.phi hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo params.phi hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.phi params.theta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase2 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo params.phi hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.phi params.theta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨hir.1.le, le_trans (le_trans hir.2.le hhi.2) theta_lt_T.le⟩)
      (alphaBetaAt_eq_piece2 ⟨hir.1.le,
        le_trans hir.2.le hhi.2⟩)
    have hbp := (phase2_betaPrime_neg hrphase).le
    have hr0 : 0 ≤ r := le_trans phi_pos.le hir.1.le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1, hbp]) hsin)

private theorem uVelocity_phase3_anti {t hi : ℝ}
    (hhi : hi ∈ Icc params.theta eta) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc params.theta hi) := by
  let f' : ℝ → ℝ := fun r =>
    (((-1 : ℝ) - (Romik.alphaBeta3 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta3 params r).1 - 1) * Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc params.theta hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo params.theta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.theta eta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase3 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo params.theta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo params.theta eta :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨(lt_trans phi_lt_theta hir.1).le,
          le_trans (le_trans hir.2.le hhi.2) eta_lt_T.le⟩)
      (alphaBetaAt_eq_piece3 ⟨hir.1.le, le_trans hir.2.le hhi.2⟩)
    have hr0 : 0 ≤ r := le_trans theta_pos.le hir.1.le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1]) hsin)

private theorem uVelocity_phase4_anti {t hi : ℝ}
    (hhi : hi ∈ Icc eta tau) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc eta hi) := by
  let f' : ℝ → ℝ := fun r =>
    ((((1/2 : ℝ) * r - params.d1) -
        (Romik.alphaBeta4 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta4 params r).1 - 1) * Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc eta hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo eta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo eta tau :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase4 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo eta hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo eta tau :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨(lt_trans phi_lt_eta hir.1).le,
          le_trans (le_trans hir.2.le hhi.2) tau_lt_T.le⟩)
      (alphaBetaAt_eq_piece4 ⟨hir.1.le, le_trans hir.2.le hhi.2⟩)
    have hap := (phase4_alphaPrime_neg hrphase).le
    have hr0 : 0 ≤ r := le_trans theta_pos.le (lt_trans theta_lt_eta hir.1).le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2, hap]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1]) hsin)

private theorem uVelocity_phase5_anti {t hi : ℝ}
    (hhi : hi ∈ Icc tau T) (hit : hi ≤ t) (htT : t ≤ T) :
    AntitoneOn (uVelocity t) (Icc tau hi) := by
  let f' : ℝ → ℝ := fun r =>
    (((-2 * params.e1 * Real.cos r - 2 * params.e2 * Real.sin r) -
        (Romik.alphaBeta5 params r).2) * Real.cos (t-r) +
      ((Romik.alphaBeta5 params r).1 +
        (-2 * params.e1 * Real.sin r + 2 * params.e2 * Real.cos r)) *
        Real.sin (t-r))
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := f') (convex_Icc tau hi)
  · exact (uVelocity_continuous t).continuousOn
  · intro r hr
    have hir : r ∈ Ioo tau hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo tau T :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    exact (uVelocity_hasDerivAt_phase5 (t := t) hrphase).hasDerivWithinAt
  · intro r hr
    have hir : r ∈ Ioo tau hi := by simpa only [interior_Icc] using hr
    have hrphase : r ∈ Ioo tau T :=
      ⟨hir.1, lt_of_lt_of_le hir.2 hhi.2⟩
    have hs := piece_signs
      (show r ∈ Icc params.phi T from
        ⟨(lt_trans (lt_trans phi_lt_eta eta_lt_tau) hir.1).le,
          le_trans hir.2.le hhi.2⟩)
      (alphaBetaAt_eq_piece5 ⟨hir.1.le, le_trans hir.2.le hhi.2⟩)
    obtain ⟨hap, hbp⟩ := phase5_coefficientPrime_nonpos hrphase
    have hr0 : 0 ≤ r := le_trans phi_pos.le
      (lt_trans (lt_trans phi_lt_eta eta_lt_tau) hir.1).le
    have hd0 : 0 ≤ t-r := by linarith [hir.2, hit]
    have hdT : t-r ≤ T := by linarith [htT, hr0]
    have hsin : 0 ≤ Real.sin (t-r) := Real.sin_nonneg_of_nonneg_of_le_pi hd0
      (le_trans hdT (by dsimp [T]; linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos (t-r) := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hd0], by simpa only [T] using hdT⟩
    dsimp only [f']
    exact add_nonpos
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.2, hap]) hcos)
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [hs.1, hbp]) hsin)

private theorem antitoneOn_Icc_glue {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hleft : AntitoneOn f (Icc a b))
    (hright : AntitoneOn f (Icc b c)) :
    AntitoneOn f (Icc a c) := by
  intro x hx y hy hxy
  by_cases hyb : y ≤ b
  · exact hleft ⟨hx.1, le_trans hxy hyb⟩ ⟨hy.1, hyb⟩ hxy
  by_cases hbx : b ≤ x
  · exact hright ⟨hbx, le_trans hxy hy.2⟩ ⟨le_trans hbx hxy, hy.2⟩ hxy
  have hxb : x ≤ b := le_of_not_ge hbx
  have hby : b ≤ y := le_of_not_ge hyb
  exact le_trans
    (hright ⟨le_rfl, le_trans hby hy.2⟩ ⟨hby, hy.2⟩ hby)
    (hleft ⟨hx.1, hxb⟩ ⟨hab, le_rfl⟩ hxb)

/-- For fixed terminal time, the projected path velocity is antitone on the
complete ordered no-hidden interval. -/
theorem uVelocity_antitone {t : ℝ} (ht : t ∈ Icc params.phi T) :
    AntitoneOn (uVelocity t) (Icc params.phi t) := by
  by_cases h2 : t ≤ params.theta
  · exact uVelocity_phase2_anti ⟨ht.1, h2⟩ le_rfl ht.2
  have ht2 : params.theta ≤ t := (lt_of_not_ge h2).le
  have hphase2 := uVelocity_phase2_anti
    (t := t) (hi := params.theta) ⟨phi_lt_theta.le, le_rfl⟩ ht2 ht.2
  by_cases h3 : t ≤ eta
  · exact antitoneOn_Icc_glue phi_lt_theta.le ht2 hphase2
      (uVelocity_phase3_anti ⟨ht2, h3⟩ le_rfl ht.2)
  have ht3 : eta ≤ t := (lt_of_not_ge h3).le
  have hphase3 := uVelocity_phase3_anti
    (t := t) (hi := eta) ⟨theta_lt_eta.le, le_rfl⟩ ht3 ht.2
  have h23 := antitoneOn_Icc_glue phi_lt_theta.le theta_lt_eta.le
    hphase2 hphase3
  by_cases h4 : t ≤ tau
  · exact antitoneOn_Icc_glue phi_lt_eta.le ht3 h23
      (uVelocity_phase4_anti ⟨ht3, h4⟩ le_rfl ht.2)
  have ht4 : tau ≤ t := (lt_of_not_ge h4).le
  have hphase4 := uVelocity_phase4_anti
    (t := t) (hi := tau) ⟨eta_lt_tau.le, le_rfl⟩ ht4 ht.2
  have h234 := antitoneOn_Icc_glue phi_lt_eta.le eta_lt_tau.le h23 hphase4
  exact antitoneOn_Icc_glue
    (lt_trans phi_lt_eta eta_lt_tau).le ht4 h234
    (uVelocity_phase5_anti ⟨ht4, ht.2⟩ le_rfl ht.2)

private theorem dot_fixed_hasDerivAt {f : ℝ → Point} {f' : Point}
    {r : ℝ} (hf : HasDerivAt f f' r) (w : Point) :
    HasDerivAt (fun s => dot (f s) w) (dot f' w) r := by
  have h1 := HasDerivAt.const_mul w.1 hf.fst
  have h2 := HasDerivAt.const_mul w.2 hf.snd
  simpa [dot, mul_comm] using h1.fun_add h2

/-- Derivative of `U(r,t)` in its first variable. -/
theorem UValue_hasDerivAt_noHidden (r t : ℝ) :
    HasDerivAt (fun s => Stage2.UValue s t) (uVelocity t r) r := by
  have hpRaw := (path_hasDerivAt_noHidden r).fun_sub
    (hasDerivAt_const r (Romik.path params t))
  have hp : HasDerivAt
      (fun s => Romik.path params s - Romik.path params t)
      (Romik.rot r (alphaBetaAt r)) r := by
    exact hpRaw.congr_deriv (by simp)
  have hd := dot_fixed_hasDerivAt hp (u t)
  have hrot : dot (Romik.rot r (alphaBetaAt r)) (u t) = uVelocity t r := by
    dsimp [dot, Romik.rot, u, uVelocity, alpha, beta]
    rw [Real.cos_sub, Real.sin_sub]
    ring
  exact hd.congr_deriv hrot

/-- Concavity form of the manuscript's one-turn tangent argument. -/
theorem U_concave_on (t : ℝ) (ht : t ∈ Icc params.phi T) :
    ConcaveOn ℝ (Icc params.phi t) (fun r => Stage2.UValue r t) := by
  have hanti := uVelocity_antitone ht
  have hantiDeriv : AntitoneOn
      (deriv (fun r => Stage2.UValue r t)) (interior (Icc params.phi t)) := by
    intro x hx y hy hxy
    rw [(UValue_hasDerivAt_noHidden x t).deriv,
      (UValue_hasDerivAt_noHidden y t).deriv]
    exact hanti (interior_subset hx) (interior_subset hy) hxy
  exact hantiDeriv.concaveOn_of_deriv (convex_Icc params.phi t)
    (by
      intro r hr
      exact (UValue_hasDerivAt_noHidden r t).continuousAt.continuousWithinAt)
    (by
      intro r hr
      exact (UValue_hasDerivAt_noHidden r t).differentiableAt.differentiableWithinAt)

end Stage4
end PartC
end GerverSofa
