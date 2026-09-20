import GerverSofa.KernelOnly.PartF.F01PhaseAlgebra

/-!
# F04: literal integral data and its branch primitives

The parameterized definitions below are the pinned upstream scalar integrals.
The phase boundaries are preserved. Integrating across the jumps will use
equality on open intervals, not an incorrect global continuity assertion for r.
-/

noncomputable section
open MeasureTheory
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.Integrals

open Phases

def eta (d : Reduced.Params) : ℝ := T - d.theta
def tau (d : Reduced.Params) : ℝ := T - d.phi
def Ordered (d : Reduced.Params) : Prop :=
  0 ≤ d.phi ∧ d.phi ≤ d.theta ∧ d.theta ≤ Real.pi / 4

theorem ordered_knots (d : Reduced.Params) (ho : Ordered d) :
    0 ≤ d.phi ∧ d.phi ≤ d.theta ∧ d.theta ≤ eta d ∧
      eta d ≤ tau d ∧ tau d ≤ T := by
  rcases ho with ⟨h0, h1, h2⟩
  dsimp [eta, tau, T]
  exact ⟨h0, h1, by linarith, by linarith, by linarith⟩

def r1 (_d : Reduced.Params) (_t : ℝ) : ℝ := 1 / 2
def r2 (d : Reduced.Params) (t : ℝ) : ℝ := g2 d t
def r3 (d : Reduced.Params) (t : ℝ) : ℝ := g3 d t
def r4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  d.b - (T - t - d.phi) * (1 + d.a) / 2 - (T - t - d.phi) ^ 2 / 4

def r (d : Reduced.Params) (t : ℝ) : ℝ :=
  if t ≤ d.phi then r1 d t
  else if t ≤ d.theta then r2 d t
  else if t ≤ eta d then r3 d t
  else if t ≤ tau d then r4 d t
  else 0

def xi (d : Reduced.Params) (t : ℝ) : ℝ :=
  1 - ∫ s in t..tau d, r d s * Real.cos s
def zeta (d : Reduced.Params) (t : ℝ) : ℝ :=
  ∫ s in t..tau d, r d s * Real.sin s

def path (d : Reduced.Params) (t : ℝ) : Point :=
  (if t ≤ d.phi then Real.cos t - 1
   else xi d (T - t) * Real.cos t + zeta d (T - t) * Real.sin t - 1,
   if t ≤ tau d then
     zeta d t * Real.cos t - (4 * xi d 0 - 2 - xi d t) * Real.sin t - 1
   else -(4 * xi d 0 - 3) * Real.sin t - 1)

def dg4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  (1 + d.a) / 2 + (T - d.phi - t) / 2

def primitiveX (V : ℝ) (g gp : ℝ → ℝ) (t : ℝ) : ℝ :=
  V + g t * Real.sin t + gp t * Real.cos t
def primitiveY (U : ℝ) (g gp : ℝ → ℝ) (t : ℝ) : ℝ :=
  U + g t * Real.cos t - gp t * Real.sin t

def X1 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V1 d) (r1 d) (fun _ => 0)
def Y1 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U1 d) (r1 d) (fun _ => 0)
def X2 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V2 d) (g2 d) (fun _ => 1 / 2)
def Y2 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U2 d) (g2 d) (fun _ => 1 / 2)
def X3 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V3 d) (g3 d) (fun _ => 1)
def Y3 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U3 d) (g3 d) (fun _ => 1)
def X4 (d : Reduced.Params) : ℝ → ℝ := primitiveX (V4 d) (g4 d) (dg4 d)
def Y4 (d : Reduced.Params) : ℝ → ℝ := primitiveY (U4 d) (g4 d) (dg4 d)

/-- F05 repair: normalize only the scalar derivative, never typeclass arguments. -/
theorem primitiveX_hasDerivAt (V : ℝ) {g gp : ℝ → ℝ} {t gpp : ℝ}
    (hg : HasDerivAt g (gp t) t) (hgp : HasDerivAt gp gpp t) :
    HasDerivAt (primitiveX V g gp) ((g t + gpp) * Real.cos t) t := by
  change HasDerivAt (fun s => V + g s * Real.sin s + gp s * Real.cos s) _ t
  have h := ((hasDerivAt_const t V).fun_add
    (hg.fun_mul (Real.hasDerivAt_sin t))).fun_add
    (hgp.fun_mul (Real.hasDerivAt_cos t))
  exact h.congr_deriv (by ring)

theorem primitiveY_hasDerivAt (U : ℝ) {g gp : ℝ → ℝ} {t gpp : ℝ}
    (hg : HasDerivAt g (gp t) t) (hgp : HasDerivAt gp gpp t) :
    HasDerivAt (primitiveY U g gp) (-(g t + gpp) * Real.sin t) t := by
  change HasDerivAt (fun s => U + g s * Real.cos s - gp s * Real.sin s) _ t
  have h := ((hasDerivAt_const t U).fun_add
    (hg.fun_mul (Real.hasDerivAt_cos t))).fun_sub
    (hgp.fun_mul (Real.hasDerivAt_sin t))
  exact h.congr_deriv (by ring)

theorem g2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g2 d) (1 / 2) t := by
  change HasDerivAt (fun s => (1 + d.a + s - d.phi) / 2) _ t
  have h := (((hasDerivAt_const t (1 + d.a)).fun_add
    (hasDerivAt_id t)).fun_sub (hasDerivAt_const t d.phi)).div_const 2
  exact h.congr_deriv (by ring)

theorem g3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g3 d) 1 t := by
  change HasDerivAt (fun s => d.a + s - d.phi) _ t
  have h := ((hasDerivAt_const t d.a).fun_add
    (hasDerivAt_id t)).fun_sub (hasDerivAt_const t d.phi)
  exact h.congr_deriv (by ring)

theorem g4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (g4 d) (dg4 d t) t := by
  change HasDerivAt (fun s => d.b + 1 / 2 -
    (T - d.phi - s) * (1 + d.a) / 2 - (T - d.phi - s)^2 / 4) _ t
  have h := (hasDerivAt_const t (T - d.phi)).fun_sub (hasDerivAt_id t)
  have hfull := ((hasDerivAt_const t (d.b + 1 / 2)).fun_sub
    ((h.mul_const (1 + d.a)).div_const 2)).fun_sub ((h.pow 2).div_const 4)
  exact hfull.congr_deriv (by dsimp [dg4]; ring)

theorem dg4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (dg4 d) (-1 / 2) t := by
  change HasDerivAt (fun s => (1 + d.a) / 2 + (T - d.phi - s) / 2) _ t
  have h := (hasDerivAt_const t ((1 + d.a) / 2)).fun_add
    (((hasDerivAt_const t (T - d.phi)).fun_sub (hasDerivAt_id t)).div_const 2)
  exact h.congr_deriv (by ring)

theorem X1_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X1 d) (r1 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V1 d) (g := r1 d) (gp := fun _ => 0)
    (hasDerivAt_const t (1 / 2 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y1_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y1 d) (-r1 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U1 d) (g := r1 d) (gp := fun _ => 0)
    (hasDerivAt_const t (1 / 2 : ℝ)) (hasDerivAt_const t (0 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X2 d) (r2 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V2 d) (g := g2 d) (gp := fun _ => 1 / 2)
    (g2_hasDerivAt d t) (hasDerivAt_const t (1 / 2 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y2_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y2 d) (-r2 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U2 d) (g := g2 d) (gp := fun _ => 1 / 2)
    (g2_hasDerivAt d t) (hasDerivAt_const t (1 / 2 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X3 d) (r3 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V3 d) (g := g3 d) (gp := fun _ => 1)
    (g3_hasDerivAt d t) (hasDerivAt_const t (1 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y3_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y3 d) (-r3 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U3 d) (g := g3 d) (gp := fun _ => 1)
    (g3_hasDerivAt d t) (hasDerivAt_const t (1 : ℝ))
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (X4 d) (r4 d t * Real.cos t) t := by
  have h := primitiveX_hasDerivAt (V4 d) (g := g4 d) (gp := dg4 d)
    (g4_hasDerivAt d t) (dg4_hasDerivAt d t)
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem Y4_hasDerivAt (d : Reduced.Params) (t : ℝ) :
    HasDerivAt (Y4 d) (-r4 d t * Real.sin t) t := by
  have h := primitiveY_hasDerivAt (U4 d) (g := g4 d) (gp := dg4 d)
    (g4_hasDerivAt d t) (dg4_hasDerivAt d t)
  exact h.congr_deriv (by dsimp [r1, r2, r3, r4, g2, g3, g4]; ring)

theorem X1_join (d : Reduced.Params) :
    X1 d d.phi = X2 d d.phi := by
  dsimp [X1, X2, primitiveX, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem Y1_join (d : Reduced.Params) :
    Y1 d d.phi = Y2 d d.phi := by
  dsimp [Y1, Y2, primitiveY, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem X2_join (d : Reduced.Params) :
    X2 d d.theta = X3 d d.theta := by
  dsimp [X2, X3, primitiveX, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem Y2_join (d : Reduced.Params) :
    Y2 d d.theta = Y3 d d.theta := by
  dsimp [Y2, Y3, primitiveY, r1, g2, g3,
    U1, U2, U3, V1, V2, V3, hStar]
  ring

theorem fourth_equation (d : Reduced.Params) (hd : Reduced.Equations d) :
    d.a + T - d.phi - d.theta - d.b +
      (1 / 2 : ℝ) * (d.theta - d.phi) * (1 + d.a) +
      (1 / 4 : ℝ) * (d.theta - d.phi) * (d.theta - d.phi) = 0 := by
  exact congrFun hd (3 : Fin 4)

theorem X3_join (d : Reduced.Params) (hd : Reduced.Equations d) :
    X3 d (eta d) = X4 d (eta d) := by
  have he := fourth_equation d hd
  dsimp [X3, X4, primitiveX, eta, g3, g4, dg4, U3, V3, hStar, T] at *
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination Real.cos d.theta * he

theorem Y3_join (d : Reduced.Params) (hd : Reduced.Equations d) :
    Y3 d (eta d) = Y4 d (eta d) := by
  have he := fourth_equation d hd
  dsimp [Y3, Y4, primitiveY, eta, g3, g4, dg4, U3, V3, hStar, T] at *
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  linear_combination Real.sin d.theta * he

theorem X4_terminal (d : Reduced.Params) :
    X4 d (tau d) = 1 := by
  dsimp [X4, primitiveX, tau, g4, dg4, U4, V4, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem Y4_terminal (d : Reduced.Params) :
    Y4 d (tau d) = 0 := by
  dsimp [Y4, primitiveY, tau, g4, dg4, U4, V4, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

theorem r_phase1 (d : Reduced.Params) {t : ℝ} (ht : t ≤ d.phi) :
    r d t = r1 d t := by simp only [r, if_pos ht]

theorem r_phase2 (d : Reduced.Params) {t : ℝ}
    (hlo : d.phi < t) (hhi : t ≤ d.theta) : r d t = r2 d t := by
  simp only [r, if_neg (not_le.mpr hlo), if_pos hhi]

theorem r_phase3 (d : Reduced.Params) (ho : Ordered d) {t : ℝ}
    (hlo : d.theta < t) (hhi : t ≤ eta d) : r d t = r3 d t := by
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 hlo
  simp only [r, if_neg (not_le.mpr hphi), if_neg (not_le.mpr hlo), if_pos hhi]

theorem r_phase4 (d : Reduced.Params) (ho : Ordered d) {t : ℝ}
    (hlo : eta d < t) (hhi : t ≤ tau d) : r d t = r4 d t := by
  have htheta : d.theta < t := lt_of_le_of_lt (ordered_knots d ho).2.2.1 hlo
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 htheta
  simp only [r, if_neg (not_le.mpr hphi), if_neg (not_le.mpr htheta),
    if_neg (not_le.mpr hlo), if_pos hhi]

end GerverSofa.PartF.Integrals
