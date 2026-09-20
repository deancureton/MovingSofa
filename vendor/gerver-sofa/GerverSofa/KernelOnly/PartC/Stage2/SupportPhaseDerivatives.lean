import GerverSofa.KernelOnly.PartC.Stage2.EnvelopeAlgebra
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# C10: source-clean phase derivative identities — residual batch fix

This revision keeps the C09 no-`convert` architecture and fixes the complete residual class from the C09 clean build.
It uses eta-expanded derivative combinators (`fun_add`, `fun_sub`, `fun_mul`,
`fun_neg`, `fun_smul`) so the function carried by `HasDerivAt` is in the desired
shape from the start.  The proof remains organized in body coordinates and the
accompanying runner forces a fresh build of this module.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

/-- Phase-local outer `A` contact, written in vector form. -/
def phaseA1 (t : ℝ) : Point :=
  Romik.path1 params t + (Romik.alphaBeta1 params t).1 • v t + u t

def phaseA2 (t : ℝ) : Point :=
  Romik.path2 params t + (Romik.alphaBeta2 params t).1 • v t + u t

def phaseA3 (t : ℝ) : Point :=
  Romik.path3 params t + (Romik.alphaBeta3 params t).1 • v t + u t

def phaseA4 (t : ℝ) : Point :=
  Romik.path4 params t + (Romik.alphaBeta4 params t).1 • v t + u t

def phaseA5 (t : ℝ) : Point :=
  Romik.path5 params t + (Romik.alphaBeta5 params t).1 • v t + u t

/-- Phase-local outer `C` contact, written in vector form. -/
def phaseC1 (t : ℝ) : Point :=
  Romik.path1 params t - (Romik.alphaBeta1 params t).2 • u t + v t

def phaseC2 (t : ℝ) : Point :=
  Romik.path2 params t - (Romik.alphaBeta2 params t).2 • u t + v t

def phaseC3 (t : ℝ) : Point :=
  Romik.path3 params t - (Romik.alphaBeta3 params t).2 • u t + v t

def phaseC4 (t : ℝ) : Point :=
  Romik.path4 params t - (Romik.alphaBeta4 params t).2 • u t + v t

def phaseC5 (t : ℝ) : Point :=
  Romik.path5 params t - (Romik.alphaBeta5 params t).2 • u t + v t

private def vecA (r t : ℝ) : Point :=
  (-r * Real.sin t, r * Real.cos t)

private def vecC (r t : ℝ) : Point :=
  (-r * Real.cos t, -r * Real.sin t)

private theorem square_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
  have h := (hasDerivAt_id t).fun_mul (hasDerivAt_id t)
  simpa only [id_eq, one_mul, mul_one] using h

private theorem u_hasDerivAt (t : ℝ) : HasDerivAt u (v t) t := by
  change HasDerivAt (fun s : ℝ => (Real.cos s, Real.sin s))
    (-Real.sin t, Real.cos t) t
  exact (Real.hasDerivAt_cos t).prodMk (Real.hasDerivAt_sin t)

private theorem v_hasDerivAt (t : ℝ) : HasDerivAt v (-u t) t := by
  change HasDerivAt (fun s : ℝ => (-Real.sin s, Real.cos s))
    (-Real.cos t, -Real.sin t) t
  exact (Real.hasDerivAt_sin t).fun_neg.prodMk (Real.hasDerivAt_cos t)

/-- Derivative of `addK (rot t (z1 t,z2 t))` in body coordinates. -/
private theorem rotAddK_hasDerivAt
    {z1 z2 : ℝ → ℝ} {z1' z2' k1 k2 : ℝ} (t : ℝ)
    (hz1 : HasDerivAt z1 z1' t) (hz2 : HasDerivAt z2 z2' t) :
    HasDerivAt
      (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) k1 k2)
      (Romik.rot t (z1' - z2 t, z2' + z1 t)) t := by
  apply HasDerivAt.prodMk
  · change HasDerivAt
      (fun s => Real.cos s * z1 s - Real.sin s * z2 s + k1)
      (Real.cos t * (z1' - z2 t) - Real.sin t * (z2' + z1 t)) t
    have h1 := (Real.hasDerivAt_cos t).fun_mul hz1
    have h2 := (Real.hasDerivAt_sin t).fun_mul hz2
    have h := (h1.fun_sub h2).fun_add (hasDerivAt_const t k1)
    exact h.congr_deriv (by ring)
  · change HasDerivAt
      (fun s => Real.sin s * z1 s + Real.cos s * z2 s + k2)
      (Real.sin t * (z1' - z2 t) + Real.cos t * (z2' + z1 t)) t
    have h1 := (Real.hasDerivAt_sin t).fun_mul hz1
    have h2 := (Real.hasDerivAt_cos t).fun_mul hz2
    have h := (h1.fun_add h2).fun_add (hasDerivAt_const t k2)
    exact h.congr_deriv (by ring)

private theorem path1_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path1 params)
      (Romik.rot t (Romik.alphaBeta1 params t)) t := by
  let z1 : ℝ → ℝ := fun s =>
    params.a1 * Real.cos s + params.a2 * Real.sin s - 1
  let z2 : ℝ → ℝ := fun s =>
    -params.a2 * Real.cos s + params.a1 * Real.sin s - 1 / 2
  have hz1 : HasDerivAt z1
      (-params.a1 * Real.sin t + params.a2 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul params.a1 (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.a2 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2
      (params.a2 * Real.sin t + params.a1 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul (-params.a2) (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.a1 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 / 2 : ℝ))
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k11 params.k12)
    (Romik.rot t (Romik.alphaBeta1 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k11) (k2 := params.k12) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta1] <;> ring

private theorem path2_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path2 params)
      (Romik.rot t (Romik.alphaBeta2 params t)) t := by
  let z1 : ℝ → ℝ := fun s =>
    -(1 / 4 : ℝ) * s * s + params.b1 * s + params.b2
  let z2 : ℝ → ℝ := fun s =>
    (1 / 2 : ℝ) * s - params.b1 - 1
  have hz1 : HasDerivAt z1 (-(1 / 2 : ℝ) * t + params.b1) t := by
    have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ)) (square_hasDerivAt t)
    have h2 := HasDerivAt.const_mul params.b1 (hasDerivAt_id t)
    have hraw := (h1.fun_add h2).fun_add (hasDerivAt_const t params.b2)
    have heq : (-(1 / 4 : ℝ)) * (t + t) + params.b1 * 1 + 0 =
        -(1 / 2 : ℝ) * t + params.b1 := by ring
    rw [← heq]
    simpa only [z1, id_eq, mul_assoc] using hraw
  have hz2 : HasDerivAt z2 (1 / 2 : ℝ) t := by
    have h1 := HasDerivAt.const_mul (1 / 2 : ℝ) (hasDerivAt_id t)
    have h := (h1.fun_sub (hasDerivAt_const t params.b1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k21 params.k22)
    (Romik.rot t (Romik.alphaBeta2 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k21) (k2 := params.k22) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta2] <;> ring

private theorem path3_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path3 params)
      (Romik.rot t (Romik.alphaBeta3 params t)) t := by
  let z1 : ℝ → ℝ := fun s => params.c1 - s
  let z2 : ℝ → ℝ := fun s => params.c2 + s
  have hz1 : HasDerivAt z1 (-1) t := by
    have h := (hasDerivAt_const t params.c1).fun_sub (hasDerivAt_id t)
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2 1 t := by
    have h := (hasDerivAt_const t params.c2).fun_add (hasDerivAt_id t)
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k31 params.k32)
    (Romik.rot t (Romik.alphaBeta3 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k31) (k2 := params.k32) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta3] <;> ring

private theorem path4_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path4 params)
      (Romik.rot t (Romik.alphaBeta4 params t)) t := by
  let z1 : ℝ → ℝ := fun s => -(1 / 2 : ℝ) * s + params.d1 - 1
  let z2 : ℝ → ℝ := fun s =>
    -(1 / 4 : ℝ) * s * s + params.d1 * s + params.d2
  have hz1 : HasDerivAt z1 (-(1 / 2 : ℝ)) t := by
    have h1 := HasDerivAt.const_mul (-(1 / 2 : ℝ)) (hasDerivAt_id t)
    have h := (h1.fun_add (hasDerivAt_const t params.d1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2 (-(1 / 2 : ℝ) * t + params.d1) t := by
    have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ)) (square_hasDerivAt t)
    have h2 := HasDerivAt.const_mul params.d1 (hasDerivAt_id t)
    have hraw := (h1.fun_add h2).fun_add (hasDerivAt_const t params.d2)
    have heq : (-(1 / 4 : ℝ)) * (t + t) + params.d1 * 1 + 0 =
        -(1 / 2 : ℝ) * t + params.d1 := by ring
    rw [← heq]
    simpa only [z2, id_eq, mul_assoc] using hraw
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k41 params.k42)
    (Romik.rot t (Romik.alphaBeta4 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k41) (k2 := params.k42) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta4] <;> ring

private theorem path5_hasDerivAt (t : ℝ) :
    HasDerivAt (Romik.path5 params)
      (Romik.rot t (Romik.alphaBeta5 params t)) t := by
  let z1 : ℝ → ℝ := fun s =>
    params.e1 * Real.cos s + params.e2 * Real.sin s - 1 / 2
  let z2 : ℝ → ℝ := fun s =>
    -params.e2 * Real.cos s + params.e1 * Real.sin s - 1
  have hz1 : HasDerivAt z1
      (-params.e1 * Real.sin t + params.e2 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul params.e1 (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.e2 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 / 2 : ℝ))
    dsimp [z1]
    exact h.congr_deriv (by ring)
  have hz2 : HasDerivAt z2
      (params.e2 * Real.sin t + params.e1 * Real.cos t) t := by
    have h1 := HasDerivAt.const_mul (-params.e2) (Real.hasDerivAt_cos t)
    have h2 := HasDerivAt.const_mul params.e1 (Real.hasDerivAt_sin t)
    have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
    dsimp [z2]
    exact h.congr_deriv (by ring)
  change HasDerivAt
    (fun s => Romik.addK (Romik.rot s (z1 s, z2 s)) params.k51 params.k52)
    (Romik.rot t (Romik.alphaBeta5 params t)) t
  have h := rotAddK_hasDerivAt (k1 := params.k51) (k2 := params.k52) t hz1 hz2
  refine h.congr_deriv ?_
  apply congrArg (Romik.rot t)
  ext <;> dsimp [z1, z2, Romik.alphaBeta5] <;> ring

/-- Generic outer-A envelope identity from `x'=R_t(alpha,beta)`. -/
private theorem contactA_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {a' : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (ha : HasDerivAt (fun s => (ab s).1) a' t) :
    HasDerivAt
      (fun s => x s + (ab s).1 • v s + u s)
      (vecA ((ab t).2 + a' + 1) t) t := by
  have hscaled := ha.fun_smul (v_hasDerivAt t)
  have h := (hx.fun_add hscaled).fun_add (u_hasDerivAt t)
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v, vecA] <;> ring

/-- Generic outer-C envelope identity from `x'=R_t(alpha,beta)`. -/
private theorem contactC_hasDerivAt
    {x : ℝ → Point} {ab : ℝ → Point} {b' : ℝ} (t : ℝ)
    (hx : HasDerivAt x (Romik.rot t (ab t)) t)
    (hb : HasDerivAt (fun s => (ab s).2) b' t) :
    HasDerivAt
      (fun s => x s - (ab s).2 • u s + v s)
      (vecC (b' + 1 - (ab t).1) t) t := by
  have hscaled := hb.fun_smul (u_hasDerivAt t)
  have h := (hx.fun_sub hscaled).fun_add (v_hasDerivAt t)
  refine h.congr_deriv ?_
  ext <;> simp [Romik.rot, u, v, vecC] <;> ring

private theorem alpha1_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta1 params s).1)
      (-2 * params.a1 * Real.cos t - 2 * params.a2 * Real.sin t) t := by
  have h1 := HasDerivAt.const_mul (-2 * params.a1) (Real.hasDerivAt_sin t)
  have h2 := HasDerivAt.const_mul (2 * params.a2) (Real.hasDerivAt_cos t)
  have h := (h1.fun_add h2).fun_add (hasDerivAt_const t (1 / 2 : ℝ))
  dsimp [Romik.alphaBeta1]
  exact h.congr_deriv (by ring)

private theorem alpha2_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).1) (-1) t := by
  have h := (hasDerivAt_const t (1 + 2 * params.b1)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta2]
  exact h.congr_deriv (by ring)

private theorem alpha3_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).1) (-1) t := by
  have h := (hasDerivAt_const t (-1 - params.c2)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta3]
  exact h.congr_deriv (by ring)

private theorem alpha4_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).1)
      ((1 / 2 : ℝ) * t - params.d1) t := by
  have h1 := HasDerivAt.const_mul (1 / 4 : ℝ) (square_hasDerivAt t)
  have h2 := HasDerivAt.const_mul params.d1 (hasDerivAt_id t)
  have hraw := (((h1.fun_sub h2).fun_sub (hasDerivAt_const t params.d2)).fun_sub
    (hasDerivAt_const t (1 / 2 : ℝ)))
  have heq : (1 / 4 : ℝ) * (t + t) - params.d1 * 1 - 0 - 0 =
      (1 / 2 : ℝ) * t - params.d1 := by ring
  rw [← heq]
  simpa only [Romik.alphaBeta4, id_eq, mul_assoc] using hraw

private theorem alpha5_fst_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).1)
      (-2 * params.e1 * Real.cos t - 2 * params.e2 * Real.sin t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.e1) (Real.hasDerivAt_sin t)
  have h2 := HasDerivAt.const_mul (2 * params.e2) (Real.hasDerivAt_cos t)
  have h := ((hasDerivAt_const t (1 : ℝ)).fun_sub h1).fun_add h2
  dsimp [Romik.alphaBeta5]
  exact h.congr_deriv (by ring)

private theorem beta1_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta1 params s).2)
      (-2 * params.a1 * Real.sin t + 2 * params.a2 * Real.cos t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.a1) (Real.hasDerivAt_cos t)
  have h2 := HasDerivAt.const_mul (2 * params.a2) (Real.hasDerivAt_sin t)
  have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 : ℝ))
  dsimp [Romik.alphaBeta1]
  exact h.congr_deriv (by ring)

private theorem beta2_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta2 params s).2)
      (-(1 / 2 : ℝ) * t + params.b1) t := by
  have h1 := HasDerivAt.const_mul (-(1 / 4 : ℝ)) (square_hasDerivAt t)
  have h2 := HasDerivAt.const_mul params.b1 (hasDerivAt_id t)
  have hraw := ((h1.fun_add h2).fun_add (hasDerivAt_const t params.b2)).fun_add
    (hasDerivAt_const t (1 / 2 : ℝ))
  have heq : (-(1 / 4 : ℝ)) * (t + t) + params.b1 * 1 + 0 + 0 =
      -(1 / 2 : ℝ) * t + params.b1 := by ring
  rw [← heq]
  simpa only [Romik.alphaBeta2, id_eq, mul_assoc] using hraw

private theorem beta3_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta3 params s).2) (-1) t := by
  have h := (hasDerivAt_const t (1 + params.c1)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta3]
  exact h.congr_deriv (by ring)

private theorem beta4_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta4 params s).2) (-1) t := by
  have h := (hasDerivAt_const t (2 * params.d1 - 1)).fun_sub (hasDerivAt_id t)
  dsimp [Romik.alphaBeta4]
  exact h.congr_deriv (by ring)

private theorem beta5_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s => (Romik.alphaBeta5 params s).2)
      (-2 * params.e1 * Real.sin t + 2 * params.e2 * Real.cos t) t := by
  have h1 := HasDerivAt.const_mul (2 * params.e1) (Real.hasDerivAt_cos t)
  have h2 := HasDerivAt.const_mul (2 * params.e2) (Real.hasDerivAt_sin t)
  have h := (h1.fun_add h2).fun_sub (hasDerivAt_const t (1 / 2 : ℝ))
  dsimp [Romik.alphaBeta5]
  exact h.congr_deriv (by ring)

/-- Phase 1: `A' = 0 * v`. -/
theorem A1_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA1 (vecA 0 t) t := by
  change HasDerivAt
    (fun s => Romik.path1 params s + (Romik.alphaBeta1 params s).1 • v s + u s)
    (vecA 0 t) t
  have h := contactA_hasDerivAt t (path1_hasDerivAt t) (alpha1_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta1]
  ring

/-- Phase 2: `A' = beta_2 * v`. -/
theorem A2_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA2
      (vecA (-(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2) t) t := by
  change HasDerivAt
    (fun s => Romik.path2 params s + (Romik.alphaBeta2 params s).1 • v s + u s)
    (vecA (-(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2) t) t
  have h := contactA_hasDerivAt t (path2_hasDerivAt t) (alpha2_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta2]
  ring

/-- Phase 3: `A' = beta_3 * v`. -/
theorem A3_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA3 (vecA (1 + params.c1 - t) t) t := by
  change HasDerivAt
    (fun s => Romik.path3 params s + (Romik.alphaBeta3 params s).1 • v s + u s)
    (vecA (1 + params.c1 - t) t) t
  have h := contactA_hasDerivAt t (path3_hasDerivAt t) (alpha3_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta3]
  ring

/-- Phase 4: `A' = (d1-t/2) * v`. -/
theorem A4_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA4 (vecA (params.d1 - t / 2) t) t := by
  change HasDerivAt
    (fun s => Romik.path4 params s + (Romik.alphaBeta4 params s).1 • v s + u s)
    (vecA (params.d1 - t / 2) t) t
  have h := contactA_hasDerivAt t (path4_hasDerivAt t) (alpha4_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta4]
  ring

/-- Phase 5: `A' = (1/2) * v`. -/
theorem A5_hasDerivAt (t : ℝ) :
    HasDerivAt phaseA5 (vecA (1 / 2 : ℝ) t) t := by
  change HasDerivAt
    (fun s => Romik.path5 params s + (Romik.alphaBeta5 params s).1 • v s + u s)
    (vecA (1 / 2 : ℝ) t) t
  have h := contactA_hasDerivAt t (path5_hasDerivAt t) (alpha5_fst_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecA r t)
  dsimp [Romik.alphaBeta5]
  ring

/-- Phase 1: `C' = -(1/2) * u`. -/
theorem C1_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC1 (vecC (1 / 2 : ℝ) t) t := by
  change HasDerivAt
    (fun s => Romik.path1 params s - (Romik.alphaBeta1 params s).2 • u s + v s)
    (vecC (1 / 2 : ℝ) t) t
  have h := contactC_hasDerivAt t (path1_hasDerivAt t) (beta1_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta1]
  ring

/-- Phase 2: `C' = -(t/2-b1) * u`. -/
theorem C2_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC2 (vecC (t / 2 - params.b1) t) t := by
  change HasDerivAt
    (fun s => Romik.path2 params s - (Romik.alphaBeta2 params s).2 • u s + v s)
    (vecC (t / 2 - params.b1) t) t
  have h := contactC_hasDerivAt t (path2_hasDerivAt t) (beta2_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta2]
  ring

/-- Phase 3: `C' = -(1+c2+t) * u`. -/
theorem C3_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC3 (vecC (1 + params.c2 + t) t) t := by
  change HasDerivAt
    (fun s => Romik.path3 params s - (Romik.alphaBeta3 params s).2 • u s + v s)
    (vecC (1 + params.c2 + t) t) t
  have h := contactC_hasDerivAt t (path3_hasDerivAt t) (beta3_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta3]
  ring

/-- Phase 4: `C' = -rhoC_4 * u`. -/
theorem C4_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC4
      (vecC (-(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2) t) t := by
  change HasDerivAt
    (fun s => Romik.path4 params s - (Romik.alphaBeta4 params s).2 • u s + v s)
    (vecC (-(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2) t) t
  have h := contactC_hasDerivAt t (path4_hasDerivAt t) (beta4_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta4]
  ring

/-- Phase 5: `C' = 0 * u`. -/
theorem C5_hasDerivAt (t : ℝ) :
    HasDerivAt phaseC5 (vecC 0 t) t := by
  change HasDerivAt
    (fun s => Romik.path5 params s - (Romik.alphaBeta5 params s).2 • u s + v s)
    (vecC 0 t) t
  have h := contactC_hasDerivAt t (path5_hasDerivAt t) (beta5_hasDerivAt t)
  refine h.congr_deriv ?_
  apply congrArg (fun r => vecC r t)
  dsimp [Romik.alphaBeta5]
  ring


/-! ## Public derivative shapes for downstream Part C closure

The source-clean phase proofs above use private `vecA`/`vecC` helpers.
These public lemmas expose exactly the stable geometric derivative shapes used
by the direct support proof.  The transport is derivative-only: the function
itself is unchanged, and the remaining pair equality is elementary algebra.
-/

theorem A1_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA1 ((0 : ℝ) • v t) t := by
  refine (A1_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v]

theorem A2_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA2
      ((-(1 / 4 : ℝ) * t * t + params.b1 * t + params.b2 + 1 / 2) • v t) t := by
  refine (A2_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v] <;> ring

theorem A3_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA3 ((1 + params.c1 - t) • v t) t := by
  refine (A3_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v] <;> ring

theorem A4_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA4 ((params.d1 - t / 2) • v t) t := by
  refine (A4_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v] <;> ring

theorem A5_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseA5 ((1 / 2 : ℝ) • v t) t := by
  refine (A5_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecA, v] <;> ring

theorem C1_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC1 ((-(1 / 2 : ℝ)) • u t) t := by
  refine (C1_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u] <;> ring

theorem C2_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC2 ((-(t / 2 - params.b1)) • u t) t := by
  refine (C2_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u] <;> ring

theorem C3_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC3 ((-(1 + params.c2 + t)) • u t) t := by
  refine (C3_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u] <;> ring

theorem C4_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC4
      ((-(-(1 / 4 : ℝ) * t * t + params.d1 * t + params.d2 + 1 / 2)) • u t) t := by
  refine (C4_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u] <;> ring

theorem C5_hasDerivAt_public (t : ℝ) :
    HasDerivAt phaseC5 ((0 : ℝ) • u t) t := by
  refine (C5_hasDerivAt t).congr_deriv ?_
  apply Prod.ext <;> simp [vecC, u]

end Stage2
end PartC
end GerverSofa
