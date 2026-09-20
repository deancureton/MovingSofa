import GerverSofa.KernelOnly.PartC.Stage2.SupportPhaseDerivatives

/-!
# Part C Stage 4: public path differential layer

Source-clean phase derivatives of the five Gerver path pieces.  These are
re-exposed here because the Stage 2 implementations were intentionally private.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

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

theorem path1_hasDerivAt_public (t : ℝ) :
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

theorem path2_hasDerivAt_public (t : ℝ) :
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

theorem path3_hasDerivAt_public (t : ℝ) :
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

theorem path4_hasDerivAt_public (t : ℝ) :
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

theorem path5_hasDerivAt_public (t : ℝ) :
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



/-! The five public phase derivative theorems above are the complete differential
interface used by Stage 4.  We intentionally do not assert a global `HasDerivAt`
for the nested-if path at switching times: such a theorem requires a separate
matching-of-derivatives argument and is neither needed nor used by the Part C
closure. -/


end Stage4
end PartC
end GerverSofa
