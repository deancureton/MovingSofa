import GerverSofa.KernelOnly.PartC.Stage4.ExactGeometryFacts
import GerverSofa.KernelOnly.PartC.Stage3.FinalClosureDirect
import Mathlib.Analysis.Convex.PathConnected

/-!
# Part C Stage 4: independent cap convexity and anchor foundation

This module separates the already direct cap geometry from the later theorem
that removing the downward niche preserves connectedness.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- The concrete endpoint anchor belongs to the reconstructed cap. -/
theorem anchor_mem_K_direct : anchor ∈ K := by
  have hA0 : A 0 = anchor := Stage2.A_zero_eq_anchor
  rw [← hA0]
  exact Stage3.supportA_direct 0 (by
    constructor
    · norm_num
    · dsimp [T]
      positivity)

/-- Convexity of the literal cap follows directly from its half-plane
definition. -/
theorem K_convex_direct : Convex ℝ K := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · change 0 ≤ a * x.2 + b * y.2
    exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
  · intro t ht
    constructor
    · change dot (a • x + b • y) (u t) ≤
        dot (Romik.path params t) (u t) + 1
      have hxU := (hx.2 t ht).1
      have hyU := (hy.2 t ht).1
      dsimp [supportHalfU, dot] at hxU hyU ⊢
      have hax := mul_le_mul_of_nonneg_left hxU ha
      have hby := mul_le_mul_of_nonneg_left hyU hb
      calc
        (a * x.1 + b * y.1) * (u t).1 +
            (a * x.2 + b * y.2) * (u t).2 =
            a * (x.1 * (u t).1 + x.2 * (u t).2) +
              b * (y.1 * (u t).1 + y.2 * (u t).2) := by ring
        _ ≤ a * ((Romik.path params t).1 * (u t).1 +
              (Romik.path params t).2 * (u t).2 + 1) +
            b * ((Romik.path params t).1 * (u t).1 +
              (Romik.path params t).2 * (u t).2 + 1) := add_le_add hax hby
        _ = (Romik.path params t).1 * (u t).1 +
              (Romik.path params t).2 * (u t).2 + 1 := by
            rw [← add_mul, hab]
            ring
    · change dot (a • x + b • y) (v t) ≤
        dot (Romik.path params t) (v t) + 1
      have hxV := (hx.2 t ht).2
      have hyV := (hy.2 t ht).2
      dsimp [supportHalfV, dot] at hxV hyV ⊢
      have hax := mul_le_mul_of_nonneg_left hxV ha
      have hby := mul_le_mul_of_nonneg_left hyV hb
      calc
        (a * x.1 + b * y.1) * (v t).1 +
            (a * x.2 + b * y.2) * (v t).2 =
            a * (x.1 * (v t).1 + x.2 * (v t).2) +
              b * (y.1 * (v t).1 + y.2 * (v t).2) := by ring
        _ ≤ a * ((Romik.path params t).1 * (v t).1 +
              (Romik.path params t).2 * (v t).2 + 1) +
            b * ((Romik.path params t).1 * (v t).1 +
              (Romik.path params t).2 * (v t).2 + 1) := add_le_add hax hby
        _ = (Romik.path params t).1 * (v t).1 +
              (Romik.path params t).2 * (v t).2 + 1 := by
            rw [← add_mul, hab]
            ring

/-- The nonempty convex cap is connected. -/
theorem K_connected_direct : IsConnected K :=
  K_convex_direct.isConnected ⟨anchor, anchor_mem_K_direct⟩

end Stage4
end PartC
end GerverSofa
