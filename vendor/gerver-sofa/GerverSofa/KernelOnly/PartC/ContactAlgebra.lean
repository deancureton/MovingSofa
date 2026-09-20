import GerverSofa.KernelOnly.PartC.Parameters

/-!
# Exact contact-curve algebra

These identities are independent of every interval estimate.  They record
that `A` and `C` lie on the two outer supporting lines, while `B` and `D` lie
on the corresponding inner-wall lines.  Later geometric work only has to prove
that the relevant contact points belong to the cap and that no hidden crossing
changes the boundary envelope.
-/

noncomputable section

namespace GerverSofa
namespace PartC

/-- `A(t)` lies on the first outer support line. -/
theorem A_support_identity (t : ℝ) :
    dot (A t) (u t) = dot (Romik.path params t) (u t) + 1 := by
  simp only [A, dot, u, v]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- `C(t)` lies on the second outer support line. -/
theorem C_support_identity (t : ℝ) :
    dot (C t) (v t) = dot (Romik.path params t) (v t) + 1 := by
  simp only [C, dot, u, v]
  nlinarith [Real.sin_sq_add_cos_sq t]

/-- `B(t)` lies on the first inner wall through the corner path. -/
theorem B_inner_u_identity (t : ℝ) :
    dot (B t - Romik.path params t) (u t) = 0 := by
  change
    ((B t).1 - (Romik.path params t).1) * Real.cos t +
      ((B t).2 - (Romik.path params t).2) * Real.sin t = 0
  simp [B, u, v] <;> ring

/-- `D(t)` lies on the second inner wall through the corner path. -/
theorem D_inner_v_identity (t : ℝ) :
    dot (D t - Romik.path params t) (v t) = 0 := by
  change
    ((D t).1 - (Romik.path params t).1) * (-Real.sin t) +
      ((D t).2 - (Romik.path params t).2) * Real.cos t = 0
  simp [D, u, v] <;> ring

end PartC
end GerverSofa
