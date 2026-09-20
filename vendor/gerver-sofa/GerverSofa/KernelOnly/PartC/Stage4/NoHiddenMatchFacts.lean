import GerverSofa.KernelOnly.PartC.Stage4.ExactGeometryFacts

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

noncomputable section

/-- Reflection on the `(alpha,beta)` coefficient plane induced by `t ↦ T-t`. -/
def noHiddenReflAB (z : Point) : Point := (-z.2, -z.1)

private theorem rot_dot_u_noHidden (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (u t) = z.1 := by
  dsimp [dot, Romik.rot, u]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * Real.cos t +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.sin t =
      z.1 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.1 := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem rot_dot_v_noHidden (t : ℝ) (z : Point) :
    dot (Romik.rot t z) (v t) = z.2 := by
  dsimp [dot, Romik.rot, v]
  calc
    (Real.cos t * z.1 - Real.sin t * z.2) * (-Real.sin t) +
        (Real.sin t * z.1 + Real.cos t * z.2) * Real.cos t =
      z.2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
    _ = z.2 := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem rot_injective_noHidden (t : ℝ) {z w : Point}
    (h : Romik.rot t z = Romik.rot t w) : z = w := by
  have hu := congrArg (fun q : Point => dot q (u t)) h
  have hv := congrArg (fun q : Point => dot q (v t)) h
  rw [rot_dot_u_noHidden, rot_dot_u_noHidden] at hu
  rw [rot_dot_v_noHidden, rot_dot_v_noHidden] at hv
  exact Prod.ext hu hv

private theorem matchPrime12_noHidden :
    Romik.pathPrime1 params params.phi = Romik.pathPrime2 params params.phi := by
  have h10 := congrFun params_equations (10 : Fin 22)
  have h11 := congrFun params_equations (11 : Fin 22)
  simp [Romik.Equations, Romik.system] at h10 h11
  exact Prod.ext (by linarith) (by linarith)

private theorem matchPrime23_noHidden :
    Romik.pathPrime2 params params.theta = Romik.pathPrime3 params params.theta := by
  have h14 := congrFun params_equations (14 : Fin 22)
  have h15 := congrFun params_equations (15 : Fin 22)
  simp [Romik.Equations, Romik.system] at h14 h15
  exact Prod.ext (by linarith) (by linarith)

private theorem pathPrime1_eq_rot_noHidden (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime1 p t = Romik.rot t (Romik.alphaBeta1 p t) := rfl

private theorem pathPrime2_eq_rot_noHidden (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime2 p t = Romik.rot t (Romik.alphaBeta2 p t) := rfl

private theorem pathPrime3_eq_rot_noHidden (p : Romik.Params) (t : ℝ) :
    Romik.pathPrime3 p t = Romik.rot t (Romik.alphaBeta3 p t) := rfl

/-- Exact matching of the coefficient pair at the first switch. -/
theorem alphaBeta_match12_direct :
    Romik.alphaBeta1 params params.phi = Romik.alphaBeta2 params params.phi := by
  apply rot_injective_noHidden params.phi
  simpa [pathPrime1_eq_rot_noHidden, pathPrime2_eq_rot_noHidden] using matchPrime12_noHidden

/-- Exact matching of the coefficient pair at the second switch. -/
theorem alphaBeta_match23_direct :
    Romik.alphaBeta2 params params.theta = Romik.alphaBeta3 params params.theta := by
  apply rot_injective_noHidden params.theta
  simpa [pathPrime2_eq_rot_noHidden, pathPrime3_eq_rot_noHidden] using matchPrime23_noHidden

/-- Phase four is the reflected phase two coefficient pair. -/
theorem alphaBeta4_reflect2_direct (s : ℝ) :
    Romik.alphaBeta4 params (T - s) = noHiddenReflAB (Romik.alphaBeta2 params s) := by
  dsimp [T, noHiddenReflAB, Romik.alphaBeta4, Romik.alphaBeta2]
  rw [Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations,
      Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations]
  ring

/-- Phase three has the same coefficient reflection symmetry. -/
theorem alphaBeta3_reflect_direct (s : ℝ) :
    Romik.alphaBeta3 params (T - s) = noHiddenReflAB (Romik.alphaBeta3 params s) := by
  dsimp [T, noHiddenReflAB, Romik.alphaBeta3]
  rw [Romik.c2_eq_c1_sub_halfPi_of_equations params_equations]
  ring

/-- Phase five is the reflected phase one coefficient pair. -/
theorem alphaBeta5_reflect1_direct (s : ℝ) :
    Romik.alphaBeta5 params (T - s) = noHiddenReflAB (Romik.alphaBeta1 params s) := by
  dsimp [T, noHiddenReflAB, Romik.alphaBeta5, Romik.alphaBeta1]
  rw [Romik.e1_eq_a1_of_equations params_equations,
      Romik.e2_eq_neg_a2_of_equations params_equations]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

/-- Exact matching of the coefficient pair at the third switch. -/
theorem alphaBeta_match34_direct :
    Romik.alphaBeta3 params eta = Romik.alphaBeta4 params eta := by
  have h3 := alphaBeta3_reflect_direct params.theta
  have h4 := alphaBeta4_reflect2_direct params.theta
  have hm := congrArg noHiddenReflAB alphaBeta_match23_direct
  simpa [eta] using h3.trans (hm.symm.trans h4.symm)

/-- Exact matching of the coefficient pair at the fourth switch. -/
theorem alphaBeta_match45_direct :
    Romik.alphaBeta4 params tau = Romik.alphaBeta5 params tau := by
  have h4 := alphaBeta4_reflect2_direct params.phi
  have h5 := alphaBeta5_reflect1_direct params.phi
  have hm := congrArg noHiddenReflAB alphaBeta_match12_direct
  simpa [tau] using h4.trans (hm.symm.trans h5.symm)

end

end Stage4
end PartC
end GerverSofa
