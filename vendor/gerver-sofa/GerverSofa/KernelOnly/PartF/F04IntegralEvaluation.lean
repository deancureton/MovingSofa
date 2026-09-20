import GerverSofa.KernelOnly.PartF.F04IntegralPrimitives

/-!
# F04: evaluation of the literal integrals on all four closed intervals

The fundamental theorem is applied to smooth branch primitives. Equality with
the discontinuous integrand is required only on the open interval. Adjacent
integrals are then added, using the proved matching values at every switch.
-/

noncomputable section
open MeasureTheory
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.Integrals

open Phases

theorem integrate_branch (f f' P : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf' : Continuous f')
    (hderiv : ∀ t, HasDerivAt P (f' t) t)
    (heq : ∀ t ∈ Set.Ioo a b, f t = f' t) :
    IntervalIntegrable f volume a b ∧
      (∫ t in a..b, f t) = P b - P a := by
  have hi : IntervalIntegrable f' volume a b := hf'.intervalIntegrable a b
  have hf : IntervalIntegrable f volume a b := hi.congr_uIoo (by
    rw [Set.uIoo_of_le hab]
    intro t ht
    exact (heq t ht).symm)
  refine ⟨hf, ?_⟩
  calc
    (∫ t in a..b, f t) = ∫ t in a..b, f' t :=
      intervalIntegral.integral_congr_Ioo_of_le hab heq
    _ = P b - P a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hi

theorem cos_tail4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X4 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r4 d u * Real.cos u)
    (X4 d) t (tau d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X4_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase4 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  refine ⟨hpiece.1, ?_⟩
  rw [hpiece.2]
  rw [X4_terminal] <;> ring

theorem sin_tail4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y4 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r4 d u * Real.sin u)
    (fun u => -Y4 d u) t (tau d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y4_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase4 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  refine ⟨hpiece.1, ?_⟩
  rw [hpiece.2]
  rw [Y4_terminal] <;> ring

theorem cos_tail3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X3 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r3 d u * Real.cos u)
    (X3 d) t (eta d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X3_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase3 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := cos_tail4 d ho (eta d) ⟨le_rfl, (ordered_knots d ho).2.2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X3_join d hd] <;> ring

theorem sin_tail3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y3 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r3 d u * Real.sin u)
    (fun u => -Y3 d u) t (eta d) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y3_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase3 d ho (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := sin_tail4 d ho (eta d) ⟨le_rfl, (ordered_knots d ho).2.2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y3_join d hd] <;> ring

theorem cos_tail2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X2 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r2 d u * Real.cos u)
    (X2 d) t (d.theta) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X2_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase2 d (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := cos_tail3 d ho hd (d.theta) ⟨le_rfl, (ordered_knots d ho).2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X2_join d] <;> ring

theorem sin_tail2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y2 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r2 d u * Real.sin u)
    (fun u => -Y2 d u) t (d.theta) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y2_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase2 d (lt_of_le_of_lt ht.1 hu.1) (le_of_lt hu.2)])
  have hrest := sin_tail3 d ho hd (d.theta) ⟨le_rfl, (ordered_knots d ho).2.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y2_join d] <;> ring

theorem cos_tail1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    IntervalIntegrable (fun u => r d u * Real.cos u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.cos u) = 1 - X1 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.cos u) (fun u => r1 d u * Real.cos u)
    (X1 d) t (d.phi) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact X1_hasDerivAt d u)
    (by
      intro u hu
      rw [r_phase1 d (le_of_lt hu.2)])
  have hrest := cos_tail2 d ho hd (d.phi) ⟨le_rfl, ho.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [X1_join d] <;> ring

theorem sin_tail1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    IntervalIntegrable (fun u => r d u * Real.sin u) volume t (tau d) ∧
      (∫ u in t..tau d, r d u * Real.sin u) = Y1 d t := by
  have hpiece := integrate_branch
    (fun u => r d u * Real.sin u) (fun u => r1 d u * Real.sin u)
    (fun u => -Y1 d u) t (d.phi) ht.2
    (by dsimp [r1, r2, r3, r4, g2, g3]; fun_prop)
    (by
      intro u
      exact (Y1_hasDerivAt d u).fun_neg.congr_deriv (by ring))
    (by
      intro u hu
      rw [r_phase1 d (le_of_lt hu.2)])
  have hrest := sin_tail2 d ho hd (d.phi) ⟨le_rfl, ho.2.1⟩
  refine ⟨hpiece.1.trans hrest.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hpiece.1 hrest.1,
    hpiece.2, hrest.2]
  rw [Y1_join d] <;> ring

theorem xi_zeta_phase1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    xi d t = X1 d t ∧ zeta d t = Y1 d t := by
  constructor
  · unfold xi
    rw [(cos_tail1 d ho hd t ht).2]
    ring
  · exact (sin_tail1 d ho hd t ht).2

theorem xi_zeta_phase2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    xi d t = X2 d t ∧ zeta d t = Y2 d t := by
  constructor
  · unfold xi
    rw [(cos_tail2 d ho hd t ht).2]
    ring
  · exact (sin_tail2 d ho hd t ht).2

theorem xi_zeta_phase3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    xi d t = X3 d t ∧ zeta d t = Y3 d t := by
  constructor
  · unfold xi
    rw [(cos_tail3 d ho hd t ht).2]
    ring
  · exact (sin_tail3 d ho hd t ht).2

theorem xi_zeta_phase4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    xi d t = X4 d t ∧ zeta d t = Y4 d t := by
  constructor
  · unfold xi
    rw [(cos_tail4 d ho t ht).2]
    ring
  · exact (sin_tail4 d ho t ht).2

theorem xi_zero (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) : xi d 0 = V1 d := by
  have h := (xi_zeta_phase1 d ho hd 0 ⟨le_rfl, ho.1⟩).1
  simpa [X1, primitiveX] using h

def W (d : Reduced.Params) (t : ℝ) : ℝ :=
  xi d t * Real.sin t + zeta d t * Real.cos t

theorem primitive_W (g gp U V t : ℝ) :
    (V + g * Real.sin t + gp * Real.cos t) * Real.sin t +
      (U + g * Real.cos t - gp * Real.sin t) * Real.cos t =
      g + U * Real.cos t + V * Real.sin t := by
  linear_combination g * Real.sin_sq_add_cos_sq t

theorem W_phase1 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (0) (d.phi)) :
    W d t = r1 d t + U1 d * Real.cos t + V1 d * Real.sin t := by
  rcases xi_zeta_phase1 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (r1 d t) (0) (U1 d) (V1 d) t

theorem W_phase2 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.phi) (d.theta)) :
    W d t = g2 d t + U2 d * Real.cos t + V2 d * Real.sin t := by
  rcases xi_zeta_phase2 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g2 d t) (1 / 2) (U2 d) (V2 d) t

theorem W_phase3 (d : Reduced.Params) (ho : Ordered d) (hd : Reduced.Equations d)
    (t : ℝ) (ht : t ∈ Set.Icc (d.theta) (eta d)) :
    W d t = g3 d t + U3 d * Real.cos t + V3 d * Real.sin t := by
  rcases xi_zeta_phase3 d ho hd t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g3 d t) (1) (U3 d) (V3 d) t

theorem W_phase4 (d : Reduced.Params) (ho : Ordered d)
    (t : ℝ) (ht : t ∈ Set.Icc (eta d) (tau d)) :
    W d t = g4 d t + U4 d * Real.cos t + V4 d * Real.sin t := by
  rcases xi_zeta_phase4 d ho t ht with ⟨hx, hy⟩
  unfold W
  rw [hx, hy]
  exact primitive_W (g4 d t) (dg4 d t) (U4 d) (V4 d) t

end GerverSofa.PartF.Integrals
