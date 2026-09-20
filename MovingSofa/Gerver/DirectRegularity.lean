import MovingSofa.ForMathlib.Analysis.Calculus.Interval
import MovingSofa.Gerver.ReversePhysicalDomain

/-!
# Matching and `C¹` regularity of the direct Gerver path

The vendor library assembles the Gerver path `GerverSofa.Romik.path` from five smooth
branches `path1, …, path5` switched at `φ < θ < π/2 - θ < π/2 - φ`.  This file supplies the
differential interface for those branches — each `pathᵢ` has derivative
`rot t (alphaBetaᵢ p t)` — and deduces from the direct equations that values and derivatives
agree at all four switches, hence that `path p` is continuously differentiable with
`path p 0 = 0`.

It also records, for each stage, that the glued path agrees with its analytic branch on the
*closed* stage interval and that `deriv (path p)` is the corresponding `rot t (alphaBetaᵢ p t)`
there, endpoints included.
-/

noncomputable section

open scoped ContDiff

namespace GerverSofa.Romik

/-! ### Differential interface for the five direct branches -/

/-- Rotating a differentiable body-frame curve and translating it differentiates by the
product rule, contributing the infinitesimal rotation `(z₁, z₂) ↦ (-z₂, z₁)`. -/
theorem hasDerivAt_addK_rot {z₁ z₂ : ℝ → ℝ} {z₁' z₂' k₁ k₂ t : ℝ}
    (hz₁ : HasDerivAt z₁ z₁' t) (hz₂ : HasDerivAt z₂ z₂' t) :
    HasDerivAt (fun s => addK (rot s (z₁ s, z₂ s)) k₁ k₂)
      (rot t (z₁' - z₂ t, z₂' + z₁ t)) t := by
  apply HasDerivAt.prodMk
  · change HasDerivAt (fun s => Real.cos s * z₁ s - Real.sin s * z₂ s + k₁)
      (Real.cos t * (z₁' - z₂ t) - Real.sin t * (z₂' + z₁ t)) t
    exact ((((Real.hasDerivAt_cos t).fun_mul hz₁).fun_sub
        ((Real.hasDerivAt_sin t).fun_mul hz₂)).fun_add
      (hasDerivAt_const t k₁)).congr_deriv (by ring)
  · change HasDerivAt (fun s => Real.sin s * z₁ s + Real.cos s * z₂ s + k₂)
      (Real.sin t * (z₁' - z₂ t) + Real.cos t * (z₂' + z₁ t)) t
    exact ((((Real.hasDerivAt_sin t).fun_mul hz₁).fun_add
        ((Real.hasDerivAt_cos t).fun_mul hz₂)).fun_add
      (hasDerivAt_const t k₂)).congr_deriv (by ring)

private theorem hasDerivAt_mul_self (t : ℝ) : HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
  simpa only [id_eq, one_mul, mul_one] using (hasDerivAt_id t).fun_mul (hasDerivAt_id t)

/-- The first direct branch has body-frame velocity `alphaBeta1`. -/
theorem hasDerivAt_path1 (p : Params) (t : ℝ) :
    HasDerivAt (path1 p) (rot t (alphaBeta1 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.a1 * Real.cos s + p.a2 * Real.sin s - 1)
      (-p.a1 * Real.sin t + p.a2 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul p.a1).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.a2)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => -p.a2 * Real.cos s + p.a1 * Real.sin s - 1 / 2)
      (p.a2 * Real.sin t + p.a1 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul (-p.a2)).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.a1)).fun_sub
      (hasDerivAt_const t (1 / 2 : ℝ))).congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k11) (k₂ := p.k12) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta1] <;> ring

/-- The second direct branch has body-frame velocity `alphaBeta2`. -/
theorem hasDerivAt_path2 (p : Params) (t : ℝ) :
    HasDerivAt (path2 p) (rot t (alphaBeta2 p t)) t := by
  have hz₁ : HasDerivAt (fun s => -(1 / 4 : ℝ) * s * s + p.b1 * s + p.b2)
      (-(1 / 2 : ℝ) * t + p.b1) t := by
    have h := (((hasDerivAt_mul_self t).const_mul (-(1 / 4 : ℝ))).fun_add
      ((hasDerivAt_id t).const_mul p.b1)).fun_add (hasDerivAt_const t p.b2)
    simpa only [id_eq, mul_assoc] using h.congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => (1 / 2 : ℝ) * s - p.b1 - 1) (1 / 2 : ℝ) t :=
    ((((hasDerivAt_id t).const_mul (1 / 2 : ℝ)).fun_sub (hasDerivAt_const t p.b1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by simp)
  refine (hasDerivAt_addK_rot (k₁ := p.k21) (k₂ := p.k22) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta2] <;> ring

/-- The third direct branch has body-frame velocity `alphaBeta3`. -/
theorem hasDerivAt_path3 (p : Params) (t : ℝ) :
    HasDerivAt (path3 p) (rot t (alphaBeta3 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.c1 - s) (-1) t :=
    ((hasDerivAt_const t p.c1).fun_sub (hasDerivAt_id t)).congr_deriv (by simp)
  have hz₂ : HasDerivAt (fun s => p.c2 + s) 1 t :=
    ((hasDerivAt_const t p.c2).fun_add (hasDerivAt_id t)).congr_deriv (by simp)
  refine (hasDerivAt_addK_rot (k₁ := p.k31) (k₂ := p.k32) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta3] <;> ring

/-- The fourth direct branch has body-frame velocity `alphaBeta4`. -/
theorem hasDerivAt_path4 (p : Params) (t : ℝ) :
    HasDerivAt (path4 p) (rot t (alphaBeta4 p t)) t := by
  have hz₁ : HasDerivAt (fun s => -(1 / 2 : ℝ) * s + p.d1 - 1) (-(1 / 2 : ℝ)) t :=
    ((((hasDerivAt_id t).const_mul (-(1 / 2 : ℝ))).fun_add (hasDerivAt_const t p.d1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by simp)
  have hz₂ : HasDerivAt (fun s => -(1 / 4 : ℝ) * s * s + p.d1 * s + p.d2)
      (-(1 / 2 : ℝ) * t + p.d1) t := by
    have h := (((hasDerivAt_mul_self t).const_mul (-(1 / 4 : ℝ))).fun_add
      ((hasDerivAt_id t).const_mul p.d1)).fun_add (hasDerivAt_const t p.d2)
    simpa only [id_eq, mul_assoc] using h.congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k41) (k₂ := p.k42) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta4] <;> ring

/-- The fifth direct branch has body-frame velocity `alphaBeta5`. -/
theorem hasDerivAt_path5 (p : Params) (t : ℝ) :
    HasDerivAt (path5 p) (rot t (alphaBeta5 p t)) t := by
  have hz₁ : HasDerivAt (fun s => p.e1 * Real.cos s + p.e2 * Real.sin s - 1 / 2)
      (-p.e1 * Real.sin t + p.e2 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul p.e1).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.e2)).fun_sub
      (hasDerivAt_const t (1 / 2 : ℝ))).congr_deriv (by ring)
  have hz₂ : HasDerivAt (fun s => -p.e2 * Real.cos s + p.e1 * Real.sin s - 1)
      (p.e2 * Real.sin t + p.e1 * Real.cos t) t :=
    ((((Real.hasDerivAt_cos t).const_mul (-p.e2)).fun_add
      ((Real.hasDerivAt_sin t).const_mul p.e1)).fun_sub
      (hasDerivAt_const t (1 : ℝ))).congr_deriv (by ring)
  refine (hasDerivAt_addK_rot (k₁ := p.k51) (k₂ := p.k52) hz₁ hz₂).congr_deriv ?_
  apply congrArg (rot t)
  ext <;> simp [alphaBeta5] <;> ring

/-- Continuity of the body-frame velocity field on each branch, transported to the world
frame by the rotation. -/
theorem continuous_rot_alphaBeta1 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta1 p t) := by
  unfold rot alphaBeta1; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta2 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta2 p t) := by
  unfold rot alphaBeta2; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta3 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta3 p t) := by
  unfold rot alphaBeta3; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta4 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta4 p t) := by
  unfold rot alphaBeta4; fun_prop

@[inherit_doc continuous_rot_alphaBeta1]
theorem continuous_rot_alphaBeta5 (p : Params) :
    Continuous fun t : ℝ => rot t (alphaBeta5 p t) := by
  unfold rot alphaBeta5; fun_prop

/-- Equation 32 of the direct system.  The remaining scalar consequences used here are
already extracted by the vendor in `GerverSofa/KernelOnly/EndpointSymmetry.lean`. -/
theorem k11_eq_one_sub_a1_of_equations {p : Params} (heq : Equations p) :
    p.k11 = 1 - p.a1 := by
  have h5 := congrFun heq (5 : Fin 22)
  simp [system] at h5
  linarith

/-! ### Reflection identities for the body-frame velocities

With `S (r, s) = (-s, -r)` the direct equations give `w₃(π/2 - t) = S w₃(t)`,
`w₄(π/2 - t) = S w₂(t)` and `w₅(π/2 - t) = S w₁(t)`. -/

/-- The middle branch velocity is anti-symmetric about `π/4`. -/
theorem alphaBeta3_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta3 p (Real.pi / 2 - t) = (-(alphaBeta3 p t).2, -(alphaBeta3 p t).1) := by
  have hc2 := c2_eq_c1_sub_halfPi_of_equations heq
  simp only [alphaBeta3, Prod.mk.injEq]
  constructor <;> rw [hc2] <;> ring

/-- The fourth branch velocity reflects onto the second. -/
theorem alphaBeta4_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta4 p (Real.pi / 2 - t) = (-(alphaBeta2 p t).2, -(alphaBeta2 p t).1) := by
  have hd1 := d1_eq_quarterPi_sub_b1_of_equations heq
  have hd2 := d2_eq_b2_add_quarterPi_correction_of_equations heq
  simp only [alphaBeta4, alphaBeta2, Prod.mk.injEq]
  constructor <;> simp only [hd1, hd2] <;> ring

/-- The fifth branch velocity reflects onto the first. -/
theorem alphaBeta5_pi_div_two_sub {p : Params} (heq : Equations p) (t : ℝ) :
    alphaBeta5 p (Real.pi / 2 - t) = (-(alphaBeta1 p t).2, -(alphaBeta1 p t).1) := by
  have he1 := e1_eq_a1_of_equations heq
  have he2 := e2_eq_neg_a2_of_equations heq
  simp only [alphaBeta5, alphaBeta1, Prod.mk.injEq, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]
  constructor <;> simp only [he1, he2] <;> ring

/-- Velocity matching at the third switch `π/2 - θ`, by reflecting the match at `θ`. -/
theorem alphaBeta34_eq {p : Params} (heq : Equations p) :
    alphaBeta3 p (Real.pi / 2 - p.theta) = alphaBeta4 p (Real.pi / 2 - p.theta) := by
  rw [alphaBeta3_pi_div_two_sub heq, alphaBeta4_pi_div_two_sub heq,
    GerverSofa.PartF.Phases.alphaBeta23_eq heq]

/-- Velocity matching at the fourth switch `π/2 - φ`, by reflecting the match at `φ`. -/
theorem alphaBeta45_eq {p : Params} (heq : Equations p) :
    alphaBeta4 p (Real.pi / 2 - p.phi) = alphaBeta5 p (Real.pi / 2 - p.phi) := by
  rw [alphaBeta4_pi_div_two_sub heq, alphaBeta5_pi_div_two_sub heq,
    GerverSofa.PartF.Phases.alphaBeta12_eq heq]

/-! ### Branch selection on the closed stages

Each stage interval is closed, so the two stages adjacent to a switch both contain it.  The
glued `path` picks the *earlier* branch there, and the certified value-matching equations
say that this is also the later branch's value. -/

/-- The glued direct path unfolds to the nested selection of its five analytic branches. -/
theorem path_eq_ite (p : Params) (t : ℝ) :
    path p t =
      if t ≤ p.phi then path1 p t
      else if t ≤ p.theta then path2 p t
      else if t ≤ Real.pi / 2 - p.theta then path3 p t
      else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t := rfl

/-- On the closed first stage `[0, φ]` the glued path is the first branch. -/
theorem path_eq_path1_of_mem_Icc (p : Params) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) p.phi) :
    path p s = path1 p s := by
  rw [path_eq_ite, ite_eq_left hs.2]

/-- On the closed second stage `[φ, θ]` the glued path is the second branch; at the left
endpoint this is the certified value match `match_path12_of_equations`. -/
theorem path_eq_path2_of_mem_Icc {p : Params} (heq : Equations p) {s : ℝ}
    (hs : s ∈ Set.Icc p.phi p.theta) : path p s = path2 p s := by
  rw [path_eq_ite]
  by_cases hc : s ≤ p.phi
  · obtain rfl : s = p.phi := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path12_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed third stage `[θ, π/2 - θ]` the glued path is the third branch; at the left
endpoint this is the certified value match `match_path23_of_equations`. -/
theorem path_eq_path3_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    {s : ℝ} (hs : s ∈ Set.Icc p.theta (Real.pi / 2 - p.theta)) : path p s = path3 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi)]
  by_cases hc : s ≤ p.theta
  · obtain rfl : s = p.theta := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path23_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed fourth stage `[π/2 - θ, π/2 - φ]` the glued path is the fourth branch; at
the left endpoint this is the certified value match `match_path34_of_equations`. -/
theorem path_eq_path4_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi)) :
    path p s = path4 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi),
    ite_eq_right (by linarith : ¬ s ≤ p.theta)]
  by_cases hc : s ≤ Real.pi / 2 - p.theta
  · obtain rfl : s = Real.pi / 2 - p.theta := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path34_of_equations heq
  · rw [ite_eq_right hc, ite_eq_left hs.2]

/-- On the closed fifth stage `[π/2 - φ, π/2]` the glued path is the fifth branch; at the
left endpoint this is the certified value match `match_path45_of_equations`. -/
theorem path_eq_path5_of_mem_Icc {p : Params} (heq : Equations p) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {s : ℝ}
    (hs : s ∈ Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2)) : path p s = path5 p s := by
  have hb := hs.1
  rw [path_eq_ite, ite_eq_right (by linarith : ¬ s ≤ p.phi),
    ite_eq_right (by linarith : ¬ s ≤ p.theta),
    ite_eq_right (by linarith : ¬ s ≤ Real.pi / 2 - p.theta)]
  by_cases hc : s ≤ Real.pi / 2 - p.phi
  · obtain rfl : s = Real.pi / 2 - p.phi := le_antisymm hc hs.1
    rw [ite_eq_left hc]
    exact match_path45_of_equations heq
  · rw [ite_eq_right hc]

/-! ### Smoothness of the branches and of their body-frame velocities -/

/-- The first analytic branch is smooth on all of `ℝ`. -/
theorem contDiff_path1 (p : Params) : ContDiff ℝ ∞ (path1 p) := by
  unfold path1 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path2 (p : Params) : ContDiff ℝ ∞ (path2 p) := by
  unfold path2 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path3 (p : Params) : ContDiff ℝ ∞ (path3 p) := by
  unfold path3 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path4 (p : Params) : ContDiff ℝ ∞ (path4 p) := by
  unfold path4 addK rot; fun_prop

@[inherit_doc contDiff_path1]
theorem contDiff_path5 (p : Params) : ContDiff ℝ ∞ (path5 p) := by
  unfold path5 addK rot; fun_prop

/-- The first body-frame velocity pair is smooth on all of `ℝ`. -/
theorem contDiff_alphaBeta1 (p : Params) : ContDiff ℝ ∞ (alphaBeta1 p) := by
  unfold alphaBeta1; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta2 (p : Params) : ContDiff ℝ ∞ (alphaBeta2 p) := by
  unfold alphaBeta2; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta3 (p : Params) : ContDiff ℝ ∞ (alphaBeta3 p) := by
  unfold alphaBeta3; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta4 (p : Params) : ContDiff ℝ ∞ (alphaBeta4 p) := by
  unfold alphaBeta4; fun_prop

@[inherit_doc contDiff_alphaBeta1]
theorem contDiff_alphaBeta5 (p : Params) : ContDiff ℝ ∞ (alphaBeta5 p) := by
  unfold alphaBeta5; fun_prop

/-! ### The stage derivatives, endpoints included

A nondegenerate closed interval has a unique tangent direction at each of its points,
including its endpoints, so a `C¹` function agreeing there with a differentiable curve
already has that curve's derivative at every point of the interval. -/

/-- If the `C¹` glued path agrees on a nondegenerate closed interval with a curve whose
derivative is `rot s (W s)`, then that is its derivative everywhere on the interval,
endpoints included. -/
theorem deriv_path_of_eqOn_Icc {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    {X W : ℝ → Point} {a b t : ℝ} (hab : a < b)
    (hX : ∀ s, HasDerivAt X (rot s (W s)) s) (hXe : ∀ s ∈ Set.Icc a b, path p s = X s)
    (ht : t ∈ Set.Icc a b) : deriv (path p) t = rot t (W t) := by
  have h1 : HasDerivWithinAt (path p) (deriv (path p) t) (Set.Icc a b) t :=
    ((hC1.differentiable one_ne_zero t).hasDerivAt).hasDerivWithinAt
  have h2 : HasDerivWithinAt (path p) (rot t (W t)) (Set.Icc a b) t :=
    ((hX t).hasDerivWithinAt).congr hXe (hXe t ht)
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ h1 h2

/-- On the closed first stage the glued path has body-frame velocity `alphaBeta1`. -/
theorem deriv_path_eq_rot_alphaBeta1 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (hphi : 0 < p.phi) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) p.phi) :
    deriv (path p) t = rot t (alphaBeta1 p t) :=
  deriv_path_of_eqOn_Icc hC1 hphi (hasDerivAt_path1 p)
    (fun _ hs => path_eq_path1_of_mem_Icc p hs) ht

/-- On the closed second stage the glued path has body-frame velocity `alphaBeta2`. -/
theorem deriv_path_eq_rot_alphaBeta2 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) {t : ℝ} (ht : t ∈ Set.Icc p.phi p.theta) :
    deriv (path p) t = rot t (alphaBeta2 p t) :=
  deriv_path_of_eqOn_Icc hC1 hpt (hasDerivAt_path2 p)
    (fun _ hs => path_eq_path2_of_mem_Icc heq hs) ht

/-- On the closed third stage the glued path has body-frame velocity `alphaBeta3`. -/
theorem deriv_path_eq_rot_alphaBeta3 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc p.theta (Real.pi / 2 - p.theta)) :
    deriv (path p) t = rot t (alphaBeta3 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path3 p)
    (fun _ hs => path_eq_path3_of_mem_Icc heq hpt hs) ht

/-- On the closed fourth stage the glued path has body-frame velocity `alphaBeta4`. -/
theorem deriv_path_eq_rot_alphaBeta4 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hpt : p.phi < p.theta) (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc (Real.pi / 2 - p.theta) (Real.pi / 2 - p.phi)) :
    deriv (path p) t = rot t (alphaBeta4 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path4 p)
    (fun _ hs => path_eq_path4_of_mem_Icc heq hpt hq hs) ht

/-- On the closed fifth stage the glued path has body-frame velocity `alphaBeta5`. -/
theorem deriv_path_eq_rot_alphaBeta5 {p : Params} (hC1 : ContDiff ℝ 1 (path p))
    (heq : Equations p) (hphi : 0 < p.phi) (hpt : p.phi < p.theta)
    (hq : p.theta < Real.pi / 4) {t : ℝ}
    (ht : t ∈ Set.Icc (Real.pi / 2 - p.phi) (Real.pi / 2)) :
    deriv (path p) t = rot t (alphaBeta5 p t) :=
  deriv_path_of_eqOn_Icc hC1 (by linarith) (hasDerivAt_path5 p)
    (fun _ hs => path_eq_path5_of_mem_Icc heq hpt hq hs) ht

end GerverSofa.Romik

namespace MovingSofa

open GerverSofa.Romik

def gerverDirectBranches (p : GerverSofa.Romik.Params) : Fin 5 → ℝ → GerverSofa.Point :=
  ![GerverSofa.Romik.path1 p, GerverSofa.Romik.path2 p, GerverSofa.Romik.path3 p,
    GerverSofa.Romik.path4 p, GerverSofa.Romik.path5 p]

def gerverDirectSwitches (p : GerverSofa.Romik.Params) : Fin 4 → ℝ :=
  ![p.phi, p.theta, Real.pi / 2 - p.theta, Real.pi / 2 - p.phi]

theorem gerver_direct_path_regularity (p : GerverSofa.Romik.Params)
    (hp : p ∈ gerverDirectBox) (heq : gerverDirectEquations p) :
    ContDiff ℝ 1 (GerverSofa.Romik.path p) ∧ GerverSofa.Romik.path p 0 = 0 ∧
    ∀ i : Fin 4,
      gerverDirectBranches p i.castSucc (gerverDirectSwitches p i) =
        gerverDirectBranches p i.succ (gerverDirectSwitches p i) ∧
      deriv (gerverDirectBranches p i.castSucc) (gerverDirectSwitches p i) =
        deriv (gerverDirectBranches p i.succ) (gerverDirectSwitches p i) := by
  -- The switching angles are strictly ordered by the reverse-domain bounds.
  have hdom := gerver_reverse_physical_domain p hp
  have hphi_pos : 0 < p.phi := hdom.1
  have hphi_theta : p.phi < p.theta := hdom.2.1
  have htheta_quarter : p.theta < Real.pi / 4 := hdom.2.2.1
  have htheta_eta : p.theta < Real.pi / 2 - p.theta := by linarith
  have heta_tau : Real.pi / 2 - p.theta < Real.pi / 2 - p.phi := by linarith
  -- The body-frame velocity matches at the four switches.
  have hw12 := GerverSofa.PartF.Phases.alphaBeta12_eq (p := p) heq
  have hw23 := GerverSofa.PartF.Phases.alphaBeta23_eq (p := p) heq
  have hw34 := alphaBeta34_eq (p := p) heq
  have hw45 := alphaBeta45_eq (p := p) heq
  -- The four positional matches, from the certified vendor extraction.
  have hv12 := match_path12_of_equations (p := p) heq
  have hv23 := match_path23_of_equations (p := p) heq
  have hv34 := match_path34_of_equations (p := p) heq
  have hv45 := match_path45_of_equations (p := p) heq
  -- Glue the branches from the last switch backwards.
  have hD45 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path4 p) (hasDerivAt_path5 p) hv45
      (congrArg (rot (Real.pi / 2 - p.phi)) hw45)
  have hC45 : Continuous fun t : ℝ =>
      if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t) else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta4 p).if_le (continuous_rot_alphaBeta5 p)
      continuous_id continuous_const (by
        intro t ht
        subst ht
        exact congrArg (rot (Real.pi / 2 - p.phi)) hw45)
  have hD345 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ Real.pi / 2 - p.theta then path3 p s
        else if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path3 p) hD45
      (by rw [ite_eq_left heta_tau.le]; exact hv34)
      (by rw [ite_eq_left heta_tau.le]
          exact congrArg (rot (Real.pi / 2 - p.theta)) hw34)
  have hC345 : Continuous fun t : ℝ =>
      if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta3 p).if_le hC45 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left heta_tau.le]
      exact congrArg (rot (Real.pi / 2 - p.theta)) hw34)
  have hD2345 : ∀ t : ℝ, HasDerivAt
      (fun s => if s ≤ p.theta then path2 p s
        else if s ≤ Real.pi / 2 - p.theta then path3 p s
        else if s ≤ Real.pi / 2 - p.phi then path4 p s else path5 p s)
      (if t ≤ p.theta then rot t (alphaBeta2 p t)
        else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path2 p) hD345
      (by rw [ite_eq_left htheta_eta.le]; exact hv23)
      (by rw [ite_eq_left htheta_eta.le]
          exact congrArg (rot p.theta) hw23)
  have hC2345 : Continuous fun t : ℝ =>
      if t ≤ p.theta then rot t (alphaBeta2 p t)
      else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta2 p).if_le hC345 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left htheta_eta.le]
      exact congrArg (rot p.theta) hw23)
  have hDpath : ∀ t : ℝ, HasDerivAt (path p)
      (if t ≤ p.phi then rot t (alphaBeta1 p t)
        else if t ≤ p.theta then rot t (alphaBeta2 p t)
        else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
        else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
        else rot t (alphaBeta5 p t)) t :=
    hasDerivAt_if_le (hasDerivAt_path1 p) hD2345
      (by rw [ite_eq_left hphi_theta.le]; exact hv12)
      (by rw [ite_eq_left hphi_theta.le]
          exact congrArg (rot p.phi) hw12)
  have hCpath : Continuous fun t : ℝ =>
      if t ≤ p.phi then rot t (alphaBeta1 p t)
      else if t ≤ p.theta then rot t (alphaBeta2 p t)
      else if t ≤ Real.pi / 2 - p.theta then rot t (alphaBeta3 p t)
      else if t ≤ Real.pi / 2 - p.phi then rot t (alphaBeta4 p t)
      else rot t (alphaBeta5 p t) :=
    (continuous_rot_alphaBeta1 p).if_le hC2345 continuous_id continuous_const (by
      intro t ht
      subst ht
      rw [ite_eq_left hphi_theta.le]
      exact congrArg (rot p.phi) hw12)
  -- The four derivative matches.
  have hdv12 : deriv (path1 p) p.phi = deriv (path2 p) p.phi := by
    rw [(hasDerivAt_path1 p p.phi).deriv, (hasDerivAt_path2 p p.phi).deriv, hw12]
  have hdv23 : deriv (path2 p) p.theta = deriv (path3 p) p.theta := by
    rw [(hasDerivAt_path2 p p.theta).deriv, (hasDerivAt_path3 p p.theta).deriv, hw23]
  have hdv34 : deriv (path3 p) (Real.pi / 2 - p.theta) =
      deriv (path4 p) (Real.pi / 2 - p.theta) := by
    rw [(hasDerivAt_path3 p _).deriv, (hasDerivAt_path4 p _).deriv, hw34]
  have hdv45 : deriv (path4 p) (Real.pi / 2 - p.phi) =
      deriv (path5 p) (Real.pi / 2 - p.phi) := by
    rw [(hasDerivAt_path4 p _).deriv, (hasDerivAt_path5 p _).deriv, hw45]
  refine ⟨contDiff_one_of_hasDerivAt hDpath hCpath, ?_, ?_⟩
  · -- `0 < φ` selects the first branch, and the normalizations make it vanish at `0`.
    have hk11 := k11_eq_one_sub_a1_of_equations (p := p) heq
    have hk12 := k12_eq_quarter_of_equations (p := p) heq
    have ha2 := a2_eq_neg_quarter_of_equations (p := p) heq
    have h0 : path p 0 = path1 p 0 := by
      unfold GerverSofa.Romik.path
      exact ite_eq_left hphi_pos.le
    rw [h0]
    simp only [path1, addK, rot, Real.cos_zero, Real.sin_zero, Prod.ext_iff, Prod.fst_zero,
      Prod.snd_zero]
    constructor <;> linarith
  · intro i
    fin_cases i
    · exact ⟨hv12, hdv12⟩
    · exact ⟨hv23, hdv23⟩
    · exact ⟨hv34, hdv34⟩
    · exact ⟨hv45, hdv45⟩

end MovingSofa
