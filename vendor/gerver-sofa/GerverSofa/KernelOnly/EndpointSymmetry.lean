import GerverSofa.Boxes

/-!
# Endpoint symmetry derived from the direct 22-dimensional system

The manuscript obtains the terminal condition `x₂(π/2)=0` from the reflection
symmetry of the five phases.  This file proves the required consequence
without introducing a symmetry assumption and without using numerical
approximations.

FIX12 keeps the BATCH11 mathematics and public theorem statements unchanged,
but factors the formula-level algebra into small coordinate identities.  This
avoids asking `ring` to normalize the fully unfolded five-phase expressions in
one large proof term.
-/

noncomputable section

namespace GerverSofa.Romik

/-! ## Exact parameter consequences of equations 27--34 -/

/-- Equation 27. -/
theorem e1_eq_a1_of_equations {p : Params} (heq : Equations p) :
    p.e1 = p.a1 := by
  have h0 := congrFun heq (0 : Fin 22)
  simp [Equations, system] at h0
  linarith

/-- Equation 28. -/
theorem e2_eq_neg_a2_of_equations {p : Params} (heq : Equations p) :
    p.e2 = -p.a2 := by
  have h1 := congrFun heq (1 : Fin 22)
  simp [Equations, system] at h1
  linarith

/-- Equation 29. -/
theorem d1_eq_quarterPi_sub_b1_of_equations
    {p : Params} (heq : Equations p) :
    p.d1 = Real.pi / 4 - p.b1 := by
  have h2 := congrFun heq (2 : Fin 22)
  simp [Equations, system] at h2
  linarith

/-- Equation 30. -/
theorem d2_eq_b2_add_quarterPi_correction_of_equations
    {p : Params} (heq : Equations p) :
    p.d2 = p.b2 + (Real.pi / 4) * (2 * p.b1 - Real.pi / 4) := by
  have h3 := congrFun heq (3 : Fin 22)
  simp [Equations, system] at h3
  linarith

/-- Equation 31. -/
theorem c2_eq_c1_sub_halfPi_of_equations
    {p : Params} (heq : Equations p) :
    p.c2 = p.c1 - Real.pi / 2 := by
  have h4 := congrFun heq (4 : Fin 22)
  simp [Equations, system] at h4
  linarith

/-- Equation 33. -/
theorem k12_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.k12 = (1 / 4 : ℝ) := by
  have h6 := congrFun heq (6 : Fin 22)
  simp [Equations, system] at h6
  linarith

/-- Equation 34. -/
theorem a2_eq_neg_quarter_of_equations {p : Params} (heq : Equations p) :
    p.a2 = -(1 / 4 : ℝ) := by
  have h7 := congrFun heq (7 : Fin 22)
  simp [Equations, system] at h7
  linarith

/-- Equations 28 and 34. -/
theorem e2_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.e2 = (1 / 4 : ℝ) := by
  rw [e2_eq_neg_a2_of_equations heq, a2_eq_neg_quarter_of_equations heq]
  norm_num

/-! ## Small definitional coordinate identities

These are deliberately `rfl`: they expose only the second coordinate of one
phase at a time.  Downstream algebra therefore operates on compact scalar
expressions rather than on the fully unfolded `Point`/`rot`/`addK` terms. -/

private theorem path1_snd_formula (p : Params) (t : ℝ) :
    (path1 p t).2 =
      Real.sin t *
          (p.a1 * Real.cos t + p.a2 * Real.sin t - 1) +
        Real.cos t *
          (-p.a2 * Real.cos t + p.a1 * Real.sin t - 1 / 2) +
        p.k12 := by
  rfl

private theorem path2_snd_formula (p : Params) (t : ℝ) :
    (path2 p t).2 =
      Real.sin t *
          (-(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2) +
        Real.cos t *
          ((1 / 2 : ℝ) * t - p.b1 - 1) +
        p.k22 := by
  rfl

private theorem path3_snd_formula (p : Params) (t : ℝ) :
    (path3 p t).2 =
      Real.sin t * (p.c1 - t) +
        Real.cos t * (p.c2 + t) +
        p.k32 := by
  rfl

private theorem path4_snd_formula (p : Params) (t : ℝ) :
    (path4 p t).2 =
      Real.sin t *
          (-(1 / 2 : ℝ) * t + p.d1 - 1) +
        Real.cos t *
          (-(1 / 4 : ℝ) * t * t + p.d1 * t + p.d2) +
        p.k42 := by
  rfl

private theorem path5_snd_formula (p : Params) (t : ℝ) :
    (path5 p t).2 =
      Real.sin t *
          (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2) +
        Real.cos t *
          (-p.e2 * Real.cos t + p.e1 * Real.sin t - 1) +
        p.k52 := by
  rfl

/-! ## Formula-level reflection identities -/

/-- The vertical phase-5 formula at reflected time differs from phase 1 only
by its vertical translation constant. -/
theorem phase15_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path5 p (Real.pi / 2 - t)).2 - p.k52 =
      (path1 p t).2 - p.k12 := by
  rw [path5_snd_formula, path1_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [e1_eq_a1_of_equations heq, e2_eq_neg_a2_of_equations heq]
  ring

/-- The vertical phase-4 formula at reflected time differs from phase 2 only
by its vertical translation constant. -/
theorem phase24_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path4 p (Real.pi / 2 - t)).2 - p.k42 =
      (path2 p t).2 - p.k22 := by
  rw [path4_snd_formula, path2_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  rw [d1_eq_quarterPi_sub_b1_of_equations heq,
    d2_eq_b2_add_quarterPi_correction_of_equations heq]
  have hlinear :
      -(1 / 2 : ℝ) * (Real.pi / 2 - t) +
          (Real.pi / 4 - p.b1) - 1 =
        (1 / 2 : ℝ) * t - p.b1 - 1 := by
    ring
  have hquadratic :
      -(1 / 4 : ℝ) * (Real.pi / 2 - t) * (Real.pi / 2 - t) +
          (Real.pi / 4 - p.b1) * (Real.pi / 2 - t) +
          (p.b2 + (Real.pi / 4) * (2 * p.b1 - Real.pi / 4)) =
        -(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2 := by
    ring <;> norm_num
  rw [hlinear, hquadratic]
  ring

/-- The middle phase has exact vertical reflection symmetry. -/
theorem phase3_vertical_reflection_of_equations
    {p : Params} (heq : Equations p) (t : ℝ) :
    (path3 p (Real.pi / 2 - t)).2 = (path3 p t).2 := by
  rw [path3_snd_formula, path3_snd_formula]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  have hc2 := c2_eq_c1_sub_halfPi_of_equations heq
  have hleft :
      p.c1 - (Real.pi / 2 - t) = p.c2 + t := by
    rw [hc2]
    ring
  have hright :
      p.c2 + (Real.pi / 2 - t) = p.c1 - t := by
    rw [hc2]
    ring
  rw [hleft, hright]
  ring

/-! ## Translation constants forced by matching -/

/-- Matching at `θ` and `π/2-θ`, together with middle-phase reflection,
forces the phase-2 and phase-4 vertical translations to coincide. -/
theorem k42_eq_k22_of_equations {p : Params} (heq : Equations p) :
    p.k42 = p.k22 := by
  have h23 : (path2 p p.theta).2 = (path3 p p.theta).2 :=
    congrArg Prod.snd (match_path23_of_equations heq)
  have h34 : (path3 p (Real.pi / 2 - p.theta)).2 =
      (path4 p (Real.pi / 2 - p.theta)).2 :=
    congrArg Prod.snd (match_path34_of_equations heq)
  have h24 := phase24_vertical_reflection_of_equations heq p.theta
  have h33 := phase3_vertical_reflection_of_equations heq p.theta
  rw [← h34, h33, ← h23] at h24
  linarith

/-- Matching at `φ` and `π/2-φ` then forces the phase-1 and phase-5 vertical
translations to coincide. -/
theorem k52_eq_k12_of_equations {p : Params} (heq : Equations p) :
    p.k52 = p.k12 := by
  have h12 : (path1 p p.phi).2 = (path2 p p.phi).2 :=
    congrArg Prod.snd (match_path12_of_equations heq)
  have h45 : (path4 p (Real.pi / 2 - p.phi)).2 =
      (path5 p (Real.pi / 2 - p.phi)).2 :=
    congrArg Prod.snd (match_path45_of_equations heq)
  have h24 := phase24_vertical_reflection_of_equations heq p.phi
  have hk := k42_eq_k22_of_equations heq
  rw [hk] at h24
  have hy42 :
      (path4 p (Real.pi / 2 - p.phi)).2 = (path2 p p.phi).2 := by
    linarith
  have hy51 :
      (path5 p (Real.pi / 2 - p.phi)).2 = (path1 p p.phi).2 := by
    calc
      (path5 p (Real.pi / 2 - p.phi)).2 =
          (path4 p (Real.pi / 2 - p.phi)).2 := by
            exact h45.symm
      _ = (path2 p p.phi).2 := hy42
      _ = (path1 p p.phi).2 := h12.symm
  have h15 := phase15_vertical_reflection_of_equations heq p.phi
  rw [hy51] at h15
  linarith

/-- Equations 27--41 force the previously dependent coefficient `k₅₂=1/4`.
It is not an independent hypothesis of the final certificate. -/
theorem k52_eq_quarter_of_equations {p : Params} (heq : Equations p) :
    p.k52 = (1 / 4 : ℝ) := by
  rw [k52_eq_k12_of_equations heq, k12_eq_quarter_of_equations heq]

/-! ## Terminal condition -/

/-- The explicit fifth phase ends at vertical coordinate zero. -/
theorem path5_end_y_zero_of_equations {p : Params} (heq : Equations p) :
    (path5 p (Real.pi / 2)).2 = 0 := by
  rw [path5_snd_formula]
  simp [e2_eq_quarter_of_equations heq,
    k52_eq_quarter_of_equations heq] <;> norm_num

/-- The certified direct-system box places `π/2` strictly after the fourth
switch, so the literal nested-`if` path uses phase 5 at the endpoint. -/
theorem path_halfPi_eq_path5_of_mem_box {p : Params} (hp : p ∈ box) :
    path p (Real.pi / 2) = path5 p (Real.pi / 2) := by
  have hphi : 0 < p.phi := phi_pos_of_mem_box hp
  have hord : SwitchOrder p := switchOrder_of_mem_box hp
  have hthetaPos : 0 < p.theta := lt_of_lt_of_le hphi hord.phi_le_theta
  have hthetaLt : p.theta < Real.pi / 2 := by
    linarith [hord.theta_le_eta]
  have hphiLt : p.phi < Real.pi / 2 :=
    lt_of_le_of_lt hord.phi_le_theta hthetaLt
  have hetaLt : Real.pi / 2 - p.theta < Real.pi / 2 := by
    linarith
  have htauLt : Real.pi / 2 - p.phi < Real.pi / 2 := by
    linarith
  simp [path, not_le.mpr hphiLt, not_le.mpr hthetaLt,
    not_le.mpr hetaLt, not_le.mpr htauLt]

/-- The terminal vertical normalisation is a theorem of the concrete box and
22 equations.  No reflection hypothesis and no certificate field remain. -/
theorem path_end_y_zero_of_mem_box_and_equations
    {p : Params} (hp : p ∈ box) (heq : Equations p) :
    (path p (Real.pi / 2)).2 = 0 := by
  rw [path_halfPi_eq_path5_of_mem_box hp]
  exact path5_end_y_zero_of_equations heq

end GerverSofa.Romik
