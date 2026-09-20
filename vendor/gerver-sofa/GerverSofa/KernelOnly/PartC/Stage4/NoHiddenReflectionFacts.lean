import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenDifferentialFacts

/-!
# Part C Stage 4: exact reflection bridge for the second no-hidden inequality

The affine reflection is derived phase by phase from the certified matching
equations.  No global symmetry hypothesis is introduced.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

def noHiddenHReflect (z : Point) : Point :=
  (2 * params.k31 - z.1, z.2)

@[simp] theorem noHiddenHReflect_involutive (z : Point) :
    noHiddenHReflect (noHiddenHReflect z) = z := by
  ext <;> simp [noHiddenHReflect]

private theorem phase24_horizontal_reflection_noHidden (s : ℝ) :
    (Romik.path4 params (T - s)).1 + (Romik.path2 params s).1 =
      params.k41 + params.k21 := by
  have hd1 := Romik.d1_eq_quarterPi_sub_b1_of_equations params_equations
  have hd2 :=
    Romik.d2_eq_b2_add_quarterPi_correction_of_equations params_equations
  dsimp [T, Romik.path4, Romik.path2, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hd1, hd2]
  ring

private theorem phase3_horizontal_reflection_noHidden (s : ℝ) :
    (Romik.path3 params (T - s)).1 + (Romik.path3 params s).1 =
      2 * params.k31 := by
  have hc2 := Romik.c2_eq_c1_sub_halfPi_of_equations params_equations
  dsimp [T, Romik.path3, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, hc2]
  ring

private theorem k41_add_k21_eq_two_k31_noHidden :
    params.k41 + params.k21 = 2 * params.k31 := by
  have h24 := phase24_horizontal_reflection_noHidden params.theta
  have h33 := phase3_horizontal_reflection_noHidden params.theta
  have h23 := congrArg Prod.fst PartB.match23
  have h34 := congrArg Prod.fst PartB.match34
  simp only [eta, T] at h24 h33 h34
  linarith

private theorem phase24_reflect_noHidden (s : ℝ) :
    Romik.path4 params (T - s) =
      noHiddenHReflect (Romik.path2 params s) := by
  apply Prod.ext
  · have h := phase24_horizontal_reflection_noHidden s
    rw [k41_add_k21_eq_two_k31_noHidden] at h
    dsimp [noHiddenHReflect]
    linarith
  · have h :=
      Romik.phase24_vertical_reflection_of_equations params_equations s
    have hk := Romik.k42_eq_k22_of_equations params_equations
    rw [hk] at h
    dsimp [T] at h ⊢
    dsimp [noHiddenHReflect]
    linarith

private theorem phase42_reflect_noHidden (s : ℝ) :
    Romik.path2 params (T - s) =
      noHiddenHReflect (Romik.path4 params s) := by
  have h := congrArg noHiddenHReflect
    (phase24_reflect_noHidden (T - s))
  have hT : T - (T - s) = s := by ring
  rw [hT, noHiddenHReflect_involutive] at h
  exact h.symm

private theorem phase3_reflect_noHidden (s : ℝ) :
    Romik.path3 params (T - s) =
      noHiddenHReflect (Romik.path3 params s) := by
  apply Prod.ext
  · have h := phase3_horizontal_reflection_noHidden s
    dsimp [noHiddenHReflect]
    linarith
  · have h :=
      Romik.phase3_vertical_reflection_of_equations params_equations s
    simpa [T, noHiddenHReflect] using h

private theorem phase15_horizontal_reflection_noHidden (s : ℝ) :
    (Romik.path5 params (T - s)).1 + (Romik.path1 params s).1 =
      params.k51 + params.k11 := by
  have he1 := Romik.e1_eq_a1_of_equations params_equations
  have he2 := Romik.e2_eq_neg_a2_of_equations params_equations
  dsimp [T, Romik.path5, Romik.path1, Romik.rot, Romik.addK]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub, he1, he2]
  ring

private theorem k51_add_k11_eq_two_k31_noHidden :
    params.k51 + params.k11 = 2 * params.k31 := by
  have h15 := phase15_horizontal_reflection_noHidden params.phi
  have h24 := phase24_horizontal_reflection_noHidden params.phi
  have h12 := congrArg Prod.fst PartB.match12
  have h45 := congrArg Prod.fst PartB.match45
  rw [k41_add_k21_eq_two_k31_noHidden] at h24
  simp only [tau, T] at h15 h24 h45
  linarith

private theorem phase15_reflect_noHidden (s : ℝ) :
    Romik.path5 params (T - s) =
      noHiddenHReflect (Romik.path1 params s) := by
  apply Prod.ext
  · have h := phase15_horizontal_reflection_noHidden s
    rw [k51_add_k11_eq_two_k31_noHidden] at h
    dsimp [noHiddenHReflect]
    linarith
  · have h :=
      Romik.phase15_vertical_reflection_of_equations params_equations s
    have hk := Romik.k52_eq_k12_of_equations params_equations
    rw [hk] at h
    dsimp [T] at h ⊢
    dsimp [noHiddenHReflect]
    linarith

private theorem phase51_reflect_noHidden (s : ℝ) :
    Romik.path1 params (T - s) =
      noHiddenHReflect (Romik.path5 params s) := by
  have h := congrArg noHiddenHReflect
    (phase15_reflect_noHidden (T - s))
  have hT : T - (T - s) = s := by ring
  rw [hT, noHiddenHReflect_involutive] at h
  exact h.symm

private theorem path_eq_phase1_noHidden {s : ℝ} (hs : s ≤ params.phi) :
    Romik.path params s = Romik.path1 params s := by
  simp only [Romik.path, if_pos hs]

private theorem path_eq_phase2_noHidden {s : ℝ}
    (hphi : params.phi < s) (hs : s ≤ params.theta) :
    Romik.path params s = Romik.path2 params s := by
  simp only [Romik.path, if_neg (not_le.mpr hphi), if_pos hs]

private theorem path_eq_phase3_noHidden {s : ℝ}
    (htheta : params.theta < s) (hs : s ≤ eta) :
    Romik.path params s = Romik.path3 params s := by
  have hphi : params.phi < s := lt_trans phi_lt_theta htheta
  simpa only [eta, T] using
    (show Romik.path params s = Romik.path3 params s by
      simp only [Romik.path, if_neg (not_le.mpr hphi),
        if_neg (not_le.mpr htheta), if_pos (by simpa [eta, T] using hs)])

private theorem path_eq_phase4_noHidden {s : ℝ}
    (heta : eta < s) (hs : s ≤ tau) :
    Romik.path params s = Romik.path4 params s := by
  have htheta : params.theta < s := lt_trans theta_lt_eta heta
  have hphi : params.phi < s := lt_trans phi_lt_theta htheta
  have hnotEta : ¬ s ≤ Real.pi / 2 - params.theta := by
    apply not_le.mpr
    simpa only [eta, T] using heta
  have hleTau : s ≤ Real.pi / 2 - params.phi := by
    simpa only [tau, T] using hs
  simp only [Romik.path, if_neg (not_le.mpr hphi),
    if_neg (not_le.mpr htheta),
    if_neg hnotEta, if_pos hleTau]

private theorem path_eq_phase5_noHidden {s : ℝ} (hs : tau < s) :
    Romik.path params s = Romik.path5 params s := by
  have heta : eta < s := lt_trans eta_lt_tau hs
  have htheta : params.theta < s := lt_trans theta_lt_eta heta
  have hphi : params.phi < s := lt_trans phi_lt_theta htheta
  have hnotEta : ¬ s ≤ Real.pi / 2 - params.theta := by
    apply not_le.mpr
    simpa only [eta, T] using heta
  have hnotTau : ¬ s ≤ Real.pi / 2 - params.phi := by
    apply not_le.mpr
    simpa only [tau, T] using hs
  simp only [Romik.path, if_neg (not_le.mpr hphi),
    if_neg (not_le.mpr htheta),
    if_neg hnotEta, if_neg hnotTau]

/-- Exact global horizontal reflection of the literal five-piece path. -/
theorem path_reflect_noHidden {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    Romik.path params (T - s) =
      noHiddenHReflect (Romik.path params s) := by
  by_cases h1 : s ≤ params.phi
  · by_cases he : s = params.phi
    · subst s
      rw [show T - params.phi = tau by rfl,
        path_eq_phase4_noHidden eta_lt_tau le_rfl,
        path_eq_phase1_noHidden le_rfl]
      exact (phase24_reflect_noHidden params.phi).trans
        (congrArg noHiddenHReflect PartB.match12.symm)
    · have hsphi : s < params.phi := lt_of_le_of_ne h1 he
      have href : tau < T - s := by dsimp [tau]; linarith
      rw [path_eq_phase5_noHidden href, path_eq_phase1_noHidden h1]
      exact phase15_reflect_noHidden s
  · have hphi : params.phi < s := lt_of_not_ge h1
    by_cases h2 : s ≤ params.theta
    · by_cases he : s = params.theta
      · subst s
        rw [show T - params.theta = eta by rfl,
          path_eq_phase3_noHidden theta_lt_eta le_rfl,
          path_eq_phase2_noHidden phi_lt_theta le_rfl]
        exact (phase3_reflect_noHidden params.theta).trans
          (congrArg noHiddenHReflect PartB.match23.symm)
      · have hstheta : s < params.theta := lt_of_le_of_ne h2 he
        have hetaRef : eta < T - s := by dsimp [eta]; linarith
        have htauRef : T - s ≤ tau := by dsimp [tau]; linarith
        rw [path_eq_phase4_noHidden hetaRef htauRef,
          path_eq_phase2_noHidden hphi h2]
        exact phase24_reflect_noHidden s
    · have htheta : params.theta < s := lt_of_not_ge h2
      by_cases h3 : s ≤ eta
      · by_cases he : s = eta
        · subst s
          rw [show T - eta = params.theta by
                dsimp [eta]; ring,
            path_eq_phase2_noHidden phi_lt_theta le_rfl,
            path_eq_phase3_noHidden theta_lt_eta le_rfl]
          have h := congrArg noHiddenHReflect
            (phase3_reflect_noHidden params.theta)
          rw [noHiddenHReflect_involutive] at h
          simpa [eta] using (PartB.match23.trans h.symm)
        · have hseta : s < eta := lt_of_le_of_ne h3 he
          have hthetaRef : params.theta < T - s := by
            dsimp [eta] at hseta
            linarith
          have hetaRef : T - s ≤ eta := by dsimp [eta]; linarith
          rw [path_eq_phase3_noHidden hthetaRef hetaRef,
            path_eq_phase3_noHidden htheta h3]
          exact phase3_reflect_noHidden s
      · have hetaS : eta < s := lt_of_not_ge h3
        by_cases h4 : s ≤ tau
        · by_cases he : s = tau
          · subst s
            rw [show T - tau = params.phi by
                  dsimp [tau]; ring,
              path_eq_phase1_noHidden le_rfl,
              path_eq_phase4_noHidden eta_lt_tau le_rfl]
            have h := congrArg noHiddenHReflect
              (phase24_reflect_noHidden params.phi)
            rw [noHiddenHReflect_involutive] at h
            simpa [tau] using (PartB.match12.trans h.symm)
          · have hstau : s < tau := lt_of_le_of_ne h4 he
            have hphiRef : params.phi < T - s := by
              dsimp [tau] at hstau
              linarith
            have hthetaRef : T - s ≤ params.theta := by
              dsimp [eta] at hetaS
              linarith
            rw [path_eq_phase2_noHidden hphiRef hthetaRef,
              path_eq_phase4_noHidden hetaS h4]
            exact phase42_reflect_noHidden s
        · have htauS : tau < s := lt_of_not_ge h4
          have href0 : 0 ≤ T - s := by linarith [hs.2]
          have hrefphi : T - s ≤ params.phi := by
            dsimp [tau] at htauS
            linarith
          rw [path_eq_phase1_noHidden hrefphi,
            path_eq_phase5_noHidden htauS]
          exact phase51_reflect_noHidden s

/-- Reflection transports the second no-hidden scalar to the first one. -/
theorem VValue_eq_reflected_UValue {t r : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (hr : r ∈ Icc (0 : ℝ) T) :
    Stage2.VValue t r = Stage2.UValue (T-r) (T-t) := by
  rw [Stage2.VValue, Stage2.UValue,
    path_reflect_noHidden hr, path_reflect_noHidden ht]
  dsimp [dot, noHiddenHReflect, u, v, T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  ring

end Stage4
end PartC
end GerverSofa
