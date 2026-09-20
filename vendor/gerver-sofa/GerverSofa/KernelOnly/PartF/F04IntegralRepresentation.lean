import GerverSofa.KernelOnly.PartF.F04IntegralEvaluation
import GerverSofa.KernelOnly.PartF.F03SetIdentification
import GerverSofa.KernelOnly.PartF.F01ParameterChoice

/-!
# F04: the literal integral path equals the closed five-phase path

All integral identities are proved in F04IntegralEvaluation. Reflection of the
closed intervals then gives the same five branches and the same endpoint choices
as F01. The final identification with PartC.params still requires the 22D
dictionary theorem; it remains an explicit hypothesis in the two last results.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.Integrals

open Phases Coordinates

theorem path_first_of_le (d : Reduced.Params) (t : ℝ) (ht : t ≤ d.phi) :
    (path d t).1 = Real.cos t - 1 := by
  simp only [path, if_pos ht]

theorem path_first_of_gt (d : Reduced.Params) (t : ℝ) (ht : d.phi < t) :
    (path d t).1 = W d (T - t) - 1 := by
  simp only [path, if_neg (not_le.mpr ht)]
  unfold W
  dsimp only [T]
  rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]

theorem path_second_of_le (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ≤ tau d) :
    (path d t).2 = W d t - ell d * Real.sin t - 1 := by
  simp only [path, if_pos ht]
  rw [xi_zero d ho hd]
  unfold W ell
  ring

theorem path_second_of_gt (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : tau d < t) :
    (path d t).2 = (1 - ell d) * Real.sin t - 1 := by
  simp only [path, if_neg (not_le.mpr ht)]
  rw [xi_zero d ho hd]
  unfold ell
  ring

theorem path_phase1 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ∈ Set.Icc 0 d.phi) :
    path d t = closed1 d t := by
  have hk := ordered_knots d ho
  have htau : t ≤ tau d := ht.2.trans (hk.2.1.trans (hk.2.2.1.trans hk.2.2.2.1))
  apply Prod.ext
  · exact path_first_of_le d t ht.2
  · rw [path_second_of_le d ho hd t htau, W_phase1 d ho hd t ht, U1_eq_half d hd]
    dsimp [closed1, r1]
    ring

theorem path_phase2 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : d.phi < t) (hhi : t ≤ d.theta) : path d t = closed2 d t := by
  have hk := ordered_knots d ho
  have hr : T - t ∈ Set.Icc (eta d) (tau d) := by
    dsimp [eta, tau]
    constructor <;> linarith
  have htau : t ≤ tau d := hhi.trans (hk.2.2.1.trans hk.2.2.2.1)
  apply Prod.ext
  · rw [path_first_of_gt d t hlo, W_phase4 d ho (T - t) hr]
    simp only [closed2, T, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · rw [path_second_of_le d ho hd t htau, W_phase2 d ho hd t ⟨hlo.le, hhi⟩]
    dsimp [closed2, U2]
    ring

theorem path_phase3 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : d.theta < t) (hhi : t ≤ eta d) : path d t = closed3 d t := by
  have hk := ordered_knots d ho
  have hphi : d.phi < t := lt_of_le_of_lt ho.2.1 hlo
  have hr : T - t ∈ Set.Icc d.theta (eta d) := by
    dsimp [eta] at *
    constructor <;> linarith
  have htau : t ≤ tau d := hhi.trans hk.2.2.2.1
  apply Prod.ext
  · rw [path_first_of_gt d t hphi, W_phase3 d ho hd (T - t) hr]
    simp only [closed3, T, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · rw [path_second_of_le d ho hd t htau, W_phase3 d ho hd t ⟨hlo.le, hhi⟩]
    dsimp [closed3]
    ring

theorem path_phase4 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : eta d < t) (hhi : t ≤ tau d) : path d t = closed4 d t := by
  have hk := ordered_knots d ho
  have hphi : d.phi < t := lt_of_le_of_lt (ho.2.1.trans hk.2.2.1) hlo
  have hr : T - t ∈ Set.Icc d.phi d.theta := by
    dsimp [eta, tau] at *
    constructor <;> linarith
  apply Prod.ext
  · rw [path_first_of_gt d t hphi, W_phase2 d ho hd (T - t) hr]
    simp only [closed4, U2, T, Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
  · rw [path_second_of_le d ho hd t hhi, W_phase4 d ho t ⟨hlo.le, hhi⟩]
    dsimp [closed4]
    ring

theorem path_phase5 (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ)
    (hlo : tau d < t) (hhi : t ≤ T) : path d t = closed5 d t := by
  have hk := ordered_knots d ho
  have hphi : d.phi < t :=
    lt_of_le_of_lt (ho.2.1.trans (hk.2.2.1.trans hk.2.2.2.1)) hlo
  have hr : T - t ∈ Set.Icc 0 d.phi := by
    dsimp [tau] at *
    constructor <;> linarith
  apply Prod.ext
  · rw [path_first_of_gt d t hphi, W_phase1 d ho hd (T - t) hr, U1_eq_half d hd]
    dsimp only [closed5, r1, T]
    rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub]
    ring
  · exact path_second_of_gt d ho hd t hlo

/-- The literal integral path, not just its formal candidate, has these phases. -/
theorem path_eq_closedPath (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    path d t = closedPath d t := by
  change path d t =
    (if t ≤ d.phi then closed1 d t
     else if t ≤ d.theta then closed2 d t
     else if t ≤ eta d then closed3 d t
     else if t ≤ tau d then closed4 d t
     else closed5 d t)
  by_cases h1 : t ≤ d.phi
  · simpa only [if_pos h1] using path_phase1 d ho hd t ⟨ht.1, h1⟩
  by_cases h2 : t ≤ d.theta
  · simpa only [if_neg h1, if_pos h2] using path_phase2 d ho hd t (lt_of_not_ge h1) h2
  by_cases h3 : t ≤ eta d
  · simpa only [if_neg h1, if_neg h2, if_pos h3] using
      path_phase3 d ho hd t (lt_of_not_ge h2) h3
  by_cases h4 : t ≤ tau d
  · simpa only [if_neg h1, if_neg h2, if_neg h3, if_pos h4] using
      path_phase4 d ho hd t (lt_of_not_ge h3) h4
  · simpa only [if_neg h1, if_neg h2, if_neg h3, if_neg h4] using
      path_phase5 d ho hd t (lt_of_not_ge h4) ht.2

theorem integral_rotation (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    rotation t (toPlane (path d t)) = toPlane (Romik.path (dictionary d) t) := by
  rw [path_eq_closedPath d ho hd t ht, CanonicalRotation.closedPath_rotation d hd t]

theorem integral_sofa_eq_worldSofa (d : Reduced.Params) (ho : Ordered d)
    (hd : Reduced.Equations d) :
    bodySofa (fun t => toPlane (path d t))
        Model.horizontalHallway Model.verticalHallway Model.hallway =
      worldSofa (fun t => toPlane (Romik.path (dictionary d) t))
        Model.horizontalHallway Model.verticalHallway Model.hallway := by
  apply bodySofa_eq_worldSofa_of_path_identity
  intro t ht
  exact (integral_rotation d ho hd t ht).symm

def certified : Reduced.Params := PartALeanCert.reducedCertifiedUniqueSolution.solution

theorem certified_ordered : Ordered certified := by
  have h := PartE.physicalDomain_of_mem_reducedBox
    PartALeanCert.reducedCertifiedUniqueSolution.solution_mem
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem certified_equations : Reduced.Equations certified :=
  PartALeanCert.reducedCertifiedUniqueSolution.satisfies

/-- An unconditional representation theorem for the certified reduced tuple. -/
theorem certified_integral_rotation (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    rotation t (toPlane (path certified t)) =
      toPlane (Romik.path (dictionary certified) t) :=
  integral_rotation certified certified_ordered certified_equations t ht

/-- Remaining obligation: identify the full dictionary with the independent 22D root. -/
theorem integral_sofa_eq_certified_of_dictionary
    (hdictionary : dictionary certified = PartC.params) :
    bodySofa (fun t => toPlane (path certified t))
        Model.horizontalHallway Model.verticalHallway Model.hallway =
      EuclideanMotion.sofa := by
  rw [integral_sofa_eq_worldSofa certified certified_ordered certified_equations,
    hdictionary, ← SetIdentification.sofa_eq_worldSofa]

end GerverSofa.PartF.Integrals
