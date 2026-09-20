import GerverSofa.SE2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The concrete reduced and 22-dimensional Romik systems

These are direct Lean transcriptions of equations (F1)--(F4) and of the
independent equations (27)--(39), (41), (43) used by the companion verifier.
-/

namespace GerverSofa

noncomputable section

namespace Reduced

structure Params where
  a : ℝ
  b : ℝ
  phi : ℝ
  theta : ℝ

/-- Four-dimensional reduced switching system. -/
def system (p : Params) : Fin 4 → ℝ :=
  let cp := Real.cos p.phi
  let sp := Real.sin p.phi
  let ct := Real.cos p.theta
  let st := Real.sin p.theta
  let delta := p.theta - p.phi
  ![
    p.a * (ct - cp) - 2 * p.b * sp + (delta - 1) * ct - st + cp + sp,
    p.a * (3 * st + sp) - 2 * p.b * cp + 3 * (delta - 1) * st + 3 * ct - sp + cp,
    p.a * cp - sp - (1 / 2 : ℝ) + (1 / 2 : ℝ) * cp - p.b * sp,
    p.a + Real.pi / 2 - p.phi - p.theta - p.b
      + (1 / 2 : ℝ) * delta * (1 + p.a) + (1 / 4 : ℝ) * delta * delta
  ]

/-- The proposition that all four reduced equations vanish. -/
def Equations (p : Params) : Prop := system p = 0

end Reduced

namespace Romik

structure Params where
  k11 : ℝ
  k12 : ℝ
  k21 : ℝ
  k22 : ℝ
  k31 : ℝ
  k32 : ℝ
  k41 : ℝ
  k42 : ℝ
  k51 : ℝ
  k52 : ℝ
  a1 : ℝ
  a2 : ℝ
  b1 : ℝ
  b2 : ℝ
  c1 : ℝ
  c2 : ℝ
  d1 : ℝ
  d2 : ℝ
  e1 : ℝ
  e2 : ℝ
  phi : ℝ
  theta : ℝ

/-- Rotation of a body-frame vector into the world frame. -/
def rot (t : ℝ) (z : Point) : Point :=
  (Real.cos t * z.1 - Real.sin t * z.2,
   Real.sin t * z.1 + Real.cos t * z.2)

def addK (r : Point) (kx ky : ℝ) : Point := (r.1 + kx, r.2 + ky)

/-- Phase 1 of the five-phase Gerver path. -/
def path1 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (p.a1 * Real.cos t + p.a2 * Real.sin t - 1,
     -p.a2 * Real.cos t + p.a1 * Real.sin t - 1 / 2)
  addK (rot t z) p.k11 p.k12

/-- Phase 2 of the five-phase Gerver path. -/
def path2 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (-(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2,
     (1 / 2 : ℝ) * t - p.b1 - 1)
  addK (rot t z) p.k21 p.k22

/-- Phase 3 of the five-phase Gerver path. -/
def path3 (p : Params) (t : ℝ) : Point :=
  addK (rot t (p.c1 - t, p.c2 + t)) p.k31 p.k32

/-- Phase 4 of the five-phase Gerver path. -/
def path4 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (-(1 / 2 : ℝ) * t + p.d1 - 1,
     -(1 / 4 : ℝ) * t * t + p.d1 * t + p.d2)
  addK (rot t z) p.k41 p.k42

/-- Phase 5 of the five-phase Gerver path. -/
def path5 (p : Params) (t : ℝ) : Point :=
  let z : Point :=
    (p.e1 * Real.cos t + p.e2 * Real.sin t - 1 / 2,
     -p.e2 * Real.cos t + p.e1 * Real.sin t - 1)
  addK (rot t z) p.k51 p.k52

/-- Body-frame derivative coefficients `(alpha,beta)` on phase 1. -/
def alphaBeta1 (p : Params) (t : ℝ) : Point :=
  (-2 * p.a1 * Real.sin t + 2 * p.a2 * Real.cos t + 1 / 2,
   2 * p.a1 * Real.cos t + 2 * p.a2 * Real.sin t - 1)

def alphaBeta2 (p : Params) (t : ℝ) : Point :=
  (1 + 2 * p.b1 - t,
   -(1 / 4 : ℝ) * t * t + p.b1 * t + p.b2 + 1 / 2)

def alphaBeta3 (p : Params) (t : ℝ) : Point :=
  (-1 - p.c2 - t, 1 + p.c1 - t)

def alphaBeta4 (p : Params) (t : ℝ) : Point :=
  ((1 / 4 : ℝ) * t * t - p.d1 * t - p.d2 - 1 / 2,
   2 * p.d1 - 1 - t)

def alphaBeta5 (p : Params) (t : ℝ) : Point :=
  (1 - 2 * p.e1 * Real.sin t + 2 * p.e2 * Real.cos t,
   2 * p.e1 * Real.cos t + 2 * p.e2 * Real.sin t - 1 / 2)

private def pathPrimeFromAB (t : ℝ) (ab : Point) : Point := rot t ab

def pathPrime1 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta1 p t)
def pathPrime2 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta2 p t)
def pathPrime3 (p : Params) (t : ℝ) : Point := pathPrimeFromAB t (alphaBeta3 p t)

/-- Romik's 22 independent scalar equations. -/
def system (p : Params) : Fin 22 → ℝ :=
  let halfPi := Real.pi / 2
  let quarterPi := Real.pi / 4
  let eta := halfPi - p.theta
  let tau := halfPi - p.phi
  let x1phi := path1 p p.phi
  let x2phi := path2 p p.phi
  let v1phi := pathPrime1 p p.phi
  let v2phi := pathPrime2 p p.phi
  let x2theta := path2 p p.theta
  let x3theta := path3 p p.theta
  let v2theta := pathPrime2 p p.theta
  let v3theta := pathPrime3 p p.theta
  let x3eta := path3 p eta
  let x4eta := path4 p eta
  let x4tau := path4 p tau
  let x5tau := path5 p tau
  let abEta := alphaBeta3 p eta
  let bEta : Point :=
    (x3eta.1 - abEta.1 * Real.sin eta,
     x3eta.2 + abEta.1 * Real.cos eta)
  ![
    p.e1 - p.a1,
    p.e2 + p.a2,
    p.d1 + p.b1 - quarterPi,
    p.d2 - p.b2 - quarterPi * (2 * p.b1 - quarterPi),
    p.c2 - p.c1 + halfPi,
    p.k11 - 1 + p.a1,
    p.k12 - 1 / 4,
    p.a2 + 1 / 4,
    x1phi.1 - x2phi.1,
    x1phi.2 - x2phi.2,
    v1phi.1 - v2phi.1,
    v1phi.2 - v2phi.2,
    x2theta.1 - x3theta.1,
    x2theta.2 - x3theta.2,
    v2theta.1 - v3theta.1,
    v2theta.2 - v3theta.2,
    x3eta.1 - x4eta.1,
    x3eta.2 - x4eta.2,
    x4tau.1 - x5tau.1,
    x4tau.2 - x5tau.2,
    x1phi.1 - bEta.1,
    x1phi.2 - bEta.2
  ]

/-- The proposition that all 22 independent equations vanish. -/
def Equations (p : Params) : Prop := system p = 0

end Romik

namespace Romik

/-- The physical five-phase path on `[0,π/2]`.  At a switching angle either
adjacent formula may be chosen; the certified matching equations prove they
coincide. -/
def path (p : Params) (t : ℝ) : Point :=
  let eta := Real.pi / 2 - p.theta
  let tau := Real.pi / 2 - p.phi
  if t ≤ p.phi then path1 p t
  else if t ≤ p.theta then path2 p t
  else if t ≤ eta then path3 p t
  else if t ≤ tau then path4 p t
  else path5 p t

/-- Linear normalization from unit time to physical rotation angle. -/
def angle (u : ℝ) : ℝ := u * (Real.pi / 2)

/-- Standard-to-world frame `q ↦ x(t)+R_t q` for normalized time. -/
def frame (p : Params) (u : ℝ) : SE2 :=
  let t := angle u
  let x := path p t
  { c := Real.cos t
    s := Real.sin t
    tx := x.1
    ty := x.2
    unit := by nlinarith [Real.sin_sq_add_cos_sq t] }

end Romik

namespace Romik

@[simp] theorem angle_zero : angle 0 = 0 := by
  simp [angle]

@[simp] theorem angle_one : angle 1 = Real.pi / 2 := by
  simp [angle]

/-- The normalized physical angle depends continuously on time. -/
theorem continuous_angle : Continuous angle := by
  unfold angle
  fun_prop

/-- Continuity of the five-phase path implies componentwise continuity of the
supporting `SE(2)` frame. -/
theorem continuousPath_frame_of_path
    (p : Params) (hpath : Continuous (path p)) :
    SE2.ContinuousPath (frame p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change Continuous (fun u : ℝ => Real.cos (angle u))
    simpa [Function.comp_def] using (Real.continuous_cos.comp continuous_angle)
  · change Continuous (fun u : ℝ => Real.sin (angle u))
    simpa [Function.comp_def] using (Real.continuous_sin.comp continuous_angle)
  · change Continuous (fun u : ℝ => (path p (angle u)).1)
    have hp : Continuous (fun u : ℝ => path p (angle u)) := by
      simpa [Function.comp_def] using (hpath.comp continuous_angle)
    exact hp.fst
  · change Continuous (fun u : ℝ => (path p (angle u)).2)
    have hp : Continuous (fun u : ℝ => path p (angle u)) := by
      simpa [Function.comp_def] using (hpath.comp continuous_angle)
    exact hp.snd

end Romik

namespace Romik

/-! ## Continuity from the independent matching equations -/

/-- Ordering data needed to read the five branches in their intended order. -/
structure SwitchOrder (p : Params) : Prop where
  phi_le_theta : p.phi ≤ p.theta
  theta_le_eta : p.theta ≤ Real.pi / 2 - p.theta
  eta_le_tau : Real.pi / 2 - p.theta ≤ Real.pi / 2 - p.phi

private theorem continuous_path1 (p : Params) : Continuous (path1 p) := by
  unfold path1 addK rot
  fun_prop

private theorem continuous_path2 (p : Params) : Continuous (path2 p) := by
  unfold path2 addK rot
  fun_prop

private theorem continuous_path3 (p : Params) : Continuous (path3 p) := by
  unfold path3 addK rot
  fun_prop

private theorem continuous_path4 (p : Params) : Continuous (path4 p) := by
  unfold path4 addK rot
  fun_prop

private theorem continuous_path5 (p : Params) : Continuous (path5 p) := by
  unfold path5 addK rot
  fun_prop

/-- Equation (35), extracted from the direct 22D system. -/
theorem match_path12_of_equations {p : Params} (heq : Equations p) :
    path1 p p.phi = path2 p p.phi := by
  have h8 := congrFun heq (8 : Fin 22)
  have h9 := congrFun heq (9 : Fin 22)
  simp [Equations, system] at h8 h9
  apply Prod.ext <;> linarith

/-- Equation (37), extracted from the direct 22D system. -/
theorem match_path23_of_equations {p : Params} (heq : Equations p) :
    path2 p p.theta = path3 p p.theta := by
  have h12 := congrFun heq (12 : Fin 22)
  have h13 := congrFun heq (13 : Fin 22)
  simp [Equations, system] at h12 h13
  apply Prod.ext <;> linarith

/-- Equation (39), extracted from the direct 22D system. -/
theorem match_path34_of_equations {p : Params} (heq : Equations p) :
    path3 p (Real.pi / 2 - p.theta) =
      path4 p (Real.pi / 2 - p.theta) := by
  have h16 := congrFun heq (16 : Fin 22)
  have h17 := congrFun heq (17 : Fin 22)
  simp [Equations, system] at h16 h17
  apply Prod.ext <;> linarith

/-- Equation (41), extracted from the direct 22D system. -/
theorem match_path45_of_equations {p : Params} (heq : Equations p) :
    path4 p (Real.pi / 2 - p.phi) =
      path5 p (Real.pi / 2 - p.phi) := by
  have h18 := congrFun heq (18 : Fin 22)
  have h19 := congrFun heq (19 : Fin 22)
  simp [Equations, system] at h18 h19
  apply Prod.ext <;> linarith

/-- The four positional matching equations make the literal nested-`if`
five-phase path continuous whenever its switches are ordered. -/
theorem continuous_path_of_order_and_equations
    {p : Params} (hord : SwitchOrder p) (heq : Equations p) :
    Continuous (path p) := by
  have h12 := match_path12_of_equations heq
  have h23 := match_path23_of_equations heq
  have h34 := match_path34_of_equations heq
  have h45 := match_path45_of_equations heq

  have hc45 : Continuous
      (fun t : ℝ =>
        if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path4 p).if_le (continuous_path5 p)
      continuous_id continuous_const (by
        intro t ht
        subst t
        exact h45)

  have hc345 : Continuous
      (fun t : ℝ =>
        if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path3 p).if_le hc45
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [if_pos hord.eta_le_tau]
        exact h34)

  have hc2345 : Continuous
      (fun t : ℝ =>
        if t ≤ p.theta then path2 p t
        else if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path2 p).if_le hc345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [if_pos hord.theta_le_eta]
        exact h23)

  have hc12345 : Continuous
      (fun t : ℝ =>
        if t ≤ p.phi then path1 p t
        else if t ≤ p.theta then path2 p t
        else if t ≤ Real.pi / 2 - p.theta then path3 p t
        else if t ≤ Real.pi / 2 - p.phi then path4 p t else path5 p t) := by
    exact (continuous_path1 p).if_le hc2345
      continuous_id continuous_const (by
        intro t ht
        subst t
        rw [if_pos hord.phi_le_theta]
        exact h12)

  unfold path
  exact hc12345

end Romik

end
end GerverSofa
