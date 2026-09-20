import GerverSofa.Systems
import Mathlib

/-!
# F01: algebraic half of the integral-to-five-phase representation

The coefficient dictionary and the five explicit body-frame branches come
from the 4 September integral-motion excerpt. They are compared to the
actual `Romik.path1` ... `Romik.path5` definitions, then assembled using the
same `if` boundaries as `Romik.path`.

This module does NOT evaluate the integrals: `closedPath` is explicitly
named as a closed-form candidate. Proving that the pinned integral path
equals it, and identifying `dictionary d` with the certified 22D tuple,
remain separate obligations. No such equality is assumed here.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.Phases

def T : ℝ := Real.pi / 2
def hStar (d : Reduced.Params) : ℝ := (d.a + d.theta - d.phi - 1) / 2
def U4 (d : Reduced.Params) : ℝ :=
  (1 + d.a) / 2 * Real.cos d.phi - (d.b + 1 / 2) * Real.sin d.phi
def V4 (d : Reduced.Params) : ℝ :=
  1 - (d.b + 1 / 2) * Real.cos d.phi - (1 + d.a) / 2 * Real.sin d.phi
def U3 (d : Reduced.Params) : ℝ :=
  U4 d + 1 / 2 * Real.sin d.theta - hStar d * Real.cos d.theta
def V3 (d : Reduced.Params) : ℝ :=
  V4 d + 1 / 2 * Real.cos d.theta + hStar d * Real.sin d.theta
def U2 (d : Reduced.Params) : ℝ := U4 d
def V2 (d : Reduced.Params) : ℝ :=
  V4 d + Real.cos d.theta + 2 * hStar d * Real.sin d.theta
def U1 (d : Reduced.Params) : ℝ :=
  U2 d + d.a / 2 * Real.cos d.phi - 1 / 2 * Real.sin d.phi
def V1 (d : Reduced.Params) : ℝ :=
  V2 d + d.a / 2 * Real.sin d.phi + 1 / 2 * Real.cos d.phi
def ell (d : Reduced.Params) : ℝ := 4 * V1 d - 2

theorem U1_eq_half (d : Reduced.Params) (hd : Reduced.Equations d) :
    U1 d = 1 / 2 := by
  change Reduced.system d = 0 at hd
  have h := congrFun hd (2 : Fin 4)
  change d.a * Real.cos d.phi - Real.sin d.phi - 1 / 2 +
    1 / 2 * Real.cos d.phi - d.b * Real.sin d.phi = 0 at h
  dsimp [U1, U2, U4]
  linear_combination h

theorem ell_eq (d : Reduced.Params) (hd : Reduced.Equations d) :
    ell d = V2 d + V4 d := by
  change Reduced.system d = 0 at hd
  have h := congrFun hd (1 : Fin 4)
  change d.a * (3 * Real.sin d.theta + Real.sin d.phi) -
    2 * d.b * Real.cos d.phi +
    3 * (d.theta - d.phi - 1) * Real.sin d.theta +
    3 * Real.cos d.theta - Real.sin d.phi + Real.cos d.phi = 0 at h
  dsimp [ell, V1, V2, V4, hStar]
  linear_combination h

theorem ell_eq_two_V3 (d : Reduced.Params) (hd : Reduced.Equations d) :
    ell d = 2 * V3 d := by
  rw [ell_eq d hd]
  dsimp [V2, V3]
  ring

def dictionary (d : Reduced.Params) : Romik.Params where
  k11 := 1 - 3 / 2 * (1 - V1 d)
  k12 := 1 / 4
  k21 := V4 d
  k22 := U4 d
  k31 := V3 d
  k32 := U3 d
  k41 := V2 d
  k42 := U4 d
  k51 := V1 d - 3 / 2 * (1 - V1 d)
  k52 := 1 / 4
  a1 := 3 / 2 * (1 - V1 d)
  a2 := -1 / 4
  b1 := (d.phi - 1 - d.a) / 2
  b2 := d.b - 1 / 2 + (1 + d.a) / 2 * d.phi - d.phi ^ 2 / 4
  c1 := d.a + T - d.phi - 1
  c2 := d.a - d.phi - 1
  d1 := (T - d.phi + 1 + d.a) / 2
  d2 := d.b - 1 / 2 - (1 + d.a) / 2 * (T - d.phi) - (T - d.phi)^2 / 4
  e1 := 3 / 2 * (1 - V1 d)
  e2 := 1 / 4
  phi := d.phi
  theta := d.theta

@[simp] theorem dictionary_phi (d : Reduced.Params) : (dictionary d).phi = d.phi := rfl
@[simp] theorem dictionary_theta (d : Reduced.Params) : (dictionary d).theta = d.theta := rfl

def g2 (d : Reduced.Params) (t : ℝ) : ℝ := (1 + d.a + t - d.phi) / 2
def g3 (d : Reduced.Params) (t : ℝ) : ℝ := d.a + t - d.phi
def g4 (d : Reduced.Params) (t : ℝ) : ℝ :=
  d.b + 1 / 2 - (T - d.phi - t) * (1 + d.a) / 2 - (T - d.phi - t)^2 / 4

def closed1 (d : Reduced.Params) (t : ℝ) : Point :=
  (Real.cos t - 1,
    -1 / 2 + 1 / 2 * Real.cos t + (V1 d - ell d) * Real.sin t)

def closed2 (d : Reduced.Params) (t : ℝ) : Point :=
  (g4 d (T - t) + U4 d * Real.sin t + V4 d * Real.cos t - 1,
    g2 d t + U4 d * Real.cos t + (V2 d - ell d) * Real.sin t - 1)

def closed3 (d : Reduced.Params) (t : ℝ) : Point :=
  (g3 d (T - t) + U3 d * Real.sin t + V3 d * Real.cos t - 1,
    g3 d t + U3 d * Real.cos t + (V3 d - ell d) * Real.sin t - 1)

def closed4 (d : Reduced.Params) (t : ℝ) : Point :=
  (g2 d (T - t) + U4 d * Real.sin t + V2 d * Real.cos t - 1,
    g4 d t + U4 d * Real.cos t + (V4 d - ell d) * Real.sin t - 1)

def closed5 (d : Reduced.Params) (t : ℝ) : Point :=
  (-1 / 2 + V1 d * Real.cos t + 1 / 2 * Real.sin t,
    (1 - ell d) * Real.sin t - 1)

theorem phase1 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed1 d t) = Romik.path1 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed1, Romik.path1, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

theorem phase2 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed2 d t) = Romik.path2 (dictionary d) t := by
  unfold closed2
  rw [ell_eq d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path2, Romik.addK, dictionary, g2, g4, T]
    linear_combination V4 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path2, Romik.addK, dictionary, g2, g4, T]
    linear_combination U4 d * Real.sin_sq_add_cos_sq t

theorem phase3 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed3 d t) = Romik.path3 (dictionary d) t := by
  unfold closed3
  rw [ell_eq_two_V3 d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path3, Romik.addK, dictionary, g3, T]
    linear_combination V3 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path3, Romik.addK, dictionary, g3, T]
    linear_combination U3 d * Real.sin_sq_add_cos_sq t

theorem phase4 (d : Reduced.Params) (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closed4 d t) = Romik.path4 (dictionary d) t := by
  unfold closed4
  rw [ell_eq d hd]
  apply Prod.ext
  · dsimp [Romik.rot, Romik.path4, Romik.addK, dictionary, g2, g4, T]
    linear_combination V2 d * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, Romik.path4, Romik.addK, dictionary, g2, g4, T]
    linear_combination U4 d * Real.sin_sq_add_cos_sq t

theorem phase5 (d : Reduced.Params) (t : ℝ) :
    Romik.rot t (closed5 d t) = Romik.path5 (dictionary d) t := by
  apply Prod.ext
  · dsimp [Romik.rot, closed5, Romik.path5, Romik.addK, dictionary, ell]
    linear_combination (V1 d - 3 / 2 * (1 - V1 d)) * Real.sin_sq_add_cos_sq t
  · dsimp [Romik.rot, closed5, Romik.path5, Romik.addK, dictionary, ell]
    linear_combination (1 / 4 : ℝ) * Real.sin_sq_add_cos_sq t

def closedPath (d : Reduced.Params) (t : ℝ) : Point :=
  if t ≤ d.phi then closed1 d t
  else if t ≤ d.theta then closed2 d t
  else if t ≤ Real.pi / 2 - d.theta then closed3 d t
  else if t ≤ Real.pi / 2 - d.phi then closed4 d t
  else closed5 d t

/-- Exact assembly for the explicit closed path, including every switching
endpoint. This is not yet the corresponding theorem for the integral path. -/
theorem fivePhaseRepresentation (d : Reduced.Params)
    (hd : Reduced.Equations d) (t : ℝ) :
    Romik.rot t (closedPath d t) = Romik.path (dictionary d) t := by
  -- Expose both sets of conditions, including the local `eta` and `tau`
  -- definitions inside `Romik.path`, before choosing a branch.
  change Romik.rot t
      (if t ≤ d.phi then closed1 d t
       else if t ≤ d.theta then closed2 d t
       else if t ≤ Real.pi / 2 - d.theta then closed3 d t
       else if t ≤ Real.pi / 2 - d.phi then closed4 d t
       else closed5 d t) =
    (if t ≤ d.phi then Romik.path1 (dictionary d) t
     else if t ≤ d.theta then Romik.path2 (dictionary d) t
     else if t ≤ Real.pi / 2 - d.theta then Romik.path3 (dictionary d) t
     else if t ≤ Real.pi / 2 - d.phi then Romik.path4 (dictionary d) t
     else Romik.path5 (dictionary d) t)
  by_cases h1 : t ≤ d.phi
  · simpa only [if_pos h1] using phase1 d t
  by_cases h2 : t ≤ d.theta
  · simpa only [if_neg h1, if_pos h2] using phase2 d hd t
  by_cases h3 : t ≤ Real.pi / 2 - d.theta
  · simpa only [if_neg h1, if_neg h2, if_pos h3] using phase3 d hd t
  by_cases h4 : t ≤ Real.pi / 2 - d.phi
  · simpa only [if_neg h1, if_neg h2, if_neg h3, if_pos h4] using phase4 d hd t
  · simpa only [if_neg h1, if_neg h2, if_neg h3, if_neg h4] using phase5 d t

end GerverSofa.PartF.Phases
