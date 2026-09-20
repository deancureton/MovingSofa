import MovingSofa.Geometry.HallwayParts
import MovingSofa.ForMathlib.Analysis.SpecialFunctions.Trigonometric

noncomputable section

namespace MovingSofa

/-- Exchange the two coordinates of the Euclidean plane. -/
def coordinateSwap : Point ≃ₗᵢ[ℝ] Point :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap 0 1)

/-- Reflection exchanging the normals at angles zero and `ω + π / 2`. -/
def capReflection (ω : ℝ) : Point ≃ₗᵢ[ℝ] Point :=
  coordinateSwap.trans (EuclideanGeometry.o.rotation (ω : Real.Angle))

/-- First coordinate of the cap reflection. -/
theorem capReflection_apply_zero (ω : ℝ) (p : Point) :
    capReflection ω p 0 = -Real.sin ω * p 0 + Real.cos ω * p 1 := by
  rw [capReflection, LinearIsometryEquiv.trans_apply, Orientation.rotation_apply,
    rightAngleRotation_apply]
  simp [coordinateSwap]
  ring

/-- Second coordinate of the cap reflection. -/
theorem capReflection_apply_one (ω : ℝ) (p : Point) :
    capReflection ω p 1 = Real.cos ω * p 0 + Real.sin ω * p 1 := by
  rw [capReflection, LinearIsometryEquiv.trans_apply, Orientation.rotation_apply,
    rightAngleRotation_apply]
  simp [coordinateSwap]

/-- Reflection across the line through the upper vertex of the cap strip. -/
def stripTopReflection (ω : ℝ) (p : Point) : Point :=
  (2 * inner ℝ p (stripParallelogram ω).2.2 /
    inner ℝ (stripParallelogram ω).2.2 (stripParallelogram ω).2.2) •
      (stripParallelogram ω).2.2 - p

/-- The strip-top reflection is the explicit cap reflection. -/
theorem stripTopReflection_eq_capReflection (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    stripTopReflection ω = capReflection ω := by
  funext p
  by_cases hωtop : ω = Real.pi / 2
  · subst ω
    have harg : Real.pi / 4 - (Real.pi / 2) / 2 = 0 := by ring
    ext i
    fin_cases i
    · change stripTopReflection (Real.pi / 2) p 0 = capReflection (Real.pi / 2) p 0
      rw [capReflection_apply_zero]
      simp [stripTopReflection, stripParallelogram, harg, PiLp.inner_apply,
        Fin.sum_univ_two]
    · change stripTopReflection (Real.pi / 2) p 1 = capReflection (Real.pi / 2) p 1
      rw [capReflection_apply_one]
      have hnorm : ‖(!₂[0, 1] : Point)‖ ^ 2 = 1 := by
        simpa [Fin.sum_univ_two] using
          (EuclideanSpace.norm_sq_eq (!₂[0, 1] : Point))
      simp [stripTopReflection, stripParallelogram, harg, PiLp.inner_apply,
        Fin.sum_univ_two, hnorm]
      ring
  · have hωlt : ω < Real.pi / 2 := lt_of_le_of_ne hωle hωtop
    let C := Real.cos ω
    let S := Real.sin ω
    let c := Real.tan (Real.pi / 4 - ω / 2)
    have hC : 0 < C :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω0], hωlt⟩
    have hgap : c = C⁻¹ - Real.tan ω := by
      simpa [c, show Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 by ring]
        using Real.tan_pi_div_two_sub_div_two ω ⟨hω0.le, hωlt⟩
    have htan : Real.tan ω = S / C := Real.tan_eq_sin_div_cos ω
    have hcC : c * C = 1 - S := by
      rw [hgap, htan]
      field_simp [hC.ne']
    have hc : c * (1 + S) = C := by
      rw [hgap, htan]
      field_simp [hC.ne']
      nlinarith [hcC, Real.sin_sq_add_cos_sq ω]
    have hcsq : c * c * (1 + S) = 1 - S := by
      calc
        c * c * (1 + S) = c * (c * (1 + S)) := by ring
        _ = c * C := by rw [hc]
        _ = 1 - S := hcC
    have hcoef₀ : c * c - 1 = -S * (c * c + 1) := by
      nlinarith [hcsq]
    have hbase : 2 = (1 + S) * (c * c + 1) := by
      nlinarith [hcoef₀]
    have hcoef₁ : 2 * c = C * (c * c + 1) := by
      rw [← hc]
      linear_combination c * hbase
    have hcoef₂ : 1 - c * c = S * (c * c + 1) := by
      nlinarith [hcsq]
    have hden : c * c + 1 ≠ 0 := by nlinarith [sq_nonneg c]
    ext i
    fin_cases i
    · change stripTopReflection ω p 0 = capReflection ω p 0
      rw [capReflection_apply_zero]
      simp only [stripTopReflection, stripParallelogram, PiLp.inner_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.inner_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      simp only [mul_one]
      change 2 * (p 0 * c + p 1) / (c * c + 1) * c - p 0 =
        -S * p 0 + C * p 1
      field_simp [hden]
      linear_combination (p 0) * hcoef₀ + (p 1) * hcoef₁
    · change stripTopReflection ω p 1 = capReflection ω p 1
      rw [capReflection_apply_one]
      simp only [stripTopReflection, stripParallelogram, PiLp.inner_apply,
        Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Real.inner_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
      simp only [mul_one]
      change 2 * (p 0 * c + p 1) / (c * c + 1) - p 1 =
        C * p 0 + S * p 1
      field_simp [hden]
      linear_combination (p 0) * hcoef₁ + (p 1) * hcoef₂

/-- The strip-top reflection fixes the upper strip vertex. -/
theorem stripTopReflection_stripTop (ω : ℝ) :
    stripTopReflection ω (stripParallelogram ω).2.2 =
      (stripParallelogram ω).2.2 := by
  have ho : (stripParallelogram ω).2.2 ≠ (0 : Point) := by
    intro h
    have h1 := congrArg (fun p : Point ↦ p 1) h
    simp [stripParallelogram] at h1
  unfold stripTopReflection
  have hden : inner ℝ (stripParallelogram ω).2.2
      (stripParallelogram ω).2.2 ≠ 0 := inner_self_ne_zero.mpr ho
  rw [mul_div_assoc, div_self hden]
  module

/-- The cap reflection is an involution. -/
theorem capReflection_involutive (ω : ℝ) (p : Point) :
    capReflection ω (capReflection ω p) = p := by
  ext i
  fin_cases i
  · change capReflection ω (capReflection ω p) 0 = p 0
    rw [capReflection_apply_zero, capReflection_apply_zero, capReflection_apply_one]
    linear_combination (p 0) * (Real.sin_sq_add_cos_sq ω)
  · change capReflection ω (capReflection ω p) 1 = p 1
    rw [capReflection_apply_one, capReflection_apply_zero, capReflection_apply_one]
    linear_combination (p 1) * (Real.sin_sq_add_cos_sq ω)

/-- Reflection of a normal angle across the cap-reflection axis. -/
def reflectedAngle (ω : ℝ) (a : Real.Angle) : Real.Angle :=
  ((ω + Real.pi / 2 : ℝ) : Real.Angle) - a

/-- Reflection of normal angles is involutive. -/
theorem reflectedAngle_involutive (ω : ℝ) (a : Real.Angle) :
    reflectedAngle ω (reflectedAngle ω a) = a := by
  simp only [reflectedAngle]
  abel

/-- Coercion formula for a reflected real angle. -/
theorem reflectedAngle_coe (ω t : ℝ) :
    reflectedAngle ω (t : Real.Angle) =
      ((ω + Real.pi / 2 - t : ℝ) : Real.Angle) := by
  simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add]

/-- The cap reflection transports normal vectors at real angles. -/
theorem capReflection_normalVector (ω a : ℝ) :
    capReflection ω (normalVector (a : Real.Angle)) =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
  have hrho : (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) -
      (a : Real.Angle) = ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (normalVector (a : Real.Angle)) 0 =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) 0
    rw [capReflection_apply_zero, ← hrho]
    simp [normalVector, frame]
    rw [hrho, Real.Angle.cos_coe, Real.cos_sub, Real.sin_add, Real.cos_add]
    simp
  · change capReflection ω (normalVector (a : Real.Angle)) 1 =
      normalVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) 1
    rw [capReflection_apply_one, ← hrho]
    simp [normalVector, frame]
    rw [hrho, Real.Angle.sin_coe, Real.sin_sub, Real.sin_add, Real.cos_add]
    simp

/-- The cap reflection reverses tangent vectors at real angles. -/
theorem capReflection_tangentVector (ω a : ℝ) :
    capReflection ω (tangentVector (a : Real.Angle)) =
      -tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
  have hrho : (ω : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) -
      (a : Real.Angle) = ((ω + Real.pi / 2 - a : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add, ← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (tangentVector (a : Real.Angle)) 0 =
      (-tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle)) 0
    rw [capReflection_apply_zero, ← hrho]
    simp [tangentVector, frame]
    rw [hrho, Real.Angle.sin_coe, Real.sin_sub, Real.sin_add, Real.cos_add]
    simp
    ring
  · change capReflection ω (tangentVector (a : Real.Angle)) 1 =
      (-tangentVector ((ω + Real.pi / 2 - a : ℝ) : Real.Angle)) 1
    rw [capReflection_apply_one, ← hrho]
    simp [tangentVector, frame]
    rw [hrho, Real.Angle.cos_coe, Real.cos_sub, Real.sin_add, Real.cos_add]
    simp

/-- The cap reflection transports normal vectors by reflected angles. -/
theorem capReflection_normalVector_angle (ω : ℝ) (a : Real.Angle) :
    capReflection ω (normalVector a) = normalVector (reflectedAngle ω a) := by
  calc
    capReflection ω (normalVector a) =
        capReflection ω (normalVector (a.toReal : Real.Angle)) := by rw [a.coe_toReal]
    _ = normalVector ((ω + Real.pi / 2 - a.toReal : ℝ) : Real.Angle) :=
      capReflection_normalVector ω a.toReal
    _ = normalVector (reflectedAngle ω a) := by
      congr 1
      simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add, a.coe_toReal]

/-- The cap reflection reverses tangent vectors at reflected angles. -/
theorem capReflection_tangentVector_angle (ω : ℝ) (a : Real.Angle) :
    capReflection ω (tangentVector a) = -tangentVector (reflectedAngle ω a) := by
  calc
    capReflection ω (tangentVector a) =
        capReflection ω (tangentVector (a.toReal : Real.Angle)) := by rw [a.coe_toReal]
    _ = -tangentVector ((ω + Real.pi / 2 - a.toReal : ℝ) : Real.Angle) :=
      capReflection_tangentVector ω a.toReal
    _ = -tangentVector (reflectedAngle ω a) := by
      congr 2
      simp only [reflectedAngle, Real.Angle.coe_sub, Real.Angle.coe_add, a.coe_toReal]

/-- Inner products with normals transform under the cap reflection. -/
theorem inner_capReflection_normalVector (ω : ℝ) (p : Point)
    (a : Real.Angle) :
    inner ℝ (capReflection ω p) (normalVector a) =
      inner ℝ p (normalVector (reflectedAngle ω a)) := by
  have hn : capReflection ω (normalVector (reflectedAngle ω a)) =
      normalVector a := by
    rw [capReflection_normalVector_angle, reflectedAngle_involutive]
  rw [← hn]
  exact (capReflection ω).inner_map_map p (normalVector (reflectedAngle ω a))

/-- Inner products with tangents transform under the cap reflection. -/
theorem inner_capReflection_tangentVector (ω : ℝ) (p : Point)
    (a : Real.Angle) :
    inner ℝ (capReflection ω p) (tangentVector a) =
      -inner ℝ p (tangentVector (reflectedAngle ω a)) := by
  have ht : capReflection ω (-tangentVector (reflectedAngle ω a)) =
      tangentVector a := by
    rw [map_neg, capReflection_tangentVector_angle, reflectedAngle_involutive,
      neg_neg]
  rw [← ht, (capReflection ω).inner_map_map, inner_neg_right]

/-- The cap reflection transports every open or closed normal half-plane. -/
theorem capReflection_image_normalHalfPlane (ω h : ℝ)
    (a : Real.Angle) (upper strict : Bool) :
    capReflection ω '' normalHalfPlane a h upper strict =
      normalHalfPlane (reflectedAngle ω a) h upper strict := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    cases upper <;> cases strict <;>
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq] at hq ⊢ <;>
      rwa [inner_capReflection_normalVector, reflectedAngle_involutive]
  · intro hp
    refine ⟨capReflection ω p, ?_, capReflection_involutive ω p⟩
    cases upper <;> cases strict <;>
      simp only [normalHalfPlane, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq] at hp ⊢ <;>
      rwa [inner_capReflection_normalVector]

end MovingSofa
