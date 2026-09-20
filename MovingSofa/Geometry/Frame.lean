import MovingSofa.Geometry.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

namespace MovingSofa

/-- Every unit vector is the normal vector of an angular frame. -/
theorem exists_angle_normalVector_eq {u : Point} (hu : ‖u‖ = 1) :
    ∃ t : Real.Angle, normalVector t = u := by
  let z : ℂ := ⟨u 0, u 1⟩
  have hzNorm : ‖z‖ = 1 := by
    rw [Complex.norm_def, show Complex.normSq z = ‖u‖ ^ 2 by
      rw [EuclideanSpace.norm_sq_eq]
      simp [z, Complex.normSq_apply, Fin.sum_univ_two, pow_two, Real.norm_eq_abs]]
    simp [hu]
  have hz : z ≠ 0 := by
    intro hz
    simp [hz] at hzNorm
  refine ⟨(z.arg : ℝ), ?_⟩
  ext i
  fin_cases i
  · simpa [normalVector, frame, z, hzNorm] using Complex.cos_arg hz
  · simpa [normalVector, frame, z, hzNorm] using Complex.sin_arg z


theorem continuous_normalVector_real :
    Continuous (fun t : ℝ ↦ normalVector (t : Real.Angle)) := by
  let c : ℝ → (i : Fin 2) → ℝ := fun t i ↦
    Fin.cases (Real.cos t) (fun _ ↦ Real.sin t) i
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.continuous_cos
    · exact Real.continuous_sin
  have heq : (fun t : ℝ ↦ normalVector (t : Real.Angle)) =
      (fun t ↦ WithLp.toLp 2 (c t)) := by
    funext t
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc

/-- Opposite real angles give opposite normal vectors. -/
theorem normalVector_add_pi (t : ℝ) :
    normalVector ((t + Real.pi : ℝ) : Real.Angle) = -normalVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- Opposite real angles give opposite tangent vectors. -/
theorem tangentVector_add_pi (t : ℝ) :
    tangentVector ((t + Real.pi : ℝ) : Real.Angle) = -tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [tangentVector, frame, Real.Angle.cos_coe, Real.Angle.sin_coe]

/-- The projection onto the normal direction of a real angle, in coordinates. -/
theorem inner_normalVector_real (p : Point) (t : ℝ) :
    inner ℝ p (normalVector (t : Real.Angle)) = p 0 * Real.cos t + p 1 * Real.sin t := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The projection onto the tangent direction of a real angle, in coordinates. -/
theorem inner_tangentVector_real (p : Point) (t : ℝ) :
    inner ℝ p (tangentVector (t : Real.Angle)) = -(p 0 * Real.sin t) + p 1 * Real.cos t := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- The inner product of two unit normals is the cosine of their angle difference. -/
theorem inner_normalVector_normalVector (s t : ℝ) :
    inner ℝ (normalVector (s : Real.Angle)) (normalVector (t : Real.Angle)) =
      Real.cos (s - t) := by
  simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- A normal vector has squared length one. -/
theorem inner_normalVector_self (t : ℝ) :
    inner ℝ (normalVector (t : Real.Angle)) (normalVector (t : Real.Angle)) = 1 := by
  rw [inner_normalVector_normalVector]
  simp

/-- A normal vector at an angle has squared length one. -/
theorem inner_normalVector_self_angle (t : Real.Angle) :
    inner ℝ (normalVector t) (normalVector t) = 1 := by
  induction t using Real.Angle.induction_on with
  | _ r => exact inner_normalVector_self r

/-- A normal vector at a real angle has length one. -/
theorem norm_normalVector_real (t : ℝ) : ‖normalVector (t : Real.Angle)‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp [normalVector, frame, Fin.sum_univ_two]

theorem inner_normalVector_smul_add_inner_tangentVector_smul (p : Point) (t : Real.Angle) :
    inner ℝ p (normalVector t) • normalVector t +
      inner ℝ p (tangentVector t) • tangentVector t = p := by
  ext i
  fin_cases i <;>
    simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two] <;>
    nlinarith [congrArg (fun r : ℝ ↦ r * p 0) t.cos_sq_add_sin_sq,
      congrArg (fun r : ℝ ↦ r * p 1) t.cos_sq_add_sin_sq]

theorem normalVector_add_real (t δ : ℝ) :
    normalVector ((t + δ : ℝ) : Real.Angle) =
      Real.cos δ • normalVector (t : Real.Angle) +
      Real.sin δ • tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame, -Real.Angle.coe_add, Real.cos_add, Real.sin_add] <;> ring

theorem inner_normalVector_tangentVector (t : ℝ) :
    inner ℝ (normalVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 0 := by
  simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  ring

theorem inner_tangentVector_self (t : ℝ) :
    inner ℝ (tangentVector (t : Real.Angle)) (tangentVector (t : Real.Angle)) = 1 := by
  rw [PiLp.inner_apply]
  simp [tangentVector, frame, Fin.sum_univ_two, Real.sin_sq_add_cos_sq]

theorem tangentVector_add_pi_div_two (t : ℝ) :
    tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle) = -normalVector (t : Real.Angle) := by
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

/-- Adding pi to an angle reverses its normal vector. -/
theorem normalVector_add_pi_angle (a : Real.Angle) :
    normalVector (a + ((Real.pi : ℝ) : Real.Angle)) = -normalVector a := by
  induction a using Real.Angle.induction_on with
  | _ a => simpa only [Real.Angle.coe_add] using normalVector_add_pi a

/-- The sine convolution kernel is the negative normal projection of the moving tangent. -/
theorem sin_sub_eq_neg_inner_normalVector_tangentVector (t u : Real.Angle) :
    (u - t).sin = -inner ℝ (normalVector t) (tangentVector u) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    induction u using Real.Angle.induction_on with
    | _ u =>
      change Real.sin (u - t) = _
      simp [normalVector, tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.sin_sub]
      ring

/-- The normal projection of a tangent vector is the sine of the angle difference. -/
theorem inner_tangentVector_normalVector_real (t s : ℝ) :
    inner ℝ (tangentVector (t : Real.Angle)) (normalVector (s : Real.Angle)) =
      Real.sin (s - t) := by
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Real.sin_sub]
  ring

/-- The inner product of two unit tangents is the cosine of their angle difference. -/
theorem inner_tangentVector_tangentVector (s t : ℝ) :
    inner ℝ (tangentVector (s : Real.Angle)) (tangentVector (t : Real.Angle)) =
      Real.cos (s - t) := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

/-- The normal coordinate of a vector in the frame at another angle. -/
theorem inner_normalVector_eq_frame_rotate (w : Point) (s t : ℝ) :
    inner ℝ w (normalVector (t : Real.Angle)) =
      inner ℝ w (normalVector (s : Real.Angle)) * Real.cos (s - t) -
        inner ℝ w (tangentVector (s : Real.Angle)) * Real.sin (s - t) := by
  nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul w (s : Real.Angle)]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_normalVector_normalVector, inner_tangentVector_normalVector_real,
    show t - s = -(s - t) by ring, Real.sin_neg]
  ring

/-- The tangent coordinate of a vector in the frame at another angle. -/
theorem inner_tangentVector_eq_frame_rotate (w : Point) (s t : ℝ) :
    inner ℝ w (tangentVector (t : Real.Angle)) =
      inner ℝ w (normalVector (s : Real.Angle)) * Real.sin (s - t) +
        inner ℝ w (tangentVector (s : Real.Angle)) * Real.cos (s - t) := by
  have hcross : inner ℝ (normalVector (s : Real.Angle)) (tangentVector (t : Real.Angle)) =
      Real.sin (s - t) := by
    rw [real_inner_comm]
    exact inner_tangentVector_normalVector_real t s
  nth_rewrite 1 [← inner_normalVector_smul_add_inner_tangentVector_smul w (s : Real.Angle)]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
    inner_tangentVector_tangentVector, hcross]

/-- Two points whose normal coordinates agree at two transverse angles coincide. -/
theorem eq_of_inner_normalVector_eq {p q : Point} {s t : ℝ}
    (hst : Real.sin (s - t) ≠ 0)
    (hs : inner ℝ p (normalVector (s : Real.Angle)) =
      inner ℝ q (normalVector (s : Real.Angle)))
    (ht : inner ℝ p (normalVector (t : Real.Angle)) =
      inner ℝ q (normalVector (t : Real.Angle))) : p = q := by
  have hp := inner_normalVector_eq_frame_rotate p s t
  have hq := inner_normalVector_eq_frame_rotate q s t
  have hmul : (inner ℝ p (tangentVector (s : Real.Angle)) -
      inner ℝ q (tangentVector (s : Real.Angle))) * Real.sin (s - t) = 0 := by
    linear_combination hp - hq - ht + Real.cos (s - t) * hs
  have hv : inner ℝ p (tangentVector (s : Real.Angle)) =
      inner ℝ q (tangentVector (s : Real.Angle)) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hst)
  calc p = inner ℝ p (normalVector (s : Real.Angle)) • normalVector (s : Real.Angle) +
        inner ℝ p (tangentVector (s : Real.Angle)) • tangentVector (s : Real.Angle) :=
        (inner_normalVector_smul_add_inner_tangentVector_smul p (s : Real.Angle)).symm
    _ = inner ℝ q (normalVector (s : Real.Angle)) • normalVector (s : Real.Angle) +
        inner ℝ q (tangentVector (s : Real.Angle)) • tangentVector (s : Real.Angle) := by
        rw [hs, hv]
    _ = q := inner_normalVector_smul_add_inner_tangentVector_smul q (s : Real.Angle)


/-- Each coordinate of the frame tangent is continuous in the angle. -/
theorem continuous_tangentVector_coordinate (i : Fin 2) :
    Continuous fun u : Real.Angle ↦ tangentVector u i := by
  fin_cases i
  · exact Real.Angle.continuous_sin.neg
  · exact Real.Angle.continuous_cos

/-- The frame tangent is a unit vector. -/
theorem norm_tangentVector (t : Real.Angle) : ‖tangentVector t‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1), Point.norm_sq_eq]
  simp [tangentVector, frame, add_comm]

/-- Each coordinate of the frame tangent is bounded by one. -/
theorem norm_tangentVector_coordinate_le_one (t : Real.Angle) (i : Fin 2) :
    ‖tangentVector t i‖ ≤ 1 := by
  simpa [Real.norm_eq_abs, norm_tangentVector t] using
    Point.abs_apply_le_norm (tangentVector t) i

end MovingSofa
