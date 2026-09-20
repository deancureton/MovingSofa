import MovingSofa.Geometry.Parallelogram
import MovingSofa.ForMathlib.Analysis.SpecialFunctions.Trigonometric
import Mathlib.Analysis.Convex.Segment

noncomputable section

namespace MovingSofa

theorem parallelogram_gap (ω : ℝ) (hω : ω ∈ Set.Ico 0 (Real.pi / 2)) :
    (stripParallelogram ω).2.2 - tangentVector 0 =
      Real.tan ((Real.pi / 2 - ω) / 2) • normalVector 0 ∧
    (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) • tangentVector (ω : Real.Angle) ∧
    (stripParallelogram ω).1 ∩
        (supportingLineHalfPlane (stripParallelogram ω).1
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      segment ℝ (0 : Point) ((Real.cos ω)⁻¹ • normalVector 0) ∧
    normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (ω : Real.Angle) 1 =
      {((Real.cos ω)⁻¹ • normalVector 0 : Point)} ∧
    Real.tan ((Real.pi / 2 - ω) / 2) = (Real.cos ω)⁻¹ - Real.tan ω := by
  have hcos : 0 < Real.cos ω :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1], hω.2⟩
  have hgap := Real.tan_pi_div_two_sub_div_two ω hω
  have hfirst : (stripParallelogram ω).2.2 - tangentVector 0 =
      Real.tan ((Real.pi / 2 - ω) / 2) • normalVector 0 := by
    ext i
    fin_cases i <;> simp [stripParallelogram, normalVector, tangentVector, frame]
    ring_nf
  have hsecond : (stripParallelogram ω).2.2 - normalVector (ω : Real.Angle) =
      Real.tan ((Real.pi / 2 - ω) / 2) • tangentVector (ω : Real.Angle) := by
    have harg : Real.pi / 4 - ω / 2 = (Real.pi / 2 - ω) / 2 := by ring
    have hc : Real.tan ((Real.pi / 2 - ω) / 2) * Real.cos ω = 1 - Real.sin ω := by
      rw [hgap, Real.tan_eq_sin_div_cos]
      field_simp [hcos.ne']
    have hc' : Real.tan ((Real.pi / 2 - ω) / 2) * (1 + Real.sin ω) =
        Real.cos ω := by
      rw [hgap, Real.tan_eq_sin_div_cos]
      field_simp [hcos.ne']
      nlinarith [Real.sin_sq_add_cos_sq ω]
    ext i
    fin_cases i <;>
      simp [stripParallelogram, normalVector, tangentVector, frame, harg] <;> nlinarith
  have hedge : (stripParallelogram ω).1 ∩
        (supportingLineHalfPlane (stripParallelogram ω).1
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 =
      segment ℝ (0 : Point) ((Real.cos ω)⁻¹ • normalVector 0) := by
    rw [supportingLineHalfPlane, supportValue_stripParallelogram_bottom]
    ext p
    simp only [Set.mem_inter_iff, mem_stripParallelogram_iff, normalLine,
      Set.mem_ofPred_eq, segment_eq_image, Set.mem_image, Set.mem_Icc]
    rw [inner_normalVector_three_pi_div_two]
    constructor
    · rintro ⟨⟨⟨hp₀, hp₁⟩, hq₀, hq₁⟩, hbottom⟩
      have hpzero : p 1 = 0 := by linarith
      have hx₀ : 0 ≤ p 0 * Real.cos ω := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpzero,
          mul_comm] using hq₀
      have hx₁ : p 0 * Real.cos ω ≤ 1 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpzero,
          mul_comm] using hq₁
      refine ⟨p 0 * Real.cos ω, ⟨hx₀, hx₁⟩, ?_⟩
      ext i
      fin_cases i <;> simp [normalVector, frame, hpzero, hcos.ne']
    · rintro ⟨x, hx, rfl⟩
      have hinner : inner ℝ (x • (Real.cos ω)⁻¹ • normalVector 0)
          (normalVector (ω : Real.Angle)) = x := by
        simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        field_simp [hcos.ne']
      constructor
      · exact ⟨by simp [normalVector, frame], by simpa [hinner] using hx⟩
      · simp [normalVector, frame]
  have hintersection : normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (ω : Real.Angle) 1 =
      {((Real.cos ω)⁻¹ • normalVector 0 : Point)} := by
    ext p
    simp only [Set.mem_inter_iff, normalLine, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hvertical, hrotated⟩
      have hpone : p 1 = 0 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hvertical
      have hpzero : p 0 * Real.cos ω = 1 := by
        simpa [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, hpone,
          mul_comm] using hrotated
      ext i
      fin_cases i
      · simp [normalVector, frame]
        field_simp [hcos.ne']
        exact hpzero
      · simp [normalVector, frame, hpone]
    · intro hp
      rw [hp]
      constructor
      · simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      · simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
        field_simp [hcos.ne']
  exact ⟨hfirst, hsecond, hedge, hintersection, hgap⟩

end MovingSofa
