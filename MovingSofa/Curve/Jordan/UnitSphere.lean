import MovingSofa.Curve.Jordan.Basic
import Mathlib.Tactic

noncomputable section
namespace MovingSofa

private def circlePoint (z : Circle) : Point := WithLp.toLp 2 ![(z : ℂ).re, (z : ℂ).im]

private lemma norm_circlePoint (z : Circle) : ‖circlePoint z‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp only [circlePoint, Fin.sum_univ_two, WithLp.ofLp_toLp, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, one_pow, Real.norm_eq_abs, sq_abs]
  have h := Complex.sq_norm (z : ℂ)
  simp only [Complex.normSq_apply, Circle.norm_coe] at h
  nlinarith


private lemma continuous_circlePoint : Continuous circlePoint := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact Complex.continuous_re.comp continuous_subtype_val
  · exact Complex.continuous_im.comp continuous_subtype_val

/-- A planar set homeomorphic to the unit sphere is a Jordan curve. -/
lemma isJordanCurve_of_unitSphere_homeomorph {Γ : Set Point}
    (e : {u : Point | ‖u‖ = 1} ≃ₜ ↥Γ) : IsJordanCurve Γ := by
  let f : Circle → {u : Point | ‖u‖ = 1} := fun z ↦ ⟨circlePoint z, norm_circlePoint z⟩
  refine ⟨fun z ↦ (e (f z) : Point), continuous_subtype_val.comp
    (e.continuous.comp (continuous_circlePoint.subtype_mk _)), ?_, ?_⟩
  · intro z w h
    have he := e.injective (Subtype.ext h)
    have hpoint := congrArg Subtype.val he
    apply Subtype.ext
    apply Complex.ext
    · exact congrFun (congrArg WithLp.ofLp hpoint) 0
    · exact congrFun (congrArg WithLp.ofLp hpoint) 1
  · apply Set.Subset.antisymm
    · rintro p ⟨z, rfl⟩
      exact (e (f z)).property
    · intro p hp
      let u := e.symm ⟨p, hp⟩
      let z : ℂ := ⟨u.val 0, u.val 1⟩
      have hz : ‖z‖ = 1 := by
        rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
        rw [Complex.sq_norm]
        have hu : ‖u.val‖ = 1 := u.property
        have hsq := congrArg (fun r : ℝ ↦ r ^ 2) hu
        rw [EuclideanSpace.norm_sq_eq] at hsq
        simpa [z, Fin.sum_univ_two, sq] using hsq
      let ζ : Circle := ⟨z, by
        change z ∈ Metric.sphere 0 1
        simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
      refine ⟨ζ, ?_⟩
      have hf : f ζ = u := by
        apply Subtype.ext
        ext i
        fin_cases i <;> rfl
      change (e (f ζ) : Point) = p
      rw [hf]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨p, hp⟩)

end MovingSofa
