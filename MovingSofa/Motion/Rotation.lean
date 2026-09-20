import MovingSofa.Classical.Area
import MovingSofa.Geometry.Hallway
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

noncomputable section

open Set
open scoped unitInterval

namespace MovingSofa

/-- The linear part of a continuous rigid motion varies continuously on each vector. -/
theorem continuous_motion_linear_apply (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (x : Point) :
    Continuous (fun t ↦ (m t).linearIsometryEquiv x) := by
  have hmc : Continuous (fun t ↦ (m t).toAffineIsometry.toContinuousAffineMap) :=
    continuous_induced_dom.comp hm
  have he (t : I) : (m t).linearIsometryEquiv x = m t x - m t 0 := by
    have he := (m t).map_vadd (0 : Point) x
    change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
    rw [add_zero] at he
    exact eq_sub_iff_add_eq.mpr he.symm
  simp_rw [he]
  exact (hmc.eval_const x).sub (hmc.eval_const 0)

/-- The linear parts of an identity-starting continuous rigid motion have positive determinant. -/
theorem motion_linear_det_pos (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    0 < LinearMap.det (m t).linearIsometryEquiv.toLinearEquiv.toLinearMap := by
  let L : I → Point →L[ℝ] Point := fun t ↦ (m t).linearIsometryEquiv.toContinuousLinearEquiv
  have hL : Continuous L := continuous_clm_apply.mpr
    (continuous_motion_linear_apply m hm)
  have hdet : Continuous (fun t ↦ (L t).det) := ContinuousLinearMap.continuous_det.comp hL
  have hne (u : I) : (L u).det ≠ 0 := (m u).linearIsometryEquiv.toLinearEquiv.isUnit_det'.ne_zero
  have hL0 : L 0 = ContinuousLinearMap.id ℝ Point := by
    ext x
    simp only [L, hzero]
    rfl
  have hzero' : (L 0).det = 1 := by rw [hL0]; simp [ContinuousLinearMap.det]
  change 0 < (L t).det
  by_contra hneg
  have hle : (L t).det ≤ 0 := le_of_not_gt hneg
  obtain ⟨u, hu⟩ := intermediate_value_univ t 0 hdet ⟨hle, by rw [hzero']; norm_num⟩
  exact hne u hu

/-- Each placement of an identity-starting continuous rigid motion is a rotation and translation. -/
theorem exists_motion_rotation (m : I → Point ≃ᵃⁱ[ℝ] Point)
    (hm : Continuous m) (hzero : m 0 = AffineIsometryEquiv.refl ℝ Point) (t : I) :
    ∃ θ : Real.Angle, ∀ x, m t x = rotationMap θ x + m t 0 := by
  obtain ⟨θ, hθ⟩ := EuclideanGeometry.o.exists_linearIsometryEquiv_eq_of_det_pos
    (motion_linear_det_pos m hm hzero t)
  refine ⟨θ, fun x ↦ ?_⟩
  have he := (m t).map_vadd (0 : Point) x
  change m t (x + 0) = (m t).linearIsometryEquiv x + m t 0 at he
  simpa only [add_zero, hθ, rotationMap] using he

/-- Translation followed by a varying rotation depends continuously on both parameters. -/
theorem continuous_vaddConst_trans_rotation :
    Continuous (fun q : Real.Angle × Point ↦ ((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)) := by
  rw [continuous_induced_rng]
  apply ContinuousAffineMap.continuous_rng
  · intro p
    change Continuous (fun q : Real.Angle × Point ↦
      (EuclideanGeometry.o.rotation q.1) (p + q.2))
    simp only [Orientation.rotation_apply]
    exact ((Real.Angle.continuous_cos.comp continuous_fst).smul
      (continuous_const.add continuous_snd)).add
      ((Real.Angle.continuous_sin.comp continuous_fst).smul
        (EuclideanGeometry.o.rightAngleRotation.continuous.comp
          (continuous_const.add continuous_snd)))
  · have heq : (fun q : Real.Angle × Point ↦
        (((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)).toAffineIsometry.toContinuousAffineMap.contLinear) =
        (fun q : Real.Angle × Point ↦
          q.1.cos • ContinuousLinearMap.id ℝ Point +
          q.1.sin • EuclideanGeometry.o.rightAngleRotation.toContinuousLinearMap) := by
      funext q
      apply ContinuousLinearMap.ext
      intro p
      change (EuclideanGeometry.o.rotation q.1) p = _
      exact EuclideanGeometry.o.rotation_apply q.1 p
    change Continuous (fun q : Real.Angle × Point ↦
      (((AffineIsometryEquiv.vaddConst ℝ q.2).trans
        (EuclideanGeometry.o.rotation q.1).toAffineIsometryEquiv)).toAffineIsometry.toContinuousAffineMap.contLinear)
    rw [heq]
    exact ((Real.Angle.continuous_cos.comp continuous_fst).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp continuous_fst).smul continuous_const)

/-- A continuously varying rotation about the origin followed by a continuously varying
translation is a continuous family of rigid motions. -/
theorem continuous_rotation_trans_vaddConst {X : Type*} [TopologicalSpace X]
    {θ : X → Real.Angle} {c : X → Point} (hθ : Continuous θ) (hc : Continuous c) :
    Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst ℝ (c x))) := by
  rw [continuous_induced_rng]
  apply ContinuousAffineMap.continuous_rng
  · intro p
    change Continuous (fun x ↦ (EuclideanGeometry.o.rotation (θ x)) p + c x)
    simp only [Orientation.rotation_apply]
    exact (((Real.Angle.continuous_cos.comp hθ).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp hθ).smul continuous_const)).add hc
  · have heq : (fun x ↦
        ((EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
          (AffineIsometryEquiv.vaddConst ℝ
            (c x))).toAffineIsometry.toContinuousAffineMap.contLinear) =
        (fun x ↦ (θ x).cos • ContinuousLinearMap.id ℝ Point +
            (θ x).sin • EuclideanGeometry.o.rightAngleRotation.toContinuousLinearMap) := by
      funext x
      apply ContinuousLinearMap.ext
      intro p
      change (EuclideanGeometry.o.rotation (θ x)) p = _
      exact EuclideanGeometry.o.rotation_apply (θ x) p
    change Continuous (fun x ↦
      ((EuclideanGeometry.o.rotation (θ x)).toAffineIsometryEquiv.trans
        (AffineIsometryEquiv.vaddConst ℝ
          (c x))).toAffineIsometry.toContinuousAffineMap.contLinear)
    rw [heq]
    exact ((Real.Angle.continuous_cos.comp hθ).smul continuous_const).add
      ((Real.Angle.continuous_sin.comp hθ).smul continuous_const)

/-- Planar area is invariant under rotation about the origin, with no measurability
hypothesis on the set. -/
theorem area_image_rotationMap (α : Real.Angle) (S : Set Point) :
    ClassicalResults.area (rotationMap α '' S) = ClassicalResults.area S := by
  have himg : rotationMap α '' S = (EuclideanGeometry.o.rotation α).symm ⁻¹' S := by
    ext p
    simp only [rotationMap, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      exact ⟨_, h, (EuclideanGeometry.o.rotation α).apply_symm_apply p⟩
  change (MeasureTheory.volume (rotationMap α '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [himg]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (EuclideanGeometry.o.rotation α).symm
    (E := Point) (F := Point)).measure_preimage_emb
    ((EuclideanGeometry.o.rotation α).symm.toHomeomorph.measurableEmbedding) S

end MovingSofa
