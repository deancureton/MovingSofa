import MovingSofa.Geometry.Frame
import Mathlib.Analysis.InnerProductSpace.Dual
import MovingSofa.Analysis.SurfaceMeasure.Basic
import Mathlib.Analysis.LocallyConvex.Separation

noncomputable section

namespace MovingSofa

open Set

/-- Every frontier point of a convex body with nonempty interior admits an exterior unit normal. -/
theorem exists_isExteriorNormal_of_mem_frontier
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p : Point} (hp : p ∈ frontier (K : Set Point)) :
    ∃ a, IsExteriorNormal K p a := by
  have hpnot : p ∉ interior (K : Set Point) := by
    have hpK : p ∈ K := by
      change p ∈ (K : Set Point)
      rw [← K.isClosed.closure_eq]
      exact frontier_subset_closure hp
    exact (mem_frontier_iff_notMem_interior hpK).mp hp
  obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open K.convex.interior isOpen_interior hpnot
  let fc : Point →L[ℝ] ℝ := f.toContinuousLinearMap
  have hfne : fc ≠ 0 := by
    obtain ⟨q, hq⟩ := hK
    intro hzero
    have h := hf q hq
    have hfp : fc p = 0 := by rw [hzero]; rfl
    have hfq : fc q = 0 := by rw [hzero]; rfl
    change fc p < fc q at h
    linarith
  let w : Point := -(InnerProductSpace.toDual ℝ Point).symm fc
  have hw : w ≠ 0 := by
    intro hzero
    apply hfne
    apply (InnerProductSpace.toDual ℝ Point).symm.injective
    simpa using neg_eq_zero.mp hzero
  obtain ⟨a, ha⟩ := exists_angle_normalVector_eq (u := ‖w‖⁻¹ • w) (by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)])
  refine ⟨a, ?_⟩
  rw [IsExteriorNormal, ha]
  intro q hq
  have hclosed : IsClosed {q : Point | fc p ≤ fc q} :=
    isClosed_le continuous_const fc.continuous
  have hinterior : interior (K : Set Point) ⊆ {q : Point | fc p ≤ fc q} :=
    fun q hq ↦ (hf q hq).le
  have hsubset : (K : Set Point) ⊆ {q : Point | fc p ≤ fc q} := by
    rw [← K.isClosed.closure_eq,
      ← K.convex.closure_interior_eq_closure_of_nonempty_interior hK]
    exact closure_minimal hinterior hclosed
  have hfpq := hsubset hq
  rw [inner_smul_right, inner_neg_right, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  dsimp only [fc] at hfpq ⊢
  rw [map_sub]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg w))
    (neg_nonpos.mpr (sub_nonneg.mpr hfpq))

end MovingSofa
