import MovingSofa.Analysis.SurfaceMeasure.UpperGraph
import MovingSofa.Geometry.Contacts

/-!
# Exposed faces and the boundary of a convex body

The exposed faces of a convex body are exactly the sets of boundary points realizing a support
value: each exposed face lies on the boundary, and, when the body has interior, every boundary
point lies on some exposed face.
-/

noncomputable section

namespace MovingSofa

/-- Every boundary point of a convex body with nonempty interior lies on a supporting
exposed face. -/
theorem exists_mem_exposedEdge_of_mem_frontier
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p : Point} (hp : p ∈ frontier (K : Set Point)) :
    ∃ a : Real.Angle, p ∈ exposedEdge K a := by
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    rw [← K.isClosed.closure_eq]
    exact frontier_subset_closure hp
  obtain ⟨a, ha⟩ := exists_isExteriorNormal_of_mem_frontier K hK hp
  refine ⟨a, hpK, ?_⟩
  change inner ℝ p (normalVector a) = supportValue K a
  apply le_antisymm
  · exact inner_le_supportValue K hpK a
  · obtain ⟨q, hq, hqeq⟩ := exists_mem_inner_eq_supportValue K a
    rw [← hqeq]
    have := ha q hq
    rw [inner_sub_left] at this
    linarith

/-- Every exposed face of a convex body lies on its boundary. -/
theorem exposedEdge_subset_frontier
    (K : ConvexBody Point) (a : Real.Angle) :
    exposedEdge K a ⊆ frontier (K : Set Point) := by
  intro p hp
  rw [mem_frontier_iff_notMem_interior hp.1]
  intro hpint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
  let z := p + (ε / 2) • normalVector a
  have hzball : z ∈ Metric.ball p ε := by
    simp only [Metric.mem_ball, dist_eq_norm, z, add_sub_cancel_left, norm_smul,
      norm_normalVector, mul_one, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith
  have hzK : z ∈ K := interior_subset (hball hzball)
  have hzle := inner_le_supportValue K hzK a
  have hpEq := hp.2
  change inner ℝ p (normalVector a) = supportValue K a at hpEq
  have hnorm : inner ℝ (normalVector a) (normalVector a) = 1 := by
    induction a using Real.Angle.induction_on with
    | _ a => exact inner_normalVector_self a
  rw [show z = p + (ε / 2) • normalVector a from rfl, inner_add_left,
    real_inner_smul_left, hnorm, hpEq] at hzle
  linarith

end MovingSofa

end
