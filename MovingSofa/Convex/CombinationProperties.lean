import MovingSofa.Convex.ExposedFaces
import MovingSofa.Convex.SupportEmbedding

noncomputable section

open scoped Pointwise unitInterval

namespace MovingSofa

/-- Pointwise description of the Minkowski interpolation of two convex bodies. -/
theorem mem_convexBodyCombination_iff (t : I) (K L : ConvexBody Point) (z : Point) :
    z ∈ (convexBodyCombination t K L : Set Point) ↔
      ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = (1 - (t : ℝ)) • x + (t : ℝ) • y := by
  change z ∈ (1 - (t : ℝ)) • (K : Set Point) + (t : ℝ) • (L : Set Point) ↔ _
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩

/-- The first edge vertex maximizes tangent coordinate on its exposed edge. -/
theorem inner_le_edgeVertices_fst_tangent (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a) :
    inner ℝ p (tangentVector a) ≤ inner ℝ (edgeVertices K a).1 (tangentVector a) := by
  rw [inner_edgeVertices_fst_tangent]
  exact le_csSup ((isCompact_exposedEdge K a).image
    (continuous_id.inner continuous_const) |>.bddAbove) ⟨p, hp, rfl⟩

/-- A tangent-coordinate maximizer on an exposed edge is its first vertex. -/
theorem edgeVertices_fst_eq_of_tangent_isGreatest (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a)
    (hmax : ∀ q ∈ exposedEdge K a,
      inner ℝ q (tangentVector a) ≤ inner ℝ p (tangentVector a)) :
    (edgeVertices K a).1 = p := by
  have ht := le_antisymm (hmax _ (edgeVertices_fst_mem K a))
    (inner_le_edgeVertices_fst_tangent K a hp)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K a).1 a,
    ← inner_normalVector_smul_add_inner_tangentVector_smul p a,
    (edgeVertices_fst_mem K a).2, hp.2, ht]

/-- A tangent-coordinate minimizer on an exposed edge is its second vertex. -/
theorem edgeVertices_snd_eq_of_tangent_isLeast (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a)
    (hmin : ∀ q ∈ exposedEdge K a,
      inner ℝ p (tangentVector a) ≤ inner ℝ q (tangentVector a)) :
    (edgeVertices K a).2 = p := by
  have hbdd : BddBelow
      ((fun q : Point ↦ inner ℝ q (tangentVector a)) '' exposedEdge K a) :=
    ((isCompact_exposedEdge K a).image
      (continuous_id.inner continuous_const)).bddBelow
  have ht : inner ℝ (edgeVertices K a).2 (tangentVector a) =
      inner ℝ p (tangentVector a) := by
    rw [inner_edgeVertices_snd_tangent]
    apply le_antisymm (csInf_le hbdd ⟨p, hp, rfl⟩)
    rw [← inner_edgeVertices_snd_tangent]
    exact hmin _ (edgeVertices_snd_mem K a)
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K a).2 a,
    ← inner_normalVector_smul_add_inner_tangentVector_smul p a,
    (edgeVertices_snd_mem K a).2, hp.2, ht]

private theorem inner_edgeVertices_snd_tangent_le_point (K : ConvexBody Point)
    (a : Real.Angle) {p : Point} (hp : p ∈ exposedEdge K a) :
    inner ℝ (edgeVertices K a).2 (tangentVector a) ≤ inner ℝ p (tangentVector a) := by
  rw [inner_edgeVertices_snd_tangent]
  exact csInf_le ((isCompact_exposedEdge K a).image
    (continuous_id.inner continuous_const) |>.bddBelow) ⟨p, hp, rfl⟩

/-- The extreme points of exposed edges commute with convex combinations. -/
theorem edgeVertices_convexBodyCombination (t : I) (K L : ConvexBody Point)
    (a : Real.Angle) :
    (edgeVertices (convexBodyCombination t K L) a).1 =
        (1 - (t : ℝ)) • (edgeVertices K a).1 + (t : ℝ) • (edgeVertices L a).1 ∧
      (edgeVertices (convexBodyCombination t K L) a).2 =
        (1 - (t : ℝ)) • (edgeVertices K a).2 + (t : ℝ) • (edgeVertices L a).2 := by
  let M := convexBodyCombination t K L
  have hedge := exposedEdge_convexBodyCombination K L a t
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  have htnonneg : 0 ≤ (t : ℝ) := t.property.1
  constructor
  · apply edgeVertices_fst_eq_of_tangent_isGreatest M a
    · rw [hedge]
      exact Set.add_mem_add (Set.smul_mem_smul_set (edgeVertices_fst_mem K a))
        (Set.smul_mem_smul_set (edgeVertices_fst_mem L a))
    · intro q hq
      rw [hedge] at hq
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_le_edgeVertices_fst_tangent K a hx) hnonneg)
        (mul_le_mul_of_nonneg_left (inner_le_edgeVertices_fst_tangent L a hy) htnonneg)
  · apply edgeVertices_snd_eq_of_tangent_isLeast M a
    · rw [hedge]
      exact Set.add_mem_add (Set.smul_mem_smul_set (edgeVertices_snd_mem K a))
        (Set.smul_mem_smul_set (edgeVertices_snd_mem L a))
    · intro q hq
      rw [hedge] at hq
      obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩ := hq
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (inner_edgeVertices_snd_tangent_le_point K a hx) hnonneg)
        (mul_le_mul_of_nonneg_left (inner_edgeVertices_snd_tangent_le_point L a hy) htnonneg)

/-- Support values commute with convex combinations. -/
theorem supportValue_convexBodyCombination (t : I) (K L : ConvexBody Point)
    (a : Real.Angle) :
    supportValue (convexBodyCombination t K L) a =
      (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a := by
  rw [show (convexBodyCombination t K L : Set Point) =
      {z : Point | ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = (1 - (t : ℝ)) • x + (t : ℝ) • y} from
    Set.ext (mem_convexBodyCombination_iff t K L)]
  exact (supportFunction_minkowski_embedding K L).1
    (1 - (t : ℝ)) t (sub_nonneg.mpr t.property.2) t.property.1 a

end MovingSofa
