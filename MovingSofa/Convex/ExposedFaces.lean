import MovingSofa.Geometry.Contacts
import MovingSofa.Convex.Combination
import Mathlib.Tactic.Linarith

noncomputable section

open scoped Pointwise unitInterval

namespace MovingSofa

private theorem support_bound (K : ConvexBody Point) (a : Real.Angle)
    {x : Point} (hx : x ∈ K) : inner ℝ x (normalVector a) ≤ supportValue K a := by
  apply le_csSup
  · exact (K.isCompact.image (continuous_id.inner continuous_const)).bddAbove
  · exact ⟨x, hx, rfl⟩

private theorem edge_nonempty (K : ConvexBody Point) (a : Real.Angle) :
    (exposedEdge K a).Nonempty := by
  obtain ⟨x, hx, he⟩ := (K.isCompact.image (continuous_id.inner continuous_const)).sSup_mem
    (K.nonempty.image (fun x ↦ inner ℝ x (normalVector a)))
  exact ⟨x, hx, he⟩

private theorem mem_edge_iff (K : ConvexBody Point) (a : Real.Angle) (x : Point) :
    x ∈ exposedEdge K a ↔ x ∈ K ∧ ∀ y ∈ K,
      inner ℝ y (normalVector a) ≤ inner ℝ x (normalVector a) := by
  change (x ∈ K ∧ inner ℝ x (normalVector a) = supportValue K a) ↔ _
  constructor
  · rintro ⟨hx, he⟩
    exact ⟨hx, fun y hy ↦ he ▸ support_bound K a hy⟩
  · rintro ⟨hx, hm⟩
    refine ⟨hx, le_antisymm (support_bound K a hx) ?_⟩
    exact csSup_le (K.nonempty.image _) (by rintro _ ⟨y, hy, rfl⟩; exact hm y hy)

private theorem combination_zero (K L : ConvexBody Point) :
    convexBodyCombination 0 K L = K := by
  apply SetLike.coe_injective
  simp [convexBodyCombination, Set.zero_smul_set L.nonempty]

private theorem combination_one (K L : ConvexBody Point) :
    convexBodyCombination 1 K L = L := by
  apply SetLike.coe_injective
  simp [convexBodyCombination, Set.zero_smul_set K.nonempty]

/-- Exposed faces commute with convex interpolation, including zero and unit weights. -/
theorem exposedEdge_convexBodyCombination (K L : ConvexBody Point) (a : Real.Angle)
    (t : unitInterval) :
    exposedEdge (convexBodyCombination t K L) a =
      (1 - (t : ℝ)) • exposedEdge K a + (t : ℝ) • exposedEdge L a := by
  by_cases h0 : t = 0
  · subst t
    simp [combination_zero, Set.zero_smul_set (edge_nonempty L a)]
  by_cases h1 : t = 1
  · subst t
    simp [combination_one, Set.zero_smul_set (edge_nonempty K a)]
  have ht : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
    intro h; exact h0 (Subtype.ext h.symm))
  have hu : 0 < 1 - (t : ℝ) := sub_pos.mpr (lt_of_le_of_ne t.property.2 (by
    intro h; exact h1 (Subtype.ext h)))
  have mem_combo (x y : Point) (hx : x ∈ K) (hy : y ∈ L) :
      (1 - (t : ℝ)) • x + (t : ℝ) • y ∈ convexBodyCombination t K L := by
    exact Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
  ext p
  constructor
  · intro hp
    obtain ⟨hp, hm⟩ := (mem_edge_iff _ a p).mp hp
    obtain ⟨u, huK, v, hvL, rfl⟩ := hp
    obtain ⟨x, hx, rfl⟩ := huK
    obtain ⟨y, hy, rfl⟩ := hvL
    have hxedge : x ∈ exposedEdge K a := (mem_edge_iff K a x).mpr ⟨hx, by
      intro z hz
      have h := hm _ (mem_combo z y hz hy)
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h
      nlinarith⟩
    have hyedge : y ∈ exposedEdge L a := (mem_edge_iff L a y).mpr ⟨hy, by
      intro z hz
      have h := hm _ (mem_combo x z hx hz)
      simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real] at h
      nlinarith⟩
    exact Set.add_mem_add (Set.smul_mem_smul_set hxedge) (Set.smul_mem_smul_set hyedge)
  · rintro ⟨u, huK, v, hvL, rfl⟩
    obtain ⟨x, hx, rfl⟩ := huK
    obtain ⟨y, hy, rfl⟩ := hvL
    obtain ⟨hx, hmx⟩ := (mem_edge_iff K a x).mp hx
    obtain ⟨hy, hmy⟩ := (mem_edge_iff L a y).mp hy
    apply (mem_edge_iff _ a _).mpr
    refine ⟨mem_combo x y hx hy, ?_⟩
    rintro p ⟨u, huK, v, hvL, rfl⟩
    obtain ⟨z, hz, rfl⟩ := huK
    obtain ⟨w, hw, rfl⟩ := hvL
    have hxz := hmx z hz
    have hyw := hmy w hw
    simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
    nlinarith

end MovingSofa
