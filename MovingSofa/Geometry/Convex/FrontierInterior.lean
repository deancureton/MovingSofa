import MovingSofa.Curve.Jordan.Orientation
import MovingSofa.Geometry.Basic
import Mathlib.Tactic

open Set
open scoped Topology


namespace MovingSofa

/-- A bounded component of the frontier complement that meets the set lies in its interior. -/
lemma connectedComponentIn_compl_frontier_subset_interior {s : Set Point}
    (hs : IsClosed s) {p : Point} (hp : p ∈ interior s) :
    connectedComponentIn (frontier s)ᶜ p ⊆ interior s := by
  have hsub : connectedComponentIn (frontier s)ᶜ p ⊆ interior s ∪ sᶜ := by
    intro q hq
    have hq' := connectedComponentIn_subset (frontier s)ᶜ p hq
    simp only [frontier, hs.closure_eq, mem_compl_iff, mem_sdiff, not_and_or,
      not_not] at hq'
    exact hq'.symm
  rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      hs.isOpen_compl (disjoint_left.mpr (fun _ hx hy ↦ hy (interior_subset hx))) hsub with h | h
  · exact h
  · have hp' : p ∈ (frontier s)ᶜ := by
      simp only [frontier, hs.closure_eq, mem_compl_iff, mem_sdiff, not_and_or,
        not_not]
      exact Or.inr hp
    exact False.elim ((h (mem_connectedComponentIn hp')) (interior_subset hp))

/-- The interior of a bounded closed set lies in the bounded component of its frontier complement. -/
lemma interior_subset_jordanInterior_frontier {s : Set Point}
    (hs : IsClosed s) (hb : Bornology.IsBounded s) :
    interior s ⊆ jordanInterior (frontier s) := by
  intro p hp
  refine ⟨?_, hb.subset ((connectedComponentIn_compl_frontier_subset_interior hs hp).trans
    interior_subset)⟩
  intro hfront
  exact hfront.2 hp

/-- The outward ray from a point outside a convex set remains outside the set. -/
lemma ray_smul_sub_notMem {s : Set Point} (hs : Convex ℝ s)
    {o p : Point} (ho : o ∈ s) (hp : p ∉ s) {r : ℝ} (hr : 1 ≤ r) :
    o + r • (p - o) ∉ s := by
  intro hq
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have h := (hs.starConvex ho).add_smul_sub_mem hq
    (inv_nonneg.mpr hrpos.le) (inv_le_one_of_one_le₀ hr)
  have heq : o + r⁻¹ • (o + r • (p - o) - o) = p := by
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hrpos.ne', one_smul]
    abel
  exact hp (heq ▸ h)

/-- Every exterior point of a nonempty bounded closed convex set has an unbounded component outside its frontier. -/
lemma exterior_component_unbounded {s : Set Point} (hs : Convex ℝ s)
    (hclosed : IsClosed s) {o p : Point} (ho : o ∈ s) (hp : p ∉ s) :
    ¬ Bornology.IsBounded (connectedComponentIn (frontier s)ᶜ p) := by
  let f : ℝ → Point := fun r ↦ o + r • (p - o)
  have hf : Continuous f := continuous_const.add (continuous_id.smul continuous_const)
  have hpre : IsPreconnected (f '' Set.Ici 1) :=
    isPreconnected_Ici.image f hf.continuousOn
  have hsub : f '' Set.Ici 1 ⊆ (frontier s)ᶜ := by
    rintro q ⟨r, hr, rfl⟩ hq
    exact ray_smul_sub_notMem hs ho hp hr (hclosed.closure_eq ▸ hq.1)
  have hpmem : p ∈ f '' Set.Ici 1 := ⟨1, by simp, by simp [f]⟩
  have hcomp := hpre.subset_connectedComponentIn hpmem hsub
  intro hb
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  have hnorm : 0 < ‖p - o‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by
    intro h; exact hp (h ▸ ho)))
  let r := max 1 ((C + ‖o‖ + 1) / ‖p - o‖)
  have hr : 1 ≤ r := le_max_left _ _
  have hq := hC (f r) (hcomp ⟨r, hr, rfl⟩)
  have hdiff : ‖r • (p - o)‖ ≤ C + ‖o‖ := by
    calc
      ‖r • (p - o)‖ = ‖f r - o‖ := by simp [f]
      _ ≤ ‖f r‖ + ‖o‖ := norm_sub_le _ _
      _ ≤ C + ‖o‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r)] at hdiff
  have hlower := (div_le_iff₀ hnorm).mp (le_max_right 1 ((C + ‖o‖ + 1) / ‖p - o‖))
  change C + ‖o‖ + 1 ≤ r * ‖p - o‖ at hlower
  linarith

/-- The bounded complementary region of a nonempty compact convex set frontier is its interior. -/
lemma jordanInterior_frontier_eq_interior {s : Set Point} (hs : Convex ℝ s)
    (hclosed : IsClosed s) (hb : Bornology.IsBounded s) (hne : s.Nonempty) :
    jordanInterior (frontier s) = interior s := by
  apply Set.Subset.antisymm
  · intro p hp
    have hps : p ∈ s := by
      by_contra hnot
      obtain ⟨o, ho⟩ := hne
      exact exterior_component_unbounded hs hclosed ho hnot hp.2
    by_contra hnot
    exact hp.1 ⟨subset_closure hps, hnot⟩
  · exact interior_subset_jordanInterior_frontier hclosed hb

end MovingSofa
