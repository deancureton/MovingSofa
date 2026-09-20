import MovingSofa.ForMathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.Convex.Topology

/-!
# Radial exit points of a convex set

From an interior base point of a compact convex set, every point of the set lies on a segment
ending at a boundary point, and that boundary point is unique. These are the facts behind a
radial decomposition of a convex body into cones over its boundary.
-/

open Set
open scoped Topology Pointwise

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point lying a fixed fraction of the way, less than all of it, from an interior point of a
convex set towards a point of the set is itself an interior point. -/
theorem Convex.mem_interior_of_sub_eq_smul_sub {s : Set E} (hs : Convex ℝ s) {o w z : E}
    {γ : ℝ} (ho : o ∈ interior s) (hw : w ∈ s) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (h : z - o = γ • (w - o)) : z ∈ interior s := by
  have hz : z = (1 - γ) • o + γ • w := by
    have hzo : z = o + γ • (w - o) := by rw [← h]; abel
    rw [hzo, smul_sub, sub_smul, one_smul]
    abel
  rw [hz]
  exact hs.combo_interior_closure_mem_interior ho (subset_closure hw) (by linarith) hγ₀ (by ring)

/-- From an interior base point, every point of a compact convex set lies on a segment ending at
a boundary point: the radial exit point of its direction. -/
theorem Convex.exists_mem_frontier_mem_segment [Nontrivial E] {s : Set E} (hs : Convex ℝ s)
    (hcomp : IsCompact s) {o : E} (ho : o ∈ interior s) {x : E} (hx : x ∈ s) :
    ∃ p ∈ frontier s, x ∈ segment ℝ o p := by
  have himage : ((-o) +ᵥ s) = (fun z : E ↦ -o + z) '' s := (Set.image_vadd).symm
  have hsconv : Convex ℝ ((-o) +ᵥ s) := by
    rw [himage]; exact hs.translate (-o)
  have hscompact : IsCompact ((-o) +ᵥ s) := by
    rw [himage]; exact hcomp.image (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ interior ((-o) +ᵥ s) := by
    rw [interior_vadd]
    exact ⟨o, ho, by simp only [vadd_eq_add]; abel⟩
  have hnhds : ((-o) +ᵥ s) ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0
  have hgbound := NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
  have hfrontier : ∀ {z : E}, z ∈ frontier ((-o) +ᵥ s) → o + z ∈ frontier s := by
    intro z hz
    have hzs : z ∈ ((-o) +ᵥ s) := by
      have h := frontier_subset_closure hz
      rwa [hscompact.isClosed.closure_eq] at h
    obtain ⟨k, hk, hkeq⟩ := hzs
    have hok : o + z = k := by rw [← hkeq]; simp only [vadd_eq_add]; abel
    rw [hok, mem_frontier_iff_notMem_interior hk]
    intro hkint
    exact hz.2 (by rw [interior_vadd]; exact ⟨k, hkint, hkeq⟩)
  by_cases hxo : x = o
  · obtain ⟨u, hu⟩ := exists_ne (0 : E)
    obtain ⟨r, hr, -⟩ := hsconv.existsUnique_pos_smul_mem_frontier hnhds hgbound hu
    exact ⟨o + r • u, hfrontier hr.2, hxo ▸ left_mem_segment ℝ o _⟩
  have hxs : x - o ∈ ((-o) +ᵥ s) := ⟨x, hx, by simp only [vadd_eq_add]; abel⟩
  have hgpos : 0 < gauge ((-o) +ᵥ s) (x - o) :=
    (gauge_pos (absorbent_nhds_zero hnhds) hgbound).mpr (sub_ne_zero.mpr hxo)
  have hgle : gauge ((-o) +ᵥ s) (x - o) ≤ 1 := gauge_le_one_of_mem hxs
  have hfr : (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o) ∈ frontier ((-o) +ᵥ s) := by
    apply (gauge_eq_one_iff_mem_frontier hsconv hnhds).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le), smul_eq_mul, inv_mul_cancel₀ hgpos.ne']
  refine ⟨o + (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o), hfrontier hfr, ?_⟩
  rw [segment_eq_image']
  refine ⟨gauge ((-o) +ᵥ s) (x - o), ⟨hgpos.le, hgle⟩, ?_⟩
  show o + gauge ((-o) +ᵥ s) (x - o) • (o + (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o) - o) = x
  rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hgpos.ne', one_smul]
  abel

/-- The radial exit point from an interior base point is unique. -/
theorem Convex.eq_of_mem_frontier_of_mem_segment {s : Set E} (hs : Convex ℝ s)
    (hclosed : IsClosed s) {o x z w : E} (ho : o ∈ interior s) (hxo : x ≠ o)
    (hz : z ∈ frontier s) (hw : w ∈ frontier s) (hxz : x ∈ segment ℝ o z)
    (hxw : x ∈ segment ℝ o w) : z = w := by
  have hzs : z ∈ s := hclosed.frontier_subset hz
  have hws : w ∈ s := hclosed.frontier_subset hw
  have hzint : z ∉ interior s := (mem_frontier_iff_notMem_interior hzs).mp hz
  have hwint : w ∉ interior s := (mem_frontier_iff_notMem_interior hws).mp hw
  rw [segment_eq_image'] at hxz hxw
  obtain ⟨α, hα, hxα⟩ := hxz
  obtain ⟨β, hβ, hxβ⟩ := hxw
  have hxα' : o + α • (z - o) = x := hxα
  have hxβ' : o + β • (w - o) = x := hxβ
  have hαpos : 0 < α := hα.1.lt_or_eq.resolve_right fun h ↦ hxo (by rw [← hxα', ← h]; simp)
  have hβpos : 0 < β := hβ.1.lt_or_eq.resolve_right fun h ↦ hxo (by rw [← hxβ', ← h]; simp)
  have hkey : α • (z - o) = β • (w - o) := add_left_cancel (hxα'.trans hxβ'.symm)
  have hzw : z - o = (α⁻¹ * β) • (w - o) := by
    rw [mul_smul, ← hkey, smul_smul, inv_mul_cancel₀ hαpos.ne', one_smul]
  have hwz : w - o = (α⁻¹ * β)⁻¹ • (z - o) := by
    rw [hzw, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rcases lt_trichotomy (α⁻¹ * β) 1 with hlt | heq | hgt
  · exact absurd (hs.mem_interior_of_sub_eq_smul_sub ho hws (by positivity) hlt hzw) hzint
  · have hzo : z - o = w - o := by rw [hzw, heq, one_smul]
    simpa using congrArg (fun p : E ↦ p + o) hzo
  · refine absurd (hs.mem_interior_of_sub_eq_smul_sub ho hzs (by positivity) ?_ hwz) hwint
    rw [inv_lt_one_iff₀]
    exact Or.inr hgt

