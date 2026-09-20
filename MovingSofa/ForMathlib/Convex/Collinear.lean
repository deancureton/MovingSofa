import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

open Module

/-- A convex set with empty interior in dimension at most two is collinear. -/
theorem Convex.collinear_of_interior_eq_empty {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : Convex ℝ s) (hdim : finrank ℝ E ≤ 2)
    (hint : interior s = ∅) : Collinear ℝ s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact collinear_empty ℝ E
  have hspan : vectorSpan ℝ s ≠ ⊤ := by
    intro h
    have ha : affineSpan ℝ s = ⊤ :=
      (AffineSubspace.direction_eq_top_iff_of_nonempty
        (hne.mono (subset_affineSpan ℝ s))).mp (by simpa only [direction_affineSpan] using h)
    have hi := hs.interior_nonempty_iff_affineSpan_eq_top.mpr ha
    simp [hint] at hi
  apply collinear_iff_finrank_le_one.mpr
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hspan)
  simp only [finrank_top] at hlt
  omega

/-- A separating linear functional orders points on a line into a segment. -/
theorem Collinear.mem_segment_of_apply_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Collinear ℝ s) {a p x : E}
    (ha : a ∈ s) (hp : p ∈ s) (hx : x ∈ s) (f : E →ₗ[ℝ] ℝ)
    (hpos : 0 < f (p - a)) (hle : f p ≤ f x) : p ∈ segment ℝ a x := by
  have hne : a ≠ p := by
    intro h
    simp [h] at hpos
  obtain ⟨r, hr⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp
    (hs.mem_affineSpan_of_mem_of_ne ha hp hx hne)
  have hrle : 1 ≤ r := by
    rw [← hr, AffineMap.lineMap_apply_module', map_add, map_smul] at hle
    have hsub := f.map_sub p a
    change f p ≤ r * f (p - a) + f a at hle
    nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hrle
  have hinv : r⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr hrpos.le, inv_le_one_of_one_le₀ hrle⟩
  have hmem := lineMap_mem_segment ℝ a x hinv
  rw [← hr, AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ hrpos.ne',
    AffineMap.lineMap_apply_one] at hmem
  simpa only [hr] using hmem
