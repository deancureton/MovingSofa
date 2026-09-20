import MovingSofa.ForMathlib.Convex.Collinear
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped Pointwise

namespace ConvexBody

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A nonsingleton planar convex body with empty interior is a nontrivial segment. -/
theorem exists_eq_segment_of_interior_empty
    (K : ConvexBody (EuclideanSpace ℝ (Fin 2)))
    (hsub : ¬(K : Set (EuclideanSpace ℝ (Fin 2))).Subsingleton)
    (hint : interior (K : Set (EuclideanSpace ℝ (Fin 2))) = ∅) :
    ∃ a b, a ≠ b ∧
      (K : Set (EuclideanSpace ℝ (Fin 2))) = segment ℝ a b := by
  have hcol : Collinear ℝ (K : Set Plane) :=
    K.convex.collinear_of_interior_eq_empty
      (by simp) hint
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd
    (k := ℝ) (K : Set Plane)).mp hcol
  have hv₀ : v ≠ 0 := by
    intro hz
    apply hsub
    intro p hp q hq
    obtain ⟨r, hr⟩ := hv p hp
    obtain ⟨s, hs⟩ := hv q hq
    simpa [hz] using hr.trans (by simpa [hz] using hs.symm)
  let f : Plane → ℝ := fun p ↦ inner ℝ v (p - p₀) / inner ℝ v v
  have hvv : inner ℝ v v ≠ 0 := inner_self_ne_zero.mpr hv₀
  have hrepr : ∀ p ∈ (K : Set Plane), p = f p • v + p₀ := by
    intro p hp
    obtain ⟨r, rfl⟩ := hv p hp
    have hf : f (r • v + p₀) = r := by
      dsimp [f]
      rw [add_sub_cancel_right, inner_smul_right]
      field_simp [hvv]
    change r • v + p₀ = f (r • v + p₀) • v + p₀
    rw [hf]
  have hfcont : Continuous f := by fun_prop
  obtain ⟨a, ha, hamin⟩ := K.isCompact.exists_isMinOn K.nonempty hfcont.continuousOn
  obtain ⟨b, hb, hbmax⟩ := K.isCompact.exists_isMaxOn K.nonempty hfcont.continuousOn
  have habf : f a < f b := by
    apply lt_of_le_of_ne (hamin hb)
    intro heq
    apply hsub
    intro p hp q hq
    rw [hrepr p hp, hrepr q hq]
    have hpfa : f p = f a :=
      le_antisymm ((hbmax hp).trans_eq heq.symm) (hamin hp)
    have hqfa : f q = f a :=
      le_antisymm ((hbmax hq).trans_eq heq.symm) (hamin hq)
    rw [hpfa, hqfa]
  refine ⟨a, b, ?_, Set.Subset.antisymm ?_ ?_⟩
  · intro hab
    rw [hab] at habf
    exact habf.false
  · intro p hp
    rw [segment_eq_image']
    let t := (f p - f a) / (f b - f a)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := ⟨
      div_nonneg (sub_nonneg.mpr (hamin hp)) (sub_nonneg.mpr habf.le),
      (div_le_one (sub_pos.mpr habf)).mpr (sub_le_sub_right (hbmax hp) _)⟩
    refine ⟨t, ht, ?_⟩
    rw [hrepr p hp, hrepr a ha, hrepr b hb]
    have hden : f b - f a ≠ 0 := sub_ne_zero.mpr habf.ne'
    have htalg : f a + t * (f b - f a) = f p := by
      dsimp [t]
      field_simp [hden]
      ring
    rw [← htalg]
    module
  · exact K.convex.segment_subset ha hb

end ConvexBody
