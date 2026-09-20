import MovingSofa.Geometry.Contacts
import MovingSofa.ForMathlib.BoundedVariation

noncomputable section

namespace MovingSofa

private theorem tangent_cone_decomposition (p : Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    p = (inner ℝ p (normalVector (t : Real.Angle)) / Real.sin (t - s)) •
        tangentVector (s : Real.Angle) +
      (-inner ℝ p (normalVector (s : Real.Angle)) / Real.sin (t - s)) •
        tangentVector (t : Real.Angle) := by
  ext i
  fin_cases i <;>
    simp only [normalVector, tangentVector, frame, PiLp.inner_apply,
      Fin.sum_univ_two, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Real.Angle.cos_coe,
      Real.Angle.sin_coe, Real.inner_apply] <;>
    norm_num <;> field_simp [h] <;> rw [Real.sin_sub] <;> ring

private theorem exists_nonneg_tangent_coefficients (p q : Point) (s t : ℝ)
    (hst : s < t) (hts : t < s + Real.pi)
    (hs : inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ p (normalVector (s : Real.Angle)))
    (ht : inner ℝ p (normalVector (t : Real.Angle)) ≤
      inner ℝ q (normalVector (t : Real.Angle))) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      q - p = α • tangentVector (s : Real.Angle) +
        β • tangentVector (t : Real.Angle) := by
  have hsin : 0 < Real.sin (t - s) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hst) (by linarith)
  refine ⟨inner ℝ (q - p) (normalVector (t : Real.Angle)) / Real.sin (t - s),
    -inner ℝ (q - p) (normalVector (s : Real.Angle)) / Real.sin (t - s),
    ?_, ?_, tangent_cone_decomposition (q - p) s t hsin.ne'⟩
  · apply div_nonneg _ hsin.le
    rw [inner_sub_left]
    exact sub_nonneg.mpr ht
  · apply div_nonneg _ hsin.le
    rw [inner_sub_left]
    linarith

private theorem inner_tangent_normal (r a : ℝ) :
    inner ℝ (tangentVector (r : Real.Angle)) (normalVector (a : Real.Angle)) =
      -Real.sin (r - a) := by
  simp [tangentVector, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
    Real.sin_sub]
  ring

private theorem inner_tangent_tangent (r a : ℝ) :
    inner ℝ (tangentVector (r : Real.Angle)) (tangentVector (a : Real.Angle)) =
      Real.cos (r - a) := by
  simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, Real.cos_sub]
  ring

private theorem tangent_projection_signs {a r : ℝ}
    (hr : r ∈ Set.Icc a (a + Real.pi / 2)) :
    inner ℝ (tangentVector (r : Real.Angle)) (normalVector (a : Real.Angle)) ≤ 0 ∧
    0 ≤ inner ℝ (tangentVector (r : Real.Angle)) (tangentVector (a : Real.Angle)) := by
  rw [inner_tangent_normal, inner_tangent_tangent]
  constructor
  · exact neg_nonpos.mpr (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hr.1])
      (by linarith [hr.2, Real.pi_pos]))
  · exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hr.1, Real.pi_pos],
      by linarith [hr.2]⟩

private theorem support_selection_projection_order (K : ConvexBody Point)
    {a s t : ℝ} (hs : s ∈ Set.Icc a (a + Real.pi / 2))
    (ht : t ∈ Set.Icc a (a + Real.pi / 2)) (hst : s < t)
    {p q : Point} (hp : p ∈ exposedEdge K (s : Real.Angle))
    (hq : q ∈ exposedEdge K (t : Real.Angle)) :
    inner ℝ q (normalVector (a : Real.Angle)) ≤
        inner ℝ p (normalVector (a : Real.Angle)) ∧
      inner ℝ p (tangentVector (a : Real.Angle)) ≤
        inner ℝ q (tangentVector (a : Real.Angle)) := by
  have hsp := inner_le_supportValue K hq.1 (s : Real.Angle)
  have htp := inner_le_supportValue K hp.1 (t : Real.Angle)
  rw [← hp.2] at hsp
  rw [← hq.2] at htp
  obtain ⟨α, β, hα, hβ, hrepr⟩ := exists_nonneg_tangent_coefficients p q s t hst
    (by linarith [hs.1, ht.2, Real.pi_pos]) hsp htp
  have hsigns := tangent_projection_signs hs
  have hsignt := tangent_projection_signs ht
  constructor
  · have h := congrArg (fun p ↦ inner ℝ p (normalVector (a : Real.Angle))) hrepr
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith [mul_nonpos_of_nonneg_of_nonpos hα hsigns.1,
      mul_nonpos_of_nonneg_of_nonpos hβ hsignt.1]
  · have h := congrArg (fun p ↦ inner ℝ p (tangentVector (a : Real.Angle))) hrepr
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left] at h
    linarith [mul_nonneg hα hsigns.2, mul_nonneg hβ hsignt.2]

private theorem support_selection_boundedVariationOn_quarter (K : ConvexBody Point)
    (f : ℝ → Point) (a : ℝ)
    (hf : ∀ t ∈ Set.Icc a (a + Real.pi / 2), f t ∈ exposedEdge K (t : Real.Angle)) :
    BoundedVariationOn f (Set.Icc a (a + Real.pi / 2)) := by
  let x : ℝ → ℝ := fun t ↦ -inner ℝ (f t) (normalVector (a : Real.Angle))
  let y : ℝ → ℝ := fun t ↦ inner ℝ (f t) (tangentVector (a : Real.Angle))
  have hx : MonotoneOn x (Set.Icc a (a + Real.pi / 2)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · rfl
    · exact neg_le_neg (support_selection_projection_order K hs ht hst (hf s hs) (hf t ht)).1
  have hy : MonotoneOn y (Set.Icc a (a + Real.pi / 2)) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl | hst
    · rfl
    · exact (support_selection_projection_order K hs ht hst (hf s hs) (hf t ht)).2
  have ha : a ≤ a + Real.pi / 2 := by linarith [Real.pi_pos]
  have hxv : BoundedVariationOn x (Set.Icc a (a + Real.pi / 2)) := by
    simpa only [Set.inter_self] using
      hx.locallyBoundedVariationOn a (a + Real.pi / 2) ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩
  have hyv : BoundedVariationOn y (Set.Icc a (a + Real.pi / 2)) := by
    simpa only [Set.inter_self] using
      hy.locallyBoundedVariationOn a (a + Real.pi / 2) ⟨le_rfl, ha⟩ ⟨ha, le_rfl⟩
  let U := ContinuousLinearMap.toSpanSingleton ℝ (-normalVector (a : Real.Angle))
  let V := ContinuousLinearMap.toSpanSingleton ℝ (tangentVector (a : Real.Angle))
  have hsum := (U.lipschitzWith.comp_boundedVariationOn hxv).add
    (V.lipschitzWith.comp_boundedVariationOn hyv)
  have heq : (U ∘ x) + (V ∘ y) = f := by
    funext t
    simpa [U, V, x, y, Function.comp_def] using
      inner_normalVector_smul_add_inner_tangentVector_smul (f t) (a : Real.Angle)
  rwa [heq] at hsum

private theorem boundedVariationOn_Icc_trans {f : ℝ → Point} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hf : BoundedVariationOn f (Set.Icc a b))
    (hg : BoundedVariationOn f (Set.Icc b c)) :
    BoundedVariationOn f (Set.Icc a c) := by
  have h := eVariationOn.Icc_add_Icc f (s := Set.univ) hab hbc (Set.mem_univ b)
  simp only [Set.univ_inter] at h
  change eVariationOn f (Set.Icc a c) ≠ ⊤
  rw [← h]
  exact ENNReal.add_ne_top.mpr ⟨hf, hg⟩

/-- Every selection of points from the exposed edges has bounded variation on bounded intervals. -/
theorem boundedVariationOn_of_mem_exposedEdge (K : ConvexBody Point)
    (f : ℝ → Point) (hf : ∀ t : ℝ, f t ∈ exposedEdge K (t : Real.Angle)) (a b : ℝ) :
    BoundedVariationOn f (Set.Icc a b) := by
  have hN : ∀ n : ℕ, BoundedVariationOn f (Set.Icc a (a + n * (Real.pi / 2))) := by
    intro n
    induction n with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      exact BoundedVariationOn.of_subsingleton (Set.subsingleton_Icc_of_ge (le_refl a))
    | succ n ih =>
      have hn : a ≤ a + n * (Real.pi / 2) :=
        le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (by positivity))
      have hn' : a + n * (Real.pi / 2) ≤ a + (n + 1) * (Real.pi / 2) := by
        linarith [Real.pi_pos]
      have hpiece := support_selection_boundedVariationOn_quarter K f
        (a + n * (Real.pi / 2)) (fun t _ ↦ hf t)
      have hstep := boundedVariationOn_Icc_trans hn hn' ih
        (by convert hpiece using 1; congr 1; ring)
      simpa only [Nat.cast_add, Nat.cast_one] using hstep
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / (Real.pi / 2))
  have hb : b ≤ a + n * (Real.pi / 2) := by
    have h := (div_lt_iff₀ (by positivity : 0 < Real.pi / 2)).mp hn
    linarith
  exact (hN n).mono (Set.Icc_subset_Icc_right hb)

end MovingSofa
