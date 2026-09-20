import MovingSofa.Convex.Limits

noncomputable section

namespace MovingSofa

theorem supportFunction_minkowski_embedding (K L : ConvexBody Point) :
    (∀ (a b : ℝ), 0 ≤ a → 0 ≤ b → ∀ t : Real.Angle,
      supportValue {z : Point | ∃ x ∈ (K : Set Point), ∃ y ∈ (L : Set Point),
        z = a • x + b • y} t =
        a * supportValue K t + b * supportValue L t) ∧
    ((∀ t : Real.Angle, supportValue K t = supportValue L t) → K = L) ∧
    Continuous (fun t : Real.Angle ↦ supportValue K t) ∧
    (K : Set Point) = ⋂ u ∈ {u : Point | ‖u‖ = 1},
      {p : Point | inner ℝ p u ≤ vectorSupport K u} := by
  refine ⟨?_, ?_, (compactSet_support_continuity K K K.nonempty K.isCompact
    K.nonempty K.isCompact).2.2.1, K.eq_iInter_halfSpaces⟩
  · intro a b ha hb t
    obtain ⟨x, hx, hxmax, hxle⟩ := K.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : Point ↦ inner ℝ x (normalVector t)) K.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    obtain ⟨y, hy, hymax, hyle⟩ := L.isCompact.exists_sSup_image_eq_and_ge
      (f := fun x : Point ↦ inner ℝ x (normalVector t)) L.nonempty
      (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
    change sSup ((fun p ↦ inner ℝ p (normalVector t)) '' K) = _ at hxmax
    change sSup ((fun p ↦ inner ℝ p (normalVector t)) '' L) = _ at hymax
    unfold supportValue
    apply IsGreatest.csSup_eq
    constructor
    · refine ⟨a • x + b • y, ?_, ?_⟩
      · exact ⟨x, hx, y, hy, rfl⟩
      · change inner ℝ (a • x + b • y) (normalVector t) = _
        rw [inner_add_left, inner_smul_left, inner_smul_left, ← hxmax, ← hymax]
        simp
    · intro r hr
      obtain ⟨z, ⟨x', hx', y', hy', rfl⟩, rfl⟩ := hr
      change inner ℝ (a • x' + b • y') (normalVector t) ≤ _
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      rw [hxmax, hymax]
      exact add_le_add (mul_le_mul_of_nonneg_left (hxle x' hx') ha)
        (mul_le_mul_of_nonneg_left (hyle y' hy') hb)
  · intro hKL
    have hvector (u : Point) (hu : ‖u‖ = 1) : vectorSupport K u = vectorSupport L u := by
      obtain ⟨t, rfl⟩ := exists_angle_normalVector_eq hu
      exact hKL t
    simp only [vectorSupport] at hvector
    apply ConvexBody.ext
    rw [K.eq_iInter_halfSpaces,
      L.eq_iInter_halfSpaces]
    ext p
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor <;> intro hp u hu
    · simpa [hvector u hu] using hp u hu
    · simpa [hvector u hu] using hp u hu


end MovingSofa
