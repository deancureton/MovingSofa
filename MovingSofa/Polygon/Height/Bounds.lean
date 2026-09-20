import MovingSofa.Geometry.QuadrantBounds
import MovingSofa.Polygon.Height.Space
import MovingSofa.Geometry.Support

namespace MovingSofa

/-- A height cap satisfies each selected upper half-plane constraint. -/
theorem polygonHeightCap_subset_normalHalfPlane {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    polygonHeightCap h ⊆ normalHalfPlane (t : Real.Angle)
      (polygonHeightValue h t) false false := by
  intro p hp
  rcases ht with ht | ht
  · exact Set.mem_iInter₂.mp hp.2 t ht
  · exact (Set.mem_iInter₂.mp hp.1 t ht).1

/-- The support of a reconstructed height cap is bounded by each defining height. -/
theorem supportValue_le_polygonHeightValue {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (K : ConvexBody Point) (hK : polygonHeightCap h = (K : Set Point))
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    supportValue K (t : Real.Angle) ≤ polygonHeightValue h t := by
  apply supportValue_le_of_subset_normalHalfPlane
  rw [← hK]
  exact polygonHeightCap_subset_normalHalfPlane h ht

/-- Unit width forces equality with the height of a distinguished strip. -/
theorem supportValue_eq_polygonHeightValue_of_width_one {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) (K : ConvexBody Point)
    (hK : polygonHeightCap h = (K : Set Point)) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hw : supportValue K (t : Real.Angle) +
      supportValue K ((t + Real.pi : ℝ) : Real.Angle) = 1) :
    supportValue K (t : Real.Angle) = polygonHeightValue h t := by
  apply le_antisymm (supportValue_le_polygonHeightValue h K hK (Or.inr ht))
  have hopp : supportValue K ((t + Real.pi : ℝ) : Real.Angle) ≤
      1 - polygonHeightValue h t := by
    apply supportValue_le_of_subset_normalHalfPlane
    intro p hp
    have hp' : p ∈ polygonHeightCap h := hK.symm ▸ hp
    have hl := (Set.mem_iInter₂.mp hp'.1 t ht).2
    change polygonHeightValue h t - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) at hl
    change inner ℝ p (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤ _
    rw [normalVector_add_pi, inner_neg_right]
    linarith
  linarith

/-- Niches grow with their heights when the fan remains fixed. -/
theorem polygonHeightNiche_mono_of_eq_endpoints {Θ : AngleSet}
    {h g : PolygonHeightSpace Θ} (hle : ∀ t, h t ≤ g t)
    (heq : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      polygonHeightValue h t = polygonHeightValue g t) :
    polygonHeightNiche h ⊆ polygonHeightNiche g := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue h t ≤ polygonHeightValue g t := by
    simpa only [polygonHeightValue, dite_eq_left ht] using hle ⟨t, ht⟩
  rintro p ⟨hpF, hpN⟩
  constructor
  · apply Set.mem_iInter₂.mpr
    intro t ht
    have hp := Set.mem_iInter₂.mp hpF t ht
    rwa [heq t ht] at hp
  · obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_, ?_⟩
    · change inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue g t - 1
      have hp₁ : inner ℝ p (normalVector (t : Real.Angle)) <
          polygonHeightValue h t - 1 := hp.1
      exact hp₁.trans_le (sub_le_sub_right (hval t (Or.inl (Or.inl ht))) 1)
    · change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
        polygonHeightValue g (t + Real.pi / 2) - 1
      have hp₂ : inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
          polygonHeightValue h (t + Real.pi / 2) - 1 := hp.2
      exact hp₂.trans_le (sub_le_sub_right
        (hval (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))) 1)

/-- Every polygon height niche is bounded. -/
theorem isBounded_polygonHeightNiche {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Bornology.IsBounded (polygonHeightNiche h) := by
  let a := polygonHeightValue h (Real.pi / 2) - 1
  let Q (t : ℝ) : Set Point := {p | a ≤ p 1 ∧
    inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue h t - 1 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      polygonHeightValue h (t + Real.pi / 2) - 1}
  have hQ : Bornology.IsBounded (⋃ t ∈ Θ.directions, Q t) := by
    apply (Bornology.isBounded_biUnion_finset Θ.directions).2
    intro t ht
    exact isBounded_setOf_le_snd_and_inner_lt _ _ _ t
      ⟨(Θ.interior t ht).1, (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  apply hQ.subset
  rintro p ⟨hpF, hpN⟩
  obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
  apply Set.mem_iUnion₂.mpr
  refine ⟨t, ht, ?_, hp⟩
  have hpT := Set.mem_iInter₂.mp hpF (Real.pi / 2) (by simp)
  change a ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
  simpa [normalVector, frame, PiLp.inner_apply] using hpT

end MovingSofa
