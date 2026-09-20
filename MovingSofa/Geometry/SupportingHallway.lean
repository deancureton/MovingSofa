import MovingSofa.Geometry.HallwayParts

noncomputable section

namespace MovingSofa

private theorem supportValue_le_of_subset_rotatedHallway (s : Set Point) (t : Real.Angle)
    (hs : s.Nonempty) (v : Point)
    (hv : s ⊆ (fun p ↦ rotationMap t p + v) '' hallway) :
    supportValue s t ≤ 1 + inner ℝ v (normalVector t) ∧
      supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        1 + inner ℝ v (tangentVector t) := by
  have hbound₁ : supportValue s t ≤ 1 + inner ℝ v (normalVector t) := by
    apply csSup_le (hs.image _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hv hp
    dsimp only
    rw [inner_add_left, inner_rotationMap_normalVector]
    linarith [(mem_hallway_iff q).mp hq |>.1.1]
  have hbound₂ : supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
      1 + inner ℝ v (tangentVector t) := by
    apply csSup_le (hs.image _)
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hv hp
    dsimp only
    rw [normalVector_add_pi_div_two, inner_add_left, inner_rotationMap_tangentVector]
    linarith [(mem_hallway_iff q).mp hq |>.1.2]
  exact ⟨hbound₁, hbound₂⟩

theorem subset_supportingHallway (s : Set Point) (t : Real.Angle)
    (hs : s.Nonempty) (hc : IsCompact s)
    (hL : ∃ v : Point, s ⊆ (fun p ↦ rotationMap t p + v) '' hallway) :
    s ⊆ supportingHallway s t := by
  rcases hL with ⟨v, hv⟩
  obtain ⟨hbound₁, hbound₂⟩ := supportValue_le_of_subset_rotatedHallway s t hs v hv
  intro p hp
  obtain ⟨x, hx⟩ := (EuclideanGeometry.o.rotation t).surjective
    (p - (supportValue s t - 1) • normalVector t -
      (supportValue s (t + ((Real.pi / 2 : ℝ) : Real.Angle)) - 1) • tangentVector t)
  have hxp : supportingPlacement s t x = p := by
    simp only [supportingPlacement, rotationMap, hx]
    abel
  have hx₀ := inner_supportingPlacement_normalVector s t x
  have hx₁ := inner_supportingPlacement_tangentVector s t x
  rw [hxp] at hx₀ hx₁
  have hsup (w : Real.Angle) : inner ℝ p (normalVector w) ≤ supportValue s w :=
    le_csSup (hc.bddAbove_image (continuous_id.inner continuous_const).continuousOn)
      ⟨p, hp, rfl⟩
  have hupper₀ := hsup t
  have hupper₁ := hsup (t + ((Real.pi / 2 : ℝ) : Real.Angle))
  rw [normalVector_add_pi_div_two] at hupper₁
  refine ⟨x, (mem_hallway_iff x).mpr ⟨⟨by linarith, by linarith⟩, ?_⟩, hxp⟩
  obtain ⟨q, hq, hqp⟩ := hv hp
  rcases (mem_hallway_iff q).mp hq |>.2 with hq₀ | hq₁
  · have hcoord : inner ℝ p (normalVector t) = q 0 + inner ℝ v (normalVector t) := by
      rw [← hqp, inner_add_left, inner_rotationMap_normalVector]
    exact Or.inl (by linarith)
  · have hcoord : inner ℝ p (tangentVector t) = q 1 + inner ℝ v (tangentVector t) := by
      rw [← hqp, inner_add_left, inner_rotationMap_tangentVector]
    exact Or.inr (by linarith)

end MovingSofa
