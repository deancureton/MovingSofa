import MovingSofa.Curve.Jordan.Separation
import MovingSofa.Curve.Jordan.Orientation

namespace MovingSofa

/-- A Jordan curve has a point in its bounded complementary component. -/
theorem IsJordanCurve.jordanInterior_nonempty {Γ : Set Point}
    (hΓ : IsJordanCurve Γ) : (jordanInterior Γ).Nonempty := by
  obtain ⟨U, V, _, _, hU, _, hUb, _, _, hcover, _, _, hcomp, _⟩ :=
    jordan_separation hΓ
  obtain ⟨p, hp⟩ := hU.nonempty
  refine ⟨p, ?_, ?_⟩
  · have : p ∈ Γᶜ := hcover ▸ Set.mem_union_left V hp
    exact this
  · rw [hcomp p hp]
    exact hUb

/-- The frontier of the bounded complementary component of a Jordan curve is the curve
itself. -/
theorem IsJordanCurve.frontier_jordanInterior {Γ : Set Point} (hΓ : IsJordanCurve Γ) :
    frontier (jordanInterior Γ) = Γ := by
  obtain ⟨U, V, -, -, -, -, hUbdd, hVunbdd, -, hcover, hfrontU, -, hUcomp, hVcomp⟩ :=
    jordan_separation hΓ
  have hUeq : jordanInterior Γ = U := by
    ext p
    simp only [jordanInterior, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hpΓ, hpb⟩
      rcases hcover.symm.subset hpΓ with h | h
      · exact h
      · rw [hVcomp p h] at hpb
        exact absurd hpb hVunbdd
    · intro hpU
      refine ⟨?_, ?_⟩
      · have hmem : p ∈ Γᶜ := by rw [← hcover]; exact Or.inl hpU
        exact hmem
      · rw [hUcomp p hpU]
        exact hUbdd
  rw [hUeq]
  exact hfrontU

end MovingSofa
