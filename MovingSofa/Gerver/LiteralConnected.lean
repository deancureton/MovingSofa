import MovingSofa.Gerver.LiteralSets

noncomputable section

namespace MovingSofa

theorem gerver_literal_connected : IsConnected gerverLiteralSofa := by
  have hu : ∀ (q : Point) (t : ℝ),
      inner ℝ q (normalVector (t : Real.Angle)) =
        GerverSofa.dot (GerverSofa.PartF.Coordinates.fromPlane q) (GerverSofa.u t) := by
    intro q t
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two, GerverSofa.dot,
      GerverSofa.u, GerverSofa.PartF.Coordinates.fromPlane, mul_comm]
  have hv : ∀ (q : Point) (t : ℝ),
      inner ℝ q (tangentVector (t : Real.Angle)) =
        GerverSofa.dot (GerverSofa.PartF.Coordinates.fromPlane q) (GerverSofa.v t) := by
    intro q t
    simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two, GerverSofa.dot,
      GerverSofa.v, GerverSofa.PartF.Coordinates.fromPlane, mul_comm]
  have hpath : ∀ t : ℝ,
      GerverSofa.PartF.Coordinates.fromPlane (paperGerverPath t) =
        GerverSofa.Romik.path GerverSofa.PartC.params t := fun _ => rfl
  have hcap : ∀ q : Point,
      q ∈ gerverOuterCap ↔
        GerverSofa.PartF.Coordinates.fromPlane q ∈
          GerverSofa.Romik.K0 GerverSofa.PartC.params := by
    intro q
    constructor
    · rintro ⟨hy, hs⟩
      refine ⟨hy, fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := hs t ht
      rw [hu, hu, hpath] at h1
      rw [hv, hv, hpath] at h2
      exact ⟨h1, h2⟩
    · rintro ⟨hy, hs⟩
      refine ⟨hy, fun t ht => ?_⟩
      obtain ⟨h1, h2⟩ := hs t ht
      rw [hu, hu, hpath]
      rw [hv, hv, hpath]
      exact ⟨h1, h2⟩
  have hsub : ∀ (q : Point) (t : ℝ),
      GerverSofa.PartF.Coordinates.fromPlane (q - paperGerverPath t) =
        ((GerverSofa.PartF.Coordinates.fromPlane q).1 -
            (GerverSofa.Romik.path GerverSofa.PartC.params t).1,
          (GerverSofa.PartF.Coordinates.fromPlane q).2 -
            (GerverSofa.Romik.path GerverSofa.PartC.params t).2) := fun _ _ => rfl
  have hniche : ∀ q : Point,
      q ∈ gerverLiteralNiche ↔
        GerverSofa.PartF.Coordinates.fromPlane q ∈
          GerverSofa.Romik.niche GerverSofa.PartC.params := by
    intro q
    constructor
    · rintro ⟨hy, t, ht, h1, h2⟩
      rw [hu, hsub] at h1
      rw [hv, hsub] at h2
      exact ⟨hy, t, ht, h1, h2⟩
    · rintro ⟨hy, t, ht, h1, h2⟩
      refine ⟨hy, t, ht, ?_, ?_⟩
      · rw [hu, hsub]; exact h1
      · rw [hv, hsub]; exact h2
  have hset : gerverLiteralSofa =
      GerverSofa.PartF.Coordinates.toPlane '' GerverSofa.PartC.G := by
    rw [GerverSofa.PartF.Coordinates.image_eq_preimage]
    ext q
    exact and_congr (hcap q) (not_congr (hniche q))
  rw [hset]
  exact GerverSofa.PartF.Coordinates.isConnected_image
    GerverSofa.PartC.Stage4.G_connected_direct

end MovingSofa
