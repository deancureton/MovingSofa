import MovingSofa.Gerver.CapIdentification

noncomputable section

namespace MovingSofa

theorem gerver_paperNiche_identification :
    (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway gerverOuterCap (t : Real.Angle) =
        supportingHallway paperGerverSofa (t : Real.Angle) ∧
      supportingHallway paperGerverSofa (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway ∧
      (rotatingHallwayParts gerverOuterCap (t : Real.Angle)).innerCorner = paperGerverPath t) ∧
    (∃ K : CapSpace (Real.pi / 2), (K.val : Set Point) = gerverOuterCap ∧
      capNiche K = gerverLiteralNiche) ∧
    monotonization paperGerverSofa (Real.pi / 2) = paperGerverSofa ∧
    IsMonotoneSofa paperGerverSofa := by
  obtain ⟨-, hGeq, hstd, -, -, ⟨K, hKset, -⟩, hsup⟩ := gerver_capSupport_identification
  have hangsum : ∀ t : ℝ, (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((Real.pi / 2 + t : ℝ) : Real.Angle) := fun t => by
    rw [← Real.Angle.coe_add, add_comm]
  -- ### The supporting placement is the paper motion
  have hplace : ∀ S ∈ ({gerverOuterCap, gerverLiteralSofa} : Set (Set Point)),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement S (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t := by
    intro S hS t ht p
    rw [supportingPlacement, hangsum t, (hsup S hS t ht).1, (hsup S hS t ht).2,
      add_sub_cancel_right, add_sub_cancel_right, add_assoc,
      inner_normalVector_smul_add_inner_tangentVector_smul]
  have hplaceK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement gerverOuterCap (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t :=
    hplace gerverOuterCap (Or.inl rfl)
  have hplaceG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ p : Point,
      supportingPlacement paperGerverSofa (t : Real.Angle) p =
        rotationMap (t : Real.Angle) p + paperGerverPath t := by
    rw [hGeq]
    exact hplace gerverLiteralSofa (Or.inr rfl)
  have hhallG : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway paperGerverSofa (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway :=
    fun t ht => Set.image_congr' (hplaceG t ht)
  have hhallK : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      supportingHallway gerverOuterCap (t : Real.Angle) =
        (fun p ↦ rotationMap (t : Real.Angle) p + paperGerverPath t) '' hallway :=
    fun t ht => Set.image_congr' (hplaceK t ht)
  -- ### The monotonization fixed point
  have hmono : monotonization paperGerverSofa (Real.pi / 2) = paperGerverSofa := by
    rw [monotonization, Set.iInter₂_congr hhallG]
    rfl
  refine ⟨fun t ht => ⟨(hhallK t ht).trans (hhallG t ht).symm, hhallG t ht, ?_⟩, ⟨K, hKset, ?_⟩,
    hmono, paperGerverSofa, Real.pi / 2, by rw [hGeq]; exact hstd, hmono.symm⟩
  · show supportingPlacement gerverOuterCap (t : Real.Angle) hallwayParts.innerCorner =
      paperGerverPath t
    rw [hplaceK t ht]
    show rotationMap (t : Real.Angle) 0 + paperGerverPath t = paperGerverPath t
    rw [rotationMap, map_zero, zero_add]
  -- ### The cap niche is the literal niche
  · have hfan : ∀ q : Point, q ∈ capFan (Real.pi / 2) ↔ 0 ≤ q 1 := by
      intro q
      have h : (q ∈ capFan (Real.pi / 2)) ↔
          ((0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ∧
            (0 : ℝ) ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))) := Iff.rfl
      rw [h, inner_normalVector_pi_div_two, and_self]
    have hquad : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ q : Point,
        q ∈ innerQuadrant gerverOuterCap t ↔
          inner ℝ (q - paperGerverPath t) (normalVector (t : Real.Angle)) < 0 ∧
            inner ℝ (q - paperGerverPath t) (tangentVector (t : Real.Angle)) < 0 := by
      intro t ht q
      have hang : ((t + Real.pi / 2 : ℝ) : Real.Angle) =
          ((Real.pi / 2 + t : ℝ) : Real.Angle) := by rw [add_comm]
      have h : (q ∈ innerQuadrant gerverOuterCap t) ↔
          (inner ℝ q (normalVector (t : Real.Angle)) <
              supportValue gerverOuterCap (t : Real.Angle) - 1 ∧
            inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
              supportValue gerverOuterCap ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := Iff.rfl
      rw [h, normalVector_add_pi_div_two_real, hang,
        (hsup gerverOuterCap (Or.inl rfl) t ht).1, (hsup gerverOuterCap (Or.inl rfl) t ht).2,
        add_sub_cancel_right, add_sub_cancel_right, inner_sub_left, inner_sub_left,
        sub_neg, sub_neg]
    rw [capNiche, hKset]
    ext q
    constructor
    · rintro ⟨hq, hmem⟩
      obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.1 hmem
      exact ⟨(hfan q).1 hq, t, ht, (hquad t (Set.Ioo_subset_Icc_self ht) q).1 hqt⟩
    · rintro ⟨hy, t, ht, hqt⟩
      exact ⟨(hfan q).2 hy,
        Set.mem_iUnion₂.2 ⟨t, ht, (hquad t (Set.Ioo_subset_Icc_self ht) q).2 hqt⟩⟩

end MovingSofa
