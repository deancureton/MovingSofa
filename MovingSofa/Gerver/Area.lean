import MovingSofa.Gerver.Area.CapFan
import MovingSofa.Gerver.Area.NicheCover

/-!
# Rational area bounds for the canonical Gerver sofa

The canonical Gerver sofa is the paper's literal set (`gerver_canonical_paper_literal`), the
difference of the literal outer cap and the literal niche.  The cap and the niche are Borel
of finite area with `28609 / 10000 ≤ |K₀|` and `|N₀| ≤ 3301 / 5000`
(`gerver_geometric_area_bounds`), both numeric bounds coming from the kernel-checked
certificate `MovingSofa.Gerver.AreaCertificate` through the fan bound of
`MovingSofa.Gerver.Area.CapFan` and the rectangle cover of
`MovingSofa.Gerver.Area.NicheCover`.  Subadditivity of area then gives
`11 / 5 ≤ |G|` (`gerver_area_lower_bound`).
-/

noncomputable section

namespace MovingSofa

open MeasureTheory

theorem gerver_canonical_paper_literal :
    gerversSofa = paperGerverSofa ∧ paperGerverSofa = gerverLiteralSofa := by
  refine ⟨?_, paperGerverSofa_eq_literal⟩
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hT0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hTpos.le⟩
  have hTT : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hTpos.le, le_rfl⟩
  -- Translate-then-rotate splits into rotation of the point plus rotation of the shift.
  have hrt : ∀ (α : Real.Angle) (v s : Point),
      rotateTranslate α v s = rotationMap α s + rotationMap α v := by
    intro α v s
    show (EuclideanGeometry.o.rotation α) (s + v) = _
    exact map_add _ _ _
  -- The canonical placements agree with the paper ones on `[0, π/2]`.
  have himg : ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ S : Set Point,
      rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' S =
        (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' S := by
    intro t ht S
    apply Set.image_congr'
    intro s
    rw [hrt, canonical_path_rotation_eq_paper t ht]
  -- Membership in a rotated-translated coordinate region is read off in the moving frame.
  have himage : ∀ (P : ℝ → ℝ → Prop) (S : Set Point),
      (∀ s : Point, s ∈ S ↔ P (s 0) (s 1)) →
      ∀ (t : Real.Angle) (v z : Point),
        z ∈ (fun s ↦ rotationMap t s + v) '' S ↔
          P (inner ℝ (z - v) (normalVector t)) (inner ℝ (z - v) (tangentVector t)) := by
    intro P S hS t v z
    constructor
    · rintro ⟨s, hs, rfl⟩
      have h0 : inner ℝ (rotationMap t s + v - v) (normalVector t) = s 0 := by
        rw [add_sub_cancel_right, inner_rotationMap_normalVector]
      have h1 : inner ℝ (rotationMap t s + v - v) (tangentVector t) = s 1 := by
        rw [add_sub_cancel_right, inner_rotationMap_tangentVector]
      rw [h0, h1]
      exact (hS s).1 hs
    · intro h
      obtain ⟨s, hs⟩ := (EuclideanGeometry.o.rotation t).surjective (z - v)
      have hsz : rotationMap t s = z - v := hs
      have h0 : s 0 = inner ℝ (z - v) (normalVector t) := by
        rw [← inner_rotationMap_normalVector s t, hsz]
      have h1 : s 1 = inner ℝ (z - v) (tangentVector t) := by
        rw [← inner_rotationMap_tangentVector s t, hsz]
      refine ⟨s, (hS s).2 ?_, ?_⟩
      · rw [h0, h1]; exact h
      · show rotationMap t s + v = z
        rw [hsz]; abel
  have hhoriz : ∀ s : Point, s ∈ horizontalHallway ↔ s 0 ≤ 1 ∧ 0 ≤ s 1 ∧ s 1 ≤ 1 :=
    fun s => ⟨mem_horizontalHallway_coordinates,
      fun h => mem_horizontalHallway_of_coordinates s h.1 ⟨h.2.1, h.2.2⟩⟩
  have hvert : ∀ s : Point, s ∈ verticalHallway ↔ 0 ≤ s 0 ∧ s 0 ≤ 1 ∧ s 1 ≤ 1 :=
    fun s => ⟨mem_verticalHallway_coordinates,
      fun h => mem_verticalHallway_of_coordinates s ⟨h.1, h.2.1⟩ h.2.2⟩
  have hhall : ∀ s : Point, s ∈ hallway ↔ (s 0 ≤ 1 ∧ s 1 ≤ 1) ∧ (0 ≤ s 0 ∨ 0 ≤ s 1) :=
    mem_hallway_iff
  -- Endpoint normalisations of the paper path.
  have hreg := gerver_direct_path_regularity GerverSofa.PartB.params
    GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hpath0 : paperGerverPath 0 = 0 := by
    show GerverSofa.PartF.Coordinates.toPlane
      (GerverSofa.Romik.path GerverSofa.PartB.params 0) = 0
    rw [hreg.2.1]
    ext i
    fin_cases i <;> rfl
  have hpathT : paperGerverPath (Real.pi / 2) 1 = 0 :=
    GerverSofa.Romik.path_end_y_zero_of_mem_box_and_equations
      GerverSofa.PartB.params_mem GerverSofa.PartB.params_equations
  have hstrip : ∀ z : Point,
      z ∈ (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ↔ 0 ≤ z 1 ∧ z 1 ≤ 1 := by
    intro z
    have h := mem_stripParallelogram_iff (Real.pi / 2) z
    rw [inner_normalVector_pi_div_two] at h
    have hset : (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 =
        (stripParallelogram (Real.pi / 2)).1 := rfl
    rw [hset, h]
    tauto
  -- Rewrite both endpoint arms and the family of hallways in the paper frame.
  have hzero : ((0 : ℝ) : Real.Angle) = (0 : Real.Angle) := Real.Angle.coe_zero
  have hgs : gerversSofa =
      ((fun s ↦ rotationMap ((0 : ℝ) : Real.Angle) s + paperGerverPath 0) ''
          horizontalHallway ∩
        (fun s ↦ rotationMap ((Real.pi / 2 : ℝ) : Real.Angle) s +
          paperGerverPath (Real.pi / 2)) '' verticalHallway) ∩
      ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' hallway := by
    show rotateTranslate 0 (GerversSofa.p 0) '' horizontalHallway ∩
        rotateTranslate ((Real.pi / 2 : ℝ) : Real.Angle)
          (GerversSofa.p (Real.pi / 2)) '' verticalHallway ∩
        (⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          rotateTranslate (t : Real.Angle) (GerversSofa.p t) '' hallway) = _
    rw [← hzero, himg 0 hT0 horizontalHallway,
      himg (Real.pi / 2) hTT verticalHallway,
      Set.iInter₂_congr (fun t (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) => himg t ht hallway)]
  have hpaper : paperGerverSofa =
      {z : Point | 0 ≤ z 1 ∧ z 1 ≤ 1} ∩
        ⋂ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
          (fun s ↦ rotationMap (t : Real.Angle) s + paperGerverPath t) '' hallway := by
    show (strips (Real.pi / 2)).1 ∩ (strips (Real.pi / 2)).2.2 ∩ _ = _
    rw [Set.ext hstrip]
    rfl
  rw [hgs, hpaper]
  ext q
  have hn0 : inner ℝ (q - paperGerverPath 0) (normalVector ((0 : ℝ) : Real.Angle)) = q 0 := by
    rw [hpath0, sub_zero, inner_normalVector_zero]
  have hg0 : inner ℝ (q - paperGerverPath 0) (tangentVector ((0 : ℝ) : Real.Angle)) = q 1 := by
    rw [hpath0, sub_zero, inner_tangentVector_zero]
  have hnT : inner ℝ (q - paperGerverPath (Real.pi / 2))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = q 1 := by
    rw [inner_normalVector_pi_div_two]
    show q 1 - paperGerverPath (Real.pi / 2) 1 = q 1
    rw [hpathT, sub_zero]
  have hAhoriz := himage (fun a b => a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1) horizontalHallway hhoriz
  have hAvert := himage (fun a b => 0 ≤ a ∧ a ≤ 1 ∧ b ≤ 1) verticalHallway hvert
  have hAhall := himage (fun a b => (a ≤ 1 ∧ b ≤ 1) ∧ (0 ≤ a ∨ 0 ≤ b)) hallway hhall
  simp only [Set.mem_inter_iff, Set.mem_iInter₂, Set.mem_ofPred_eq, hAhoriz, hAvert, hAhall,
    hn0, hg0, hnT]
  constructor
  · rintro ⟨⟨⟨-, hb0, hb1⟩, -⟩, hC⟩
    exact ⟨⟨hb0, hb1⟩, hC⟩
  · rintro ⟨⟨hb0, hb1⟩, hC⟩
    refine ⟨⟨⟨?_, hb0, hb1⟩, hb0, hb1, ?_⟩, hC⟩
    · have h := (hC 0 hT0).1.1
      rwa [hn0] at h
    · exact (hC (Real.pi / 2) hTT).1.2

theorem gerver_geometric_area_bounds :
    MeasurableSet gerverOuterCap ∧ volume gerverOuterCap < ⊤ ∧
    MeasurableSet gerverLiteralNiche ∧ volume gerverLiteralNiche < ⊤ ∧
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap ∧
    ClassicalResults.area gerverLiteralNiche ≤ (3301 : ℝ) / 5000 := by
  have hfin : volume gerverLiteralNiche ≤ ENNReal.ofReal ((3301 : ℝ) / 5000) :=
    gerver_niche_volume_le
  refine ⟨measurableSet_gerverOuterCap, volume_gerverOuterCap_lt_top,
    measurableSet_gerverLiteralNiche, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top,
    gerverOuterCap_area_certified_lower_bound, ?_⟩
  calc ClassicalResults.area gerverLiteralNiche
      = (volume gerverLiteralNiche).toReal := rfl
    _ ≤ (ENNReal.ofReal ((3301 : ℝ) / 5000)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hfin
    _ = (3301 : ℝ) / 5000 := ENNReal.toReal_ofReal (by norm_num)

theorem gerver_area_lower_bound :
    volume gerversSofa < ⊤ ∧ (11 : ℝ) / 5 ≤ ClassicalResults.area gerversSofa := by
  obtain ⟨-, hKtop, -, hNtop, hKarea, hNarea⟩ := gerver_geometric_area_bounds
  have hG : gerversSofa = gerverOuterCap \ gerverLiteralNiche :=
    gerver_canonical_paper_literal.1.trans gerver_canonical_paper_literal.2
  have hGtop : volume gerversSofa < ⊤ :=
    lt_of_le_of_lt (measure_mono (hG ▸ Set.sdiff_subset)) hKtop
  refine ⟨hGtop, ?_⟩
  -- The cap is covered by the sofa together with the niche, so areas are subadditive.
  have hcover : volume gerverOuterCap ≤ volume gerversSofa + volume gerverLiteralNiche := by
    refine le_trans (measure_mono ?_) (measure_union_le _ _)
    rw [hG]
    exact Set.subset_sdiff_union _ _
  have hreal : ClassicalResults.area gerverOuterCap ≤
      ClassicalResults.area gerversSofa + ClassicalResults.area gerverLiteralNiche := by
    have h := ENNReal.toReal_mono (by finiteness) hcover
    rwa [ENNReal.toReal_add hGtop.ne hNtop.ne] at h
  linarith only [hreal, hKarea, hNarea]

end MovingSofa
