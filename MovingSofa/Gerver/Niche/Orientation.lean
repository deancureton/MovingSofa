import MovingSofa.Cap.Tail.Space
import MovingSofa.Gerver.Niche.Identification
import MovingSofa.Curve.PositiveGraphRegion
import MovingSofa.Curve.Jordan.SignedArea

/-!
# Orientation of the certified Gerver niche boundary

The niche of the certified Gerver outer cap is the strict region under the niche roof, and the
roof is the graph of a continuous height function `f` over the horizontal extent
`[gerverNicheLeft, gerverNicheRight]` of the roof (`exists_gerverRoofHeight`).  The closure of
the niche is therefore the closed subgraph of `f`, its interior the open subgraph, and the
counterclockwise loop `positiveGraphLoop` around that region traces their common frontier.

`gerverNicheBoundary` is the explicit four-piece traversal of that frontier: the second contact
curve reversed, the ambient path forwards, the fourth contact curve reversed, and the base
segment.  It runs backwards along the roof through a decreasing piecewise affine parameter
change (`gerverBoundaryParam`), so it is the positive-graph loop reparametrized by an increasing
map (`gerverNicheBoundary_orientedJordan`).  The main result `gerver_niche_orientation` collects
the consequences: the traversal is a continuous path of bounded variation, a counterclockwise
Jordan parametrization of the frontier of the closed niche, its signed curve area is the area of
the niche, and no roof point lies in the niche.

The same description of the niche as the strict region under the roof settles the opposite
inclusion for the fourth boundary piece: every interior point of the base segment does lie in
the niche (`gerver_bottom_segment_mem_gerverLiteralNiche`).
-/

noncomputable section

namespace MovingSofa

/-- The stage-time inequalities of `gerverStageTimes_strictMono`, in the packaged form used
throughout this file. -/
private theorem gerverStageTimes_order :
    gerverStageTimes 0 = 0 ∧ gerverStageTimes 5 = Real.pi / 2 ∧
      0 < gerverStageTimes 1 ∧ gerverStageTimes 1 < gerverStageTimes 2 ∧
      gerverStageTimes 2 < gerverStageTimes 3 ∧ gerverStageTimes 3 < gerverStageTimes 4 ∧
      gerverStageTimes 4 < Real.pi / 2 := by
  have h := gerverStageTimes_strictMono
  exact ⟨gerverStageTimes_zero, rfl, h (show (0 : Fin 6) < 1 by decide),
    h (show (1 : Fin 6) < 2 by decide), h (show (2 : Fin 6) < 3 by decide),
    h (show (3 : Fin 6) < 4 by decide), h (show (4 : Fin 6) < 5 by decide)⟩

/-! ## The roof as the graph of a continuous height function -/

/-- The left end of the horizontal extent of the niche roof. -/
private def gerverNicheLeft : ℝ := paperGerverContacts 0 3 0

/-- The right end of the horizontal extent of the niche roof. -/
private def gerverNicheRight : ℝ := paperGerverContacts (Real.pi / 2) 1 0

private theorem gerverNicheRoof_zero :
    gerverNicheRoof ⟨0, le_rfl, by positivity⟩ = paperGerverContacts 0 3 := by
  obtain ⟨-, -, h01, h12, -, -, -⟩ := gerverStageTimes_order
  exact gerverNicheRoof_of_le_two _ (by linarith)

private theorem gerverNicheRoof_top :
    gerverNicheRoof ⟨Real.pi / 2, by positivity, le_rfl⟩ =
      paperGerverContacts (Real.pi / 2) 1 := by
  obtain ⟨-, -, -, -, -, h34, h45⟩ := gerverStageTimes_order
  exact gerverNicheRoof_of_ge_three _ (by linarith)

/-- The niche roof is the graph of a continuous function over its horizontal extent, which
vanishes at the two ends and is positive in between. -/
private theorem exists_gerverRoofHeight :
    ∃ f : ℝ → ℝ, Continuous f ∧
      (∀ s : Set.Icc (0 : ℝ) (Real.pi / 2), f (gerverNicheRoof s 0) = gerverNicheRoof s 1) ∧
      (∀ c ∈ Set.Icc gerverNicheLeft gerverNicheRight,
        ∃ s : Set.Icc (0 : ℝ) (Real.pi / 2), gerverNicheRoof s 0 = c) ∧
      gerverNicheLeft < gerverNicheRight ∧
      f gerverNicheLeft = 0 ∧ f gerverNicheRight = 0 ∧
      ∀ c ∈ Set.Ioo gerverNicheLeft gerverNicheRight, 0 < f c := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  set A : Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨0, le_rfl, hpi.le⟩ with hA
  set B : Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨Real.pi / 2, hpi.le, le_rfl⟩ with hB
  have hk : StrictMono fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0 :=
    gerver_niche_roof_strictMono
  have hk0 : Continuous fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp continuous_gerverNicheRoof
  have hk1 : Continuous fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp continuous_gerverNicheRoof
  have hAleft : gerverNicheRoof A 0 = gerverNicheLeft := by rw [gerverNicheRoof_zero]; rfl
  have hBright : gerverNicheRoof B 0 = gerverNicheRight := by rw [gerverNicheRoof_top]; rfl
  have hab : gerverNicheLeft < gerverNicheRight := by
    rw [← hAleft, ← hBright]
    exact hk (show A < B from hpi)
  have hmem : ∀ s, gerverNicheRoof s 0 ∈ Set.Icc gerverNicheLeft gerverNicheRight := fun s ↦
    ⟨hAleft ▸ hk.monotone (show A ≤ s from s.2.1), hBright ▸ hk.monotone (show s ≤ B from s.2.2)⟩
  set kmap : Set.Icc (0 : ℝ) (Real.pi / 2) → Set.Icc gerverNicheLeft gerverNicheRight :=
    fun s ↦ ⟨gerverNicheRoof s 0, hmem s⟩ with hkmap
  have hkc : Continuous kmap := hk0.subtype_mk _
  have hkinj : Function.Injective kmap := fun x y h ↦ hk.injective (congrArg Subtype.val h)
  have : PreconnectedSpace (Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    Subtype.preconnectedSpace isPreconnected_Icc
  have hksurj : Function.Surjective kmap := by
    intro s
    obtain ⟨t, ht⟩ := intermediate_value_univ A B hk0 (by rw [hAleft, hBright]; exact s.property)
    exact ⟨t, Subtype.ext ht⟩
  set khom : Set.Icc (0 : ℝ) (Real.pi / 2) ≃ₜ Set.Icc gerverNicheLeft gerverNicheRight :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective kmap ⟨hkinj, hksurj⟩) hkc
    with hkhom
  have hkhom_apply : ∀ s, (khom s : ℝ) = gerverNicheRoof s 0 := fun _ ↦ rfl
  have hsymm : ∀ x : Set.Icc gerverNicheLeft gerverNicheRight,
      gerverNicheRoof (khom.symm x) 0 = (x : ℝ) := by
    intro x
    rw [← hkhom_apply, khom.apply_symm_apply]
  refine ⟨fun c ↦ gerverNicheRoof (khom.symm (Set.projIcc _ _ hab.le c)) 1,
    hk1.comp (khom.symm.continuous.comp continuous_projIcc), ?_, ?_, hab, ?_, ?_, ?_⟩
  · -- the height function inverts the horizontal coordinate
    intro s
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le (gerverNicheRoof s 0) =
        khom s := by
      rw [← hkhom_apply s, Set.projIcc_val]
    dsimp only
    rw [hval, khom.symm_apply_apply]
  · intro c hc
    exact ⟨khom.symm ⟨c, hc⟩, by rw [hsymm ⟨c, hc⟩]⟩
  · have hmemL : gerverNicheLeft ∈ Set.Icc gerverNicheLeft gerverNicheRight :=
      Set.left_mem_Icc.mpr hab.le
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le gerverNicheLeft =
        ⟨gerverNicheLeft, hmemL⟩ := Set.projIcc_of_mem hab.le hmemL
    have hsA : khom.symm ⟨gerverNicheLeft, hmemL⟩ = A :=
      hk.injective (by dsimp only; rw [hsymm ⟨gerverNicheLeft, hmemL⟩, hAleft])
    dsimp only
    rw [hval, hsA, hA, gerverNicheRoof_zero]
    exact gerver_niche_piece_endpoints.2.2.2
  · have hmemR : gerverNicheRight ∈ Set.Icc gerverNicheLeft gerverNicheRight :=
      Set.right_mem_Icc.mpr hab.le
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le gerverNicheRight =
        ⟨gerverNicheRight, hmemR⟩ := Set.projIcc_of_mem hab.le hmemR
    have hsB : khom.symm ⟨gerverNicheRight, hmemR⟩ = B :=
      hk.injective (by dsimp only; rw [hsymm ⟨gerverNicheRight, hmemR⟩, hBright])
    dsimp only
    rw [hval, hsB, hB, gerverNicheRoof_top]
    exact gerver_niche_piece_endpoints.2.2.1
  · intro c hc
    have hval : Set.projIcc gerverNicheLeft gerverNicheRight hab.le c =
        ⟨c, hc.1.le, hc.2.le⟩ := Set.projIcc_of_mem hab.le ⟨hc.1.le, hc.2.le⟩
    dsimp only
    rw [hval]
    set s := khom.symm (⟨c, hc.1.le, hc.2.le⟩ : Set.Icc gerverNicheLeft gerverNicheRight) with hs
    have hcs : gerverNicheRoof s 0 = c := hsymm _
    refine gerver_niche_roof_positive s ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le s.2.1 with h | h
      · exact absurd (by rw [show s = A from Subtype.ext h.symm, hAleft] at hcs; exact hcs)
          hc.1.ne
      · exact h
    · rcases eq_or_lt_of_le s.2.2 with h | h
      · exact absurd (by rw [show s = B from Subtype.ext h, hBright] at hcs; exact hcs.symm)
          hc.2.ne
      · exact h

/-! ## The literal niche is the strict region under the roof -/

/-- Every central path time is the reverse time of a middle roof parameter. -/
private theorem exists_gerverRoofReverseTime {t : ℝ}
    (ht : t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4)) :
    ∃ s : ℝ, gerverStageTimes 2 ≤ s ∧ s ≤ gerverStageTimes 3 ∧ gerverRoofReverseTime s = t := by
  obtain ⟨-, -, -, h12, h23, h34, -⟩ := gerverStageTimes_order
  have hd : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have he : (0 : ℝ) < gerverStageTimes 4 - gerverStageTimes 1 := by linarith
  refine ⟨gerverStageTimes 2 + (gerverStageTimes 4 - t) *
    (gerverStageTimes 3 - gerverStageTimes 2) / (gerverStageTimes 4 - gerverStageTimes 1),
    ?_, ?_, ?_⟩
  · have : 0 ≤ (gerverStageTimes 4 - t) * (gerverStageTimes 3 - gerverStageTimes 2) /
        (gerverStageTimes 4 - gerverStageTimes 1) :=
      div_nonneg (mul_nonneg (by linarith [ht.2]) hd.le) he.le
    linarith
  · have : (gerverStageTimes 4 - t) * (gerverStageTimes 3 - gerverStageTimes 2) /
        (gerverStageTimes 4 - gerverStageTimes 1) ≤
        gerverStageTimes 3 - gerverStageTimes 2 := by
      rw [div_le_iff₀ he]
      nlinarith [ht.1, hd]
    linarith
  · rw [gerverRoofReverseTime]
    field_simp
    ring

/-- The literal niche is the strict vertical region under the niche roof. -/
private theorem gerverLiteralNiche_eq_roofFill :
    gerverLiteralNiche =
      {q : Point | ∃ s : Set.Icc (0 : ℝ) (Real.pi / 2),
        q 0 = gerverNicheRoof s 0 ∧ 0 ≤ q 1 ∧ q 1 < gerverNicheRoof s 1} := by
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  rw [gerver_niche_vertical_fills]
  ext q
  simp only [strictVerticalFill, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ((⟨t, ht, hq0, hq1, hq2⟩ | ⟨t, ht, hq0, hq1, hq2⟩) | ⟨t, ht, hq0, hq1, hq2⟩)
    · rw [h0] at ht
      have hs : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
      refine ⟨⟨t, hs⟩, ?_, hq1, ?_⟩
      · rw [gerverNicheRoof_of_le_two hs ht.2]; exact hq0
      · rw [gerverNicheRoof_of_le_two hs ht.2]; exact hq2
    · obtain ⟨s, hs1, hs2, hsrev⟩ := exists_gerverRoofReverseTime ht
      have hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
      refine ⟨⟨s, hs⟩, ?_, hq1, ?_⟩
      · rw [gerverNicheRoof_mid hs hs1 hs2, hsrev]; exact hq0
      · rw [gerverNicheRoof_mid hs hs1 hs2, hsrev]; exact hq2
    · rw [h5] at ht
      have hs : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith [ht.1], ht.2⟩
      refine ⟨⟨t, hs⟩, ?_, hq1, ?_⟩
      · rw [gerverNicheRoof_of_ge_three hs ht.1]; exact hq0
      · rw [gerverNicheRoof_of_ge_three hs ht.1]; exact hq2
  · rintro ⟨s, hq0, hq1, hq2⟩
    rcases le_or_gt s.val (gerverStageTimes 2) with hle | hgt
    · refine Or.inl (Or.inl ⟨s.val, ⟨by rw [h0]; exact s.2.1, hle⟩, ?_, hq1, ?_⟩)
      · rw [← gerverNicheRoof_of_le_two s.2 hle]; exact hq0
      · rw [← gerverNicheRoof_of_le_two s.2 hle]; exact hq2
    rcases le_or_gt s.val (gerverStageTimes 3) with hle3 | hgt3
    · refine Or.inl (Or.inr ⟨gerverRoofReverseTime s.val,
        gerverRoofReverseTime_mem_Icc hgt.le hle3, ?_, hq1, ?_⟩)
      · rw [← gerverNicheRoof_mid s.2 hgt.le hle3]; exact hq0
      · rw [← gerverNicheRoof_mid s.2 hgt.le hle3]; exact hq2
    · refine Or.inr ⟨s.val, ⟨hgt3.le, by rw [h5]; exact s.2.2⟩, ?_, hq1, ?_⟩
      · rw [← gerverNicheRoof_of_ge_three s.2 hgt3.le]; exact hq0
      · rw [← gerverNicheRoof_of_ge_three s.2 hgt3.le]; exact hq2

/-- The horizontal coordinate of the roof stays in its horizontal extent. -/
private theorem gerverNicheRoof_fst_mem (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s 0 ∈ Set.Icc gerverNicheLeft gerverNicheRight := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hk := gerver_niche_roof_strictMono
  constructor
  · have h := hk.monotone (show (⟨0, le_rfl, hpi.le⟩ : Set.Icc (0 : ℝ) (Real.pi / 2)) ≤ s
      from s.2.1)
    simp only [gerverNicheRoof_zero] at h
    exact h
  · have h := hk.monotone (show s ≤ (⟨Real.pi / 2, hpi.le, le_rfl⟩ :
      Set.Icc (0 : ℝ) (Real.pi / 2)) from s.2.2)
    simp only [gerverNicheRoof_top] at h
    exact h

/-- Read through the roof height function, the literal niche is the strict subgraph. -/
private theorem gerverLiteralNiche_eq_strictSubgraph {f : ℝ → ℝ}
    (hfgraph : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2),
      f (gerverNicheRoof s 0) = gerverNicheRoof s 1)
    (hfsurj : ∀ c ∈ Set.Icc gerverNicheLeft gerverNicheRight,
      ∃ s : Set.Icc (0 : ℝ) (Real.pi / 2), gerverNicheRoof s 0 = c) :
    gerverLiteralNiche = strictSubgraph gerverNicheLeft gerverNicheRight f := by
  rw [gerverLiteralNiche_eq_roofFill]
  ext q
  simp only [strictSubgraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨s, hq0, hq1, hq2⟩
    have hmem := gerverNicheRoof_fst_mem s
    rw [← hq0] at hmem
    exact ⟨hmem.1, hmem.2, hq1, by rw [hq0, hfgraph s]; exact hq2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    obtain ⟨s, hs⟩ := hfsurj (q 0) ⟨h1, h2⟩
    exact ⟨s, hs.symm, h3, by rw [← hfgraph s, hs]; exact h4⟩

def gerverNicheBoundary (s : Set.Icc (0 : ℝ) 4) : Point :=
  if s.val ≤ 1 then
    paperGerverContacts
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s.val) 1
  else if s.val ≤ 2 then
    paperGerverPath
      (gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * (s.val - 1))
  else if s.val ≤ 3 then
    paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3
  else
    (4 - s.val) • paperGerverContacts 0 3 +
      (s.val - 3) • paperGerverContacts (Real.pi / 2) 1

/-! ## The four-piece traversal of the niche boundary -/

/-- On its first piece the niche traversal runs backwards along the second contact curve `B`,
from `B (π / 2)` at `s = 0` to `B t₃` at `s = 1`. -/
theorem gerverNicheBoundary_of_le_one {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4) (h : s ≤ 1) :
    gerverNicheBoundary ⟨s, hs⟩ =
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s) 1 :=
  ite_eq_left h

/-- On its second piece the niche traversal runs forwards along the direct Gerver path, from
`x t₁` at `s = 1` to `x t₄` at `s = 2`. -/
theorem gerverNicheBoundary_mid {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4)
    (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    gerverNicheBoundary ⟨s, hs⟩ =
      paperGerverPath (gerverStageTimes 1 +
        (gerverStageTimes 4 - gerverStageTimes 1) * (s - 1)) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheBoundary_of_le_one hs heq.ge, ← heq,
      show Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * 1 = gerverStageTimes 3 by ring,
      show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((1 : ℝ) - 1) =
        gerverStageTimes 1 by ring]
    exact gerver_niche_piece_endpoints.1
  · rw [gerverNicheBoundary, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- On its third piece the niche traversal runs backwards along the fourth contact curve `D`,
from `D t₂` at `s = 2` to `D 0` at `s = 3`. -/
theorem gerverNicheBoundary_third {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4)
    (h1 : 2 ≤ s) (h2 : s ≤ 3) :
    gerverNicheBoundary ⟨s, hs⟩ = paperGerverContacts (gerverStageTimes 2 * (3 - s)) 3 := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheBoundary_mid hs (by linarith) heq.ge, ← heq,
      show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((2 : ℝ) - 1) =
        gerverStageTimes 4 by ring,
      show gerverStageTimes 2 * ((3 : ℝ) - 2) = gerverStageTimes 2 by ring]
    exact gerver_niche_piece_endpoints.2.1.symm
  · rw [gerverNicheBoundary, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- On its last piece the niche traversal runs along the base segment of the niche, from `D 0`
at `s = 3` to `B (π / 2)` at `s = 4`. -/
theorem gerverNicheBoundary_base {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4) (h : 3 ≤ s) :
    gerverNicheBoundary ⟨s, hs⟩ =
      (4 - s) • paperGerverContacts 0 3 + (s - 3) • paperGerverContacts (Real.pi / 2) 1 := by
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [gerverNicheBoundary_third hs (by linarith) heq.ge, ← heq,
      show gerverStageTimes 2 * ((3 : ℝ) - 3) = 0 by ring]
    norm_num
  · rw [gerverNicheBoundary, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr (by linarith)), ite_eq_right (not_le.mpr hlt)]

private theorem continuous_gerverNicheBoundary : Continuous gerverNicheBoundary := by
  have hc1 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      paperGerverContacts (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s.val) 1 :=
    (continuous_paperGerverContact 1).comp (by fun_prop)
  have hc2 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      paperGerverPath (gerverStageTimes 1 +
        (gerverStageTimes 4 - gerverStageTimes 1) * (s.val - 1)) :=
    contDiff_paperGerverPath.continuous.comp (by fun_prop)
  have hc3 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3 :=
    (continuous_paperGerverContact 3).comp (by fun_prop)
  have hc4 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      (4 - s.val) • paperGerverContacts 0 3 +
        (s.val - 3) • paperGerverContacts (Real.pi / 2) 1 := by fun_prop
  have hinner2 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      if s.val ≤ 3 then paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3
      else (4 - s.val) • paperGerverContacts 0 3 +
        (s.val - 3) • paperGerverContacts (Real.pi / 2) 1 := by
    refine continuous_if_le continuous_subtype_val continuous_const hc3.continuousOn
      hc4.continuousOn ?_
    intro s hsv
    rw [hsv, show gerverStageTimes 2 * ((3 : ℝ) - 3) = 0 by ring]
    norm_num
  have hinner1 : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦
      if s.val ≤ 2 then
        paperGerverPath (gerverStageTimes 1 +
          (gerverStageTimes 4 - gerverStageTimes 1) * (s.val - 1))
      else if s.val ≤ 3 then paperGerverContacts (gerverStageTimes 2 * (3 - s.val)) 3
      else (4 - s.val) • paperGerverContacts 0 3 +
        (s.val - 3) • paperGerverContacts (Real.pi / 2) 1 := by
    refine continuous_if_le continuous_subtype_val continuous_const hc2.continuousOn
      hinner2.continuousOn ?_
    intro s hsv
    rw [hsv, ite_eq_left (show (2 : ℝ) ≤ 3 by norm_num),
      show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((2 : ℝ) - 1) =
        gerverStageTimes 4 by ring,
      show gerverStageTimes 2 * ((3 : ℝ) - 2) = gerverStageTimes 2 by ring]
    exact gerver_niche_piece_endpoints.2.1.symm
  unfold gerverNicheBoundary
  refine continuous_if_le continuous_subtype_val continuous_const hc1.continuousOn
    hinner1.continuousOn ?_
  intro s hsv
  rw [hsv, ite_eq_left (show (1 : ℝ) ≤ 2 by norm_num),
    show Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * (1 : ℝ) = gerverStageTimes 3 by ring,
    show gerverStageTimes 1 + (gerverStageTimes 4 - gerverStageTimes 1) * ((1 : ℝ) - 1) =
      gerverStageTimes 1 by ring]
  exact gerver_niche_piece_endpoints.1

/-- The four-piece niche traversal is a continuous path of bounded variation: each of its six
analytic pieces is continuously differentiable on a closed parameter interval. -/
private theorem gerverNicheBoundary_mem_continuousBV :
    gerverNicheBoundary ∈ continuousBVSubmodule 0 4 := by
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  refine ⟨continuous_gerverNicheBoundary, fun i ↦ ?_⟩
  have hd3 : (0 : ℝ) < Real.pi / 2 - gerverStageTimes 3 := by linarith
  set c1 : ℝ := (Real.pi / 2 - gerverStageTimes 4) / (Real.pi / 2 - gerverStageTimes 3) with hc1def
  set c2 : ℝ := 3 - gerverStageTimes 1 / gerverStageTimes 2 with hc2def
  have hv : (Real.pi / 2 - gerverStageTimes 3) * c1 = Real.pi / 2 - gerverStageTimes 4 := by
    rw [hc1def, mul_comm, div_mul_cancel₀ _ hd3.ne']
  have hu : gerverStageTimes 2 * (gerverStageTimes 1 / gerverStageTimes 2) =
      gerverStageTimes 1 := by
    rw [mul_comm, div_mul_cancel₀ _ (show gerverStageTimes 2 ≠ 0 by
      exact ne_of_gt (by linarith))]
  have hc10 : (0 : ℝ) ≤ c1 := by rw [hc1def]; exact div_nonneg (by linarith) hd3.le
  have hc11 : c1 ≤ 1 := by rw [hc1def]; exact (div_le_one hd3).mpr (by linarith)
  have hq0 : (0 : ℝ) ≤ gerverStageTimes 1 / gerverStageTimes 2 :=
    div_nonneg (by linarith) (by linarith)
  have hq1 : gerverStageTimes 1 / gerverStageTimes 2 ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  have hc22 : (2 : ℝ) ≤ c2 := by rw [hc2def]; linarith
  have hc23 : c2 ≤ 3 := by rw [hc2def]; linarith
  -- a contact curve composed with a smooth time change staying in one stage
  have hcontact : ∀ (j : Fin 4) (k : Fin 5) (arg : ℝ → ℝ) (l r : ℝ), ContDiff ℝ 1 arg →
      Set.MapsTo arg (Set.Icc l r) (gerverStageIntervals k) →
      ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts (arg s) j) (Set.Icc l r) :=
    fun j k arg l r harg hmaps ↦
      (contDiffOn_paperGerverContact j k).comp harg.contDiffOn hmaps
  have harg1 : ContDiff ℝ 1 fun s : ℝ ↦
      Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s := by fun_prop
  have harg3 : ContDiff ℝ 1 fun s : ℝ ↦ gerverStageTimes 2 * (3 - s) := by fun_prop
  -- the six pieces
  have hp1 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s) 1) (Set.Icc 0 c1) := by
    refine hcontact 1 4 _ 0 c1 harg1 ?_
    intro s hs
    rw [gerverStageIntervals_four, h5]
    have hmul := mul_le_mul_of_nonneg_left hs.2 hd3.le
    rw [hv] at hmul
    exact ⟨by linarith, by nlinarith [hs.1]⟩
  have hp2 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts
      (Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s) 1) (Set.Icc c1 1) := by
    refine hcontact 1 3 _ c1 1 harg1 ?_
    intro s hs
    rw [gerverStageIntervals_three]
    have hmul := mul_le_mul_of_nonneg_left hs.1 hd3.le
    rw [hv] at hmul
    exact ⟨by nlinarith [hs.2], by linarith⟩
  have hp3 : ContDiffOn ℝ 1 (fun s ↦ paperGerverPath (gerverStageTimes 1 +
      (gerverStageTimes 4 - gerverStageTimes 1) * (s - 1))) (Set.Icc 1 2) :=
    (contDiff_paperGerverPath.comp (by fun_prop)).contDiffOn
  have hp4 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts (gerverStageTimes 2 * (3 - s)) 3)
      (Set.Icc 2 c2) := by
    refine hcontact 3 1 _ 2 c2 harg3 ?_
    intro s hs
    rw [gerverStageIntervals_one]
    have hmul := mul_le_mul_of_nonneg_left (show 3 - s ≥ 3 - c2 by linarith [hs.2])
      (show (0:ℝ) ≤ gerverStageTimes 2 by linarith)
    rw [show (3 : ℝ) - c2 = gerverStageTimes 1 / gerverStageTimes 2 by rw [hc2def]; ring, hu]
      at hmul
    exact ⟨hmul, by nlinarith [hs.1]⟩
  have hp5 : ContDiffOn ℝ 1 (fun s ↦ paperGerverContacts (gerverStageTimes 2 * (3 - s)) 3)
      (Set.Icc c2 3) := by
    refine hcontact 3 0 _ c2 3 harg3 ?_
    intro s hs
    rw [gerverStageIntervals_zero, h0]
    have hmul := mul_le_mul_of_nonneg_left (show 3 - s ≤ 3 - c2 by linarith [hs.1])
      (show (0:ℝ) ≤ gerverStageTimes 2 by linarith)
    rw [show (3 : ℝ) - c2 = gerverStageTimes 1 / gerverStageTimes 2 by rw [hc2def]; ring, hu]
      at hmul
    exact ⟨by nlinarith [hs.2], hmul⟩
  have hp6 : ContDiffOn ℝ 1 (fun s : ℝ ↦ (4 - s) • paperGerverContacts 0 3 +
      (s - 3) • paperGerverContacts (Real.pi / 2) 1) (Set.Icc 3 4) := by
    apply ContDiff.contDiffOn
    fun_prop
  -- the variation of each coordinate on each of the six pieces
  have e1 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary le_rfl hc10
    (show c1 ≤ 4 by linarith) hp1
    (fun t ↦ gerverNicheBoundary_of_le_one _ (t.2.2.trans hc11)) i
  have e2 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary hc10 hc11
    (show (1 : ℝ) ≤ 4 by norm_num) hp2
    (fun t ↦ gerverNicheBoundary_of_le_one _ t.2.2) i
  have e3 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ 2 by norm_num)
    (show (2 : ℝ) ≤ 4 by norm_num) hp3
    (fun t ↦ gerverNicheBoundary_mid _ t.2.1 t.2.2) i
  have e4 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ 2 by norm_num) hc22 (show c2 ≤ 4 by linarith) hp4
    (fun t ↦ gerverNicheBoundary_third _ t.2.1 (t.2.2.trans hc23)) i
  have e5 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ c2 by linarith) hc23 (show (3 : ℝ) ≤ 4 by norm_num) hp5
    (fun t ↦ gerverNicheBoundary_third _ (hc22.trans t.2.1) t.2.2) i
  have e6 := boundedVariationOn_coord_Icc_of_contDiffOn gerverNicheBoundary
    (show (0 : ℝ) ≤ 3 by norm_num) (show (3 : ℝ) ≤ 4 by norm_num) le_rfl hp6
    (fun t ↦ gerverNicheBoundary_base _ t.2.1) i
  -- glue them along the subdivision `0 ≤ c₁ ≤ 1 ≤ 2 ≤ c₂ ≤ 3 ≤ 4`
  have hsub : ∀ {x y : ℝ} {hx : x ∈ Set.Icc (0 : ℝ) 4} {hy : y ∈ Set.Icc (0 : ℝ) 4},
      x ≤ y → (⟨x, hx⟩ : Set.Icc (0 : ℝ) 4) ≤ ⟨y, hy⟩ := fun h ↦ h
  have q01 : (0 : ℝ) ≤ 1 := by norm_num
  have q12 : (1 : ℝ) ≤ 2 := by norm_num
  have q02 : (0 : ℝ) ≤ 2 := by norm_num
  have q03 : (0 : ℝ) ≤ 3 := by norm_num
  have q34 : (3 : ℝ) ≤ 4 := by norm_num
  have q0c2 : (0 : ℝ) ≤ c2 := by linarith
  have g1 := BoundedVariationOn.Icc_union_Icc (hsub hc10) (hsub hc11) e1 e2
  have g2 := BoundedVariationOn.Icc_union_Icc (hsub q01) (hsub q12) g1 e3
  have g3 := BoundedVariationOn.Icc_union_Icc (hsub q02) (hsub hc22) g2 e4
  have g4 := BoundedVariationOn.Icc_union_Icc (hsub q0c2) (hsub hc23) g3 e5
  show BoundedVariationOn (fun t : Set.Icc (0 : ℝ) 4 ↦ gerverNicheBoundary t i) Set.univ
  exact BoundedVariationOn.univ_of_Icc_endpoints (show (0 : ℝ) ≤ 4 by norm_num)
    (BoundedVariationOn.Icc_union_Icc (hsub q03) (hsub q34) g4 e6)

/-! ## The traversal is the roof, run backwards -/

/-- The decreasing piecewise affine parameter change carrying `[0, 3]` onto the roof
interval `[0, π/2]`. -/
private def gerverBoundaryParam (s : ℝ) : ℝ :=
  if s ≤ 1 then Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s
  else if s ≤ 2 then gerverStageTimes 2 + (gerverStageTimes 3 - gerverStageTimes 2) * (2 - s)
  else gerverStageTimes 2 * (3 - s)

private theorem gerverBoundaryParam_first {s : ℝ} (h : s ≤ 1) :
    gerverBoundaryParam s = Real.pi / 2 - (Real.pi / 2 - gerverStageTimes 3) * s :=
  ite_eq_left h

private theorem gerverBoundaryParam_second {s : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ 2) :
    gerverBoundaryParam s =
      gerverStageTimes 2 + (gerverStageTimes 3 - gerverStageTimes 2) * (2 - s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverBoundaryParam_first heq.ge, ← heq]; ring
  · rw [gerverBoundaryParam, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

private theorem gerverBoundaryParam_third {s : ℝ} (h1 : 2 ≤ s) :
    gerverBoundaryParam s = gerverStageTimes 2 * (3 - s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverBoundaryParam_second (by linarith) heq.ge, ← heq]; ring
  · rw [gerverBoundaryParam, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt)]

private theorem gerverBoundaryParam_strictAntiOn :
    StrictAntiOn gerverBoundaryParam (Set.Icc (0 : ℝ) 3) := by
  obtain ⟨-, -, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hD : (0 : ℝ) < Real.pi / 2 - gerverStageTimes 3 := by linarith
  have hE : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have hF : (0 : ℝ) < gerverStageTimes 2 := by linarith
  have hle1 : ∀ s : ℝ, s ≤ 1 → gerverStageTimes 3 ≤ gerverBoundaryParam s := by
    intro s hs
    rw [gerverBoundaryParam_first hs]
    nlinarith
  have hlt1 : ∀ s : ℝ, 1 < s → s ≤ 3 → gerverBoundaryParam s < gerverStageTimes 3 := by
    intro s hs hs3
    rcases le_or_gt s 2 with h | h
    · rw [gerverBoundaryParam_second hs.le h]; nlinarith
    · rw [gerverBoundaryParam_third h.le]; nlinarith
  have hle2 : ∀ s : ℝ, 1 ≤ s → s ≤ 2 → gerverStageTimes 2 ≤ gerverBoundaryParam s := by
    intro s hs1 hs2
    rw [gerverBoundaryParam_second hs1 hs2]
    nlinarith
  have hlt2 : ∀ s : ℝ, 2 < s → gerverBoundaryParam s < gerverStageTimes 2 := by
    intro s hs
    rw [gerverBoundaryParam_third hs.le]
    nlinarith
  intro x hx y hy hxy
  rcases le_or_gt y 1 with hy1 | hy1
  · rw [gerverBoundaryParam_first (hxy.le.trans hy1), gerverBoundaryParam_first hy1]
    nlinarith
  rcases le_or_gt x 1 with hx1 | hx1
  · exact lt_of_lt_of_le (hlt1 y hy1 hy.2) (hle1 x hx1)
  rcases le_or_gt y 2 with hy2 | hy2
  · rw [gerverBoundaryParam_second hx1.le (hxy.le.trans hy2),
      gerverBoundaryParam_second (by linarith) hy2]
    nlinarith
  rcases le_or_gt x 2 with hx2 | hx2
  · exact lt_of_lt_of_le (hlt2 y hy2) (hle2 x hx1.le hx2)
  · rw [gerverBoundaryParam_third hx2.le, gerverBoundaryParam_third (by linarith)]
    nlinarith

private theorem gerverBoundaryParam_zero : gerverBoundaryParam 0 = Real.pi / 2 := by
  rw [gerverBoundaryParam_first (by norm_num)]; ring

private theorem gerverBoundaryParam_three : gerverBoundaryParam 3 = 0 := by
  rw [gerverBoundaryParam_third (by norm_num)]; ring

private theorem gerverBoundaryParam_mem {s : ℝ} (h1 : 0 ≤ s) (h2 : s ≤ 3) :
    gerverBoundaryParam s ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  have hanti := gerverBoundaryParam_strictAntiOn.antitoneOn
  refine ⟨?_, ?_⟩
  · rw [← gerverBoundaryParam_three]
    exact hanti ⟨h1, h2⟩ (by norm_num) h2
  · rw [← gerverBoundaryParam_zero]
    exact hanti (by norm_num) ⟨h1, h2⟩ h1

/-- On its first three pieces the traversal runs backwards along the niche roof. -/
private theorem gerverNicheBoundary_eq_roof {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 4) (h : s ≤ 3) :
    gerverNicheBoundary ⟨s, hs⟩ =
      gerverNicheRoof ⟨gerverBoundaryParam s, gerverBoundaryParam_mem hs.1 h⟩ := by
  obtain ⟨-, -, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hne : gerverStageTimes 3 - gerverStageTimes 2 ≠ 0 := by
    exact ne_of_gt (by linarith)
  rcases le_or_gt s 1 with h1 | h1
  · rw [gerverNicheBoundary_of_le_one hs h1,
      gerverNicheRoof_of_ge_three _ (by rw [gerverBoundaryParam_first h1]; nlinarith),
      gerverBoundaryParam_first h1]
  rcases le_or_gt s 2 with h2 | h2
  · rw [gerverNicheBoundary_mid hs h1.le h2,
      gerverNicheRoof_mid _ (by rw [gerverBoundaryParam_second h1.le h2]; nlinarith)
        (by rw [gerverBoundaryParam_second h1.le h2]; nlinarith)]
    congr 1
    rw [gerverRoofReverseTime, gerverBoundaryParam_second h1.le h2]
    field_simp
    ring
  · rw [gerverNicheBoundary_third hs h2.le h,
      gerverNicheRoof_of_le_two _ (by rw [gerverBoundaryParam_third h2.le]; nlinarith),
      gerverBoundaryParam_third h2.le]

/-- The four-piece traversal has the same image as the counterclockwise loop around the
region under the roof, and is a counterclockwise Jordan parametrization of it. -/
private theorem gerverNicheBoundary_orientedJordan {f : ℝ → ℝ} (hfc : Continuous f)
    (hfgraph : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2),
      f (gerverNicheRoof s 0) = gerverNicheRoof s 1)
    (hab : gerverNicheLeft < gerverNicheRight)
    (hfa : f gerverNicheLeft = 0) (hfb : f gerverNicheRight = 0)
    (hfpos : ∀ c ∈ Set.Ioo gerverNicheLeft gerverNicheRight, 0 < f c) :
    Set.range gerverNicheBoundary =
        Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f) ∧
      IsOrientedJordanParametrization (show (0 : ℝ) ≤ 4 by norm_num)
        (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)) true
        gerverNicheBoundary := by
  have hba : (0 : ℝ) < gerverNicheRight - gerverNicheLeft := by linarith
  obtain ⟨hjor, -⟩ := positiveGraphLoop_counterclockwise gerverNicheLeft gerverNicheRight
    hab f hfc.continuousOn hfa hfb hfpos
  -- the reparametrization of the loop by the four-piece traversal
  have hbnd : ∀ s : Set.Icc (0 : ℝ) 4, s.val ≤ 3 →
      gerverNicheBoundary s 0 ∈ Set.Icc gerverNicheLeft gerverNicheRight := by
    intro s hs
    rw [gerverNicheBoundary_eq_roof s.2 hs]
    exact gerverNicheRoof_fst_mem _
  have hpsimem : ∀ s : Set.Icc (0 : ℝ) 4,
      (if s.val ≤ 3 then (gerverNicheRight - gerverNicheBoundary s 0) /
        (gerverNicheRight - gerverNicheLeft) else s.val - 2) ∈ Set.Icc (0 : ℝ) 2 := by
    intro s
    by_cases hs : s.val ≤ 3
    · obtain ⟨hl, hr⟩ := hbnd s hs
      rw [ite_eq_left hs]
      exact ⟨div_nonneg (by linarith) hba.le, by
        refine le_trans ((div_le_one hba).mpr (by linarith)) (by norm_num)⟩
    · rw [ite_eq_right hs]
      exact ⟨by linarith [not_le.mp hs], by linarith [s.2.2]⟩
  set ψ : Set.Icc (0 : ℝ) 4 → Set.Icc (0 : ℝ) 2 := fun s ↦ ⟨_, hpsimem s⟩ with hψdef
  have hψval : ∀ s : Set.Icc (0 : ℝ) 4, (ψ s : ℝ) =
      if s.val ≤ 3 then (gerverNicheRight - gerverNicheBoundary s 0) /
        (gerverNicheRight - gerverNicheLeft) else s.val - 2 := fun _ ↦ rfl
  have hψle : ∀ s : Set.Icc (0 : ℝ) 4, s.val ≤ 3 → (ψ s : ℝ) ≤ 1 := by
    intro s hs
    rw [hψval, ite_eq_left hs]
    exact (div_le_one hba).mpr (by linarith [(hbnd s hs).1])
  have hψeq : ∀ s : Set.Icc (0 : ℝ) 4, s.val ≤ 3 →
      gerverNicheRight - (gerverNicheRight - gerverNicheLeft) * (ψ s : ℝ) =
        gerverNicheBoundary s 0 := by
    intro s hs
    rw [hψval, ite_eq_left hs, mul_div_cancel₀ _ hba.ne']
    ring
  have hbthree : ∀ s : Set.Icc (0 : ℝ) 4, s.val = 3 →
      gerverNicheBoundary s 0 = gerverNicheLeft := by
    intro s hs
    rw [gerverNicheBoundary_eq_roof s.2 hs.le]
    have h3 : gerverBoundaryParam s.val = 0 := by rw [hs]; exact gerverBoundaryParam_three
    simp only [h3]
    rw [gerverNicheRoof_zero]
    rfl
  have hψthree : ∀ s : Set.Icc (0 : ℝ) 4, s.val = 3 → (ψ s : ℝ) = 1 := by
    intro s hs
    rw [hψval, ite_eq_left hs.le, hbthree s hs]
    field_simp
  -- the traversal is the loop, reparametrized
  have hΓψ : ∀ s : Set.Icc (0 : ℝ) 4,
      gerverNicheBoundary s = positiveGraphLoop gerverNicheLeft gerverNicheRight f (ψ s) := by
    intro s
    by_cases hs : s.val ≤ 3
    · rw [positiveGraphLoop_apply_of_le (hpsimem s) (hψle s hs), hψeq s hs]
      have hroof := gerverNicheBoundary_eq_roof s.2 hs
      have hheight : f (gerverNicheBoundary s 0) = gerverNicheBoundary s 1 := by
        rw [hroof, hfgraph]
      rw [hheight]
      exact Point.eq_vecNotation _
    · have hs' : (3 : ℝ) ≤ s.val := (not_le.mp hs).le
      rw [positiveGraphLoop_apply_of_not_le (hpsimem s) (by
        rw [ite_eq_right hs]; exact not_le.mpr (by linarith [not_le.mp hs])),
        ite_eq_right hs, gerverNicheBoundary_base s.2 hs']
      have hD : paperGerverContacts 0 3 = !₂[gerverNicheLeft, (0 : ℝ)] := by
        rw [Point.eq_vecNotation (paperGerverContacts 0 3), gerver_niche_piece_endpoints.2.2.2]
        rfl
      have hB : paperGerverContacts (Real.pi / 2) 1 = !₂[gerverNicheRight, (0 : ℝ)] := by
        rw [Point.eq_vecNotation (paperGerverContacts (Real.pi / 2) 1),
          gerver_niche_piece_endpoints.2.2.1]
        rfl
      rw [hD, hB]
      ext i
      fin_cases i
      · simp
        ring
      · simp
  have hΓfun : gerverNicheBoundary =
      positiveGraphLoop gerverNicheLeft gerverNicheRight f ∘ ψ := funext hΓψ
  -- strict monotonicity of the reparametrization
  have hψmono : StrictMono ψ := by
    intro s t hst
    have hstv : s.val < t.val := hst
    have hlt : (ψ s : ℝ) < (ψ t : ℝ) := by
      by_cases hs : s.val ≤ 3
      · by_cases ht : t.val ≤ 3
        · have hΓ : gerverNicheBoundary t 0 < gerverNicheBoundary s 0 := by
            rw [gerverNicheBoundary_eq_roof s.2 hs, gerverNicheBoundary_eq_roof t.2 ht]
            exact gerver_niche_roof_strictMono
              (show (⟨gerverBoundaryParam t.val, gerverBoundaryParam_mem t.2.1 ht⟩ :
                  Set.Icc (0 : ℝ) (Real.pi / 2)) <
                ⟨gerverBoundaryParam s.val, gerverBoundaryParam_mem s.2.1 hs⟩ from
                gerverBoundaryParam_strictAntiOn ⟨s.2.1, hs⟩ ⟨t.2.1, ht⟩ hstv)
          rw [hψval s, hψval t, ite_eq_left hs, ite_eq_left ht]
          have h2 : gerverNicheRight - gerverNicheBoundary s 0 <
              gerverNicheRight - gerverNicheBoundary t 0 := by linarith
          gcongr
        · rw [hψval t, ite_eq_right ht]
          exact lt_of_le_of_lt (hψle s hs) (by linarith [not_le.mp ht])
      · have ht : ¬ t.val ≤ 3 := fun h ↦ hs (le_trans hstv.le h)
        rw [hψval s, hψval t, ite_eq_right hs, ite_eq_right ht]
        linarith
    exact hlt
  -- the reparametrization matches the endpoints and is a continuous surjection
  have hz0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := ⟨le_rfl, by norm_num⟩
  have hz4 : (4 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := ⟨by norm_num, le_rfl⟩
  have hu0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hu2 : (2 : ℝ) ∈ Set.Icc (0 : ℝ) 2 := ⟨by norm_num, le_rfl⟩
  have hbzero : gerverNicheBoundary ⟨0, hz0⟩ 0 = gerverNicheRight := by
    rw [gerverNicheBoundary_eq_roof hz0 (by norm_num)]
    have h3 : gerverBoundaryParam (0 : ℝ) = Real.pi / 2 := gerverBoundaryParam_zero
    simp only [h3]
    rw [gerverNicheRoof_top]
    rfl
  have hψ0 : ψ ⟨0, hz0⟩ = ⟨0, hu0⟩ := by
    refine Subtype.ext ?_
    rw [hψval, ite_eq_left (by norm_num), hbzero, sub_self, zero_div]
  have hψ4 : ψ ⟨4, hz4⟩ = ⟨2, hu2⟩ := by
    refine Subtype.ext ?_
    rw [hψval, ite_eq_right (by norm_num)]
    norm_num
  have hψcont : Continuous ψ := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_if_le continuous_subtype_val continuous_const
      ((continuous_const.sub ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
        continuous_gerverNicheBoundary)).div_const _).continuousOn
      (continuous_subtype_val.sub continuous_const).continuousOn ?_
    intro s hsv
    rw [hbthree s hsv, hsv, div_self hba.ne']
    norm_num
  have : PreconnectedSpace (Set.Icc (0 : ℝ) 4) := Subtype.preconnectedSpace isPreconnected_Icc
  have hψsurj : Function.Surjective ψ := by
    intro u
    have hcont : Continuous fun s : Set.Icc (0 : ℝ) 4 ↦ (ψ s : ℝ) :=
      continuous_subtype_val.comp hψcont
    have hmemu : (u : ℝ) ∈ Set.Icc
        ((fun s : Set.Icc (0 : ℝ) 4 ↦ (ψ s : ℝ)) ⟨0, hz0⟩)
        ((fun s : Set.Icc (0 : ℝ) 4 ↦ (ψ s : ℝ)) ⟨4, hz4⟩) := by
      simp only
      rw [congrArg Subtype.val hψ0, congrArg Subtype.val hψ4]
      exact u.property
    obtain ⟨t, ht⟩ := intermediate_value_univ _ _ hcont hmemu
    exact ⟨t, Subtype.ext ht⟩
  -- the traversal traces the loop, once
  have hrange : Set.range gerverNicheBoundary =
      Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f) := by
    rw [hΓfun, Set.range_comp, hψsurj.range_eq, Set.image_univ]
  have hinj : Set.InjOn gerverNicheBoundary {t : Set.Icc (0 : ℝ) 4 | (t : ℝ) < 4} := by
    intro x hx y hy hxy
    have hlt2 : ∀ z : Set.Icc (0 : ℝ) 4, (z : ℝ) < 4 →
        (ψ z : Set.Icc (0 : ℝ) 2) ∈ {t : Set.Icc (0 : ℝ) 2 | (t : ℝ) < 2} := by
      intro z hz
      have h := hψmono (show z < (⟨4, hz4⟩ : Set.Icc (0 : ℝ) 4) from hz)
      rw [hψ4] at h
      exact h
    refine hψmono.injective (hjor.2.2.2.2.2.1 (hlt2 x hx) (hlt2 y hy) ?_)
    rw [← hΓψ x, ← hΓψ y]
    exact hxy
  have hclosedpath : gerverNicheBoundary ⟨0, hz0⟩ = gerverNicheBoundary ⟨4, hz4⟩ := by
    rw [hΓψ, hΓψ, hψ0, hψ4]
    exact hjor.2.2.2.2.1
  have hwind : ∀ p ∈ jordanInterior
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)),
      curveWinding (show (0 : ℝ) ≤ 4 by norm_num) gerverNicheBoundary p = 1 := by
    intro p hp
    have hw2 : curveWinding (show (0 : ℝ) ≤ 2 by norm_num)
        (positiveGraphLoop gerverNicheLeft gerverNicheRight f) p = 1 := by
      simpa using hjor.2.2.2.2.2.2 p hp
    have hne : curveWinding (show (0 : ℝ) ≤ 2 by norm_num)
        (positiveGraphLoop gerverNicheLeft gerverNicheRight f) p ≠ 0 := by
      rw [hw2]; norm_num
    have hcomp := curveWinding_comp_of_endpoints (show (0 : ℝ) ≤ 2 by norm_num)
      (show (0 : ℝ) ≤ 4 by norm_num)
      (exists_curveAngleLift_of_curveWinding_ne_zero _ hne) hψcont hψ0 hψ4
    rw [← hΓfun] at hcomp
    rw [hcomp, hw2]
  have hOJP : IsOrientedJordanParametrization (show (0 : ℝ) ≤ 4 by norm_num)
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)) true
      gerverNicheBoundary :=
    ⟨by norm_num, hjor.2.1, continuous_gerverNicheBoundary, hrange, hclosedpath, hinj,
      fun p hp ↦ by simpa using hwind p hp⟩
  exact ⟨hrange, hOJP⟩

/-- No point of the niche roof lies in the strict region under the roof: the roof is the graph
of the height function, and that region lies strictly below the graph. -/
private theorem gerverNicheRoof_notMem_strictSubgraph {f : ℝ → ℝ}
    (hfgraph : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2),
      f (gerverNicheRoof s 0) = gerverNicheRoof s 1)
    (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s ∉ strictSubgraph gerverNicheLeft gerverNicheRight f := by
  intro hmem
  have h := hmem.2.2.2
  rw [hfgraph s] at h
  exact absurd h (lt_irrefl _)

theorem gerver_niche_orientation :
    ∃ K : RightAngleCapSpace, (K.val : Set Point) = gerverOuterCap ∧
      ∃ Γ : ContinuousBVPaths 0 4, Γ.val = gerverNicheBoundary ∧
        IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 4)
          (frontier (closure (capNiche K))) true Γ.val ∧
        closure (capNiche K) = jordanInterior (Set.range Γ.val) ∪ Set.range Γ.val ∧
        ClassicalResults.area (closure (capNiche K)) = ClassicalResults.area (capNiche K) ∧
        curveAreaFunctional Γ = ClassicalResults.area (capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
          paperGerverContacts t 1 ∉ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
          paperGerverPath t ∉ capNiche K) ∧
        (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
          paperGerverContacts t 3 ∉ capNiche K) := by
  obtain ⟨-, ⟨K, hKset, hKniche⟩, -, -⟩ := gerver_paperNiche_identification
  obtain ⟨f, hfc, hfgraph, hfsurj, hab, hfa, hfb, hfpos⟩ := exists_gerverRoofHeight
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hfcon : ContinuousOn f (Set.Icc gerverNicheLeft gerverNicheRight) := hfc.continuousOn
  -- the niche and its closure, read as subgraphs of the roof height
  have hniche : capNiche K = strictSubgraph gerverNicheLeft gerverNicheRight f := by
    rw [hKniche, gerverLiteralNiche_eq_strictSubgraph hfgraph hfsurj]
  have hclos : closure (capNiche K) = closedSubgraph gerverNicheLeft gerverNicheRight f := by
    rw [hniche, closure_strictSubgraph hab hfcon hfa hfb hfpos]
  -- the region enclosed by the counterclockwise loop around the same graph
  have hintU := jordanInterior_range_positiveGraphLoop hab hfcon hfa hfb hfpos
  have hdiff := closedSubgraph_sdiff_openSubgraph hab hfcon hfa hfb hfpos
  have hCUR := closedSubgraph_eq_openSubgraph_union_range hab hfcon hfa hfb hfpos
  have hfront : frontier (closure (capNiche K)) =
      Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f) := by
    rw [hclos]
    exact frontier_closedSubgraph hab hfcon hfa hfb hfpos
  obtain ⟨hrange, hOJP⟩ := gerverNicheBoundary_orientedJordan hfc hfgraph hab hfa hfb hfpos
  -- the boundary traversal sweeps a null set, so all three regions have the same area
  have hvolR : MeasureTheory.volume
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f)) = 0 := by
    rw [← hrange]
    exact ContinuousBVPaths.volume_range_eq_zero_of_injOn (show (0 : ℝ) ≤ 4 by norm_num)
      ⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩ hOJP.2.2.2.2.2.1
  have hCU : MeasureTheory.volume (closedSubgraph gerverNicheLeft gerverNicheRight f) =
      MeasureTheory.volume (openSubgraph gerverNicheLeft gerverNicheRight f) :=
    (MeasureTheory.measure_eq_measure_of_null_sdiff openSubgraph_subset_closedSubgraph
      (by rw [hdiff]; exact hvolR)).symm
  have hCS : MeasureTheory.volume (closedSubgraph gerverNicheLeft gerverNicheRight f) =
      MeasureTheory.volume (strictSubgraph gerverNicheLeft gerverNicheRight f) := by
    refine (MeasureTheory.measure_eq_measure_of_null_sdiff strictSubgraph_subset_closedSubgraph
      (MeasureTheory.measure_mono_null ?_ hvolR)).symm
    rw [← hdiff]
    exact fun q hq ↦ ⟨hq.1, fun hU ↦ hq.2 ⟨hq.1.1, hq.1.2.1, hq.1.2.2.1, hU.2.2.2⟩⟩
  have hroofnot : ∀ s : Set.Icc (0 : ℝ) (Real.pi / 2), gerverNicheRoof s ∉ capNiche K :=
    fun s ↦ hniche ▸ gerverNicheRoof_notMem_strictSubgraph hfgraph s
  refine ⟨K, hKset, ⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩, rfl, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfront]
    exact hOJP
  · rw [hclos, show Set.range (⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩ :
      ContinuousBVPaths 0 4).val = Set.range gerverNicheBoundary from rfl, hrange, hintU, hCUR]
  · rw [hclos, hniche]
    unfold ClassicalResults.area
    rw [hCS]
  · rw [curveArea_eq_jordanInterior_area 0 4 (show (0 : ℝ) ≤ 4 by norm_num)
      (Set.range (positiveGraphLoop gerverNicheLeft gerverNicheRight f))
      ⟨gerverNicheBoundary, gerverNicheBoundary_mem_continuousBV⟩ hOJP, hintU, hniche]
    unfold ClassicalResults.area
    rw [← hCU, hCS]
  · intro t ht
    rw [h5] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith [ht.1], ht.2⟩
    rw [← gerverNicheRoof_of_ge_three htI ht.1]
    exact hroofnot _
  · intro t ht
    obtain ⟨σ, hσ1, hσ2, hσ⟩ := exists_gerverRoofReverseTime ht
    have hσI : σ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
    rw [← hσ, ← gerverNicheRoof_mid hσI hσ1 hσ2]
    exact hroofnot _
  · intro t ht
    rw [h0] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [← gerverNicheRoof_of_le_two htI ht.2]
    exact hroofnot _

/-! ## The interior of the base segment -/

/-- The two ends of the base segment of the niche boundary are distinct: they are the images
of the parameters `3` and `0` of the boundary traversal, which is injective on `[0, 4)`. -/
theorem gerver_niche_bottom_ends_ne :
    paperGerverContacts 0 3 ≠ paperGerverContacts (Real.pi / 2) 1 := by
  obtain ⟨_, _, Γ, hΓ, hOJP, -⟩ := gerver_niche_orientation
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := by norm_num
  have hmem3 : (3 : ℝ) ∈ Set.Icc (0 : ℝ) 4 := by norm_num
  have hb0 : gerverNicheBoundary ⟨0, hmem0⟩ = paperGerverContacts (Real.pi / 2) 1 := by
    norm_num [gerverNicheBoundary]
  have hb3 : gerverNicheBoundary ⟨3, hmem3⟩ = paperGerverContacts 0 3 := by
    norm_num [gerverNicheBoundary]
  intro heq
  have hinj := hOJP.2.2.2.2.2.1
  rw [hΓ] at hinj
  have h := hinj (show ((⟨3, hmem3⟩ : Set.Icc (0 : ℝ) 4) : ℝ) < 4 by norm_num)
    (show ((⟨0, hmem0⟩ : Set.Icc (0 : ℝ) 4) : ℝ) < 4 by norm_num) (by rw [hb3, hb0, heq])
  have h' := congrArg Subtype.val h
  norm_num at h'

/-- Every interior point of the base segment of the niche boundary, which runs from `D(0)` to
`B(π/2)`, lies in the literal Gerver niche.  Both ends sit on the wall, so the segment is
horizontal and its interior points have strictly intermediate horizontal coordinate; the
intermediate value theorem then puts a roof point directly above such a point, where the roof
has strictly positive height, and the description of the niche as the strict region under the
roof concludes. -/
theorem gerver_bottom_segment_mem_gerverLiteralNiche {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    (1 - a) • paperGerverContacts 0 3 + a • paperGerverContacts (Real.pi / 2) 1 ∈
      gerverLiteralNiche := by
  obtain ⟨h0, h5, h01, h12, h23, h34, h45⟩ := gerverStageTimes_order
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hD0y : paperGerverContacts 0 3 1 = 0 := gerver_niche_piece_endpoints.2.2.2
  have hBTy : paperGerverContacts (Real.pi / 2) 1 1 = 0 := gerver_niche_piece_endpoints.2.2.1
  -- The two ends differ, and they agree in their second coordinate, so they differ in the first.
  have hx : paperGerverContacts 0 3 0 ≠ paperGerverContacts (Real.pi / 2) 1 0 := by
    intro h
    refine gerver_niche_bottom_ends_ne ?_
    ext i
    fin_cases i
    · exact h
    · exact hD0y.trans hBTy.symm
  set P : Point := (1 - a) • paperGerverContacts 0 3 + a • paperGerverContacts (Real.pi / 2) 1
    with hPdef
  have hP0 : P 0 = (1 - a) * paperGerverContacts 0 3 0 +
      a * paperGerverContacts (Real.pi / 2) 1 0 := by
    simp [hPdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  have hP1 : P 1 = 0 := by
    simp [hPdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hD0y, hBTy]
  -- The roof, read as a curve of a real parameter, runs from one end of the segment to the other.
  have hR0 : gerverRoofCurve 0 = paperGerverContacts 0 3 := by
    rw [gerverRoofCurve, ite_eq_left (show (0 : ℝ) ≤ gerverStageTimes 2 by linarith)]
  have hRT : gerverRoofCurve (Real.pi / 2) = paperGerverContacts (Real.pi / 2) 1 := by
    rw [gerverRoofCurve, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr (by linarith))]
  -- The intermediate value theorem produces a roof parameter above `P`.
  have hcont : ContinuousOn (fun s : ℝ ↦ gerverRoofCurve s 0) (Set.uIcc 0 (Real.pi / 2)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
      continuous_gerverRoofCurve).continuousOn
  have hPmem : P 0 ∈ Set.uIcc (gerverRoofCurve 0 0) (gerverRoofCurve (Real.pi / 2) 0) := by
    rw [hR0, hRT, Set.mem_uIcc, hP0]
    rcases lt_or_gt_of_ne hx with h | h
    · exact Or.inl ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩
    · exact Or.inr ⟨by nlinarith [ha.1, ha.2], by nlinarith [ha.1, ha.2]⟩
  obtain ⟨σ, hσmem, hσraw⟩ := intermediate_value_uIcc hcont hPmem
  have hσ : gerverRoofCurve σ 0 = P 0 := hσraw
  rw [Set.uIcc_of_le hpi.le] at hσmem
  -- That parameter is interior, because `P` is not an end of the segment.
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h, hR0, hP0] at hσ
    rcases mul_eq_zero.mp (show a * (paperGerverContacts (Real.pi / 2) 1 0 -
        paperGerverContacts 0 3 0) = 0 by linarith) with h' | h'
    · exact absurd h' (ne_of_gt ha.1)
    · exact hx (by linarith)
  have hσT : σ ≠ Real.pi / 2 := by
    intro h
    rw [h, hRT, hP0] at hσ
    rcases mul_eq_zero.mp (show (1 - a) * (paperGerverContacts (Real.pi / 2) 1 0 -
        paperGerverContacts 0 3 0) = 0 by linarith) with h' | h'
    · exact absurd h' (by linarith [ha.2] : (1 : ℝ) - a ≠ 0)
    · exact hx (by linarith)
  have hheight : 0 < gerverNicheRoof ⟨σ, hσmem⟩ 1 :=
    gerver_niche_roof_positive ⟨σ, hσmem⟩
      ⟨lt_of_le_of_ne hσmem.1 (Ne.symm hσ0), lt_of_le_of_ne hσmem.2 hσT⟩
  rw [gerverLiteralNiche_eq_roofFill]
  exact ⟨⟨σ, hσmem⟩, by rw [← gerverRoofCurve_eq ⟨σ, hσmem⟩]; exact hσ.symm,
    hP1.ge, by rw [hP1]; exact hheight⟩

end MovingSofa
