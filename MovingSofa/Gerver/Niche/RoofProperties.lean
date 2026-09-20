import MovingSofa.Gerver.Niche.Roof
import MovingSofa.Gerver.LiteralSets
import MovingSofa.Gerver.StageRegularity

/-!
# Properties of the Gerver niche roof

The main results of this file describe the upper boundary of the paper's literal Gerver
niche: the three graph pieces join up (`gerver_niche_piece_endpoints`), each piece stays
inside the outer cap (`gerver_niche_roof_membership`), the roof is a strictly monotone
positive graph (`gerver_niche_roof_strictMono`, `gerver_niche_roof_positive`), and the
niche is exactly the strict vertical region under that roof (`gerver_niche_vertical_fills`).
The three pieces are identified branch by branch in `gerverNicheRoof_of_le_two`,
`gerverNicheRoof_mid` and `gerverNicheRoof_of_ge_three`, each valid on the closed stage.

Alongside them sits the elementary API of the reverse-time reparametrization
(`continuous_gerverRoofReverseTime`, `gerverRoofReverseTime_two`,
`gerverRoofReverseTime_three`, `gerverRoofReverseTime_mem_Icc`) and the continuity of the
roof, in both its real-parameter and its restricted form (`continuous_gerverRoofCurve`,
`continuous_gerverNicheRoof`).

Every one of them is the certified Part C niche geometry read through the coordinate
dictionary `GerverSofa.PartF.Coordinates.toPlane`.  The dictionary itself is supplied by
the public readers of the lower modules — `paperGerverContacts_one_eq_toPlane` and
`paperGerverContacts_three_eq_toPlane` for the contact curves, `gerverStageTimes_zero`
through `gerverStageTimes_five` for the stage times, and `mem_gerverLiteralNiche_iff`,
`toPlane_mem_gerverOuterCap` for the two literal sets.  What remains here, and is kept
private, is the roof-specific part of the dictionary: the reverse-time reparametrization
and the identification of `gerverNicheRoof` with the certified upper arc.
-/

noncomputable section

namespace MovingSofa

section Roof

open GerverSofa.PartF.Coordinates
open GerverSofa.PartC (params eta tau)

/-- The roof reverse-time reparametrization is the certified affine reversal of the core
stage, which sends `params.theta` to `tau` and `eta` to `params.phi`. -/
private theorem gerverRoofReverseTime_eq (s : ℝ) :
    gerverRoofReverseTime s = GerverSofa.PartC.Stage4.coreReverseTime s := by
  rw [gerverRoofReverseTime, gerverStageTimes_four, gerverStageTimes_one,
    gerverStageTimes_three, gerverStageTimes_two]
  rfl

/-- The Gerver roof is the certified upper niche arc, read in plane coordinates.  The three
branches of `gerverNicheRoof` match the three branches of `nicheTopArc` piece for piece,
with the same cut points `params.theta` and `eta`. -/
private theorem gerverNicheRoof_eq_toPlane (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverNicheRoof s = toPlane (GerverSofa.PartC.Stage4.nicheTopArc s.val) := by
  have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := s.2
  simp only [gerverNicheRoof, GerverSofa.PartC.Stage4.nicheTopArc, gerverStageTimes_two,
    gerverStageTimes_three, gerverRoofReverseTime_eq]
  split_ifs with h1 h2
  · exact paperGerverContacts_three_eq_toPlane hsI
  · rfl
  · exact paperGerverContacts_one_eq_toPlane hsI

end Roof

/-- The three graph pieces of the niche roof join up: the second contact curve at `eta`
meets the ambient path at `params.phi`, the fourth contact curve at `params.theta` meets
the ambient path at `tau`, and the two outer ends touch the wall. -/
theorem gerver_niche_piece_endpoints :
    paperGerverContacts (gerverStageTimes 3) 1 = paperGerverPath (gerverStageTimes 1) ∧
    paperGerverContacts (gerverStageTimes 2) 3 = paperGerverPath (gerverStageTimes 4) ∧
    paperGerverContacts (Real.pi / 2) 1 1 = 0 ∧ paperGerverContacts 0 3 1 = 0 := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  obtain ⟨hB, hD, hBT, hD0⟩ := GerverSofa.PartC.Stage4.niche_piece_endpoints
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hchain : 0 < params.theta ∧ params.theta < eta ∧ eta < tau ∧ tau < Real.pi / 2 :=
    ⟨GerverSofa.PartC.Stage4.theta_pos, GerverSofa.PartC.Stage4.theta_lt_eta,
      GerverSofa.PartC.Stage4.eta_lt_tau, hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T⟩
  obtain ⟨hθ0, hθη, hητ, hτT⟩ := hchain
  have hth : params.theta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hθ0.le, by linarith⟩
  have heta : eta ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hTm : (Real.pi / 2) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hpi.le, le_rfl⟩
  have h0m : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨le_rfl, hpi.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gerverStageTimes_three, gerverStageTimes_one,
      paperGerverContacts_one_eq_toPlane heta, paperGerverPath_eq_toPlane]
    exact congrArg toPlane hB
  · rw [gerverStageTimes_two, gerverStageTimes_four,
      paperGerverContacts_three_eq_toPlane hth, paperGerverPath_eq_toPlane]
    exact congrArg toPlane hD
  · rw [paperGerverContacts_one_eq_toPlane hTm]
    exact hBT
  · rw [paperGerverContacts_three_eq_toPlane h0m]
    exact hD0

/-! ## The reverse-time reparametrization, and continuity of the roof -/

/-- The reverse-time reparametrization is affine, hence continuous. -/
theorem continuous_gerverRoofReverseTime : Continuous gerverRoofReverseTime := by
  unfold gerverRoofReverseTime
  fun_prop

/-- The reverse-time map sends the start of the middle roof stage to the late path time. -/
theorem gerverRoofReverseTime_two :
    gerverRoofReverseTime (gerverStageTimes 2) = gerverStageTimes 4 := by
  rw [gerverRoofReverseTime, sub_self, mul_zero, sub_zero]

/-- The reverse-time map sends the end of the middle roof stage to the early path time. -/
theorem gerverRoofReverseTime_three :
    gerverRoofReverseTime (gerverStageTimes 3) = gerverStageTimes 1 := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  rw [gerverRoofReverseTime, div_mul_cancel₀ _ (sub_ne_zero.mpr h23.ne')]
  ring

/-- The reverse-time map carries the middle roof interval into the central path interval. -/
theorem gerverRoofReverseTime_mem_Icc {s : ℝ} (h1 : gerverStageTimes 2 ≤ s)
    (h2 : s ≤ gerverStageTimes 3) :
    gerverRoofReverseTime s ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4) := by
  have h12 : gerverStageTimes 1 < gerverStageTimes 2 := gerverStageTimes_strictMono (by decide)
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have h34 : gerverStageTimes 3 < gerverStageTimes 4 := gerverStageTimes_strictMono (by decide)
  have hd : (0 : ℝ) < gerverStageTimes 3 - gerverStageTimes 2 := by linarith
  have hL : 0 < (gerverStageTimes 4 - gerverStageTimes 1) /
      (gerverStageTimes 3 - gerverStageTimes 2) := div_pos (by linarith) hd
  have hmul := mul_le_mul_of_nonneg_left (show s - gerverStageTimes 2 ≤
    gerverStageTimes 3 - gerverStageTimes 2 by linarith) hL.le
  rw [div_mul_cancel₀ _ hd.ne'] at hmul
  have hnn : 0 ≤ (gerverStageTimes 4 - gerverStageTimes 1) /
      (gerverStageTimes 3 - gerverStageTimes 2) * (s - gerverStageTimes 2) :=
    mul_nonneg hL.le (by linarith)
  rw [gerverRoofReverseTime]
  constructor <;> linarith

/-! ## The three graph pieces of the roof -/

/-- Up to the second stage time the niche roof is the fourth contact curve. -/
theorem gerverNicheRoof_of_le_two {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : s ≤ gerverStageTimes 2) : gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 3 :=
  ite_eq_left h

/-- On the middle stage the niche roof is the reverse-time ambient path.  The identification
extends to the left endpoint of the stage by the piece-endpoint gluing. -/
theorem gerverNicheRoof_mid {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h1 : gerverStageTimes 2 ≤ s) (h2 : s ≤ gerverStageTimes 3) :
    gerverNicheRoof ⟨s, hs⟩ = paperGerverPath (gerverRoofReverseTime s) := by
  rcases eq_or_lt_of_le h1 with heq | hlt
  · rw [gerverNicheRoof_of_le_two hs heq.ge, ← heq, gerverRoofReverseTime_two]
    exact gerver_niche_piece_endpoints.2.1
  · rw [gerverNicheRoof, ite_eq_right (not_le.mpr hlt), ite_eq_left h2]

/-- From the third stage time on the niche roof is the second contact curve.  The
identification extends to the left endpoint of the stage by the piece-endpoint gluing. -/
theorem gerverNicheRoof_of_ge_three {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) (Real.pi / 2))
    (h : gerverStageTimes 3 ≤ s) : gerverNicheRoof ⟨s, hs⟩ = paperGerverContacts s 1 := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  rcases eq_or_lt_of_le h with heq | hlt
  · rw [gerverNicheRoof_mid hs (by linarith) heq.ge, ← heq, gerverRoofReverseTime_three]
    exact gerver_niche_piece_endpoints.1.symm
  · rw [gerverNicheRoof, ite_eq_right (not_le.mpr (by linarith)),
      ite_eq_right (not_le.mpr hlt)]

/-- On the rotation interval the real-parameter roof curve is the niche roof. -/
theorem gerverRoofCurve_eq (s : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    gerverRoofCurve s.val = gerverNicheRoof s := rfl

/-- The roof curve is continuous: its three graph pieces join up at the two cut times, by the
two endpoint identities of `gerver_niche_piece_endpoints`. -/
theorem continuous_gerverRoofCurve : Continuous gerverRoofCurve := by
  have h23 : gerverStageTimes 2 < gerverStageTimes 3 := gerverStageTimes_strictMono (by decide)
  have hinner : Continuous fun s : ℝ ↦
      if s ≤ gerverStageTimes 3 then paperGerverPath (gerverRoofReverseTime s)
      else paperGerverContacts s 1 := by
    refine continuous_if_le continuous_id continuous_const
      ((contDiff_paperGerverPath.continuous.comp continuous_gerverRoofReverseTime).continuousOn)
      ((continuous_paperGerverContact 1).continuousOn) ?_
    intro s hs
    rw [hs, gerverRoofReverseTime_three]
    exact gerver_niche_piece_endpoints.1.symm
  refine continuous_if_le continuous_id continuous_const
    ((continuous_paperGerverContact 3).continuousOn) hinner.continuousOn ?_
  intro s hs
  rw [ite_eq_left (by rw [hs]; exact h23.le), hs, gerverRoofReverseTime_two]
  exact gerver_niche_piece_endpoints.2.1

/-- The niche roof is continuous. -/
theorem continuous_gerverNicheRoof : Continuous gerverNicheRoof :=
  continuous_gerverRoofCurve.comp continuous_subtype_val

/-- The first coordinate of the niche roof is strictly increasing, so the roof really is a
graph over the horizontal axis. -/
theorem gerver_niche_roof_strictMono :
    StrictMono (fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ gerverNicheRoof s 0) := by
  intro a b hab
  have h := GerverSofa.PartC.Stage4.nicheTopArc_fst_strictMono a.2 b.2 hab
  simp only [gerverNicheRoof_eq_toPlane]
  exact h

/-- The niche roof has positive height strictly inside the rotation interval. -/
theorem gerver_niche_roof_positive
    (s : Set.Icc (0 : ℝ) (Real.pi / 2)) (hs : 0 < s.val ∧ s.val < Real.pi / 2) :
    0 < gerverNicheRoof s 1 := by
  rw [gerverNicheRoof_eq_toPlane]
  exact GerverSofa.PartC.Stage4.nicheTopArc_y_pos ⟨hs.1, hs.2⟩

/-- Each of the three graph pieces of the niche roof stays inside the paper outer cap. -/
theorem gerver_niche_roof_membership :
    (∀ t ∈ Set.Icc (gerverStageTimes 0) (gerverStageTimes 2),
      paperGerverContacts t 3 ∈ gerverOuterCap) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 1) (gerverStageTimes 4),
      paperGerverPath t ∈ gerverOuterCap) ∧
    (∀ t ∈ Set.Icc (gerverStageTimes 3) (gerverStageTimes 5),
      paperGerverContacts t 1 ∈ gerverOuterCap) := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  obtain ⟨hD, hx, hB⟩ := GerverSofa.PartC.Stage4.certified_roof_mem_K
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hθ0 : 0 < params.theta := GerverSofa.PartC.Stage4.theta_pos
  have hθη : params.theta < eta := GerverSofa.PartC.Stage4.theta_lt_eta
  have hητ : eta < tau := GerverSofa.PartC.Stage4.eta_lt_tau
  have hτT : tau < Real.pi / 2 := hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [gerverStageTimes_zero, gerverStageTimes_two] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2]⟩
    rw [paperGerverContacts_three_eq_toPlane htI]
    exact toPlane_mem_gerverOuterCap (hD t ht)
  · intro t ht
    rw [gerverStageTimes_one, gerverStageTimes_four] at ht
    exact toPlane_mem_gerverOuterCap (hx t ht)
  · intro t ht
    rw [gerverStageTimes_three, gerverStageTimes_five] at ht
    have htI : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [ht.1], hTeq ▸ ht.2⟩
    rw [paperGerverContacts_one_eq_toPlane htI]
    exact toPlane_mem_gerverOuterCap (hB t ht)

/-- The strict region between the wall and the graph of `f` over the parameter set `I`. -/
def strictVerticalFill (f : ℝ → Point) (I : Set ℝ) : Set Point :=
  {q | ∃ t ∈ I, q 0 = f t 0 ∧ 0 ≤ q 1 ∧ q 1 < f t 1}

section Fills

open GerverSofa.PartF.Coordinates
open GerverSofa.PartC (params eta tau)

/-- A strict vertical fill is the coordinate preimage of the certified vertical fill under
the plane dictionary. -/
private theorem strictVerticalFill_eq_preimage {F : ℝ → Point} {g : ℝ → GerverSofa.Point}
    {I : Set ℝ} (h : ∀ t ∈ I, F t = toPlane (g t)) :
    strictVerticalFill F I = fromPlane ⁻¹' GerverSofa.PartC.Stage4.verticalFill g I := by
  ext q
  constructor
  · rintro ⟨t, ht, h0, h1, h2⟩
    rw [h t ht] at h0 h2
    exact ⟨t, ht, h0, h1, h2⟩
  · rintro ⟨t, ht, h0, h1, h2⟩
    refine ⟨t, ht, ?_, h1, ?_⟩
    · rw [h t ht]; exact h0
    · rw [h t ht]; exact h2

end Fills

/-- The paper literal niche is exactly the union of the three strict vertical fills under
the three graph pieces of the niche roof. -/
theorem gerver_niche_vertical_fills :
    gerverLiteralNiche =
      strictVerticalFill (fun t ↦ paperGerverContacts t 3)
        (Set.Icc (gerverStageTimes 0) (gerverStageTimes 2)) ∪
      strictVerticalFill paperGerverPath
        (Set.Icc (gerverStageTimes 1) (gerverStageTimes 4)) ∪
      strictVerticalFill (fun t ↦ paperGerverContacts t 1)
        (Set.Icc (gerverStageTimes 3) (gerverStageTimes 5)) := by
  open GerverSofa.PartF.Coordinates GerverSofa.PartC GerverSofa.PartC.Stage4 in
  have hTeq : GerverSofa.PartC.T = Real.pi / 2 := rfl
  have hθ0 : 0 < params.theta := GerverSofa.PartC.Stage4.theta_pos
  have hθη : params.theta < eta := GerverSofa.PartC.Stage4.theta_lt_eta
  have hητ : eta < tau := GerverSofa.PartC.Stage4.eta_lt_tau
  have hτT : tau < Real.pi / 2 := hTeq ▸ GerverSofa.PartC.Stage4.tau_lt_T
  have hDeq : ∀ t ∈ Set.Icc (0 : ℝ) params.theta,
      (fun t ↦ paperGerverContacts t 3) t = toPlane (GerverSofa.PartC.D t) := fun t ht =>
    paperGerverContacts_three_eq_toPlane ⟨ht.1, by linarith [ht.2]⟩
  have hpeq : ∀ t ∈ Set.Icc params.phi tau,
      paperGerverPath t = toPlane (GerverSofa.Romik.path params t) := fun _ _ => rfl
  have hBeq : ∀ t ∈ Set.Icc eta GerverSofa.PartC.T,
      (fun t ↦ paperGerverContacts t 1) t = toPlane (GerverSofa.PartC.B t) := fun t ht =>
    paperGerverContacts_one_eq_toPlane ⟨by linarith [ht.1], hTeq ▸ ht.2⟩
  rw [gerverStageTimes_zero, gerverStageTimes_two, gerverStageTimes_one, gerverStageTimes_four,
    gerverStageTimes_three, gerverStageTimes_five, strictVerticalFill_eq_preimage hDeq,
    strictVerticalFill_eq_preimage hpeq, strictVerticalFill_eq_preimage hBeq,
    ← Set.preimage_union, ← Set.preimage_union]
  exact Set.ext fun q =>
    (mem_gerverLiteralNiche_iff q).trans
      (by rw [GerverSofa.PartC.Stage4.niche_eq_certifiedNicheRegion]; rfl)

end MovingSofa
