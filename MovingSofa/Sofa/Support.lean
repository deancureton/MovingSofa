import MovingSofa.Motion.StandardPosition
import MovingSofa.Geometry.SupportingHallway
import MovingSofa.Geometry.HallwayPartsProperties

noncomputable section

namespace MovingSofa

theorem standardPosition_subset_monotonization (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) : s ⊆ monotonization s ω := by
  have hω : ω ∈ Set.Ioc 0 (Real.pi / 2) := ⟨hs.2.2.1, hs.2.2.2.1⟩
  have hcommon := movingSofa_commonSubset s ω hs.2.1 hω
  have hs_ne : s.Nonempty := by
    obtain ⟨_, hm, _⟩ := hs.2.1
    exact hm.1.nonempty
  have hshape : s ⊆ (stripParallelogram ω).1 := by
    have htranslated :=
      (exists_standardPosition_translation s ω hs.2.1 hω).2.2.2 (0 : Point)
    have hstandard :
        IsStandardPosition ((fun p : Point ↦ p + (0 : Point)) '' s) ω := by
      simpa using hs
    simpa using htranslated hstandard
  rw [monotonization]
  intro p hp
  refine ⟨hshape hp, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  exact subset_supportingHallway s (t : Real.Angle) hs_ne hcommon.1
    (hcommon.2.2.2.1 t ht) hp

theorem standardPosition_subset_cap (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    s ⊆ monotonization s ω ∧ monotonization s ω ⊆ capOfSofa s ω := by
  refine ⟨standardPosition_subset_monotonization s ω hs, ?_⟩
  rw [monotonization, capOfSofa]
  rintro p ⟨hpP, hpL⟩
  refine ⟨hpP, Set.mem_iInter.2 fun t ↦ Set.mem_iInter.2 fun ht ↦ ?_⟩
  apply supportingHallway_subset_outerQuadrant s (t : Real.Angle)
  exact Set.mem_iInter.1 (Set.mem_iInter.1 hpL t) ht

private theorem inner_le_supportValue_of_mem_capOfSofa {s : Set Point} {ω t : ℝ}
    (ht : t ∈ capUpperAngles ω) {p : Point} (hp : p ∈ capOfSofa s ω) :
    inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue s (t : Real.Angle) := by
  rcases ht with ht | ht
  · have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 t) ht
    obtain ⟨q, hq, rfl⟩ := hq
    rw [inner_supportingPlacement_normalVector]
    change q 0 ≤ 1 ∧ q 1 ≤ 1 at hq
    linarith [hq.1]
  · have ht' : t - Real.pi / 2 ∈ Set.Icc 0 ω := by
      constructor <;> linarith [ht.1, ht.2]
    have hq := Set.mem_iInter.1 (Set.mem_iInter.1 hp.2 (t - Real.pi / 2)) ht'
    obtain ⟨q, hq, rfl⟩ := hq
    have ha : (t : Real.Angle) = ((t - Real.pi / 2 : ℝ) : Real.Angle) +
        ((Real.pi / 2 : ℝ) : Real.Angle) := by
      rw [← Real.Angle.coe_add, sub_add_cancel]
    rw [ha, normalVector_add_pi_div_two, inner_supportingPlacement_tangentVector]
    change q 0 ≤ 1 ∧ q 1 ≤ 1 at hq
    linarith [hq.2]

theorem standardPosition_support_eq (s : Set Point) (ω : ℝ)
    (hs : IsStandardPosition s ω) :
    (∀ t ∈ capUpperAngles ω,
      supportValue (monotonization s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) ∧
      supportValue (capOfSofa s ω) (t : Real.Angle) = supportValue s (t : Real.Angle)) ∧
    (∀ t ∈ Set.Icc 0 ω,
      supportingHallway (monotonization s ω) (t : Real.Angle) =
        supportingHallway s (t : Real.Angle) ∧
      supportingHallway (capOfSofa s ω) (t : Real.Angle) =
        supportingHallway s (t : Real.Angle)) := by
  have hs_ne : s.Nonempty := by
    by_contra h
    have he : s = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hnorm := hs.2.2.2.2.1
    simp [he, supportValue] at hnorm
  obtain ⟨hsm, hmc⟩ := standardPosition_subset_cap s ω hs
  have hsupport (t : ℝ) (ht : t ∈ capUpperAngles ω) :
      supportValue (monotonization s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) ∧
      supportValue (capOfSofa s ω) (t : Real.Angle) = supportValue s (t : Real.Angle) := by
    have hc (p : Point) (hp : p ∈ capOfSofa s ω) :=
      inner_le_supportValue_of_mem_capOfSofa ht hp
    exact ⟨supportValue_eq_of_subset_of_inner_le hs_ne hsm _ (fun p hp ↦ hc p (hmc hp)),
      supportValue_eq_of_subset_of_inner_le hs_ne (hsm.trans hmc) _ hc⟩
  refine ⟨hsupport, ?_⟩
  intro t ht
  have ht' : t + Real.pi / 2 ∈ capUpperAngles ω :=
    Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h₀ := hsupport t (Or.inl ht)
  have h₁ := hsupport (t + Real.pi / 2) ht'
  simp only [Real.Angle.coe_add] at h₁
  constructor
  · unfold supportingHallway
    congr 1
    funext p
    simp only [supportingPlacement, h₀.1, h₁.1]
  · unfold supportingHallway
    congr 1
    funext p
    simp only [supportingPlacement, h₀.2, h₁.2]

end MovingSofa
