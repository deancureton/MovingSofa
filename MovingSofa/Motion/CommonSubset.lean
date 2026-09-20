import MovingSofa.Motion.Basic
import MovingSofa.Geometry.HallwayParts
import Mathlib.Topology.Order.IntermediateValue

noncomputable section

namespace MovingSofa

theorem HasRotationAngle.exists_translated_rotated_hallway {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) {t : ℝ} (ht : t ∈ Set.Icc 0 ω) :
    ∃ v : Point, s ⊆ (fun p ↦ rotationMap (t : Real.Angle) p + v) '' hallway := by
  obtain ⟨m, hm, α, hα, hα0, hα1, hmotion⟩ := hs
  obtain ⟨_, _, _, _, _, _, hhallway, _⟩ := hm
  obtain ⟨τ, hτ⟩ := mem_range_of_exists_le_of_exists_ge (c := -t) hα
    ⟨1, by rw [hα1]; linarith [ht.2]⟩ ⟨0, by rw [hα0]; linarith [ht.1]⟩
  refine ⟨-rotationMap (t : Real.Angle) (m τ 0), ?_⟩
  intro p hp
  refine ⟨m τ p, hhallway τ ⟨p, hp, rfl⟩, ?_⟩
  rw [hmotion τ p, hτ]
  simp only [rotationMap, Real.Angle.coe_neg, map_add,
    ← EuclideanGeometry.o.rotation_symm, LinearIsometryEquiv.apply_symm_apply,
    add_neg_cancel_right]

theorem HasRotationAngle.exists_translated_horizontal_strip {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    ∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).1 := by
  obtain ⟨m, hm, _⟩ := hs
  obtain ⟨_, _, _, ⟨v, hv⟩, _, hstart, _, _⟩ := hm
  refine ⟨-v, ?_⟩
  intro p hp
  have hmem := hstart ⟨p, hp, rfl⟩
  obtain ⟨x, y, hxy, heq⟩ := hmem
  refine ⟨p + v, ?_, by simp⟩
  change 0 ≤ (p + v) 1 ∧ (p + v) 1 ≤ 1
  rw [← hv p, ← heq]
  exact ⟨hxy.2.1, hxy.2.2⟩

theorem HasRotationAngle.exists_translated_vertical_strip {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    ∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).2.2 := by
  obtain ⟨m, hm, α, _, _, hα1, hmotion⟩ := hs
  obtain ⟨_, _, _, _, _, _, _, hend⟩ := hm
  refine ⟨-rotationMap (ω : Real.Angle) (m 1 0), ?_⟩
  intro p hp
  have hmem := hend ⟨p, hp, rfl⟩
  obtain ⟨x, y, hxy, heq⟩ := hmem
  refine ⟨rotationMap (ω : Real.Angle) (m 1 p), ?_, ?_⟩
  · refine ⟨m 1 p, ?_, rfl⟩
    change 0 ≤ (m 1 p) 0 ∧ (m 1 p) 0 ≤ 1
    rw [← heq]
    exact ⟨hxy.1, hxy.2.1⟩
  · rw [hmotion 1 p, hα1]
    simp only [rotationMap, Real.Angle.coe_neg, map_add,
      ← EuclideanGeometry.o.rotation_symm, LinearIsometryEquiv.apply_symm_apply,
      add_neg_cancel_right]

private theorem isBounded_of_oblique_bounds (s : Set Point) (a c d A B : ℝ)
    (hc : 0 < c) (hd : 0 < d)
    (hy : ∀ p ∈ s, a ≤ p 1 ∧ p 1 ≤ a + 1)
    (hx : ∀ p ∈ s, c * p 0 + d * p 1 ≤ A ∧ -d * p 0 + c * p 1 ≤ B) :
    Bornology.IsBounded s := by
  let l := (c * a - B) / d
  let u := (A - d * a) / c
  let M := |l| + |u|
  let N := |a| + |a + 1|
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + N, ?_⟩
  intro p hp
  obtain ⟨hy0, hy1⟩ := hy p hp
  obtain ⟨hx0, hx1⟩ := hx p hp
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hu : p 0 ≤ u := by
    apply (le_div_iff₀ hc).2
    nlinarith
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hN : 0 ≤ N := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hxabs : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self u, abs_nonneg l, abs_nonneg u]
  have hyabs : |p 1| ≤ N := by
    apply abs_le.mpr
    dsimp [N]
    constructor <;> linarith [neg_abs_le a, le_abs_self (a + 1),
      abs_nonneg a, abs_nonneg (a + 1)]
  have hx2 := pow_le_pow_left₀ (abs_nonneg (p 0)) hxabs 2
  have hy2 := pow_le_pow_left₀ (abs_nonneg (p 1)) hyabs 2
  have hnorm := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hnorm hx2 hy2
  nlinarith [mul_nonneg hM hN, norm_nonneg p]

theorem HasRotationAngle.isCompact {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) : IsCompact s := by
  obtain ⟨v, hv⟩ := hs.exists_translated_horizontal_strip
  have ht : ω / 2 ∈ Set.Icc 0 ω := ⟨by linarith [hω.1], by linarith [hω.1]⟩
  obtain ⟨w, hw⟩ := hs.exists_translated_rotated_hallway ht
  have hc : 0 < Real.cos (ω / 2) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hω.1, Real.pi_pos], by linarith [hω.2, Real.pi_pos]⟩
  have hd : 0 < Real.sin (ω / 2) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hω.1]) (by linarith [hω.2, Real.pi_pos])
  have hb : Bornology.IsBounded s := isBounded_of_oblique_bounds s (v 1)
      (Real.cos (ω / 2)) (Real.sin (ω / 2))
      (1 + inner ℝ w (normalVector ((ω / 2 : ℝ) : Real.Angle)))
      (1 + inner ℝ w (tangentVector ((ω / 2 : ℝ) : Real.Angle))) hc hd
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := hv hp
        change 0 ≤ q 1 ∧ q 1 ≤ 1 at hq
        change v 1 ≤ q 1 + v 1 ∧ q 1 + v 1 ≤ v 1 + 1
        constructor <;> linarith [hq.1, hq.2])
      (by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := hw hp
        have hq01 : q 0 ≤ 1 ∧ q 1 ≤ 1 := by
          rcases hq with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
          · exact ⟨h.1, h.2.2⟩
          · exact ⟨h.2.1, h.2.2⟩
        obtain ⟨hq0, hq1⟩ := hq01
        have hn : inner ℝ (rotationMap ((ω / 2 : ℝ) : Real.Angle) q + w)
            (normalVector ((ω / 2 : ℝ) : Real.Angle)) ≤
              1 + inner ℝ w (normalVector ((ω / 2 : ℝ) : Real.Angle)) := by
          rw [inner_add_left, inner_rotationMap_normalVector]
          linarith
        have ht : inner ℝ (rotationMap ((ω / 2 : ℝ) : Real.Angle) q + w)
            (tangentVector ((ω / 2 : ℝ) : Real.Angle)) ≤
              1 + inner ℝ w (tangentVector ((ω / 2 : ℝ) : Real.Angle)) := by
          rw [inner_add_left, inner_rotationMap_tangentVector]
          linarith
        simpa [normalVector, tangentVector, frame, PiLp.inner_apply,
          Fin.sum_univ_two, Real.inner_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
          mul_comm] using And.intro hn ht)
  obtain ⟨m, hm, _⟩ := hs
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hm.2.1, hb⟩

private theorem width_le_of_forall_mem_Icc {s : Set Point} (hne : s.Nonempty)
    (f : Point → ℝ) (a b : ℝ) (h : ∀ p ∈ s, a ≤ f p ∧ f p ≤ b) :
    sSup (f '' s) - sInf (f '' s) ≤ b - a := by
  have hu : sSup (f '' s) ≤ b := csSup_le (hne.image f) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (h p hp).2)
  have hl : a ≤ sInf (f '' s) := le_csInf (hne.image f) (by
    rintro _ ⟨p, hp, rfl⟩
    exact (h p hp).1)
  linarith

theorem HasRotationAngle.horizontal_width_le {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    sSup ((fun p : Point ↦ p 1) '' s) - sInf ((fun p : Point ↦ p 1) '' s) ≤ 1 := by
  obtain ⟨v, hv⟩ := hs.exists_translated_horizontal_strip
  obtain ⟨m, hm, _⟩ := hs
  have hb := width_le_of_forall_mem_Icc hm.1.nonempty (fun p ↦ p 1) (v 1) (v 1 + 1)
    (by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := hv hp
      change 0 ≤ q 1 ∧ q 1 ≤ 1 at hq
      change v 1 ≤ q 1 + v 1 ∧ q 1 + v 1 ≤ v 1 + 1
      constructor <;> linarith [hq.1, hq.2])
  simpa using hb

theorem HasRotationAngle.normal_width_le {s : Set Point} {ω : ℝ}
    (hs : HasRotationAngle s ω) :
    sSup ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) -
      sInf ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) ≤ 1 := by
  obtain ⟨v, hv⟩ := hs.exists_translated_vertical_strip
  obtain ⟨m, hm, _⟩ := hs
  have hb := width_le_of_forall_mem_Icc hm.1.nonempty
    (fun p ↦ inner ℝ p (normalVector (ω : Real.Angle)))
    (inner ℝ v (normalVector (ω : Real.Angle)))
    (inner ℝ v (normalVector (ω : Real.Angle)) + 1) (by
      intro p hp
      obtain ⟨q, ⟨r, hr, rfl⟩, rfl⟩ := hv hp
      change 0 ≤ r 0 ∧ r 0 ≤ 1 at hr
      rw [inner_add_left, inner_rotationMap_normalVector]
      constructor <;> linarith [hr.1, hr.2])
  simpa using hb

private theorem subset_Icc_of_width_le_of_csSup_eq {s : Set ℝ}
    (hbelow : BddBelow s) (habove : BddAbove s)
    (hwidth : sSup s - sInf s ≤ 1) (hsup : sSup s = 1) : s ⊆ Set.Icc 0 1 := by
  intro x hx
  have hl := csInf_le hbelow hx
  have hu := le_csSup habove hx
  rw [hsup] at hwidth hu
  exact ⟨by linarith, hu⟩

theorem IsStandardPosition.subset_strips {s : Set Point} {ω : ℝ}
    (hs : IsStandardPosition s ω) : s ⊆ (strips ω).1 ∩ (strips ω).2.2 := by
  obtain ⟨hcompact, hmotion, _, _, hnormal, hvertical⟩ := hs
  have hcy : IsCompact ((fun p : Point ↦ p 1) '' s) := hcompact.image (by fun_prop)
  have hcn : IsCompact ((fun p : Point ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) :=
    hcompact.image (by fun_prop)
  have hsupy : sSup ((fun p : Point ↦ p 1) '' s) = 1 := by
    simpa [supportValue, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] using hvertical
  have hy := subset_Icc_of_width_le_of_csSup_eq hcy.bddBelow hcy.bddAbove
    hmotion.horizontal_width_le hsupy
  have hn := subset_Icc_of_width_le_of_csSup_eq hcn.bddBelow hcn.bddAbove
    hmotion.normal_width_le hnormal
  intro p hp
  refine ⟨hy ⟨p, hp, rfl⟩, ?_⟩
  obtain ⟨q, rfl⟩ := (EuclideanGeometry.o.rotation (ω : Real.Angle)).surjective p
  refine ⟨q, ?_, rfl⟩
  have hb := hn ⟨rotationMap (ω : Real.Angle) q, hp, rfl⟩
  change 0 ≤ q 0 ∧ q 0 ≤ 1
  simpa only [Set.mem_Icc, inner_rotationMap_normalVector] using hb

theorem movingSofa_commonSubset (s : Set Point) (ω : ℝ)
    (hs : HasRotationAngle s ω) (hω : ω ∈ Set.Ioc 0 (Real.pi / 2)) :
    IsCompact s ∧
    (∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).1) ∧
    (∃ v : Point, s ⊆ (fun p ↦ p + v) '' (strips ω).2.2) ∧
    (∀ t ∈ Set.Icc 0 ω, ∃ v : Point,
      s ⊆ (fun p ↦ rotationMap (t : Real.Angle) p + v) '' hallway) ∧
    (sSup ((fun p : Point ↦ p 1) '' s) - sInf ((fun p : Point ↦ p 1) '' s) ≤ 1) ∧
    (sSup ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) -
      sInf ((fun p ↦ inner ℝ p (normalVector (ω : Real.Angle))) '' s) ≤ 1) ∧
    (IsStandardPosition s ω → s ⊆ (strips ω).1 ∩ (strips ω).2.2) := by
  exact ⟨hs.isCompact hω, hs.exists_translated_horizontal_strip,
    hs.exists_translated_vertical_strip, fun _ ht ↦ hs.exists_translated_rotated_hallway ht,
    hs.horizontal_width_le, hs.normal_width_le, fun hstd ↦ hstd.subset_strips⟩

end MovingSofa
