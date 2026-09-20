import MovingSofa.Cap.ContactIdentities
import MovingSofa.ForMathlib.MeasureTheory.Measure.WithDensity
import MovingSofa.Cap.Balanced
import MovingSofa.Cap.Tail.Space

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MovingSofa

private theorem coe_injOn_halfTurn :
    Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Icc 0 Real.pi) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro x hx y hy heq
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show x ∈ Ico 0 (0 + 2 * Real.pi) from ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
    (show y ∈ Ico 0 (0 + 2 * Real.pi) from ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩)).mp heq

/-- A right-angle cap whose surface area measure has angular densities on the two upper quarter
circles has no atom at a normal direction of the right upper quarter. -/
theorem HasCapDensities.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico
    {K : RightAngleCapSpace} {r s : ℝ → ℝ≥0} (hK : HasCapDensities K r s) {t : ℝ}
    (ht : t ∈ Ico 0 (Real.pi / 2)) :
    surfaceAreaMeasure K.1 {(t : Real.Angle)} = 0 := by
  have he := congrArg (fun μ : Measure Real.Angle ↦ μ {(t : Real.Angle)}) hK.2.2.1
  have hm : (t : Real.Angle) ∈
      (fun x : ℝ ↦ (x : Real.Angle)) '' Ico 0 (Real.pi / 2) := ⟨t, ht, rfl⟩
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] at he
  rw [he]
  apply Measure.map_restrict_withDensity_singleton volume _ Real.Angle.continuous_coe.measurable
    _ (coe_injOn_halfTurn.mono ?_) _ ht
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩

/-- A right-angle cap whose surface area measure has angular densities on the two upper quarter
circles has no atom at a normal direction of the left upper quarter. -/
theorem HasCapDensities.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc
    {K : RightAngleCapSpace} {r s : ℝ → ℝ≥0} (hK : HasCapDensities K r s) {t : ℝ}
    (ht : t ∈ Ioc 0 (Real.pi / 2)) :
    surfaceAreaMeasure K.1 {((t + Real.pi / 2 : ℝ) : Real.Angle)} = 0 := by
  have he := congrArg (fun μ : Measure Real.Angle ↦
    μ {((t + Real.pi / 2 : ℝ) : Real.Angle)}) hK.2.2.2
  have hm : ((t + Real.pi / 2 : ℝ) : Real.Angle) ∈
      (fun x : ℝ ↦ (x : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi :=
    ⟨t + Real.pi / 2, ⟨by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
  rw [Measure.restrict_apply (measurableSet_singleton _),
    inter_eq_left.mpr (singleton_subset_iff.mpr hm)] at he
  rw [he]
  apply Measure.map_restrict_withDensity_singleton volume _
    (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
    _ ?_ _ ht
  intro x hx y hy hxy
  have heq := coe_injOn_halfTurn
    (show x + Real.pi / 2 ∈ Icc 0 Real.pi from
      ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2]⟩)
    (show y + Real.pi / 2 ∈ Icc 0 Real.pi from
      ⟨by linarith [hy.1, Real.pi_pos], by linarith [hy.2]⟩) hxy
  linarith

theorem capDensities_contact_eq (K : RightAngleCapSpace)
    (hK : ∃ r s, HasCapDensities K r s) :
    (∀ t ∈ Set.Ico (0 : ℝ) (Real.pi / 2),
      (capVertices K t).1.1 = (capVertices K t).1.2 ∧
      (tangentArmLengths K t).1.1 = (tangentArmLengths K t).1.2) ∧
    (∀ t ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
      (capVertices K t).2.1 = (capVertices K t).2.2 ∧
      (tangentArmLengths K t).2.1 = (tangentArmLengths K t).2.2) := by
  obtain ⟨r, s, hK⟩ := hK
  constructor
  · intro t ht
    have h := (surfaceAreaMeasure_atom_length K.1 (t : Real.Angle)).2.2
    rw [hK.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ico ht] at h
    simp only [ENNReal.toReal_zero, zero_smul, add_zero] at h
    have h' : (capVertices K t).1.1 = (capVertices K t).1.2 := h
    exact ⟨h', by simp only [tangentArmLengths, h']⟩
  · intro t ht
    have h := (surfaceAreaMeasure_atom_length K.1
      ((t + Real.pi / 2 : ℝ) : Real.Angle)).2.2
    rw [hK.surfaceAreaMeasure_singleton_eq_zero_of_mem_Ioc ht] at h
    simp only [ENNReal.toReal_zero, zero_smul, add_zero] at h
    have h' : (capVertices K t).2.1 = (capVertices K t).2.2 := h
    exact ⟨h', by simp only [tangentArmLengths, h']⟩

/-- A right-angle cap carrying angular densities has singleton extreme faces at every upper normal
direction except possibly the vertical one: the densities exclude atoms of the surface area measure
on the two open quarter circles, so the corresponding faces have zero side length. -/
theorem capDensities_edgeVertices_eq (K : RightAngleCapSpace)
    (hK : ∃ r s, HasCapDensities K r s) {t : ℝ} (ht : t ∈ Icc 0 Real.pi)
    (htop : t ≠ Real.pi / 2) :
    (edgeVertices K.val (t : Real.Angle)).1 = (edgeVertices K.val (t : Real.Angle)).2 := by
  rcases lt_or_gt_of_ne htop with h | h
  · exact ((capDensities_contact_eq K hK).1 t ⟨ht.1, h⟩).1
  · have hmem : t - Real.pi / 2 ∈ Ioc (0 : ℝ) (Real.pi / 2) := ⟨by linarith, by linarith [ht.2]⟩
    have h' : (edgeVertices K.val ((t - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).1 =
        (edgeVertices K.val ((t - Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle)).2 :=
      ((capDensities_contact_eq K hK).2 (t - Real.pi / 2) hmem).1
    rwa [show t - Real.pi / 2 + Real.pi / 2 = t from by ring] at h'

def nondegenerateCapData (K : RightAngleCapSpace)
    (_hK : ∃ r s, HasCapDensities K r s) :
    ((Set.Icc (0 : ℝ) (Real.pi / 2) → Point) ×
      (Set.Icc (0 : ℝ) (Real.pi / 2) → Point)) ×
    ((Set.Icc (0 : ℝ) (Real.pi / 2) → ℝ) ×
      (Set.Icc (0 : ℝ) (Real.pi / 2) → ℝ)) := by
  classical
  exact ((fun t ↦ if (t : ℝ) = Real.pi / 2 then (capVertices K t).1.2
      else (capVertices K t).1.1,
    fun t ↦ (capVertices K t).2.1),
    (fun t ↦ if (t : ℝ) = Real.pi / 2 then (tangentArmLengths K t).1.2
      else (tangentArmLengths K t).1.1,
    fun t ↦ (tangentArmLengths K t).2.1))

end MovingSofa
