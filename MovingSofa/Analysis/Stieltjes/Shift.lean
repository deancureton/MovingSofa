import MovingSofa.Analysis.Stieltjes.Transport

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- Translate a continuous interval-BV representative and its Stieltjes measure. -/
theorem exists_intervalBV_shift_add {a b c : ℝ} (hab : a ≤ b)
    (f : RightContinuousIntervalBV (a + c) (b + c)) (hfc : Continuous f.toFun) :
    ∃ g : RightContinuousIntervalBV a b,
      (∀ t, g.toFun t = f.toFun
        ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) ∧
      ∀ E : Set (Icc a b), MeasurableSet E →
        intervalStieltjesMeasure g E = intervalStieltjesMeasure f
          ((fun t : Icc a b ↦
            ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) '' E) := by
  let φ : Icc a b → Icc (a + c) (b + c) := fun t ↦
    ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩
  let ψ : Icc (a + c) (b + c) → Icc a b := fun t ↦
    ⟨(t : ℝ) - c, by constructor <;> linarith [t.property.1, t.property.2]⟩
  have hφc : Continuous φ := (continuous_subtype_val.add_const c).subtype_mk _
  have hψc : Continuous ψ := (continuous_subtype_val.sub continuous_const).subtype_mk _
  have hφm : Monotone φ := fun x y hxy ↦ by
    change (x : ℝ) + c ≤ (y : ℝ) + c
    linarith [show (x : ℝ) ≤ (y : ℝ) from hxy]
  have hφs : Function.Surjective φ := by
    intro y
    refine ⟨ψ y, ?_⟩
    apply Subtype.ext
    simp [φ, ψ]
  have hφi : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    simpa [φ] using congrArg Subtype.val hxy
  let e : Icc a b ≃ₜ Icc (a + c) (b + c) :=
    { toFun := φ
      invFun := ψ
      left_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
      right_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
      continuous_toFun := hφc
      continuous_invFun := hψc }
  let hgbv := BoundedVariationOn.comp_monotone_surjective_Icc
    (by linarith : a + c ≤ b + c)
    f.boundedVariation hφm hφs
  let g : RightContinuousIntervalBV a b :=
    { toFun := f.toFun ∘ φ
      boundedVariation := hgbv
      right_continuous := fun t ↦
        (hfc.comp hφc).continuousAt.continuousWithinAt }
  refine ⟨g, fun _ ↦ rfl, ?_⟩
  intro E hE
  have hmap := BoundedVariationOn.vectorMeasure_map_comp_monotone_surjective_Icc
    (by linarith : a + c ≤ b + c) hab f.boundedVariation hfc hφc hφm hφs
  have hφE : MeasurableSet (φ '' E) := e.measurableEmbedding.measurableSet_image' hE
  change hgbv.vectorMeasure E = f.boundedVariation.vectorMeasure (φ '' E)
  rw [← hmap, VectorMeasure.map_apply _ hφc.measurable hφE,
    hφi.preimage_image]

/-- Specialize interval translation to an interval starting at zero. -/
theorem exists_intervalBV_shift_from_zero {b c : ℝ} (hb : 0 ≤ b)
    (f : RightContinuousIntervalBV (0 + c) (b + c)) (hfc : Continuous f.toFun) :
    ∃ g : RightContinuousIntervalBV 0 b,
      (∀ t, g.toFun t = f.toFun
        ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) ∧
      ∀ E : Set (Icc 0 b), MeasurableSet E →
        intervalStieltjesMeasure g E = intervalStieltjesMeasure f
          ((fun t : Icc 0 b ↦
            ⟨(t : ℝ) + c, by constructor <;> linarith [t.property.1, t.property.2]⟩) '' E) := by
  exact exists_intervalBV_shift_add (a := 0) (b := b) (c := c) hb f hfc

end MovingSofa
