import MovingSofa.Cap.Densities
import MovingSofa.Bounds.Arm.Geometry
import MovingSofa.ForMathlib.Topology.Order.Interval
import MovingSofa.ForMathlib.Analysis.Calculus.Interval
import MovingSofa.ForMathlib.Analysis.Calculus.Deriv.Shift

noncomputable section

open Set Filter
open scoped Topology

namespace MovingSofa

private theorem continuous_nondegenerateCapData_right (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.1 := by
  have h := continuousOn_replace_right_endpoint (by positivity : (0 : ℝ) < Real.pi / 2)
    (fun t : ℝ ↦ (capVertices K t).1.1) ((capVertices K (Real.pi / 2)).1.2)
    (fun t ht ↦ (contact_oneSided_limits K.1 t).1)
    (fun t ht ↦ ?_) (contact_oneSided_limits K.1 (Real.pi / 2)).2.2.2.1
  · apply (continuousOn_iff_continuous_domRestrict.mp h).congr
    intro t
    dsimp [Set.domRestrict, nondegenerateCapData]
    split_ifs with heq
    · rw [heq]
    · rfl
  · have heq := (capDensities_contact_eq K hD).1 t ⟨ht.1.le, ht.2⟩ |>.1
    change (edgeVertices K.1 (t : Real.Angle)).1 =
      (edgeVertices K.1 (t : Real.Angle)).2 at heq
    simpa only [← heq, capVertices] using (contact_oneSided_limits K.1 t).2.2.2.1

private theorem continuous_nondegenerateCapData_left (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.2 := by
  let f : ℝ → Point := fun t ↦ (capVertices K t).2.1
  have hr (t : ℝ) : Tendsto f (𝓝[>] t) (𝓝 (f t)) := by
    apply (contact_oneSided_limits K.1 (t + Real.pi / 2)).1.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (tendsto_id.mono_left nhdsWithin_le_nhds).add_const _
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change t + Real.pi / 2 < u + Real.pi / 2
      simpa only [add_comm] using add_lt_add_right (Set.mem_Ioi.mp hu) (Real.pi / 2)
  have hl (t : ℝ) (ht : t ∈ Ioc 0 (Real.pi / 2)) :
      Tendsto f (𝓝[<] t) (𝓝 (f t)) := by
    have h := (contact_oneSided_limits K.1 (t + Real.pi / 2)).2.2.2.1
    have heq := (capDensities_contact_eq K hD).2 t ht |>.1
    change (edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 =
      (edgeVertices K.1 ((t + Real.pi / 2 : ℝ) : Real.Angle)).2 at heq
    rw [← heq] at h
    apply h.comp
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact (tendsto_id.mono_left nhdsWithin_le_nhds).add_const _
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change u + Real.pi / 2 < t + Real.pi / 2
      simpa only [add_comm] using add_lt_add_right (Set.mem_Iio.mp hu) (Real.pi / 2)
  have h := continuousOn_replace_right_endpoint (by positivity : (0 : ℝ) < Real.pi / 2)
    f (f (Real.pi / 2)) (fun t _ ↦ hr t) (fun t ht ↦ hl t ⟨ht.1, ht.2.le⟩)
    (hl (Real.pi / 2) ⟨by positivity, le_rfl⟩)
  have hc : ContinuousOn f (Icc 0 (Real.pi / 2)) := h.congr fun t ht ↦ by
    by_cases heq : t = Real.pi / 2 <;> simp [heq]
  change Continuous ((Icc 0 (Real.pi / 2)).domRestrict f)
  exact continuousOn_iff_continuous_domRestrict.mp hc

private theorem continuous_nondegenerateCapData_arms (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).2.1 ∧
    Continuous (nondegenerateCapData K hD).2.2 := by
  have hy := (continuous_outerCorner K.1).comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hn := continuous_normalVector_real.comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hv := (continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_tangentVector t).continuousAt).comp
      (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  constructor
  · apply ((hy.sub (continuous_nondegenerateCapData_right K hD)).inner hv).congr
    intro t
    dsimp [nondegenerateCapData, tangentArmLengths]
    split_ifs <;> rfl
  · exact (hy.sub (continuous_nondegenerateCapData_left K hD)).inner hn

private theorem nondegenerateCap_hasDerivWithinAt (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) (t : Icc (0 : ℝ) (Real.pi / 2)) :
    HasDerivWithinAt (capInnerCorner K)
      (-((nondegenerateCapData K hD).2.1 t - 1) • normalVector (t : Real.Angle) +
        ((nondegenerateCapData K hD).2.2 t - 1) • tangentVector (t : Real.Angle))
      (Icc 0 (Real.pi / 2)) (t : ℝ) ∧
    HasDerivWithinAt
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (-(nondegenerateCapData K hD).2.1 t • normalVector (t : Real.Angle) +
        (nondegenerateCapData K hD).2.2 t • tangentVector (t : Real.Angle))
      (Icc 0 (Real.pi / 2)) (t : ℝ) := by
  have hr (ht : (t : ℝ) < Real.pi / 2) :=
    (capCorners_oneSided_derivatives K).1 t ⟨t.property.1, ht⟩
  have hl (ht : 0 < (t : ℝ)) :=
    (capCorners_oneSided_derivatives K).2 t ⟨ht, t.property.2⟩
  have hfplus (ht : (t : ℝ) < Real.pi / 2) :
      (nondegenerateCapData K hD).2.1 t = (tangentArmLengths K t).1.1 := by
    simp only [nondegenerateCapData, ite_eq_right ht.ne]
  have hfminus (ht : 0 < (t : ℝ)) :
      (nondegenerateCapData K hD).2.1 t = (tangentArmLengths K t).1.2 := by
    dsimp [nondegenerateCapData]
    split_ifs with heq
    · rfl
    · exact ((capDensities_contact_eq K hD).1 t
        ⟨t.property.1, lt_of_le_of_ne t.property.2 heq⟩).2
  have hgminus (ht : 0 < (t : ℝ)) :
      (nondegenerateCapData K hD).2.2 t = (tangentArmLengths K t).2.2 :=
    ((capDensities_contact_eq K hD).2 t ⟨ht, t.property.2⟩).2
  constructor
  · apply hasDerivWithinAt_Icc_of_oneSided (by positivity) t.property
    · intro ht
      rw [hfplus ht]
      exact (hr ht).2
    · intro ht
      rw [hfminus ht, hgminus ht]
      exact (hl ht).2
  · apply hasDerivWithinAt_Icc_of_oneSided (by positivity) t.property
    · intro ht
      rw [hfplus ht]
      exact (hr ht).1
    · intro ht
      rw [hfminus ht, hgminus ht]
      exact (hl ht).1


theorem nondegenerateCap_continuity (K : RightAngleCapSpace)
    (hD : ∃ r s, HasCapDensities K r s) :
    Continuous (nondegenerateCapData K hD).1.1 ∧
    Continuous (nondegenerateCapData K hD).1.2 ∧
    Continuous (nondegenerateCapData K hD).2.1 ∧
    Continuous (nondegenerateCapData K hD).2.2 ∧
    ContDiffOn ℝ 1 (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) ∧
    ContDiffOn ℝ 1
      (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
      (Set.Icc 0 (Real.pi / 2)) ∧
    ∀ t : Set.Icc (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (capInnerCorner K)
        (-((nondegenerateCapData K hD).2.1 t - 1) • normalVector (t : Real.Angle) +
          ((nondegenerateCapData K hD).2.2 t - 1) • tangentVector (t : Real.Angle))
        (Set.Icc 0 (Real.pi / 2)) (t : ℝ) ∧
      HasDerivWithinAt
        (fun s : ℝ ↦ (rotatingHallwayParts (K.val : Set Point) (s : Real.Angle)).outerCorner)
        (-(nondegenerateCapData K hD).2.1 t • normalVector (t : Real.Angle) +
          (nondegenerateCapData K hD).2.2 t • tangentVector (t : Real.Angle))
        (Set.Icc 0 (Real.pi / 2)) (t : ℝ) := by
  have hA := continuous_nondegenerateCapData_right K hD
  have hC := continuous_nondegenerateCapData_left K hD
  obtain ⟨hf, hg⟩ := continuous_nondegenerateCapData_arms K hD
  have hn := continuous_normalVector_real.comp
    (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  have hv := (continuous_iff_continuousAt.mpr fun t ↦
    (hasDerivAt_tangentVector t).continuousAt).comp
      (continuous_subtype_val : Continuous (fun t : Icc (0 : ℝ) (Real.pi / 2) ↦ (t : ℝ)))
  refine ⟨hA, hC, hf, hg, ?_, ?_, nondegenerateCap_hasDerivWithinAt K hD⟩
  · exact contDiffOn_one_of_continuous_derivative
      (uniqueDiffOn_Icc (by positivity)) _ _
      (((hf.sub continuous_const).neg.smul hn).add ((hg.sub continuous_const).smul hv))
      (fun t ↦ (nondegenerateCap_hasDerivWithinAt K hD t).1)
  · exact contDiffOn_one_of_continuous_derivative
      (uniqueDiffOn_Icc (by positivity)) _ _
      ((hf.neg.smul hn).add (hg.smul hv))
      (fun t ↦ (nondegenerateCap_hasDerivWithinAt K hD t).2)

/-- The corner coordinates of a right-angle cap in its moving frame. -/
theorem inner_capInnerCorner (K : RightAngleCapSpace) (t : ℝ) :
    inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ∧
      inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 := by
  constructor
  · have h := inner_supportingPlacement_normalVector (K.1 : Set Point) (t : Real.Angle) 0
    simpa [capInnerCorner, rotatingHallwayParts, hallwayParts] using h
  · have h := inner_supportingPlacement_tangentVector (K.1 : Set Point) (t : Real.Angle) 0
    rw [← Real.Angle.coe_add] at h
    simpa [capInnerCorner, rotatingHallwayParts, hallwayParts] using h

/-- The injectivity condition supplies the support derivatives with their strict signs. -/
theorem capSupport_hasDerivAt (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) :
    ∃ dh dj : ℝ → ℝ,
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) (dh t) t) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) (dj t)
          (t + Real.pi / 2)) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        dh t - supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) + 1 < 0) ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        0 < dj t + supportValue (K.1 : Set Point) (t : Real.Angle) - 1) := by
  obtain ⟨-, hC1, hsign⟩ := hinj
  have hxn : ∀ t : ℝ, inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) =
      supportValue (K.1 : Set Point) (t : Real.Angle) - 1 := fun t => (inner_capInnerCorner K t).1
  have hxt : ∀ t : ℝ, inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) =
      supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    fun t => (inner_capInnerCorner K t).2
  have hdiff : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (capInnerCorner K) (deriv (capInnerCorner K) t) t := by
    intro t ht
    have hmem : Set.Icc (0 : ℝ) (Real.pi / 2) ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    exact (((hC1.differentiableOn one_ne_zero) t (Set.Ioo_subset_Icc_self ht)).differentiableAt
      hmem).hasDerivAt
  have hderivEq : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) t = deriv (capInnerCorner K) t :=
    fun t ht => derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hfunn : (fun u : ℝ ↦ supportValue (K.1 : Set Point) (u : Real.Angle)) =
      fun u : ℝ ↦ inner ℝ (capInnerCorner K u) (normalVector (u : Real.Angle)) + 1 := by
    funext u; rw [hxn u]; ring
  have hfunt :
      (fun u : ℝ ↦ supportValue (K.1 : Set Point) ((u + Real.pi / 2 : ℝ) : Real.Angle)) =
      fun u : ℝ ↦ inner ℝ (capInnerCorner K u) (tangentVector (u : Real.Angle)) + 1 := by
    funext u; rw [hxt u]; ring
  refine ⟨fun t ↦ inner ℝ (capInnerCorner K t) (tangentVector (t : Real.Angle)) +
      inner ℝ (deriv (capInnerCorner K) t) (normalVector (t : Real.Angle)),
    fun t ↦ -inner ℝ (capInnerCorner K t) (normalVector (t : Real.Angle)) +
      inner ℝ (deriv (capInnerCorner K) t) (tangentVector (t : Real.Angle)), ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hfunn]
    exact ((hdiff t ht).inner ℝ (hasDerivAt_normalVector t)).add_const 1
  · intro t ht
    refine (hasDerivAt_comp_add_const_iff (f := fun u : ℝ ↦
      supportValue (K.1 : Set Point) (u : Real.Angle)) t (Real.pi / 2)).mp ?_
    rw [hfunt]
    have hd := ((hdiff t ht).inner ℝ (hasDerivAt_tangentVector t)).add_const 1
    rw [inner_neg_right] at hd
    exact hd
  · intro t ht
    have h1 := (hsign t ht).1
    rw [hderivEq t ht] at h1
    dsimp only
    rw [hxt t]
    linarith only [h1]
  · intro t ht
    have h2 := (hsign t ht).2
    rw [hderivEq t ht] at h2
    dsimp only
    rw [hxn t]
    linarith only [h2]
end MovingSofa
