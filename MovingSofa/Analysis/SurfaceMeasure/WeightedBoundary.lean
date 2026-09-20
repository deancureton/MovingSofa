import MovingSofa.Analysis.SurfaceMeasure.Properties
import MovingSofa.Analysis.Stieltjes.Integral
import MovingSofa.ForMathlib.MeasureTheory.VectorMeasure.Interval
import MovingSofa.ForMathlib.MeasureTheory.VectorMeasure.WithDensity

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

/-- On a half-open parameter interval of at most one turn, the angular projection is a
measurable embedding. -/
theorem measurableEmbedding_angleCoe_Ioc {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) :
    MeasurableEmbedding fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
  refine ⟨?_, (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable, ?_⟩
  · intro x y hxy
    exact Subtype.ext (Real.Angle.injOn_coe_Ioc hturn x.property y.property hxy)
  · intro s hs
    let S : Set ℝ := Subtype.val '' s
    have hS : MeasurableSet S :=
      (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
    have hSI : Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) S := by
      intro x hx y hy hxy
      obtain ⟨tx, htx, rfl⟩ := hx
      obtain ⟨ty, hty, rfl⟩ := hy
      exact Real.Angle.injOn_coe_Ioc hturn tx.property ty.property hxy
    have hm := hS.image_of_continuousOn_injOn Real.Angle.continuous_coe.continuousOn hSI
    convert hm using 1
    ext u
    simp [S]

/-- A bounded measurable function on a half-open parameter interval of at most one full turn
extends to a bounded measurable function of the angle. -/
theorem exists_bounded_measurable_angle_extension {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (ψ : Ioc a b → ℝ) (hψm : Measurable ψ) (C : ℝ) (hC : 0 ≤ C) (hψb : ∀ t, ‖ψ t‖ ≤ C) :
    ∃ Q : Real.Angle → ℝ, Measurable Q ∧ (∀ u, ‖Q u‖ ≤ C) ∧
      ∀ t : Ioc a b, Q ((t : ℝ) : Real.Angle) = ψ t := by
  have hc : MeasurableEmbedding fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) :=
    measurableEmbedding_angleCoe_Ioc hturn
  refine ⟨Function.extend (fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) ψ (fun _ ↦ 0),
    hc.measurable_extend hψm measurable_const, fun u ↦ ?_,
    fun t ↦ hc.injective.extend_apply ψ _ t⟩
  by_cases hu : ∃ t : Ioc a b, ((t : ℝ) : Real.Angle) = u
  · obtain ⟨t, rfl⟩ := hu
    rw [hc.injective.extend_apply]
    exact hψb t
  · rw [Function.extend_apply' _ _ _ hu]
    simpa using hC

/-- A bounded measurable angular weight may be transported through the positive-vertex
Stieltjes identity, coordinate by coordinate. -/
theorem intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (i : Fin 2) (Q : Real.Angle → ℝ) (C : ℝ)
    (hQm : Measurable fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle)))
    (hQb : ∀ u, ‖Q u‖ ≤ C)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesIntegral (f i)
        (fun t ↦ Q (((t : ℝ) : Real.Angle))) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q u * tangentVector u i ∂surfaceAreaMeasure K := by
  let A := Ioc a b
  let c : A → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let j : A → Icc a b := fun t ↦ ⟨t, t.property.1.le, t.property.2⟩
  have hc : MeasurableEmbedding c := measurableEmbedding_angleCoe_Ioc hturn
  have hj : MeasurableEmbedding j := by
    refine ⟨fun x y h ↦ Subtype.ext (congrArg (fun z : Icc a b ↦ (z : ℝ)) h), ?_, ?_⟩
    · fun_prop
    · intro s hs
      have hsval : MeasurableSet ((Subtype.val : A → ℝ) '' s) :=
        (MeasurableEmbedding.subtype_coe measurableSet_Ioc).measurableSet_image' hs
      have hsj : j '' s = {t : Icc a b | (t : ℝ) ∈ (Subtype.val : A → ℝ) '' s} := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hxt⟩
          exact ⟨x, hx, Subtype.ext hxt⟩
      rw [hsj]
      exact hsval.preimage measurable_subtype_coe
  let μA := (surfaceAreaMeasure K).comap c
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  let _ : IsFiniteMeasure μA :=
    ⟨by
      rw [hc.comap_apply]
      exact measure_lt_top _ _⟩
  have htancont : Continuous (fun t : A ↦ tangentVector (c t) i) :=
    (continuous_tangentVector_coordinate i).comp
      (Real.Angle.continuous_coe.comp continuous_subtype_val)
  have htan : Integrable (fun t : A ↦ tangentVector (c t) i) μA :=
    Integrable.of_bound htancont.aestronglyMeasurable 1
      (ae_of_all _ fun t ↦ norm_tangentVector_coordinate_le_one (c t) i)
  let ν : SignedMeasure A := μA.withDensityᵥ (fun t ↦ tangentVector (c t) i)
  have hν (S : Set A) (hS : MeasurableSet S) :
      ν S = ∫ u in c '' S, tangentVector u i ∂surfaceAreaMeasure K := by
    rw [show ν S = ∫ t in S, tangentVector (c t) i ∂μA by
      exact withDensityᵥ_apply htan hS]
    have hm := hc.setIntegral_map (μ := μA) (fun u ↦ tangentVector u i) (c '' S)
    rw [hc.map_comap, hc.injective.preimage_image,
      Measure.restrict_restrict_of_subset (image_subset_range c S)] at hm
    exact hm.symm
  have hmeasure : intervalStieltjesMeasure (f i) = ν.map j := by
    apply MeasureTheory.VectorMeasure.ext_of_Ioc
    · intro x y hxy
      have hpremeas : MeasurableSet (j ⁻¹' Ioc x y) :=
        measurableSet_Ioc.preimage hj.measurable
      have himage : c '' (j ⁻¹' Ioc x y) =
          (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Ioc x y := by
        ext u
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨j t, ht, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, x.property.1.trans_lt ht.1, t.property.2⟩, ht, rfl⟩
      rw [VectorMeasure.map_apply _ hj.measurable measurableSet_Ioc, hν _ hpremeas,
        himage, hf i (Ioc x y) measurableSet_Ioc]
      intro t ht
      exact x.property.1.trans_lt ht.1
    · let aa : Icc a b := ⟨a, le_rfl, hab.le⟩
      let bb : Icc a b := ⟨b, hab.le, le_rfl⟩
      have hzero : intervalStieltjesMeasure (f i) {aa} = 0 := by
        rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
          (f i).right_continuous aa |>.rightLim_eq]
        have hbot : 𝓝[<] aa = ⊥ := by
          have hIio : Iio aa = ∅ := by
            ext t
            simp only [mem_Iio, mem_empty_iff_false, iff_false]
            exact not_lt_of_ge t.property.1
          rw [hIio]
          exact nhdsWithin_empty aa
        rw [leftLim_eq_of_eq_bot _ hbot, sub_self]
      have hsplit : (univ : Set (Icc a b)) = Ioc aa bb ∪ {aa} := by
        ext t
        simp only [mem_univ, true_iff, mem_union, mem_Ioc, mem_singleton_iff]
        by_cases hta : aa = t
        · exact Or.inr hta.symm
        · exact Or.inl ⟨lt_of_le_of_ne t.property.1 hta, t.property.2⟩
      have hlhs : intervalStieltjesMeasure (f i) univ =
          intervalStieltjesMeasure (f i) (Ioc aa bb) := by
        rw [hsplit, VectorMeasure.of_union (disjoint_singleton_right.2 (by simp))
          measurableSet_Ioc (measurableSet_singleton aa), hzero, add_zero]
      have himage : c '' (univ : Set A) =
          (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Ioc aa bb := by
        ext u
        constructor
        · rintro ⟨t, -, rfl⟩
          exact ⟨j t, t.property, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, mem_univ _, rfl⟩
      rw [hlhs, VectorMeasure.map_apply _ hj.measurable MeasurableSet.univ,
        preimage_univ, hν _ MeasurableSet.univ, himage,
        hf i (Ioc aa bb) measurableSet_Ioc]
      intro t ht
      exact ht.1
  unfold intervalStieltjesIntegral
  rw [hmeasure, hj.setIntegral_map_vectorMeasure hE]
  change (∫ᵛ t in j ⁻¹' E, Q (c t)
      ∂[ContinuousLinearMap.mul ℝ ℝ; μA.withDensityᵥ fun t ↦ tangentVector (c t) i]) = _
  rw [VectorMeasure.setIntegral_withDensity_mul_of_bounded (q := fun t : A ↦ Q (c t)) htan
    hQm.aestronglyMeasurable C (fun t ↦ hQb (c t))
    (j ⁻¹' E) (hE.preimage hj.measurable)]
  have hm := hc.setIntegral_map (μ := μA)
    (fun u ↦ Q u * tangentVector u i) (c '' (j ⁻¹' E))
  rw [hc.map_comap, hc.injective.preimage_image,
    Measure.restrict_restrict_of_subset (image_subset_range c (j ⁻¹' E))] at hm
  have himageE : c '' (j ⁻¹' E) =
      (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨j t, ht, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨t, hEa t htE, t.property.2⟩, htE, rfl⟩
  rw [← himageE]
  exact hm.symm

/-- A continuous angular weight may be transported through the positive-vertex Stieltjes
identity, coordinate by coordinate. -/
theorem intervalStieltjesIntegral_positiveVertex_coordinate
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (i : Fin 2) (Q : Real.Angle → ℝ) (hQ : Continuous Q)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesIntegral (f i)
        (fun t ↦ Q (((t : ℝ) : Real.Angle))) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q u * tangentVector u i ∂surfaceAreaMeasure K :=
  intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable K hab hturn f hf i Q
    ‖ContinuousMap.equivBoundedOfCompact Real.Angle ℝ ⟨Q, hQ⟩‖
    (hQ.comp (Real.Angle.continuous_coe.comp continuous_subtype_val)).measurable
    (fun u ↦ BoundedContinuousFunction.norm_coe_le_norm
      (ContinuousMap.equivBoundedOfCompact Real.Angle ℝ ⟨Q, hQ⟩) u) E hE hEa

/-- A bounded measurable angular weight times a frame tangent coordinate is integrable against
the surface measure on every measurable set of angles represented in the half-open parameter
interval. -/
theorem integrableOn_mul_tangentVector_of_bounded
    (K : ConvexBody Point) {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi)
    (i : Fin 2) (Q : Real.Angle → ℝ) (C : ℝ)
    (hQm : Measurable fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle)))
    (hQb : ∀ u, ‖Q u‖ ≤ C)
    (S : Set Real.Angle) (hS : MeasurableSet S)
    (hSsub : S ⊆ Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) :
    IntegrableOn (fun u ↦ Q u * tangentVector u i) S (surfaceAreaMeasure K) := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hC : 0 ≤ C := le_trans (norm_nonneg (Q 0)) (hQb 0)
  obtain ⟨Q', hQ'meas, hQ'b, hQ'eq⟩ := exists_bounded_measurable_angle_extension hturn
    (fun t : Ioc a b ↦ Q (((t : ℝ) : Real.Angle))) hQm C hC (fun t ↦ hQb _)
  have hglobal : Integrable (fun u ↦ Q' u * tangentVector u i) (surfaceAreaMeasure K) := by
    refine Integrable.of_bound
      (hQ'meas.mul (continuous_tangentVector_coordinate i).measurable).aestronglyMeasurable C
      (ae_of_all _ fun u ↦ ?_)
    calc ‖Q' u * tangentVector u i‖ = ‖Q' u‖ * ‖tangentVector u i‖ := norm_mul _ _
      _ ≤ C * 1 :=
        mul_le_mul (hQ'b u) (norm_tangentVector_coordinate_le_one u i) (norm_nonneg _) hC
      _ = C := mul_one C
  refine hglobal.integrableOn.congr_fun (fun u hu ↦ ?_) hS
  obtain ⟨t, rfl⟩ := hSsub hu
  simp only [hQ'eq t]

/-- Pairing the positive-vertex Stieltjes measures with a bounded measurable planar weight is the
surface integral of the pointwise contraction of that weight with the tangent frame. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_dot
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (φ : Fin 2 → Icc a b → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hφm : ∀ i, Measurable (φ i)) (hφb : ∀ i t, ‖φ i t‖ ≤ C)
    (g : Real.Angle → ℝ)
    (hg : ∀ t : Icc a b, a < (t : ℝ) →
      ∑ i : Fin 2, φ i t * tangentVector (((t : ℝ) : Real.Angle)) i =
        g (((t : ℝ) : Real.Angle)))
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i) (φ i) E) =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E, g u ∂surfaceAreaMeasure K := by
  set incl : Ioc a b → Icc a b := fun t ↦ ⟨(t : ℝ), t.property.1.le, t.property.2⟩
  have hinclm : Measurable incl := (Continuous.subtype_mk continuous_subtype_val _).measurable
  have himg : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E =
      (fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle)) '' (incl ⁻¹' E) := by
    ext u
    constructor
    · rintro ⟨t, htE, rfl⟩
      exact ⟨⟨(t : ℝ), hEa t htE, t.property.2⟩, htE, rfl⟩
    · rintro ⟨t, htE, rfl⟩
      exact ⟨incl t, htE, rfl⟩
  have hEmeas : MeasurableSet ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E) := by
    rw [himg]
    exact (measurableEmbedding_angleCoe_Ioc hturn).measurableSet_image' (hE.preimage hinclm)
  have hsub : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E ⊆
      Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
    rintro u ⟨t, htE, rfl⟩
    exact ⟨⟨(t : ℝ), hEa t htE, t.property.2⟩, rfl⟩
  choose Q hQm hQb hQeq using fun i : Fin 2 ↦ exists_bounded_measurable_angle_extension hturn
    (fun t : Ioc a b ↦ φ i (incl t)) ((hφm i).comp hinclm) C hC fun t ↦ hφb i (incl t)
  have hQmIoc (i : Fin 2) : Measurable fun t : Ioc a b ↦ Q i (((t : ℝ) : Real.Angle)) :=
    (hQm i).comp (Real.Angle.continuous_coe.comp continuous_subtype_val).measurable
  have hQφ (i : Fin 2) (t : Icc a b) (ht : a < (t : ℝ)) :
      Q i (((t : ℝ) : Real.Angle)) = φ i t := hQeq i ⟨(t : ℝ), ht, t.property.2⟩
  have hterm (i : Fin 2) : intervalStieltjesIntegral (f i) (φ i) E =
      ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
        Q i u * tangentVector u i ∂surfaceAreaMeasure K := by
    rw [show intervalStieltjesIntegral (f i) (φ i) E =
        intervalStieltjesIntegral (f i) (fun t ↦ Q i (((t : ℝ) : Real.Angle))) E from
      VectorMeasure.setIntegral_congr_fun fun t htE ↦ (hQφ i t (hEa t htE)).symm]
    exact intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable K hab hturn f hf i
      (Q i) C (hQmIoc i) (hQb i) E hE hEa
  have hint (i : Fin 2) : IntegrableOn (fun u ↦ Q i u * tangentVector u i)
      ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E) (surfaceAreaMeasure K) :=
    integrableOn_mul_tangentVector_of_bounded K hturn i (Q i) C (hQmIoc i) (hQb i) _ hEmeas hsub
  rw [Fin.sum_univ_two, hterm 0, hterm 1, ← integral_add (hint 0) (hint 1)]
  refine setIntegral_congr_fun hEmeas ?_
  rintro u ⟨t, htE, rfl⟩
  have ht := hEa t htE
  simpa only [hQφ 0 t ht, hQφ 1 t ht, Fin.sum_univ_two] using hg t ht

/-- Pairing the positive-vertex Stieltjes measure with the tangent frame gives surface mass. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i)
      (fun t ↦ tangentVector (((t : ℝ) : Real.Angle)) i) E) =
      (surfaceAreaMeasure K
        ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcoord (i : Fin 2) :
      intervalStieltjesIntegral (f i)
          (fun t ↦ tangentVector (((t : ℝ) : Real.Angle)) i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i * tangentVector u i ∂surfaceAreaMeasure K := by
    have hQi : Continuous (fun u : Real.Angle ↦ tangentVector u i) := by
      fin_cases i
      · exact Real.Angle.continuous_sin.neg
      · exact Real.Angle.continuous_cos
    exact intervalStieltjesIntegral_positiveVertex_coordinate K hab hturn f hf i
      (fun u ↦ tangentVector u i) hQi E hE hEa
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
  have h0 : Integrable (fun u : Real.Angle ↦ tangentVector u 0 * tangentVector u 0)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_sin.mul Real.Angle.continuous_sin using 1
      funext u
      simp [tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have h1 : Integrable (fun u : Real.Angle ↦ tangentVector u 1 * tangentVector u 1)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_cos.mul Real.Angle.continuous_cos using 1
      funext u
      simp [tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  rw [← integral_add h0.integrableOn h1.integrableOn]
  have hone : (fun u : Real.Angle ↦
      tangentVector u 0 * tangentVector u 0 + tangentVector u 1 * tangentVector u 1) = 1 := by
    funext u
    simpa [tangentVector, frame, pow_two, add_comm] using u.cos_sq_add_sin_sq
  rw [hone]
  let S := (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E
  calc
    integral ((surfaceAreaMeasure K).restrict S) 1 =
        ((surfaceAreaMeasure K).restrict S).real univ := by
          change (∫ _ : Real.Angle, (1 : ℝ) ∂(surfaceAreaMeasure K).restrict S) = _
          rw [integral_const (μ := (surfaceAreaMeasure K).restrict S) (1 : ℝ),
            smul_eq_mul, mul_one]
    _ = (surfaceAreaMeasure K).real S :=
      measureReal_restrict_apply_univ (μ := surfaceAreaMeasure K) S
    _ = (surfaceAreaMeasure K S).toReal := measureReal_def _ _

/-- Pairing the positive-vertex Stieltjes measure with the normal frame vanishes. -/
theorem sum_intervalStieltjesIntegral_positiveVertex_normal
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (f i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure K)
    (E : Set (Icc a b)) (hE : MeasurableSet E) (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∑ i : Fin 2, intervalStieltjesIntegral (f i)
      (fun t ↦ normalVector (((t : ℝ) : Real.Angle)) i) E) = 0 := by
  let _ : IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1
  have hcoord (i : Fin 2) :
      intervalStieltjesIntegral (f i)
          (fun t ↦ normalVector (((t : ℝ) : Real.Angle)) i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          normalVector u i * tangentVector u i ∂surfaceAreaMeasure K := by
    have hQi : Continuous (fun u : Real.Angle ↦ normalVector u i) := by
      fin_cases i
      · exact Real.Angle.continuous_cos
      · exact Real.Angle.continuous_sin
    exact intervalStieltjesIntegral_positiveVertex_coordinate K hab hturn f hf i
      (fun u ↦ normalVector u i) hQi E hE hEa
  rw [Fin.sum_univ_two, hcoord 0, hcoord 1]
  have h0 : Integrable (fun u : Real.Angle ↦ normalVector u 0 * tangentVector u 0)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert (Real.Angle.continuous_cos.mul Real.Angle.continuous_sin).neg using 1
      funext u
      simp [normalVector, tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  have h1 : Integrable (fun u : Real.Angle ↦ normalVector u 1 * tangentVector u 1)
      (surfaceAreaMeasure K) := by
    apply Continuous.integrable_of_hasCompactSupport
    · convert Real.Angle.continuous_sin.mul Real.Angle.continuous_cos using 1
      funext u
      simp [normalVector, tangentVector, frame]
    · exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  rw [← integral_add h0.integrableOn h1.integrableOn]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  simp [normalVector, tangentVector, frame]
  ring

end MovingSofa
