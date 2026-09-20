import MovingSofa.Analysis.Stieltjes.ConvexBoundary
import MovingSofa.ForMathlib.MeasureTheory.VectorMeasure.LocallyConstant
import MovingSofa.Cap.ContactIdentities
import MovingSofa.Analysis.Stieltjes.AbsoluteContinuity
import Mathlib.Analysis.Convex.Exposed
import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

private def quarterTurn (p : Point) : Point := !₂[-p 1, p 0]

private theorem quarterTurn_ne_zero {p : Point} (hp : p ≠ 0) : quarterTurn p ≠ 0 := by
  intro h
  apply hp
  ext i
  fin_cases i
  · exact congrFun (congrArg WithLp.ofLp h) 1
  · simpa [quarterTurn] using congrFun (congrArg WithLp.ofLp h) 0

private theorem inner_quarterTurn (p : Point) : inner ℝ p (quarterTurn p) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [quarterTurn, dotProduct, Fin.sum_univ_two]
  ring

private theorem inner_normalVector_vectorNormalAngle_quarterTurn {p : Point} (hp : p ≠ 0) :
    inner ℝ p (normalVector (vectorNormalAngle (quarterTurn p))) = 0 := by
  rw [normalVector_vectorNormalAngle (quarterTurn_ne_zero hp), inner_smul_right,
    inner_quarterTurn, mul_zero]

/-- A nonzero planar direction has only finitely many perpendicular angular normals. -/
theorem finite_orthogonalNormal_angles {p : Point} (hp : p ≠ 0) :
    Set.Finite {t : Real.Angle | inner ℝ p (normalVector t) = 0} := by
  let t₀ := vectorNormalAngle (quarterTurn p)
  apply Set.Finite.subset
    ((Set.finite_singleton (t₀ + (Real.pi : Real.Angle))).insert t₀)
  intro t ht
  have h := normalVector_eq_or_eq_add_pi_of_orthogonal hp ht
    (inner_normalVector_vectorNormalAngle_quarterTurn hp)
  rcases h with h | h
  · exact Set.mem_insert_iff.mpr (Or.inl h)
  · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr h))

/-- The possible normals perpendicular to differences of points in a finite set are finite. -/
theorem finite_pairDifferenceNormal_angles (V : Finset Point) :
    Set.Finite {t : Real.Angle | ∃ p ∈ V, ∃ q ∈ V,
      p ≠ q ∧ inner ℝ (p - q) (normalVector t) = 0} := by
  classical
  let N : Point → Point → Set Real.Angle := fun p q ↦
    if h : p = q then ∅ else {t | inner ℝ (p - q) (normalVector t) = 0}
  have hN (p q : Point) : Set.Finite (N p q) := by
    by_cases h : p = q
    · simp [N, h]
    · simpa [N, h] using finite_orthogonalNormal_angles (sub_ne_zero.mpr h)
  apply Set.Finite.subset (V.finite_toSet.biUnion fun p _ ↦
    V.finite_toSet.biUnion fun q _ ↦ hN p q)
  rintro t ⟨p, hp, q, hq, hpq, ht⟩
  apply Set.mem_iUnion₂.mpr
  refine ⟨p, hp, Set.mem_iUnion₂.mpr ⟨q, hq, ?_⟩⟩
  simp [N, hpq, ht]

private theorem isExposed_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsExposed ℝ (K : Set Point) (exposedEdge K t) := by
  intro _
  refine ⟨innerSL ℝ (normalVector t), ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, innerSL_apply_apply, real_inner_comm]
  constructor
  · intro hp
    refine ⟨hp.1, fun q hq ↦ ?_⟩
    rw [hp.2]
    exact inner_le_supportValue K hq t
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq

private theorem isExposed_singleton_edgeVertices_fst (K : ConvexBody Point)
    (t : Real.Angle) :
    IsExposed ℝ (exposedEdge K t) {(edgeVertices K t).1} := by
  intro _
  refine ⟨innerSL ℝ (tangentVector t), ?_⟩
  ext p
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, innerSL_apply_apply,
    real_inner_comm]
  constructor
  · rintro rfl
    refine ⟨edgeVertices_fst_mem K t, fun q hq ↦ ?_⟩
    rw [inner_edgeVertices_fst_tangent]
    exact le_csSup ((isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const)).bddAbove ⟨q, hq, rfl⟩
  · rintro ⟨hp, hmax⟩
    have htangent : inner ℝ p (tangentVector t) =
        inner ℝ (edgeVertices K t).1 (tangentVector t) := by
      apply le_antisymm
      · rw [inner_edgeVertices_fst_tangent]
        exact le_csSup ((isCompact_exposedEdge K t).image
          (continuous_id.inner continuous_const)).bddAbove ⟨p, hp, rfl⟩
      · exact hmax _ (edgeVertices_fst_mem K t)
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K t).1 t,
      hp.2, (edgeVertices_fst_mem K t).2, htangent]

private theorem isExposed_singleton_edgeVertices_snd (K : ConvexBody Point)
    (t : Real.Angle) :
    IsExposed ℝ (exposedEdge K t) {(edgeVertices K t).2} := by
  intro _
  refine ⟨innerSL ℝ (-tangentVector t), ?_⟩
  ext p
  simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq, innerSL_apply_apply,
    real_inner_comm, inner_neg_left]
  constructor
  · rintro rfl
    refine ⟨edgeVertices_snd_mem K t, fun q hq ↦ neg_le_neg ?_⟩
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le ((isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const)).bddBelow ⟨q, hq, rfl⟩
  · rintro ⟨hp, hmax⟩
    have htangent : inner ℝ p (tangentVector t) =
        inner ℝ (edgeVertices K t).2 (tangentVector t) := by
      apply le_antisymm
      · exact neg_le_neg_iff.mp (hmax _ (edgeVertices_snd_mem K t))
      · rw [inner_edgeVertices_snd_tangent]
        exact csInf_le ((isCompact_exposedEdge K t).image
          (continuous_id.inner continuous_const)).bddBelow ⟨p, hp, rfl⟩
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul (edgeVertices K t).2 t,
      hp.2, (edgeVertices_snd_mem K t).2, htangent]

/-- Both endpoints of a polygon's exposed edge belong to its finite generating set. -/
theorem edgeVertices_mem_of_eq_convexHull (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ V ∧ (edgeVertices K t).2 ∈ V := by
  have hedge := (isExposed_exposedEdge K t).isExtreme
  constructor
  · have hext : (edgeVertices K t).1 ∈ Set.extremePoints ℝ (K : Set Point) :=
      (hedge.trans (isExposed_singleton_edgeVertices_fst K t).isExtreme).mem_extremePoints
    rw [hKV] at hext
    exact Finset.mem_coe.mp (extremePoints_convexHull_subset hext)
  · have hext : (edgeVertices K t).2 ∈ Set.extremePoints ℝ (K : Set Point) :=
      (hedge.trans (isExposed_singleton_edgeVertices_snd K t).isExtreme).mem_extremePoints
    rw [hKV] at hext
    exact Finset.mem_coe.mp (extremePoints_convexHull_subset hext)

/-- Every proper edge normal of a finite convex hull is one of finitely many pair normals. -/
theorem finite_properEdgeNormal_angles (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    Set.Finite {t : Real.Angle | (edgeVertices K t).1 ≠ (edgeVertices K t).2} := by
  apply (finite_pairDifferenceNormal_angles V).subset
  intro t ht
  refine ⟨(edgeVertices K t).1, (edgeVertices_mem_of_eq_convexHull K V hKV t).1,
    (edgeVertices K t).2, (edgeVertices_mem_of_eq_convexHull K V hKV t).2, ht, ?_⟩
  rw [inner_sub_left, (edgeVertices_fst_mem K t).2, (edgeVertices_snd_mem K t).2,
    sub_self]

private theorem continuousAt_positiveVertex_of_eq_negativeVertex (K : ConvexBody Point)
    (t : ℝ) (ht : (edgeVertices K (t : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).2) :
    ContinuousAt (fun s : ℝ ↦ (edgeVertices K (s : Real.Angle)).1) t := by
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · show Tendsto _ (𝓝[<] t) _
    simpa only [ht] using (contact_oneSided_limits K t).2.2.2.1
  · show Tendsto _ (𝓝[>] t) _
    exact (contact_oneSided_limits K t).1

/-- Away from a proper-edge normal, the positive vertex of a finite convex hull is locally
constant. -/
theorem eventuallyEq_positiveVertex_of_eq_convexHull (K : ConvexBody Point)
    (V : Finset Point) (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (t : ℝ) (ht : (edgeVertices K (t : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).2) :
    ∀ᶠ s : ℝ in 𝓝 t, (edgeVertices K (s : Real.Angle)).1 =
      (edgeVertices K (t : Real.Angle)).1 := by
  classical
  let v := (edgeVertices K (t : Real.Angle)).1
  let W : Set Point := (↑(V.erase v) : Set Point)
  have hvV : v ∈ V := (edgeVertices_mem_of_eq_convexHull K V hKV _).1
  have hvW : v ∈ Wᶜ := by simp [W, hvV]
  have hopen : IsOpen Wᶜ := (V.erase v).finite_toSet.isClosed.isOpen_compl
  have hnhds : Wᶜ ∈ 𝓝 v := hopen.mem_nhds hvW
  have htend :=
    (continuousAt_positiveVertex_of_eq_negativeVertex K t ht).eventually hnhds
  exact htend.mono (by
    intro s hs
    have hsV : (edgeVertices K (s : Real.Angle)).1 ∈ V :=
      (edgeVertices_mem_of_eq_convexHull K V hKV _).1
    by_contra hne
    have hnev : (edgeVertices K (s : Real.Angle)).1 ≠ v := by simpa [v] using hne
    exact hs (by simp [W, hsV, hnev]))

/-- For a two-dimensional finite convex hull, surface measure is supported on its finite set of
proper-edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (hint : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hmeas : MeasurableSet Nᶜ := hNfinite.measurableSet.compl
  have hface := (surfaceAreaMeasure_face_union K).2.2.2.2 Nᶜ hmeas (Or.inl hint)
  have hunion : (⋃ t ∈ Nᶜ, exposedEdge K t) ⊆ (V : Set Point) := by
    intro p hp
    obtain ⟨t, htN, hpt⟩ := Set.mem_iUnion₂.mp hp
    have ht : (edgeVertices K t).1 = (edgeVertices K t).2 := by
      simpa only [N, Set.mem_compl_iff, Set.mem_ofPred_eq, not_not] using htN
    have hp' : p = (edgeVertices K t).1 := by
      rw [exposedEdge_eq_segment_edgeVertices, ← ht] at hpt
      simpa using hpt
    rw [hp']
    exact (edgeVertices_mem_of_eq_convexHull K V hKV t).1
  rw [show {t | (edgeVertices K t).1 = (edgeVertices K t).2} = Nᶜ by
    ext t
    simp [N], hface]
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact measure_mono_null hunion
    (V.finite_toSet.measure_zero (Measure.hausdorffMeasure 1))

/-- Surface measure of any finite convex hull, including a point or segment, is supported on its
finite set of proper-edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point)) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  by_cases hsub : (K : Set Point).Subsingleton
  · rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hsub]
    simp
  by_cases hint : (interior (K : Set Point)).Nonempty
  · exact surfaceAreaMeasure_compl_properEdgeNormals_eq_zero K V hKV hint
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  have hproper (u : Real.Angle)
      (hu : inner ℝ (d.2.1 - d.1) (normalVector u) = 0) :
      (edgeVertices K u).1 ≠ (edgeVertices K u).2 := by
    intro heq
    have hedge := exposedEdge_eq_segment_of_orthogonal K d hd u hu
    have hsingle : (K : Set Point).Subsingleton := by
      rw [← hedge, exposedEdge_eq_segment_edgeVertices, heq]
      simp
    exact hsub hsingle
  have hpi : inner ℝ (d.2.1 - d.1)
      (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    have hn : normalVector (d.2.2 + (Real.pi : Real.Angle)) =
        -normalVector d.2.2 := by
      induction d.2.2 using Real.Angle.induction_on with
      | _ t => simpa only [← Real.Angle.coe_add] using normalVector_add_pi t
    rw [hn, inner_neg_right, hd.2.2, neg_zero]
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  simp [hproper d.2.2 hd.2.2, hproper _ hpi]

/-- Surface measure is carried by the proper edge normals as soon as these are finitely many
and the degenerate faces lie in a one-dimensional null set. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_carrier
    (K : ConvexBody Point)
    (hN : {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}.Finite)
    (V : Set Point) (hV : Measure.hausdorffMeasure 1 V = 0)
    (hcarrier : (⋃ t ∈ {t | (edgeVertices K t).1 = (edgeVertices K t).2},
      exposedEdge K t) ⊆ V) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hset : {t | (edgeVertices K t).1 = (edgeVertices K t).2} = Nᶜ := by
    ext t
    simp [N]
  by_cases hsub : (K : Set Point).Subsingleton
  · rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hsub]
    simp
  by_cases hint : (interior (K : Set Point)).Nonempty
  · rw [hset, (surfaceAreaMeasure_face_union K).2.2.2.2 Nᶜ
      hN.measurableSet.compl (Or.inl hint)]
    exact measure_mono_null (by simpa only [hset] using hcarrier) hV
  obtain ⟨d, hd⟩ := exists_segmentPresentation_of_interior_empty K hsub
    (Set.not_nonempty_iff_eq_empty.mp hint)
  have hproper (u : Real.Angle)
      (hu : inner ℝ (d.2.1 - d.1) (normalVector u) = 0) :
      (edgeVertices K u).1 ≠ (edgeVertices K u).2 := by
    intro heq
    have hedge := exposedEdge_eq_segment_of_orthogonal K d hd u hu
    have hsingle : (K : Set Point).Subsingleton := by
      rw [← hedge, exposedEdge_eq_segment_edgeVertices, heq]
      simp
    exact hsub hsingle
  have hpi : inner ℝ (d.2.1 - d.1)
      (normalVector (d.2.2 + (Real.pi : Real.Angle))) = 0 := by
    rw [normalVector_add_pi_angle, inner_neg_right, hd.2.2, neg_zero]
  rw [surfaceAreaMeasure_eq_segmentPresentation K d hd]
  simp [hproper d.2.2 hd.2.2, hproper _ hpi]

/-- The surface integral of an arbitrary integrand over a finite convex hull is the sum of its
proper-edge atoms, including the point and segment cases. No regularity of the integrand is
needed: the measure is carried by a finite set. -/
theorem integral_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (φ : Real.Angle → ℝ) (E : Set Real.Angle) (hE : MeasurableSet E) :
    ∫ t in E, φ t ∂surfaceAreaMeasure K =
      Finset.sum ((finite_properEdgeNormal_angles K V hKV).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * φ t) := by
  classical
  let N : Set Real.Angle := {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}
  have hNfinite : N.Finite := finite_properEdgeNormal_angles K V hKV
  have hae : ∀ᵐ t ∂surfaceAreaMeasure K, t ∈ N := by
    rw [ae_iff]
    simpa only [N, Set.mem_ofPred_eq, not_ne_iff] using
      surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_eq_convexHull K V hKV
  have hrestrict : (surfaceAreaMeasure K).restrict N = surfaceAreaMeasure K :=
    Measure.restrict_eq_self_of_ae_mem hae
  let _ := (surfaceAreaMeasure_face_union K).1
  have hEN : E ∩ N = ↑(hNfinite.inter_of_left E).toFinset := by
    ext t
    simp [N, and_comm]
  calc
    ∫ t in E, φ t ∂surfaceAreaMeasure K =
        ∫ t in E, φ t ∂(surfaceAreaMeasure K).restrict N := by rw [hrestrict]
    _ = ∫ t in E ∩ N, φ t ∂surfaceAreaMeasure K := by
      rw [Measure.restrict_restrict hE]
    _ = _ := by
      rw [hEN]
      exact MeasureTheory.setIntegral_finset _
        (μ := surfaceAreaMeasure K) (f := φ) IntegrableOn.finset

/-- The coordinate tangent integral of a finite convex hull is the sum of its proper-edge atoms,
including the point and segment cases. -/
theorem integral_tangentCoordinate_surfaceAreaMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (i : Fin 2) (E : Set Real.Angle) (hE : MeasurableSet E) :
    ∫ t in E, tangentVector t i ∂surfaceAreaMeasure K =
      Finset.sum ((finite_properEdgeNormal_angles K V hKV).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {t} * tangentVector t i) :=
  integral_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV
    (fun t ↦ tangentVector t i) E hE

/-- On a real interval, the coordinate Stieltjes measure of a polygon's positive vertex is
supported at proper-edge normals (apart from the excluded left endpoint). -/
theorem intervalStieltjesMeasure_variation_eq_zero_off_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i) (i : Fin 2) :
    (intervalStieltjesMeasure (f i)).variation
      {t | a < (t : ℝ) ∧ (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 =
        (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2} = 0 := by
  let T : Set (Set.Icc a b) :=
    {t | a < (t : ℝ) ∧ (edgeVertices K ((t : ℝ) : Real.Angle)).1 =
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  change (f i).boundedVariation.vectorMeasure.variation T = 0
  apply measure_null_of_locally_null T
  intro x hx
  have hconst := eventuallyEq_positiveVertex_of_eq_convexHull K V hKV (x : ℝ) hx.2
  have hconst' : (f i).toFun =ᶠ[𝓝 x] fun _ ↦ (f i).toFun x := by
    filter_upwards [continuousAt_subtype_val.eventually hconst] with y hy
    rw [hf i y, hf i x, hy]
  obtain ⟨U, hU, hUzero⟩ := BoundedVariationOn.exists_nhds_variation_vectorMeasure_eq_zero_of_eventuallyEq_const
    hab (f i).boundedVariation (f i).right_continuous x hx.1 hconst'
  exact ⟨U, mem_nhdsWithin_of_mem_nhds hU, hUzero⟩

/-- The left limit of a positive-vertex coordinate at a noninitial parameter is the corresponding
coordinate of the negative vertex. -/
theorem leftLim_positiveVertex_coordinate
    (K : ConvexBody Point) {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (t : Set.Icc a b) (ht : a < (t : ℝ)) :
    Function.leftLim (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2 i := by
  have hab : a < b := ht.trans_le t.property.2
  let _ : Fact (a ≤ b) := ⟨hab.le⟩
  let _ : Nontrivial (Set.Icc a b) :=
    ⟨⟨⟨a, le_rfl, hab.le⟩, ⟨b, hab.le, le_rfl⟩, fun h ↦
      hab.ne (congrArg Subtype.val h)⟩⟩
  have hcoe : Tendsto (fun s : Set.Icc a b ↦ (s : ℝ)) (𝓝[<] t) (𝓝[<] (t : ℝ)) := by
    rw [nhdsWithin_subtype, Set.image_subtype_val_Icc_Iio,
      nhdsWithin_Ico_eq_nhdsLT ht]
    exact tendsto_comap
  have hcontact := ((contact_oneSided_limits K (t : ℝ)).2.2.2.1).comp hcoe
  have hcoord := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i).continuous.continuousAt
    |>.tendsto.comp hcontact
  have hfleft := (f i).boundedVariation.tendsto_leftLim t
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨⊥, ht⟩
  apply tendsto_nhds_unique hfleft
  apply hcoord.congr
  intro s
  simpa [Function.comp_apply] using (hf i s).symm

/-- Each noninitial Stieltjes atom of a positive-vertex coordinate is the corresponding
coordinate of the tangent-weighted surface-measure atom. -/
theorem intervalStieltjesMeasure_singleton_positiveVertex
    (K : ConvexBody Point) {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (t : Set.Icc a b) (ht : a < (t : ℝ)) :
    intervalStieltjesMeasure (f i) {t} =
      (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
        tangentVector ((t : ℝ) : Real.Angle) i := by
  rw [intervalStieltjesMeasure, (f i).boundedVariation.vectorMeasure_singleton,
    (f i).right_continuous t |>.rightLim_eq,
    leftLim_positiveVertex_coordinate K f hf i t ht, hf]
  have h := congrArg (fun p : Point ↦ p i)
    (surfaceAreaMeasure_atom_length K ((t : ℝ) : Real.Angle)).2.2
  simpa [PiLp.smul_apply] using congrArg (fun z : ℝ ↦
    z - (edgeVertices K ((t : ℝ) : Real.Angle)).2 i) h

/-- A proper-edge normal has only finitely many lifts in a half-open interval of length at most one
full turn. -/
theorem finite_properEdgeNormal_lifts (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) :
    Set.Finite {t : Set.Icc a b | a < (t : ℝ) ∧
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).2} := by
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let N : Set Real.Angle :=
    {u | (edgeVertices K u).1 ≠ (edgeVertices K u).2}
  let c : Set.Icc a b → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  change S.Finite
  apply Set.Finite.of_finite_image
  · apply (finite_properEdgeNormal_angles K V hKV).subset
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  · intro x hx y hy hxy
    apply Subtype.ext
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := 2 * Real.pi) ⟨hx.1, x.property.2.trans hturn⟩
      ⟨hy.1, y.property.2.trans hturn⟩).mp
    change ((x : ℝ) : Real.Angle) = ((y : ℝ) : Real.Angle)
    simpa [c] using hxy

/-- On a polygon, every measurable noninitial set has Stieltjes mass equal to the finite sum of
its proper-edge atoms. -/
theorem intervalStieltjesMeasure_eq_sum_properEdgeNormals
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (f : Fin 2 → RightContinuousIntervalBV a b)
    (hf : ∀ i t, (f i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (i : Fin 2) (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    intervalStieltjesMeasure (f i) E =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K
          {(((t : Set.Icc a b) : ℝ) : Real.Angle)}).toReal *
            tangentVector (((t : Set.Icc a b) : ℝ) : Real.Angle) i) := by
  classical
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let T : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 =
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  let μ := intervalStieltjesMeasure (f i)
  change μ E = _
  have hSfinite : S.Finite := finite_properEdgeNormal_lifts K V hKV hturn
  have hTzero : μ.variation T = 0 :=
    intervalStieltjesMeasure_variation_eq_zero_off_properEdgeNormals K V hKV hab f hf i
  have hdiffsub : E \ S ⊆ T := by
    intro t ht
    exact ⟨hEa t ht.1, not_ne_iff.mp (fun hne ↦ ht.2 ⟨hEa t ht.1, hne⟩)⟩
  have hdiffzero : μ (E \ S) = 0 := by
    rw [← enorm_eq_zero, ← le_zero_iff]
    exact (μ.enorm_measure_le_variation (E \ S)).trans
      (by rw [measure_mono_null hdiffsub hTzero])
  have hsplit : E = S ∩ E ∪ (E \ S) := by
    ext t
    constructor
    · intro ht
      by_cases htS : t ∈ S
      · exact Or.inl ⟨htS, ht⟩
      · exact Or.inr ⟨ht, htS⟩
    · rintro (ht | ht)
      · exact ht.2
      · exact ht.1
  have hfinite : S ∩ E =
      ↑((hSfinite.inter_of_left E).toFinset) := by
    exact (hSfinite.inter_of_left E).coe_toFinset.symm
  have hES : MeasurableSet (S ∩ E) := hSfinite.measurableSet.inter hE
  have hEdiff : MeasurableSet (E \ S) := hE.diff hSfinite.measurableSet
  have hdisj : Disjoint (S ∩ E) (E \ S) :=
    Set.disjoint_of_subset_left Set.inter_subset_left Set.disjoint_sdiff_right
  have hreduce : μ E = μ (S ∩ E) := calc
    μ E = μ (S ∩ E ∪ (E \ S)) := congrArg μ hsplit
    _ = μ (S ∩ E) + μ (E \ S) := μ.of_union hdisj hES hEdiff
    _ = μ (S ∩ E) := by rw [hdiffzero, add_zero]
  rw [hreduce]
  conv_lhs => rw [hfinite]
  let F := (hSfinite.inter_of_left E).toFinset
  have hU : (↑F : Set (Set.Icc a b)) = ⋃ t ∈ F, {t} := by
    ext t
    simp only [Finset.mem_coe, Set.mem_iUnion, Set.mem_singleton_iff]
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨u, hu, _, rfl⟩
      exact hu
  rw [hU, μ.of_biUnion_finset (by
    intro x hx y hy hxy
    simpa [Set.disjoint_singleton] using hxy) (by simp)]
  calc
    Finset.sum F (fun t ↦ μ {t}) =
        Finset.sum F (fun t ↦
          (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
            tangentVector ((t : ℝ) : Real.Angle) i) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' : t ∈ S ∩ E := by simpa [F] using ht
      exact intervalStieltjesMeasure_singleton_positiveVertex K f hf i t
        (by simpa [S] using ht'.1.1)
    _ = _ := by
      exact congrArg (fun G : Finset (Set.Icc a b) ↦
        Finset.sum G (fun t ↦
          (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
            tangentVector ((t : ℝ) : Real.Angle) i)) (by
              apply Finset.ext
              intro t
              simp [F, S])

/-- The surface integral of an arbitrary integrand over the angular image of a measurable
interval set, as a finite sum indexed by the angular lifts carrying a proper edge. The left
endpoint `a` is excluded from `E` so that each angle has at most one lift in `E`. -/
theorem integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) (φ : Real.Angle → ℝ)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
      φ u ∂surfaceAreaMeasure K) =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K).real {((t : ℝ) : Real.Angle)} *
          φ ((t : ℝ) : Real.Angle)) := by
  classical
  let c : Set.Icc a b → Real.Angle := fun t ↦ ((t : ℝ) : Real.Angle)
  let S : Set (Set.Icc a b) := {t | a < (t : ℝ) ∧
    (edgeVertices K ((t : ℝ) : Real.Angle)).1 ≠
      (edgeVertices K ((t : ℝ) : Real.Angle)).2}
  have hinj : Set.InjOn c E := by
    intro x hx y hy hxy
    apply Subtype.ext
    let _ : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := 2 * Real.pi) ⟨hEa x hx, x.property.2.trans hturn⟩
      ⟨hEa y hy, y.property.2.trans hturn⟩).mp
    change c x = c y
    exact hxy
  have hAmeas : MeasurableSet (c '' E) :=
    hE.image_of_continuousOn_injOn
      ((Real.Angle.continuous_coe : Continuous fun x : ℝ ↦ (x : Real.Angle)).comp
        continuous_subtype_val).continuousOn hinj
  rw [integral_surfaceAreaMeasure_eq_sum_properEdgeNormals K V hKV φ (c '' E) hAmeas]
  let F := ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
  let G := ((finite_properEdgeNormal_angles K V hKV).inter_of_left (c '' E)).toFinset
  have hG : G = F.image c := by
    ext u
    simp only [G, F, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_image,
      Finset.mem_image]
    constructor
    · rintro ⟨huN, t, htE, rfl⟩
      exact ⟨t, ⟨⟨hEa t htE, huN⟩, htE⟩, rfl⟩
    · rintro ⟨t, ⟨⟨hta, htN⟩, htE⟩, rfl⟩
      exact ⟨htN, t, htE, rfl⟩
  change Finset.sum G (fun u ↦ (surfaceAreaMeasure K).real {u} * φ u) = _
  rw [hG, Finset.sum_image]
  · intro x hx y hy hxy
    have hx' : x ∈ S ∩ E := by
      change (a < (x : ℝ) ∧ (edgeVertices K ((x : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((x : ℝ) : Real.Angle)).2) ∧ x ∈ E
      simpa [F] using hx
    have hy' : y ∈ S ∩ E := by
      change (a < (y : ℝ) ∧ (edgeVertices K ((y : ℝ) : Real.Angle)).1 ≠
        (edgeVertices K ((y : ℝ) : Real.Angle)).2) ∧ y ∈ E
      simpa [F] using hy
    exact hinj hx'.2 hy'.2 hxy

/-- The tangent-coordinate surface integral over the angular image of a measurable interval set is
the same finite proper-edge sum as the positive-vertex Stieltjes measure. -/
theorem integral_tangentCoordinate_image_eq_sum_properEdgeNormal_lifts
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hturn : b ≤ a + 2 * Real.pi) (i : Fin 2)
    (E : Set (Set.Icc a b)) (hE : MeasurableSet E)
    (hEa : ∀ t ∈ E, a < (t : ℝ)) :
    (∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
      tangentVector u i ∂surfaceAreaMeasure K) =
      Finset.sum ((finite_properEdgeNormal_lifts K V hKV hturn).inter_of_left E).toFinset
        (fun t ↦ (surfaceAreaMeasure K {((t : ℝ) : Real.Angle)}).toReal *
          tangentVector ((t : ℝ) : Real.Angle) i) :=
  integral_surfaceAreaMeasure_image_eq_sum_properEdgeNormal_lifts K V hKV hturn
    (fun u ↦ tangentVector u i) E hE hEa

/-- Polygon case of the positive-vertex Stieltjes/surface-measure identity, including degenerate
point and segment convex hulls. -/
theorem positiveVertex_stieltjes_surface_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    (a b : ℝ) (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) :
    ∃ f : Fin 2 → RightContinuousIntervalBV a b,
      (∀ i t, (f i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      ∀ (i : Fin 2) (E : Set (Set.Icc a b)), MeasurableSet E →
        (∀ t ∈ E, a < (t : ℝ)) →
        intervalStieltjesMeasure (f i) E =
          ∫ u in (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
            tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf⟩ := exists_positiveVertex_intervalBV K hab.le
  refine ⟨f, hf, fun i E hE hEa ↦ ?_⟩
  rw [intervalStieltjesMeasure_eq_sum_properEdgeNormals K V hKV hab hturn f hf i E hE hEa,
    integral_tangentCoordinate_image_eq_sum_properEdgeNormal_lifts
      K V hKV hturn i E hE hEa]

/-- The positive vertex increment of a polygon is the tangent-coordinate surface integral over
the corresponding angular interval. -/
theorem positiveVertex_sub_eq_integral_of_eq_convexHull
    (K : ConvexBody Point) (V : Finset Point)
    (hKV : (K : Set Point) = convexHull ℝ (V : Set Point))
    {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi) (i : Fin 2) :
    (edgeVertices K (b : Real.Angle)).1 i -
        (edgeVertices K (a : Real.Angle)).1 i =
      ∫ u in (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b,
        tangentVector u i ∂surfaceAreaMeasure K := by
  obtain ⟨f, hf, hmeasure⟩ :=
    positiveVertex_stieltjes_surface_of_eq_convexHull K V hKV a b hab hturn
  let aa : Set.Icc a b := ⟨a, le_rfl, hab.le⟩
  let bb : Set.Icc a b := ⟨b, hab.le, le_rfl⟩
  have hangularImage :
      (fun t : Set.Icc a b ↦ ((t : ℝ) : Real.Angle)) '' Set.Ioc aa bb =
        (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Ioc a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ⟨ht.1, ht.2⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1.le, ht.2⟩, ⟨ht.1, ht.2⟩, rfl⟩
  have hstieltjes := hmeasure i (Set.Ioc aa bb) measurableSet_Ioc
    (fun t ht ↦ ht.1)
  rw [intervalStieltjesMeasure_Ioc (f i) aa bb hab.le] at hstieltjes
  rw [hf i bb, hf i aa, hangularImage] at hstieltjes
  exact hstieltjes

end MovingSofa
