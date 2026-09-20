import MovingSofa.Convex.ArcArea

noncomputable section

open MeasureTheory Set

namespace MovingSofa

def openIntervalCrossIntegral {a b : ℝ} (f : Fin 2 → RightContinuousIntervalBV a b)
    (g : Set.Icc a b → Point) : ℝ :=
  (intervalStieltjesIntegral (f 1) (fun t ↦ g t 0) {t | a < (t : ℝ) ∧ (t : ℝ) < b} -
    intervalStieltjesIntegral (f 0) (fun t ↦ g t 1) {t | a < (t : ℝ) ∧ (t : ℝ) < b}) / 2

/-- The half-support integral is the vertex cross Stieltjes integral, for any bounded
measurable selection from the first body's exposed edges. -/
private theorem halfSupportIntegral_eq_openIntervalCrossIntegral
    (K L : ConvexBody Point) {a b : ℝ} (hab : a < b) (hturn : b ≤ a + 2 * Real.pi)
    (F : Fin 2 → RightContinuousIntervalBV a b)
    (hF : ∀ (i : Fin 2) (E : Set (Icc a b)), MeasurableSet E →
      (∀ t ∈ E, a < (t : ℝ)) →
      intervalStieltjesMeasure (F i) E =
        ∫ u in (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) '' E,
          tangentVector u i ∂surfaceAreaMeasure L)
    (W : Real.Angle → Point) (C : ℝ)
    (hWm : ∀ i : Fin 2, Measurable fun t : Ioc a b ↦ W (((t : ℝ) : Real.Angle)) i)
    (hWb : ∀ (u : Real.Angle) (i : Fin 2), ‖W u i‖ ≤ C)
    (hWsupp : ∀ u : Real.Angle, planeCrossProduct (W u) (tangentVector u) = supportValue K u) :
    ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
      supportValue K t ∂surfaceAreaMeasure L) =
      openIntervalCrossIntegral F (fun t ↦ W (((t : ℝ) : Real.Angle))) := by
  have hWcoord : ∀ u : Real.Angle,
      W u 0 * tangentVector u 1 - W u 1 * tangentVector u 0 = supportValue K u := hWsupp
  have hE : MeasurableSet {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} :=
    measurableSet_Ioo.preimage measurable_subtype_coe
  have hEa : ∀ t ∈ {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b}, a < (t : ℝ) :=
    fun _ ht ↦ ht.1
  have himg : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨(t : ℝ), ht, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1.le, hs.2.le⟩, hs, rfl⟩
  have hsub : (fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} ⊆
      Set.range fun t : Ioc a b ↦ ((t : ℝ) : Real.Angle) := by
    rintro u ⟨t, ht, rfl⟩
    exact ⟨⟨(t : ℝ), ht.1, ht.2.le⟩, rfl⟩
  have hSmeas : MeasurableSet ((fun t : Icc a b ↦ ((t : ℝ) : Real.Angle)) ''
      {t : Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b}) := by
    rw [himg]
    exact (Real.Angle.isOpen_image_Ioo a b).measurableSet
  have h1 := intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable L hab hturn F hF
    1 (fun u ↦ W u 0) C (hWm 0) (fun u ↦ hWb u 0) _ hE hEa
  have h0 := intervalStieltjesIntegral_positiveVertex_coordinate_of_measurable L hab hturn F hF
    0 (fun u ↦ W u 1) C (hWm 1) (fun u ↦ hWb u 1) _ hE hEa
  have hi1 := integrableOn_mul_tangentVector_of_bounded L hturn 1 (fun u ↦ W u 0) C (hWm 0)
    (fun u ↦ hWb u 0) _ hSmeas hsub
  have hi0 := integrableOn_mul_tangentVector_of_bounded L hturn 0 (fun u ↦ W u 1) C (hWm 1)
    (fun u ↦ hWb u 1) _ hSmeas hsub
  rw [openIntervalCrossIntegral, h1, h0, ← integral_sub hi1 hi0,
    setIntegral_congr_fun hSmeas (fun u _ ↦ hWcoord u), himg]
  ring

theorem convexArc_bilinear_computation (a b : ℝ) (hab : a < b) (hba : b < a + Real.pi) :
    IsConvexBilinear convexBodyCombination convexBodyCombination realCombination
      (fun K L : ConvexBody Point ↦ (1 / 2 : ℝ) *
        ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) ∧
    ∃ F : ConvexBody Point → Fin 2 → RightContinuousIntervalBV a b,
      (∀ K i t, (F K i).toFun t = (edgeVertices K ((t : ℝ) : Real.Angle)).1 i) ∧
      (∀ K L : ConvexBody Point,
        ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) =
          openIntervalCrossIntegral (F L) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) ∧
        ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
          supportValue K t ∂surfaceAreaMeasure L) =
          openIntervalCrossIntegral (F L) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2)) ∧
      (∀ K : ConvexBody Point, convexArcArea K a b =
        openIntervalCrossIntegral (F K) (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1)) := by
  have hturn : b ≤ a + 2 * Real.pi := by linarith [Real.pi_pos]
  refine ⟨convexArcIntegral_bilinear a b, ?_⟩
  choose F hFtoFun hFmeasure using fun L : ConvexBody Point ↦
    positiveVertex_stieltjes_surface L a b hab hturn
  have hcross1 (K L : ConvexBody Point) :
      ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure L) =
        openIntervalCrossIntegral (F L)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).1) := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point)
    refine halfSupportIntegral_eq_openIntervalCrossIntegral K L hab hturn (F L) (hFmeasure L)
      (fun u ↦ (edgeVertices K u).1) R
      (fun i ↦ measurable_positiveVertex_coordinate_Ioc K hab.le i)
      (fun u i ↦ ?_) (fun u ↦ ?_)
    · have hmem := hR (edgeVertices_fst_mem K u).1
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (by simpa [Real.norm_eq_abs] using Point.abs_apply_le_norm _ i) hmem
    · rw [planeCrossProduct_tangentVector, (edgeVertices_fst_mem K u).2]
  have hcross2 (K L : ConvexBody Point) :
      ((1 / 2 : ℝ) * ∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b,
        supportValue K t ∂surfaceAreaMeasure L) =
        openIntervalCrossIntegral (F L)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) := by
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : Point)
    refine halfSupportIntegral_eq_openIntervalCrossIntegral K L hab hturn (F L) (hFmeasure L)
      (fun u ↦ (edgeVertices K u).2) R
      (fun i ↦ measurable_negativeVertex_coordinate K hab.le i) (fun u i ↦ ?_) (fun u ↦ ?_)
    · have hmem := hR (edgeVertices_snd_mem K u).1
      rw [Metric.mem_closedBall, dist_zero_right] at hmem
      exact le_trans (by simpa [Real.norm_eq_abs] using Point.abs_apply_le_norm _ i) hmem
    · rw [planeCrossProduct_tangentVector, (edgeVertices_snd_mem K u).2]
  refine ⟨F, hFtoFun, fun K L ↦ ⟨hcross1 K L, hcross2 K L⟩, fun K ↦ ?_⟩
  have harea := (convexArc_area a b hab hba).2.1 K
  have hK := hcross1 K K
  rw [harea]
  linarith

/-- Antisymmetry of the vertex cross Stieltjes integral over the open interval, up to the two
endpoint corrections: the negative vertices at `b` and the positive vertices at `a`. -/
theorem openIntervalCrossIntegral_antisymm {a b : ℝ} (hab : a < b)
    (K L : ConvexBody Point) (FK FL : Fin 2 → RightContinuousIntervalBV a b)
    (hFK : ∀ i t, (FK i).toFun t =
      (edgeVertices K (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i)
    (hFL : ∀ i t, (FL i).toFun t =
      (edgeVertices L (((t : Set.Icc a b) : ℝ) : Real.Angle)).1 i) :
    openIntervalCrossIntegral FL (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2) -
        openIntervalCrossIntegral FK (fun t ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1) =
      segmentArea (edgeVertices K (b : Real.Angle)).2 (edgeVertices L (b : Real.Angle)).2 -
        segmentArea (edgeVertices K (a : Real.Angle)).1 (edgeVertices L (a : Real.Angle)).1 := by
  have key (i j : Fin 2) :
      intervalStieltjesIntegral (FL j)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2 i)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} +
        intervalStieltjesIntegral (FK i)
          (fun t ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1 j)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
      (edgeVertices K (b : Real.Angle)).2 i * (edgeVertices L (b : Real.Angle)).2 j -
        (edgeVertices K (a : Real.Angle)).1 i * (edgeVertices L (a : Real.Angle)).1 j := by
    have h := intervalStieltjes_integration_by_parts_Ioo a b hab (FK i) (FL j)
    have h1 : intervalStieltjesIntegral (FL j) (Function.leftLim (FK i).toFun)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} =
        intervalStieltjesIntegral (FL j)
          (fun t ↦ (edgeVertices K ((t : ℝ) : Real.Angle)).2 i)
          {t : Set.Icc a b | a < (t : ℝ) ∧ (t : ℝ) < b} :=
      VectorMeasure.setIntegral_congr_fun
        (fun t ht ↦ leftLim_positiveVertex_coordinate K FK hFK i t ht.1)
    have h2 : (FL j).toFun =
        fun t : Set.Icc a b ↦ (edgeVertices L ((t : ℝ) : Real.Angle)).1 j :=
      funext (hFL j)
    rw [h1, leftLim_positiveVertex_coordinate K FK hFK i ⟨b, hab.le, le_rfl⟩ hab,
      leftLim_positiveVertex_coordinate L FL hFL j ⟨b, hab.le, le_rfl⟩ hab,
      hFK i ⟨a, le_rfl, hab.le⟩, hFL j ⟨a, le_rfl, hab.le⟩, h2] at h
    exact h
  have k01 := key 0 1
  have k10 := key 1 0
  simp only [openIntervalCrossIntegral, segmentArea, planeCrossProduct]
  linarith

end MovingSofa
