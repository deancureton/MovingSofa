import MovingSofa.Analysis.SurfaceMeasure.Construction
import MovingSofa.Analysis.SurfaceMeasure.SegmentFaces
import MovingSofa.ForMathlib.MeasureTheory.Angle

noncomputable section

open MeasureTheory

namespace MovingSofa


private theorem mem_exposedEdge_iff_isExteriorNormal (K : ConvexBody Point)
    {p : Point} (hp : p ∈ K) (t : Real.Angle) :
    p ∈ exposedEdge K t ↔ IsExteriorNormal K p t := by
  constructor
  · intro h q hq
    have he : inner ℝ p (normalVector t) = supportValue K t := h.2
    rw [inner_sub_left, he]
    exact sub_nonpos.mpr (inner_le_supportValue K hq t)
  · intro h
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact sub_nonpos.mp (by simpa only [inner_sub_left] using h q hq)

private theorem mem_exposedEdge_iff_exteriorNormalAngle_eq (K : ConvexBody Point)
    {p : Point} (hp : p ∈ regularBoundary K) (t : Real.Angle) :
    p ∈ exposedEdge K t ↔ exteriorNormalAngle K p = t := by
  have hpK : p ∈ K := by
    change p ∈ (K : Set Point)
    simpa only [K.isCompact.isClosed.closure_eq] using frontier_subset_closure hp.1
  rw [mem_exposedEdge_iff_isExteriorNormal K hpK]
  have hn : IsExteriorNormal K p (exteriorNormalAngle K p) := by
    simp only [exteriorNormalAngle, dite_eq_left hp.2]
    exact hp.2.exists.choose_spec
  exact ⟨fun ht ↦ hp.2.unique hn ht, fun ht ↦ ht ▸ hn⟩

private theorem faceUnion_inter_regularBoundary (K : ConvexBody Point) (E : Set Real.Angle) :
    (⋃ t ∈ E, exposedEdge K t) ∩ regularBoundary K =
      exteriorNormalAngle K ⁻¹' E ∩ regularBoundary K := by
  ext p
  constructor
  · rintro ⟨hp, hreg⟩
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    refine ⟨?_, hreg⟩
    change exteriorNormalAngle K p ∈ E
    rwa [(mem_exposedEdge_iff_exteriorNormalAngle_eq K hreg t).mp hp]
  · rintro ⟨hp, hreg⟩
    exact ⟨Set.mem_iUnion₂.mpr ⟨exteriorNormalAngle K p, hp,
      (mem_exposedEdge_iff_exteriorNormalAngle_eq K hreg _).mpr rfl⟩, hreg⟩

private theorem surfaceAreaMeasure_face_union_of_interior_nonempty (K : ConvexBody Point)
    (hK : (interior (K : Set Point)).Nonempty)
    (E : Set Real.Angle) (hE : MeasurableSet E) :
    surfaceAreaMeasure K E = Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  simp only [surfaceAreaMeasure,
    ite_eq_right (not_subsingleton_of_interior_nonempty K hK),
    dite_eq_right (not_exists_segmentPresentation_of_interior_nonempty K hK)]
  rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_exteriorNormalAngle_restrict_regularBoundary K _) hE,
    Measure.restrict_apply' (measurableSet_regularBoundary K),
    ← faceUnion_inter_regularBoundary]
  apply measure_congr
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (fun p hp ↦ (hp.2 hp.1.1).elim) measure_empty
  · apply measure_mono_null ?_ (hausdorffMeasure_irregularBoundary_eq_zero K hK)
    rintro p ⟨hp, hnot⟩
    refine ⟨?_, fun hreg ↦ hnot ⟨hp, hreg⟩⟩
    obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hp
    exact mem_frontier_of_mem_of_isExteriorNormal K hpt.1
      ((mem_exposedEdge_iff_isExteriorNormal K hpt.1 t).mp hpt)

private theorem surfaceAreaMeasure_face_union_of_subsingleton (K : ConvexBody Point)
    (hK : (K : Set Point).Subsingleton) (E : Set Real.Angle) :
    surfaceAreaMeasure K E = Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t) := by
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton K hK]
  change 0 = _
  symm
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  obtain ⟨p, hp⟩ := K.nonempty
  apply measure_mono_null (t := {p})
  · intro q hq
    obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.mp hq
    exact hK hqt.1 hp
  · simp


theorem surfaceAreaMeasure_face_union (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) ∧
    ((K : Set Point).Subsingleton → surfaceAreaMeasure K = 0) ∧
    (∀ d, IsSegmentPresentation K d → surfaceAreaMeasure K =
      ENNReal.ofReal (dist d.1 d.2.1) •
        (Measure.dirac d.2.2 + Measure.dirac (d.2.2 + ((Real.pi : ℝ) : Real.Angle)))) ∧
    ((interior (K : Set Point)).Nonempty → surfaceAreaMeasure K =
      Measure.map (exteriorNormalAngle K)
        ((Measure.hausdorffMeasure 1).restrict (regularBoundary K))) ∧
    (∀ E : Set Real.Angle, MeasurableSet E →
      ((interior (K : Set Point)).Nonempty ∨
        ∃ a b : ℝ, a ≤ b ∧ b < a + Real.pi ∧
          E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) →
      surfaceAreaMeasure K E =
        Measure.hausdorffMeasure 1 (⋃ t ∈ E, exposedEdge K t)) := by
  obtain ⟨hfinite, hpoint, hsegment, _, _⟩ := surfaceAreaMeasure_construction K
  refine ⟨hfinite, hpoint, hsegment, ?_, ?_⟩
  · intro hK
    simp only [surfaceAreaMeasure,
      ite_eq_right (not_subsingleton_of_interior_nonempty K hK),
      dite_eq_right (not_exists_segmentPresentation_of_interior_nonempty K hK)]
  · intro E hE hdomain
    by_cases hsub : (K : Set Point).Subsingleton
    · exact surfaceAreaMeasure_face_union_of_subsingleton K hsub E
    by_cases hint : (interior (K : Set Point)).Nonempty
    · exact surfaceAreaMeasure_face_union_of_interior_nonempty K hint E hE
    obtain ⟨a, b, hab, hwidth, hsubset⟩ := hdomain.resolve_left hint
    have hseg := exists_segmentPresentation_of_interior_empty K hsub
      (Set.not_nonempty_iff_eq_empty.mp hint)
    obtain ⟨d, hd⟩ := hseg
    exact surfaceAreaMeasure_face_union_of_segmentPresentation K d hd E hE hab hwidth hsubset

instance isFiniteMeasure_surfaceAreaMeasure (K : ConvexBody Point) :
    IsFiniteMeasure (surfaceAreaMeasure K) := (surfaceAreaMeasure_face_union K).1

/-- A measurable set of normal directions lying in an angular interval of width less than `π`,
on which every face of `K` degenerates to one and the same point, is null for the surface area
measure of `K`. -/
theorem surfaceAreaMeasure_null_of_exposedEdge_subset_singleton (K : ConvexBody Point)
    {E : Set Real.Angle} (hE : MeasurableSet E) {a b : ℝ} (hab : a ≤ b) (hba : b < a + Real.pi)
    (hEab : E ⊆ (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc a b) (p : Point)
    (hsub : ∀ t ∈ E, exposedEdge K t ⊆ {p}) :
    surfaceAreaMeasure K E = 0 := by
  let _ := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  rw [(surfaceAreaMeasure_face_union K).2.2.2.2 E hE (Or.inr ⟨a, b, hab, hba, hEab⟩)]
  refine measure_mono_null (t := {p}) ?_ (by simp)
  intro x hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hx
  exact hsub t ht hxt

/-- The surface measure of a convex body vanishes on the open angular window strictly between two
normal angles less than a half turn apart at which one and the same point attains the support. -/
theorem surfaceAreaMeasure_angleImage_Ioo_eq_zero_of_mem_exposedEdge (K : ConvexBody Point)
    {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi) {p : Point}
    (hpa : p ∈ exposedEdge K (a : Real.Angle))
    (hpb : p ∈ exposedEdge K (b : Real.Angle)) :
    surfaceAreaMeasure K ((fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioo a b) = 0 := by
  refine surfaceAreaMeasure_null_of_exposedEdge_subset_singleton K
    (Real.Angle.isOpen_image_Ioo a b).measurableSet hab.le hba
    (Set.image_mono Set.Ioo_subset_Icc_self) p fun t ht ↦ ?_
  obtain ⟨s, hs, rfl⟩ := ht
  exact (exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo hba hs hpa hpb).subset

end MovingSofa
