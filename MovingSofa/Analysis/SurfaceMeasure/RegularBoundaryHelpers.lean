import MovingSofa.Analysis.SurfaceMeasure.SegmentGraph
import MovingSofa.Analysis.SurfaceMeasure.UpperGraph
import MovingSofa.ForMathlib.Convex.Body.BoundaryMeasure

noncomputable section

open MeasureTheory

namespace MovingSofa

/-- A planar convex body with nonempty interior has no segment presentation. -/
theorem not_exists_segmentPresentation_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : ¬ ∃ d, IsSegmentPresentation K d := by
  rintro ⟨d, hd⟩
  have htop : affineSpan ℝ (K : Set Point) = ⊤ :=
    K.convex.interior_nonempty_iff_affineSpan_eq_top.mp hint
  have hle : affineSpan ℝ (K : Set Point) ≤ affineSpan ℝ ({d.1, d.2.1} : Set Point) := by
    rw [hd.2.1]
    apply affineSpan_le.2
    exact (affineSpan ℝ ({d.1, d.2.1} : Set Point)).convex.segment_subset
      (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))
  rw [htop] at hle
  have heq : affineSpan ℝ ({d.1, d.2.1} : Set Point) = ⊤ := top_unique hle
  have hfin := (collinear_iff_finrank_le_one.mp (collinear_pair ℝ d.1 d.2.1))
  rw [← direction_affineSpan, heq] at hfin
  rw [AffineSubspace.direction_top ℝ Point Point, finrank_top] at hfin
  norm_num [Point, finrank_euclideanSpace_fin] at hfin

/-- A convex body with nonempty interior is not a singleton. -/
theorem not_subsingleton_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : ¬ (K : Set Point).Subsingleton := by
  intro hsub
  obtain ⟨p, hp⟩ := K.nonempty
  have hK : (K : Set Point) = {p} :=
    Set.eq_singleton_iff_unique_mem.mpr ⟨hp, fun x hx ↦ hsub hx hp⟩
  rw [hK, interior_singleton] at hint
  exact hint.ne_empty rfl

private theorem surfaceAreaMeasure_eq_map_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) :
    surfaceAreaMeasure K = Measure.map (exteriorNormalAngle K)
      ((Measure.hausdorffMeasure 1).restrict (regularBoundary K)) := by
  have hsub := not_subsingleton_of_interior_nonempty K hint
  have hseg := not_exists_segmentPresentation_of_interior_nonempty K hint
  simp [surfaceAreaMeasure, hsub, hseg]

/-- Surface area measure is finite when the convex body has nonempty interior. -/
theorem isFiniteMeasure_surfaceAreaMeasure_of_interior_nonempty (K : ConvexBody Point)
    (hint : (interior (K : Set Point)).Nonempty) : IsFiniteMeasure (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_map_of_interior_nonempty K hint]
  let μ := (Measure.hausdorffMeasure 1).restrict (regularBoundary K)
  have hμ : μ Set.univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono fun p hp ↦ hp.1)
      (K.hausdorffMeasure_frontier_lt_top hint)
  let _ : IsFiniteMeasure μ := ⟨hμ⟩
  exact Measure.isFiniteMeasure_map μ (exteriorNormalAngle K)

/-- Any extension of the exterior-normal angle from the regular boundary gives
the surface area measure as a pushforward of frontier length. -/
theorem surfaceAreaMeasure_eq_map_frontier_of_eq_on_regularBoundary
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    (ν : Point → Real.Angle)
    (hν : ∀ p ∈ regularBoundary K, ν p = exteriorNormalAngle K p) :
    surfaceAreaMeasure K = Measure.map ν
      ((Measure.hausdorffMeasure 1).restrict (frontier (K : Set Point))) := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  have hregular : regularBoundary K ⊆ frontier (K : Set Point) := fun _ hp ↦ hp.1
  have hae : frontier (K : Set Point) =ᵐ[μ] regularBoundary K := by
    rw [ae_eq_set]
    exact ⟨hausdorffMeasure_irregularBoundary_eq_zero K hK,
      measure_mono_null (fun _ hp ↦ (hp.2 (hregular hp.1)).elim) measure_empty⟩
  have hrestrict : μ.restrict (frontier (K : Set Point)) =
      μ.restrict (regularBoundary K) := Measure.restrict_congr_set hae
  rw [surfaceAreaMeasure_eq_map_of_interior_nonempty K hK, hrestrict]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_regularBoundary K)] with p hp
  exact (hν p hp).symm


end MovingSofa
