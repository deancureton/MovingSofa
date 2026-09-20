import MovingSofa.Polygon.Polyline.Length.Boundary
import MovingSofa.Cap.UpperBoundary.Polygon

noncomputable section

namespace MovingSofa

theorem polygonCap_polyline_lengths {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    (∀ t ∈ Θ.directions,
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).b =
        polygonPolylineLengthAt K t ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).bRay =
        polygonPolylineLengthAt K t ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).d =
        polygonPolylineLengthAt K (t + Real.pi / 2) ∧
      nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).dRay =
        polygonPolylineLengthAt K (t + Real.pi / 2)) ∧
    (∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      nicheBoundaryLength K (normalLine t 0) =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t ∧
      (MeasureTheory.Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine t 0)).toReal =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t) := by
  exact ⟨fun _ ht ↦ polygonNiche_wall_lengths K ht,
    fun _ ht ↦ polygonNiche_fanLine_lengths K ht⟩

private lemma polygonCapPolyline_sum_length_mul_sin {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ) :
    ∑ t ∈ D, polygonPolylineLengthAt K t * Real.sin t =
      ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
  classical
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := (polygonCap_polyline K).choose_spec
  have hmem (t : ℝ) : t ∈ D ↔ t ∈ angleDomain Θ := by
    change t ∈ (D : Set ℝ) ↔ _
    rw [hD]
  have h := p.sum_normal_lengths_mul_sin D
    (fun t ht ↦ angleDomain_subset_Ioo Θ ((hmem t).mp ht)) (by
      intro i
      obtain ⟨t, ht⟩ := hp.2.2.2.1 i
      exact ⟨t.val, (hmem t.val).mpr t.property, ht⟩)
  have heq : ∑ t ∈ D, polygonPolylineLengthAt K t * Real.sin t =
      ∑ t ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t := by
    apply Finset.sum_congr rfl
    intro t ht
    simp only [polygonPolylineLengthAt, dite_eq_left ((hmem t).mp ht), polygonCapPolylineLength]
    rfl
  rw [heq, h, hp.2.1, hp.2.2.1]

theorem polygonCap_not_balanced_positive {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (h : ¬ IsBalancedPolygonCap K) :
    ∃ t : angleDomain Θ,
      ENNReal.ofReal (polygonCapPolylineLength K t) <
        surfaceAreaMeasure K.val.val {(t.val : Real.Angle)} := by
  classical
  by_contra hnot
  push Not at hnot
  have hfinite : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union (Set.toFinite _)
  let D := hfinite.toFinset
  have hD : (D : Set ℝ) = angleDomain Θ := hfinite.coe_toFinset
  have hne : D.Nonempty := by
    refine ⟨Θ.angle, ?_⟩
    change Θ.angle ∈ hfinite.toFinset
    simp [angleDomain]
  have hmem (t : ℝ) : t ∈ D ↔ t ∈ angleDomain Θ := by
    change t ∈ (D : Set ℝ) ↔ _
    rw [hD]
  have hpoly (t : angleDomain Θ) : 0 ≤ polygonCapPolylineLength K t := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg (fun _ _ ↦ by split_ifs <;> positivity)
  have htop (t : ℝ) : surfaceAreaMeasure K.val.val {(t : Real.Angle)} ≠ ⊤ := by
    rw [(surfaceAreaMeasure_atom_length K.val.val (t : Real.Angle)).2.1]
    exact ENNReal.ofReal_ne_top
  have hle (t : ℝ) (ht : t ∈ D) :
      (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal ≤ polygonPolylineLengthAt K t := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hnot ⟨t, (hmem t).mp ht⟩)
    simpa [polygonPolylineLengthAt, (hmem t).mp ht, ENNReal.toReal_ofReal
      (hpoly ⟨t, (hmem t).mp ht⟩)] using hh
  have hsum : ∑ t ∈ D,
      (polygonPolylineLengthAt K t -
        (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal) * Real.sin t = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, polygonCapPolyline_sum_length_mul_sin K D hD]
    have hh := K.sum_hausdorffMeasure_exposedEdge_mul_sin D hne hD
    have heq : ∑ t ∈ D,
        (surfaceAreaMeasure K.val.val {(t : Real.Angle)}).toReal * Real.sin t =
        ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
      simpa only [(surfaceAreaMeasure_atom_length K.val.val _).1] using hh
    rw [heq, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun t ht ↦
    mul_nonneg (sub_nonneg.mpr (hle t ht))
      (Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ ((hmem t).mp ht)).1
        (angleDomain_subset_Ioo Θ ((hmem t).mp ht)).2).le)).mp hsum
  apply h
  intro t
  have ht := (hmem t.val).mpr t.property
  have hz := hzero t.val ht
  have hs := Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ t.property).1
    (angleDomain_subset_Ioo Θ t.property).2
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hs.ne')
  apply (ENNReal.toReal_eq_toReal_iff' (htop t.val) ENNReal.ofReal_ne_top).mp
  simpa [polygonPolylineLengthAt, t.property, ENNReal.toReal_ofReal (hpoly t)] using heq.symm

end MovingSofa
