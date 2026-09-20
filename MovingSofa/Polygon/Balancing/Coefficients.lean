import MovingSofa.Polygon.Polyline.Length

noncomputable section
namespace MovingSofa

/-- A convex body's frontier on a supporting line is its exposed edge. -/
theorem frontier_inter_supportingLine_eq_exposedEdge (K : ConvexBody Point)
    (t : Real.Angle) :
    frontier (K : Set Point) ∩ normalLine t (supportValue K t) = exposedEdge K t := by
  ext p
  constructor
  · rintro ⟨hp, hline⟩
    exact ⟨K.isCompact.isClosed.closure_subset (frontier_subset_closure hp), hline⟩
  · intro hp
    refine ⟨mem_frontier_of_mem_of_isExteriorNormal K (a := t) hp.1 ?_, hp.2⟩
    intro q hq
    change inner ℝ (q - p) (normalVector t) ≤ 0
    rw [inner_sub_left, show inner ℝ p (normalVector t) = supportValue K t from hp.2]
    exact sub_nonpos.mpr (inner_le_supportValue K hq t)

/-- The surface-area atom is the length of the frontier on its supporting line. -/
theorem hausdorffMeasure_frontier_inter_supportingLine (K : ConvexBody Point)
    (t : Real.Angle) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (K : Set Point) ∩ normalLine t (supportValue K t)) =
      surfaceAreaMeasure K {t} := by
  rw [frontier_inter_supportingLine_eq_exposedEdge]
  exact (surfaceAreaMeasure_atom_length K t).1.symm

/-- An endpoint cap's lower wall has the surface-area atom of the opposite normal. -/
theorem hausdorffMeasure_frontier_inter_lowerLine_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (K.val.val : Set Point) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)) =
      surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)} := by
  have htSupport : supportValue K.val.val (t : Real.Angle) = 1 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · subst t
      exact K.val.property.2.2.1
    · have ht' := Set.mem_singleton_iff.mp ht
      subst t
      exact K.val.property.2.2.2.1
  have htOpposite :
      supportValue K.val.val ((t + Real.pi : ℝ) : Real.Angle) = 0 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · subst t
      exact K.val.property.2.2.2.2.1
    · have ht' := Set.mem_singleton_iff.mp ht
      subst t
      convert K.val.property.2.2.2.2.2.1 using 1
      ring_nf
  rw [htSupport, sub_self, show normalLine (t : Real.Angle) 0 =
      normalLine ((t + Real.pi : ℝ) : Real.Angle) 0 by
    ext p
    change inner ℝ p (normalVector (t : Real.Angle)) = 0 ↔
      inner ℝ p (normalVector ((t : Real.Angle) + Real.pi)) = 0
    rw [normalVector_add_pi_angle]
    simp]
  rw [← htOpposite]
  exact hausdorffMeasure_frontier_inter_supportingLine K.val.val _

/-- Away from endpoint normals, the niche boundary on the lower wall has polyline length. -/
theorem nicheBoundaryLength_lowerLine_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K
        (normalLine (t.val : Real.Angle)
          (supportValue K.val.val (t.val : Real.Angle) - 1)) =
      polygonCapPolylineLength K t := by
  rw [show polygonCapPolylineLength K t = polygonPolylineLengthAt K t.val by
    simp [polygonPolylineLengthAt, t.property]]
  rcases t.property with htInner | htEndpoint
  · rcases htInner with htDirection | ⟨s, hs, hst⟩
    · have hline := (rotatingHallwayParts_formulas
        (K.val.val : Set Point) (t.val : Real.Angle)).2.2.2.2.1
      rw [← hline]
      exact ((polygonCap_polyline_lengths K).1 t.val htDirection).1
    · have hline := (rotatingHallwayParts_formulas
        (K.val.val : Set Point) (s : Real.Angle)).2.2.2.2.2.2.1
      rw [← hst]
      change nicheBoundaryLength K
          (normalLine ((s + Real.pi / 2 : ℝ) : Real.Angle)
            (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)) =
        polygonPolylineLengthAt K (s + Real.pi / 2)
      have hline' :
          (rotatingHallwayParts (K.val.val : Set Point) (s : Real.Angle)).d =
            normalLine ((s + Real.pi / 2 : ℝ) : Real.Angle)
              (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
        simpa only [Real.Angle.coe_add] using hline
      rw [← hline']
      exact ((polygonCap_polyline_lengths K).1 s hs).2.2.1
  · exact False.elim (ht htEndpoint)

/-- At an endpoint normal, the lower-wall niche length is the opposite-face length
minus the polyline length. -/
theorem nicheBoundaryLength_lowerLine_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K
        (normalLine (t.val : Real.Angle)
          (supportValue K.val.val (t.val : Real.Angle) - 1)) =
      (surfaceAreaMeasure K.val.val
        {((t.val + Real.pi : ℝ) : Real.Angle)}).toReal -
        polygonCapPolylineLength K t := by
  have htSupport : supportValue K.val.val (t.val : Real.Angle) = 1 := by
    rcases Set.mem_insert_iff.mp ht with ht | ht
    · rw [ht]
      exact K.val.property.2.2.1
    · rw [Set.mem_singleton_iff.mp ht]
      exact K.val.property.2.2.2.1
  rw [htSupport, sub_self]
  simpa [polygonPolylineLengthAt, t.property] using
    (polygonCap_polyline_lengths K).2 t.val ht |>.1

end MovingSofa
