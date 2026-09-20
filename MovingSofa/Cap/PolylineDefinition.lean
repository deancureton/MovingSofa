import MovingSofa.Cap.PolylineBoundary

noncomputable section

namespace MovingSofa

def openRay (p v : Point) : Set Point :=
  {q | ∃ s : ℝ, 0 < s ∧ q = p + s • v}

def IsCapPolyline {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (p : XMonotonePolylineData) : Prop :=
  0 < p.edges ∧
  p.vertices 0 = (capVertices K.val Θ.angle).2.1 ∧
  p.vertices (Fin.last p.edges) = (capVertices K.val 0).1.2 ∧
  (∀ i : Fin p.edges, ∃ t : angleDomain Θ,
    inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t.val : Real.Angle)) = 0) ∧
  IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) ∧
  frontier (capFan Θ.angle \ polygonNiche Θ K.val) =
    openRay ((capVertices K.val Θ.angle).2.1) (tangentVector (Θ.angle : Real.Angle)) ∪
      p.carrier ∪ openRay ((capVertices K.val 0).1.2) (normalVector 0) ∧
  Disjoint (openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle))) p.carrier ∧
  Disjoint p.carrier (openRay ((capVertices K.val 0).1.2) (normalVector 0)) ∧
  Disjoint (openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle)))
    (openRay ((capVertices K.val 0).1.2) (normalVector 0))

theorem polygonCap_polyline {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    ∃ p : XMonotonePolylineData, IsCapPolyline K p := by
  let C := (capVertices K.val Θ.angle).2.1
  let A := (capVertices K.val 0).1.2
  have hCA : C 0 < A 0 := polygonCap_left_x_lt_right_x K
  obtain ⟨p, hpedge, hpC, hpA, hcarrier, hedge⟩ :=
    exists_capBoundary_graphPolyline K hCA
  refine ⟨p, hpedge, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpC]
    exact pointOnGraph_capBoundaryHeight_leftEndpoint K
  · rw [hpA]
    exact pointOnGraph_capBoundaryHeight_rightEndpoint K
  · intro i
    obtain ⟨t, ht, hi⟩ := hedge i
    exact ⟨⟨t, ht⟩, hi⟩
  · exact (capFan_sdiff_polygonNiche_closed_frontier K).1
  · rw [(capFan_sdiff_polygonNiche_closed_frontier K).2,
      show openRay ((capVertices K.val Θ.angle).2.1)
        (tangentVector (Θ.angle : Real.Angle)) = _ by
          simpa [openRay] using capLeftOpenRay_eq_graph_image K,
      show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
          simpa [openRay] using capRightOpenRay_eq_graph_image K, hcarrier]
    ext q
    constructor
    · rintro ⟨x, rfl⟩
      rcases lt_or_ge x (C 0) with hx | hx
      · apply Or.inl
        apply Or.inl
        exact ⟨x, by simpa [C] using hx, rfl⟩
      · rcases le_or_gt x (A 0) with hxA | hxA
        · apply Or.inl
          apply Or.inr
          exact ⟨x, ⟨hx, hxA⟩, rfl⟩
        · apply Or.inr
          exact ⟨x, by simpa [A] using hxA, rfl⟩
    · rintro ((⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) | ⟨x, hx, rfl⟩) <;>
        exact ⟨x, rfl⟩
  · rw [show openRay ((capVertices K.val Θ.angle).2.1)
      (tangentVector (Θ.angle : Real.Angle)) = _ by
        simpa [openRay] using capLeftOpenRay_eq_graph_image K, hcarrier]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x < C 0 := by simpa [C] using hx
    exact (not_lt_of_ge hy.1) hx'
  · rw [hcarrier, show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
      simpa [openRay] using capRightOpenRay_eq_graph_image K]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hy' : A 0 < x := by simpa [A] using hy
    exact (not_lt_of_ge hx.2) hy'
  · rw [show openRay ((capVertices K.val Θ.angle).2.1)
      (tangentVector (Θ.angle : Real.Angle)) = _ by
        simpa [openRay] using capLeftOpenRay_eq_graph_image K,
    show openRay ((capVertices K.val 0).1.2) (normalVector 0) = _ by
      simpa [openRay] using capRightOpenRay_eq_graph_image K]
    apply pointOnGraph_image_disjoint
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' : x < C 0 := by simpa [C] using hx
    have hy' : A 0 < x := by simpa [A] using hy
    linarith

end MovingSofa
