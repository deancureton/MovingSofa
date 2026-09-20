import MovingSofa.Polygon.Polyline.Projection
import MovingSofa.Cap.Polyline
import MovingSofa.Cap.AngleDomain
import MovingSofa.Cap.Vertical
import MovingSofa.Analysis.SurfaceMeasure.DiscreteBounds

noncomputable section

namespace MovingSofa

/-- Balance bounds the polyline projections by the surface-area atoms. -/
theorem polygonCapPolyline_inner_le_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ) (s : ℝ)
    {q : Point} (hq : q ∈ (polygonCapPolyline K).carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ ((capVertices K.val 0).1.2) (normalVector (s : Real.Angle)) +
      ∑ u ∈ D, (surfaceAreaMeasure K.val.val {(u : Real.Angle)}).toReal *
        max (Real.sin (s - u)) 0 := by
  classical
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  have hmem (u : ℝ) (hu : u ∈ D) : u ∈ angleDomain Θ := by
    rw [← hD]
    exact hu
  have hb := (polygonCapPolyline K).inner_le_endpoint_add_sum_normal_lengths D
    (fun u hu ↦ angleDomain_subset_Ioo Θ (hmem u hu))
    (fun i ↦ by
      obtain ⟨t, ht⟩ := hp.2.2.2.1 i
      refine ⟨t.val, ?_, ht⟩
      have := t.property
      simpa only [← hD, Finset.mem_coe] using this) s hq
  rw [hp.2.2.1] at hb
  convert hb using 2
  apply Finset.sum_congr rfl
  intro u hu
  have heq := hK ⟨u, hmem u hu⟩
  rw [heq, ENNReal.toReal_ofReal]
  · rfl
  · unfold polygonCapPolylineLength
    positivity

/-- A balanced polygon cap bounds every upper-normal projection of its polyline. -/
theorem polygonCapPolyline_inner_le_support_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K)
    (D : Finset ℝ) (hD : (D : Set ℝ) = angleDomain Θ)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 Real.pi)
    {q : Point} (hq : q ∈ (polygonCapPolyline K).carrier) :
    inner ℝ q (normalVector (s : Real.Angle)) ≤ supportValue K.val.val (s : Real.Angle) := by
  have hpoly := polygonCapPolyline_inner_le_of_balanced K hK D hD s hq
  have hsum := sum_surfaceAreaMeasure_mul_pos_sin_le K.val.val D
    (fun t ht ↦ angleDomain_subset_Ioo Θ (by rw [← hD]; exact ht)) hs
  have hstart := inner_negativeVertex_zero_le_positiveVertex K.val.val ⟨hs.1.le, hs.2.le⟩
  change inner ℝ q (normalVector (s : Real.Angle)) ≤
    inner ℝ (edgeVertices K.val.val 0).2 (normalVector (s : Real.Angle)) + _ at hpoly
  rw [real_inner_comm (normalVector (s : Real.Angle)) (edgeVertices K.val.val 0).2] at hpoly
  linarith

/-- The polyline of a balanced polygon cap lies inside the cap. -/
theorem polygonCapPolyline_subset_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K) :
    (polygonCapPolyline K).carrier ⊆ (K.val.val : Set Point) := by
  classical
  let D := Θ.directions ∪ Θ.directions.image (fun t ↦ t + Real.pi / 2) ∪
    {Θ.angle, Real.pi / 2}
  have hD : (D : Set ℝ) = angleDomain Θ := by
    simp [D, angleDomain]
  intro q hq
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [hp.2.2.2.2.2.1]
    exact Or.inl (Or.inr hq)
  have hfan : q ∈ capFan Θ.angle := by
    have hmem := frontier_subset_closure hfront
    rw [hp.2.2.2.2.1.closure_eq] at hmem
    exact hmem.1
  rw [K.property.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · exact polygonCapPolyline_inner_le_support_of_balanced K hK D hD
      (angleDomain_subset_Ioo Θ ht) hq
  rcases ha with rfl | rfl
  · change inner ℝ q (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan.1
  · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
      congr 1
      ring
    change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hang, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hfan.2

/-- A polygon niche lies in its cap whenever its upper boundary polyline does. -/
theorem polygonNiche_subset_of_polyline_subset {Θ : AngleSet}
    (K : PolygonCapSpace Θ)
    (hpoly : (polygonCapPolyline K).carrier ⊆ (K.val.val : Set Point)) :
    polygonNiche Θ K.val ⊆ (K.val.val : Set Point) := by
  intro q hq
  have hfan : q ∈ capFan Θ.angle := hq.1
  have hheight : q 1 < capBoundaryHeight K (q 0) := by
    by_contra hn
    have hmem : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := by
      rw [capFan_sdiff_polygonNiche_eq_epigraph K]
      exact le_of_not_gt hn
    exact hmem.2 hq
  let r := pointOnGraph (capBoundaryHeight K) (q 0)
  have hrx : r 0 = q 0 := by simp [r, pointOnGraph]
  have hry : q 1 < r 1 := by simpa [r, pointOnGraph] using hheight
  have hrfront : r ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [(capFan_sdiff_polygonNiche_closed_frontier K).2]
    exact ⟨q 0, rfl⟩
  have hp : IsCapPolyline K (polygonCapPolyline K) := (polygonCap_polyline K).choose_spec
  rw [hp.2.2.2.2.2.1] at hrfront
  have hrpoly : r ∈ (polygonCapPolyline K).carrier := by
    rcases hrfront with (hrleft | hrpoly) | hrright
    · obtain ⟨c, hc, hr⟩ := hrleft
      have hrzero : inner ℝ r (normalVector (Θ.angle : Real.Angle)) = 0 := by
        rw [hr, capVertices_angle_fst_eq K, inner_add_left,
          real_inner_smul_left, real_inner_smul_left]
        have hz : inner ℝ (tangentVector (Θ.angle : Real.Angle))
            (normalVector (Θ.angle : Real.Angle)) = 0 := by
          rw [real_inner_comm (normalVector (Θ.angle : Real.Angle))]
          exact inner_normalVector_tangentVector Θ.angle
        rw [hz]
        ring
      have hqnonneg := hfan.1
      change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hqnonneg
      have hs : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
        (by linarith [Θ.angle_le, Real.pi_pos])
      simp [normalVector, frame, PiLp.inner_apply, hrx] at hrzero hqnonneg
      exfalso
      nlinarith
    · exact hrpoly
    · obtain ⟨c, hc, hr⟩ := hrright
      have hrzero : r 1 = 0 := by
        rw [hr, capVertices_zero_snd_eq K]
        simp [normalVector, frame]
      have hqnonneg := hfan.2
      change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqnonneg
      simp [normalVector, frame, PiLp.inner_apply] at hqnonneg
      exfalso
      linarith
  exact K.val.mem_of_fst_eq_of_snd_le (hpoly hrpoly) hfan hrx.symm hry.le

/-- Every balanced polygon cap contains its polygon niche. -/
theorem polygonNiche_subset_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hK : IsBalancedPolygonCap K) :
    polygonNiche Θ K.val ⊆ (K.val.val : Set Point) :=
  polygonNiche_subset_of_polyline_subset K (polygonCapPolyline_subset_of_balanced K hK)

end MovingSofa
