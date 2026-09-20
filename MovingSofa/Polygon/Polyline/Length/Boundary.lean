import MovingSofa.Polygon.Polyline.Length.Basic
import MovingSofa.Polygon.Polyline.Measure
import MovingSofa.Geometry.HallwayRay

noncomputable section

open MeasureTheory

namespace MovingSofa

private lemma fst_mem_Icc_of_mem_segment {a b q : Point}
    (hab : a 0 ≤ b 0) (hq : q ∈ segment ℝ a b) : q 0 ∈ Set.Icc (a 0) (b 0) := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  change a 0 + r * (b 0 - a 0) ∈ Set.Icc (a 0) (b 0)
  constructor <;> nlinarith [hr.1, hr.2]

private theorem frontier_inter_open_eq_frontier_sdiff_open_on_interior
    {F X : Set Point} :
    frontier (F ∩ X) ∩ interior F = frontier (F \ X) ∩ interior F := by
  have hInt : IsOpen (interior F) := isOpen_interior
  calc
    frontier (F ∩ X) ∩ interior F =
        frontier ((F ∩ X) ∩ interior F) ∩ interior F :=
      (frontier_inter_open_inter hInt).symm
    _ = frontier (X ∩ interior F) ∩ interior F := by
      congr 2
      ext p
      simp only [Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨-, hpX⟩, hpF⟩
        exact ⟨hpX, hpF⟩
      · rintro ⟨hpX, hpF⟩
        exact ⟨⟨interior_subset hpF, hpX⟩, hpF⟩
    _ = frontier X ∩ interior F := frontier_inter_open_inter hInt
    _ = frontier Xᶜ ∩ interior F := by rw [frontier_compl]
    _ = frontier (Xᶜ ∩ interior F) ∩ interior F :=
      (frontier_inter_open_inter hInt).symm
    _ = frontier ((F \ X) ∩ interior F) ∩ interior F := by
      congr 2
      ext p
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
      constructor
      · rintro ⟨hpX, hpF⟩
        exact ⟨⟨interior_subset hpF, hpX⟩, hpF⟩
      · rintro ⟨⟨-, hpX⟩, hpF⟩
        exact ⟨hpX, hpF⟩
    _ = frontier (F \ X) ∩ interior F := frontier_inter_open_inter hInt

private theorem frontier_inter_open_symmDiff_subset_frontier
    {F X : Set Point} (hF : IsClosed F) :
    (frontier (F ∩ X) \ frontier (F \ X)) ∪
        (frontier (F \ X) \ frontier (F ∩ X)) ⊆ frontier F := by
  have heq := frontier_inter_open_eq_frontier_sdiff_open_on_interior (F := F) (X := X)
  intro p hp
  by_contra hpF
  have hmemF_of_left (hpN : p ∈ frontier (F ∩ X)) : p ∈ F := by
    have hpcl : p ∈ closure (F ∩ X) := frontier_subset_closure hpN
    exact hF.closure_eq ▸ closure_mono Set.inter_subset_left hpcl
  have hmemF_of_right (hpC : p ∈ frontier (F \ X)) : p ∈ F := by
    have hpcl : p ∈ closure (F \ X) := frontier_subset_closure hpC
    exact hF.closure_eq ▸ closure_mono Set.sdiff_subset hpcl
  rcases hp with hp | hp
  · have hpInt : p ∈ interior F := by
      simpa using (mem_frontier_iff_notMem_interior (hmemF_of_left hp.1)).not.mp hpF
    have : p ∈ frontier (F \ X) ∩ interior F := heq ▸ ⟨hp.1, hpInt⟩
    exact hp.2 this.1
  · have hpInt : p ∈ interior F := by
      simpa using (mem_frontier_iff_notMem_interior (hmemF_of_right hp.1)).not.mp hpF
    have : p ∈ frontier (F ∩ X) ∩ interior F := heq.symm ▸ ⟨hp.1, hpInt⟩
    exact hp.2 this.1

private theorem measure_eq_of_symmDiff_subset_null
    (μ : Measure Point) {A B E : Set Point}
    (hsub : (A \ B) ∪ (B \ A) ⊆ E) (hE : μ E = 0) : μ A = μ B := by
  apply measure_congr
  rw [ae_eq_set]
  constructor
  · exact measure_mono_null (fun _ hp ↦ hsub (Or.inl hp)) hE
  · exact measure_mono_null (fun _ hp ↦ hsub (Or.inr hp)) hE

/-- The fan clipping the niche is closed. -/
theorem isClosed_capFan (ω : ℝ) : IsClosed (capFan ω) := by
  unfold capFan normalHalfPlane
  exact (isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le continuous_const (by fun_prop))

/-- The inward quadrant of a supporting hallway is open. -/
theorem isOpen_innerQuadrant (S : Set Point) (t : ℝ) :
    IsOpen (innerQuadrant S t) := by
  unfold innerQuadrant normalHalfPlane
  exact (isOpen_lt (by fun_prop) continuous_const).inter
    (isOpen_lt (by fun_prop) continuous_const)

private theorem frontier_normalHalfPlane_lower_strict_subset_normalLine
    (t : Real.Angle) (h : ℝ) :
    frontier (normalHalfPlane t h false true) ⊆ normalLine t h := by
  change frontier {p : Point | inner ℝ p (normalVector t) < h} ⊆
    {p | inner ℝ p (normalVector t) = h}
  exact frontier_lt_subset_eq (by fun_prop) continuous_const

private theorem frontier_normalHalfPlane_upper_closed_subset_normalLine
    (t : Real.Angle) (h : ℝ) :
    frontier (normalHalfPlane t h true false) ⊆ normalLine t h := by
  change frontier {p : Point | h ≤ inner ℝ p (normalVector t)} ⊆
    {p | inner ℝ p (normalVector t) = h}
  exact frontier_ge_subset_eq continuous_const (by fun_prop)

private def polygonCapBoundaryLines {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    Finset (Real.Angle × ℝ) := by
  classical
  exact {(((Θ.angle : ℝ) : Real.Angle), 0),
      (((Real.pi / 2 : ℝ) : Real.Angle), 0)} ∪
    Θ.directions.biUnion fun t ↦
      {(((t : ℝ) : Real.Angle), supportValue K.val.val (t : Real.Angle) - 1),
        (((t + Real.pi / 2 : ℝ) : Real.Angle),
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)}

private theorem frontier_capFan_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    frontier (capFan Θ.angle) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  intro p hp
  have hp' := frontier_inter_subset
    (normalHalfPlane (Θ.angle : Real.Angle) 0 true false)
    (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
  rcases hp' with hp' | hp'
  · have hline := frontier_normalHalfPlane_upper_closed_subset_normalLine
      (Θ.angle : Real.Angle) 0 hp'.1
    apply Set.mem_iUnion₂.mpr
    exact ⟨(((Θ.angle : ℝ) : Real.Angle), 0), by simp [polygonCapBoundaryLines], hline⟩
  · have hline := frontier_normalHalfPlane_upper_closed_subset_normalLine
      ((Real.pi / 2 : ℝ) : Real.Angle) 0 hp'.2
    apply Set.mem_iUnion₂.mpr
    exact ⟨(((Real.pi / 2 : ℝ) : Real.Angle), 0),
      by simp [polygonCapBoundaryLines], hline⟩

private theorem frontier_innerQuadrant_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    frontier (innerQuadrant K.val.val t) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  classical
  intro p hp
  have hp' := frontier_inter_subset
    (normalHalfPlane (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · have hline := frontier_normalHalfPlane_lower_strict_subset_normalLine
      (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1) hp'.1
    apply Set.mem_iUnion₂.mpr
    refine ⟨(((t : ℝ) : Real.Angle), supportValue K.val.val (t : Real.Angle) - 1),
      ?_, hline⟩
    simp only [polygonCapBoundaryLines, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩
  · have hline := frontier_normalHalfPlane_lower_strict_subset_normalLine
      ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) hp'.2
    apply Set.mem_iUnion₂.mpr
    refine ⟨(((t + Real.pi / 2 : ℝ) : Real.Angle),
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1), ?_, hline⟩
    simp only [polygonCapBoundaryLines, Finset.mem_union]
    right
    exact Finset.mem_biUnion.mpr ⟨t, ht, by simp⟩

private theorem frontier_polygonComplement_subset_boundaryLines {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    frontier (capFan Θ.angle \ polygonNiche Θ K.val) ⊆
      ⋃ l ∈ polygonCapBoundaryLines K, normalLine l.1 l.2 := by
  let X : Set Point := ⋃ t ∈ Θ.directions, innerQuadrant K.val.val t
  have hset : capFan Θ.angle \ polygonNiche Θ K.val = capFan Θ.angle \ X := by
    simp [polygonNiche, X]
  rw [hset, Set.sdiff_eq]
  intro p hp
  have hp' := frontier_inter_subset (capFan Θ.angle) Xᶜ hp
  rcases hp' with hp | hp
  · exact frontier_capFan_subset_boundaryLines K hp.1
  · have hpX : p ∈ frontier X := by simpa [frontier_compl] using hp.2
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun t ↦ innerQuadrant K.val.val t) hpX
    obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hmem
    exact frontier_innerQuadrant_subset_boundaryLines K ht hpt

private theorem real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
    {v : Point} (hv : v ≠ 0) {s t : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (hvs : inner ℝ v (normalVector (s : Real.Angle)) = 0)
    (hvt : inner ℝ v (normalVector (t : Real.Angle)) = 0) : s = t := by
  apply eq_of_inner_sub_normalVector_eq_zero_of_ne (a := 0) (b := v) hs ht hv.symm
  · simpa using hvs
  · simpa using hvt

private theorem normalLine_inter_normalLine_subsingleton {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hst : s ≠ t) :
    (normalLine (s : Real.Angle) c ∩ normalLine (t : Real.Angle) d).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  have hv : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hsorth : inner ℝ (p - q) (normalVector (s : Real.Angle)) = 0 := by
    have hps : inner ℝ p (normalVector (s : Real.Angle)) = c := hp.1
    have hqs : inner ℝ q (normalVector (s : Real.Angle)) = c := hq.1
    rw [inner_sub_left, hps, hqs, sub_self]
  have htorth : inner ℝ (p - q) (normalVector (t : Real.Angle)) = 0 := by
    have hpt : inner ℝ p (normalVector (t : Real.Angle)) = d := hp.2
    have hqt : inner ℝ q (normalVector (t : Real.Angle)) = d := hq.2
    rw [inner_sub_left, hpt, hqt, sub_self]
  exact hst (real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi hv hs ht hsorth htorth)

private theorem hausdorffMeasure_normalLine_inter_normalLine_eq_zero {s t c d : ℝ}
    (hs : s ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi) (hst : s ≠ t) :
    Measure.hausdorffMeasure 1
      (normalLine (s : Real.Angle) c ∩ normalLine (t : Real.Angle) d) = 0 := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (normalLine_inter_normalLine_subsingleton hs ht hst).countable.measure_zero _

private theorem openRay_inter_hyperplane_subsingleton {p v n : Point} {c : ℝ}
    (hvn : inner ℝ v n ≠ 0) :
    (openRay p v ∩ {q | inner ℝ q n = c}).Subsingleton := by
  rintro x ⟨⟨r, hr, rfl⟩, hxr⟩ y ⟨⟨s, hs, rfl⟩, hyr⟩
  have hrs : r * inner ℝ v n = s * inner ℝ v n := by
    simp only [Set.mem_ofPred_eq, inner_add_left, real_inner_smul_left] at hxr hyr
    linarith
  rw [mul_right_cancel₀ hvn hrs]

private theorem hausdorffMeasure_openRay_inter_hyperplane_eq_zero {p v n : Point} {c : ℝ}
    (hvn : inner ℝ v n ≠ 0) :
    Measure.hausdorffMeasure 1 (openRay p v ∩ {q | inner ℝ q n = c}) = 0 := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (openRay_inter_hyperplane_subsingleton hvn).countable.measure_zero _

private theorem hausdorffMeasure_frontier_capFan_inter_normalLine_eq_zero
    {ω t c : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (htω : t ≠ ω) (htT : t ≠ Real.pi / 2) :
    Measure.hausdorffMeasure 1
      (frontier (capFan ω) ∩ normalLine (t : Real.Angle) c) = 0 := by
  apply measure_mono_null (t :=
    (normalLine (ω : Real.Angle) 0 ∩ normalLine (t : Real.Angle) c) ∪
      (normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ∩
        normalLine (t : Real.Angle) c))
  · rintro p ⟨hp, hpt⟩
    have hp' := frontier_inter_subset
      (normalHalfPlane (ω : Real.Angle) 0 true false)
      (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
    rcases hp' with hp' | hp'
    · exact Or.inl ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.1, hpt⟩
    · exact Or.inr ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.2, hpt⟩
  · rw [measure_union_null]
    · exact hausdorffMeasure_normalLine_inter_normalLine_eq_zero hω ht htω.symm
    · exact hausdorffMeasure_normalLine_inter_normalLine_eq_zero
        ⟨by positivity, by linarith [Real.pi_pos]⟩ ht htT.symm

private theorem frontier_capFan_inter_normalLine_countable
    {ω t c : ℝ} (hω : ω ∈ Set.Ioo 0 Real.pi) (ht : t ∈ Set.Ioo 0 Real.pi)
    (htω : t ≠ ω) (htT : t ≠ Real.pi / 2) :
    (frontier (capFan ω) ∩ normalLine (t : Real.Angle) c).Countable := by
  refine ((normalLine_inter_normalLine_subsingleton hω ht htω.symm
      (c := 0) (d := c)).countable.union
    (normalLine_inter_normalLine_subsingleton
      (s := Real.pi / 2) (t := t) (c := 0) (d := c)
      ⟨by positivity, by linarith [Real.pi_pos]⟩ ht htT.symm).countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (ω : Real.Angle) 0 true false)
    (normalHalfPlane ((Real.pi / 2 : ℝ) : Real.Angle) 0 true false) hp
  rcases hp' with hp' | hp'
  · exact Or.inl ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr ⟨frontier_normalHalfPlane_upper_closed_subset_normalLine _ _ hp'.2, hpt⟩

private theorem hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t c : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi) (htω : t ≠ Θ.angle)
    (htT : t ≠ Real.pi / 2) :
    Measure.hausdorffMeasure 1
        (frontier (polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) c) =
      Measure.hausdorffMeasure 1
        (frontier (capFan Θ.angle \ polygonNiche Θ K.val) ∩
          normalLine (t : Real.Angle) c) := by
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  have hN : polygonNiche Θ K.val = capFan Θ.angle ∩ X := by simp [polygonNiche, X]
  have hC : capFan Θ.angle \ polygonNiche Θ K.val = capFan Θ.angle \ X := by
    simp [polygonNiche, X]
  rw [hC, hN]
  apply measure_eq_of_symmDiff_subset_null (E :=
    frontier (capFan Θ.angle) ∩ normalLine (t : Real.Angle) c)
  · intro p hp
    rcases hp with hp | hp
    · refine ⟨frontier_inter_open_symmDiff_subset_frontier
          (isClosed_capFan Θ.angle) (Or.inl ⟨hp.1.1, ?_⟩), hp.1.2⟩
      intro hpC
      exact hp.2 ⟨hpC, hp.1.2⟩
    · refine ⟨frontier_inter_open_symmDiff_subset_frontier
          (isClosed_capFan Θ.angle) (Or.inr ⟨hp.1.1, ?_⟩), hp.1.2⟩
      intro hpN
      exact hp.2 ⟨hpN, hp.1.2⟩
  · exact hausdorffMeasure_frontier_capFan_inter_normalLine_eq_zero
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ ht htω htT

private theorem hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t c : ℝ}
    (hleft : inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector (t : Real.Angle)) ≠ 0)
    (hright : inner ℝ (normalVector 0) (normalVector (t : Real.Angle)) ≠ 0) :
    Measure.hausdorffMeasure 1
        (frontier (capFan Θ.angle \ polygonNiche Θ K.val) ∩
          normalLine (t : Real.Angle) c) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) c) := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := (polygonCap_polyline K).choose_spec
  let L := openRay ((capVertices K.val Θ.angle).2.1)
    (tangentVector (Θ.angle : Real.Angle))
  let R := openRay ((capVertices K.val 0).1.2) (normalVector 0)
  have hnullL : Measure.hausdorffMeasure 1
      (L ∩ normalLine (t : Real.Angle) c) = 0 := by
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hleft
  have hnullR : Measure.hausdorffMeasure 1
      (R ∩ normalLine (t : Real.Angle) c) = 0 := by
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hright
  apply measure_eq_of_symmDiff_subset_null
    (E := (L ∩ normalLine (t : Real.Angle) c) ∪
      (R ∩ normalLine (t : Real.Angle) c))
  · intro q hq
    rcases hq with hq | hq
    · rw [hp.2.2.2.2.2.1] at hq
      rcases hq.1.1 with hL | hR
      · rcases hL with hL | hcarrier
        · exact Or.inl ⟨hL, hq.1.2⟩
        · exact False.elim (hq.2 ⟨hcarrier, hq.1.2⟩)
      · exact Or.inr ⟨hR, hq.1.2⟩
    · exact False.elim (hq.2 ⟨by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1), hq.1.2⟩)
  · rw [measure_union_null hnullL hnullR]

private theorem edge_direction_ne_zero (p : XMonotonePolylineData)
    (i : Fin p.edges) : p.vertices i.succ - p.vertices i.castSucc ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have hcoord := congrArg (fun q : Point ↦ q 0) h
  exact (ne_of_gt (p.increasing i.castSucc_lt_succ)) hcoord

private theorem IsCapPolyline.edge_subset_boundaryLine {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) (i : Fin p.edges) :
    ∃ l ∈ polygonCapBoundaryLines K,
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        normalLine l.1 l.2 := by
  classical
  simpa only [normalLine] using EuclideanGeometry.exists_segment_subset_hyperplane_of_finite_cover
    (I := polygonCapBoundaryLines K) (n := fun l ↦ normalVector l.1) (c := Prod.snd)
    (a := p.vertices i.castSucc) (b := p.vertices i.succ)
    (sub_ne_zero.mp (edge_direction_ne_zero p i)).symm (by
      intro q hq
      have hcarrier : q ∈ p.carrier := by
        rw [XMonotonePolylineData.carrier]
        exact Set.mem_iUnion.mpr ⟨i, hq⟩
      have hfrontier : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hcarrier)
      exact frontier_polygonComplement_subset_boundaryLines K hfrontier)

private theorem IsCapPolyline.edge_subset_bLine_of_orthogonal {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ Θ.directions)
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1) := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI hlorth hi
      linarith [(Θ.interior t ht).2]
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨by positivity, by linarith [Real.pi_pos]⟩ htI hlorth hi
      linarith [(Θ.interior t ht).2, Θ.angle_le]
  · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
    rcases hsl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨(Θ.interior s hs).1,
          ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
            (by linarith [Real.pi_pos])⟩ htI hlorth hi
      simpa [heq] using hline
    · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
        constructor
        · linarith [(Θ.interior s hs).1, Real.pi_pos]
        · linarith [(Θ.interior s hs).2, Θ.angle_le]
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      linarith [(Θ.interior t ht).2, Θ.angle_le, (Θ.interior s hs).1, Real.pi_pos]

private theorem IsCapPolyline.edge_subset_dLine_of_orthogonal {Θ : AngleSet}
    {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ Θ.directions)
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
  rcases hl with hl | hl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI hlorth hi
      linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos]
    · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i)
        ⟨by positivity, by linarith [Real.pi_pos]⟩ htI hlorth hi
      linarith [(Θ.interior t ht).1]
  · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
    rcases hsl with rfl | rfl
    · have hsI : s ∈ Set.Ioo 0 Real.pi :=
        ⟨(Θ.interior s hs).1,
          ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
            (by linarith [Real.pi_pos])⟩
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      linarith [(Θ.interior s hs).2, (Θ.interior t ht).1, Θ.angle_le]
    · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
        constructor
        · linarith [(Θ.interior s hs).1, Real.pi_pos]
        · linarith [(Θ.interior s hs).2, Θ.angle_le]
      have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
        (edge_direction_ne_zero p i) hsI htI hlorth hi
      have hst : s = t := by linarith
      simpa [hst] using hline

private theorem polygonCapPolyline_spec {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    IsCapPolyline K (polygonCapPolyline K) := by
  exact (polygonCap_polyline K).choose_spec

private theorem polygonCapPolyline_bLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K t := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector (t : Real.Angle)) (supportValue K.val.val (t : Real.Angle) - 1)
    (fun i hi ↦ hp.edge_subset_bLine_of_orthogonal ht i hi)
  have htDomain : t ∈ angleDomain Θ := by
    exact Or.inl (Or.inl ht)
  rw [show normalLine (t : Real.Angle)
      (supportValue K.val.val (t : Real.Angle) - 1) =
        {q | inner ℝ q (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) - 1} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem polygonCapPolyline_dLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (fun i hi ↦ hp.edge_subset_dLine_of_orthogonal ht i hi)
  have htDomain : t + Real.pi / 2 ∈ angleDomain Θ := by
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [show normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) =
        {q | inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
          supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem tangentVector_angle_inner_normalVector_direction_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector (t : Real.Angle)) ≠ 0 := by
  have hsin : 0 < Real.sin (Θ.angle - t) := Real.sin_pos_of_pos_of_lt_pi
    (by linarith [(Θ.interior t ht).2])
    (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
  have h := sin_sub_eq_neg_inner_normalVector_tangentVector
    (t : Real.Angle) (Θ.angle : Real.Angle)
  change Real.sin (Θ.angle - t) =
    -inner ℝ (normalVector (t : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) at h
  rw [real_inner_comm]
  linarith

private theorem tangentVector_angle_inner_normalVector_direction_add_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
  have hneg : -Real.pi < Θ.angle - (t + Real.pi / 2) := by
    linarith [(Θ.interior t ht).2, Real.pi_pos]
  have hzero : Θ.angle - (t + Real.pi / 2) < 0 := by
    linarith [(Θ.interior t ht).1, Θ.angle_le]
  have hsin : Real.sin (Θ.angle - (t + Real.pi / 2)) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt hzero hneg
  have h := sin_sub_eq_neg_inner_normalVector_tangentVector
    ((t + Real.pi / 2 : ℝ) : Real.Angle) (Θ.angle : Real.Angle)
  change Real.sin (Θ.angle - (t + Real.pi / 2)) =
    -inner ℝ (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) at h
  rw [real_inner_comm]
  linarith

private theorem normalVector_zero_inner_normalVector_direction_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (normalVector 0) (normalVector (t : Real.Angle)) ≠ 0 := by
  rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
    inner_normalVector_normalVector]
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, (Θ.interior t ht).1],
      (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  simpa [Real.cos_neg] using hcos.ne'

private theorem normalVector_zero_inner_normalVector_direction_add_ne_zero
    {Θ : AngleSet} {t : ℝ} (ht : t ∈ Θ.directions) :
    inner ℝ (normalVector 0)
      (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
  rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
    inner_normalVector_normalVector]
  have hsin : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi
    (Θ.interior t ht).1
    (by linarith [(Θ.interior t ht).2, Θ.angle_le, Real.pi_pos])
  rw [show 0 - (t + Real.pi / 2) = -(t + Real.pi / 2) by ring,
    Real.cos_neg, Real.cos_add_pi_div_two]
  exact neg_ne_zero.mpr hsin.ne'

private theorem polygonNiche_bLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K t := by
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  rw [hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement K htI
      (ne_of_lt (Θ.interior t ht).2) (ne_of_lt
        ((Θ.interior t ht).2.trans_le Θ.angle_le)),
    hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier K
      (tangentVector_angle_inner_normalVector_direction_ne_zero ht)
      (normalVector_zero_inner_normalVector_direction_ne_zero ht)]
  exact polygonCapPolyline_bLine_length K ht

private theorem polygonNiche_dLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1))).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  rw [hausdorffMeasure_frontier_polygonNiche_inter_normalLine_eq_complement K htI
      (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
      (by linarith [(Θ.interior t ht).1]),
    hausdorffMeasure_frontier_polygonComplement_inter_normalLine_eq_carrier K
      (tangentVector_angle_inner_normalVector_direction_add_ne_zero ht)
      (normalVector_zero_inner_normalVector_direction_add_ne_zero ht)]
  exact polygonCapPolyline_dLine_length K ht

private theorem frontier_innerQuadrant_inter_bLine_subset_bRay
    (s : Set Point) (t : ℝ) :
    frontier (innerQuadrant s t) ∩
        normalLine (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) ⊆
      (rotatingHallwayParts s (t : Real.Angle)).bRay := by
  intro p hp
  rw [mem_rotatingHallwayParts_bRay_iff]
  refine ⟨hp.2, ?_⟩
  apply closure_minimal (t := {q | inner ℝ q (tangentVector (t : Real.Angle)) ≤
      supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1})
      (fun q hq ↦ ?_) (isClosed_le (by fun_prop) continuous_const)
      (frontier_subset_closure hp.1)
  change q ∈ innerQuadrant s t at hq
  have h := hq.2
  change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
    supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at h
  rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
    (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
    normalVector_add_pi_div_two] at h
  exact h.le

private theorem frontier_innerQuadrant_inter_dLine_subset_dRay
    (s : Set Point) (t : ℝ) :
    frontier (innerQuadrant s t) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) ⊆
      (rotatingHallwayParts s (t : Real.Angle)).dRay := by
  intro p hp
  rw [mem_rotatingHallwayParts_dRay_iff]
  refine ⟨?_, ?_⟩
  · apply closure_minimal (t := {q | inner ℝ q (normalVector (t : Real.Angle)) ≤
        supportValue s (t : Real.Angle) - 1})
        (fun q hq ↦ ?_) (isClosed_le (by fun_prop) continuous_const)
        (frontier_subset_closure hp.1)
    change q ∈ innerQuadrant s t at hq
    have h := hq.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue s (t : Real.Angle) - 1 at h
    exact h.le
  · have hline := hp.2
    change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hline
    rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hline
    exact hline

private theorem frontier_innerQuadrant_inter_bLine_countable_of_ne
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ Θ.directions) (hst : s ≠ t) :
    (frontier (innerQuadrant K.val.val s) ∩
      normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have hfirst := normalLine_inter_normalLine_subsingleton hsI htI hst
    (c := supportValue K.val.val (s : Real.Angle) - 1)
    (d := supportValue K.val.val (t : Real.Angle) - 1)
  have hsecond := normalLine_inter_normalLine_subsingleton hsTI htI
    (by linarith [(Θ.interior s hs).1, (Θ.interior t ht).2, Θ.angle_le])
    (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (d := supportValue K.val.val (t : Real.Angle) - 1)
  refine (hfirst.countable.union hsecond.countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · exact Or.inl
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.2, hpt⟩

private theorem frontier_innerQuadrant_inter_dLine_countable_of_ne
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ Θ.directions) (hst : s ≠ t) :
    (frontier (innerQuadrant K.val.val s) ∩
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have htTI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  have hfirst := normalLine_inter_normalLine_subsingleton hsI htTI
    (by linarith [(Θ.interior s hs).2, (Θ.interior t ht).1, Θ.angle_le])
    (c := supportValue K.val.val (s : Real.Angle) - 1)
    (d := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  have hsecond := normalLine_inter_normalLine_subsingleton hsTI htTI
    (by
      intro h
      apply hst
      linarith)
    (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
    (d := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  refine (hfirst.countable.union hsecond.countable).mono ?_
  rintro p ⟨hp, hpt⟩
  have hp' := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1) false true) hp
  rcases hp' with hp' | hp'
  · exact Or.inl
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.1, hpt⟩
  · exact Or.inr
      ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hp'.2, hpt⟩

private theorem frontier_polygonNiche_bLine_sdiff_bRay_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    ((frontier (polygonNiche Θ K.val) ∩
        normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)) \
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay).Countable := by
  let L := normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  let E : Θ.directions → Set Point := fun s ↦
    (frontier (innerQuadrant K.val.val s) ∩ L) \ R
  have htI : t ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior t ht).1,
      ((Θ.interior t ht).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hfan : (frontier (capFan Θ.angle) ∩ L).Countable :=
    frontier_capFan_inter_normalLine_countable
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI
      (ne_of_lt (Θ.interior t ht).2)
      (ne_of_lt ((Θ.interior t ht).2.trans_le Θ.angle_le))
  have hE (s : Θ.directions) : (E s).Countable := by
    by_cases hst : (s : ℝ) = t
    · apply Set.countable_empty.mono
      intro p hp
      exfalso
      apply hp.2
      apply frontier_innerQuadrant_inter_bLine_subset_bRay
        (s := (K.val.val : Set Point)) (t := t)
      simpa [E, L, R, hst] using hp.1
    · exact (frontier_innerQuadrant_inter_bLine_countable_of_ne K s.property ht hst).mono
        (by intro p hp; exact hp.1)
  refine (hfan.union (Set.countable_iUnion hE)).mono ?_
  intro p hp
  have hp' : p ∈ frontier (capFan Θ.angle ∩ X) := by
    simpa [polygonNiche, X] using hp.1.1
  rcases frontier_inter_subset (capFan Θ.angle) X hp' with hpF | hpX
  · exact Or.inl ⟨hpF.1, hp.1.2⟩
  · right
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun s ↦ innerQuadrant K.val.val s) hpX.2
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨⟨hps, hp.1.2⟩, hp.2⟩⟩

private theorem frontier_polygonNiche_dLine_sdiff_dRay_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    ((frontier (polygonNiche Θ K.val) ∩
        normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
          (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)) \
      (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay).Countable := by
  let L := normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  let E : Θ.directions → Set Point := fun s ↦
    (frontier (innerQuadrant K.val.val s) ∩ L) \ R
  have htI : t + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior t ht).1, Real.pi_pos]
    · linarith [(Θ.interior t ht).2, Θ.angle_le]
  have hfan : (frontier (capFan Θ.angle) ∩ L).Countable :=
    frontier_capFan_inter_normalLine_countable
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩ htI
      (by linarith [(Θ.interior t ht).1, Θ.angle_le, Real.pi_pos])
      (by linarith [(Θ.interior t ht).1])
  have hE (s : Θ.directions) : (E s).Countable := by
    by_cases hst : (s : ℝ) = t
    · apply Set.countable_empty.mono
      intro p hp
      exfalso
      apply hp.2
      apply frontier_innerQuadrant_inter_dLine_subset_dRay
        (s := (K.val.val : Set Point)) (t := t)
      simpa [E, L, R, hst] using hp.1
    · exact (frontier_innerQuadrant_inter_dLine_countable_of_ne K s.property ht hst).mono
        (by intro p hp; exact hp.1)
  refine (hfan.union (Set.countable_iUnion hE)).mono ?_
  intro p hp
  have hp' : p ∈ frontier (capFan Θ.angle ∩ X) := by
    simpa [polygonNiche, X] using hp.1.1
  rcases frontier_inter_subset (capFan Θ.angle) X hp' with hpF | hpX
  · exact Or.inl ⟨hpF.1, hp.1.2⟩
  · right
    have hmem := Finset.frontier_biUnion_subset Θ.directions
      (fun s ↦ innerQuadrant K.val.val s) hpX.2
    obtain ⟨s, hs, hps⟩ := Set.mem_iUnion₂.mp hmem
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨⟨hps, hp.1.2⟩, hp.2⟩⟩

private theorem rotatingHallwayParts_bRay_subset_bLine
    (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).bRay ⊆
      normalLine (t : Real.Angle) (supportValue s (t : Real.Angle) - 1) := by
  intro p hp
  exact (mem_rotatingHallwayParts_bRay_iff s (t : Real.Angle) p).mp hp |>.1

private theorem rotatingHallwayParts_dRay_subset_dLine
    (s : Set Point) (t : ℝ) :
    (rotatingHallwayParts s (t : Real.Angle)).dRay ⊆
      normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) := by
  intro p hp
  have h := (mem_rotatingHallwayParts_dRay_iff s (t : Real.Angle) p).mp hp |>.2
  change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
  rw [show ((t + Real.pi / 2 : ℝ) : Real.Angle) =
    (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
    normalVector_add_pi_div_two]
  exact h

private theorem polygonNiche_bRay_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay)).toReal =
      polygonPolylineLengthAt K t := by
  let L := normalLine (t : Real.Angle) (supportValue K.val.val (t : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay
  have hRL : R ⊆ L := rotatingHallwayParts_bRay_subset_bLine K.val.val t
  have hmeasure : Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩ L) =
      Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ R) := by
    apply measure_eq_of_symmDiff_subset_null (E :=
      (frontier (polygonNiche Θ K.val) ∩ L) \ R)
    · intro p hp
      rcases hp with hp | hp
      · exact ⟨hp.1, fun hpR ↦ hp.2 ⟨hp.1.1, hpR⟩⟩
      · exfalso
        exact hp.2 ⟨hp.1.1, hRL hp.1.2⟩
    · have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
      exact (frontier_polygonNiche_bLine_sdiff_bRay_countable K ht).measure_zero _
  rw [← hmeasure]
  exact polygonNiche_bLine_length K ht

private theorem polygonNiche_dRay_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ Θ.directions) :
    (Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩
        (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay)).toReal =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  let L := normalLine ((t + Real.pi / 2 : ℝ) : Real.Angle)
    (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1)
  let R := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).dRay
  have hRL : R ⊆ L := rotatingHallwayParts_dRay_subset_dLine K.val.val t
  have hmeasure : Measure.hausdorffMeasure 1
      (frontier (polygonNiche Θ K.val) ∩ L) =
      Measure.hausdorffMeasure 1 (frontier (polygonNiche Θ K.val) ∩ R) := by
    apply measure_eq_of_symmDiff_subset_null (E :=
      (frontier (polygonNiche Θ K.val) ∩ L) \ R)
    · intro p hp
      rcases hp with hp | hp
      · exact ⟨hp.1, fun hpR ↦ hp.2 ⟨hp.1.1, hpR⟩⟩
      · exfalso
        exact hp.2 ⟨hp.1.1, hRL hp.1.2⟩
    · have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
      exact (frontier_polygonNiche_dLine_sdiff_dRay_countable K ht).measure_zero _
  rw [← hmeasure]
  exact polygonNiche_dLine_length K ht

private theorem exposedEdge_bottom_eq_segment_zero_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      segment ℝ 0 (capVertices K.val 0).1.2 := by
  let A := (capVertices K.val 0).1.2
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have htangent : tangentVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, normalVector, frame,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hAK : A ∈ (K.val.val : Set Point) := by
    rw [hAeq]
    exact supportValue_zero_smul_normalVector_mem K.val
  have hAedge : A ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hAeq, inner_normalVector_three_pi_div_two]
    simp [normalVector, frame]
  have h0edge : (0 : Point) ∈
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨zero_mem_cap_of_lt K.val hω, ?_⟩
    change inner ℝ (0 : Point) (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1]
    simp
  have hfst : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 = A := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hAedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    rw [htangent]
    exact hqx.trans_eq hA.symm
  have hsnd : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = 0 := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ h0edge
    intro q hq
    have hfan := K.val.subset_capFan hq.1
    have hqy : q 1 = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) at h
      rw [K.val.property.2.2.2.2.2.1] at h
      simpa only [inner_normalVector_three_pi_div_two, neg_eq_zero] using h
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hqx : 0 ≤ q 0 := by
      have h := hfan.1
      change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at h
      simp [normalVector, frame, PiLp.inner_apply, hqy] at h
      exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using h) hcos
    rw [htangent]
    simpa [normalVector, frame, PiLp.inner_apply] using hqx
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd]

private theorem exposedEdge_left_eq_segment_zero_left {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      segment ℝ 0 (capVertices K.val Θ.angle).2.1 := by
  let C := (capVertices K.val Θ.angle).2.1
  let L := supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
  have hCeq := capVertices_angle_fst_eq K
  change C = L • tangentVector (Θ.angle : Real.Angle) at hCeq
  have hnormal : normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      -normalVector (Θ.angle : Real.Angle) := normalVector_add_pi Θ.angle
  have htangent : tangentVector ((Θ.angle + Real.pi : ℝ) : Real.Angle) =
      -tangentVector (Θ.angle : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, frame, Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hCK : C ∈ (K.val.val : Set Point) := by
    rw [hCeq]
    exact supportValue_add_pi_div_two_smul_tangentVector_mem_of_lt K.val hω
  have hCedge : C ∈ exposedEdge K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1, hnormal, hCeq, inner_neg_right,
      real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
    simp
  have h0edge : (0 : Point) ∈
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
    refine ⟨zero_mem_cap_of_lt K.val hω, ?_⟩
    change inner ℝ (0 : Point) (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
      supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.1]
    simp
  have hfst : (edgeVertices K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle)).1 = 0 := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ h0edge
    intro q hq
    have hfan := K.val.subset_capFan hq.1
    have hqn : inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) =
        supportValue K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) at h
      rw [K.val.property.2.2.2.2.1, hnormal, inner_neg_right] at h
      linarith
    let μ := inner ℝ q (tangentVector (Θ.angle : Real.Angle))
    have hqeq : μ • tangentVector (Θ.angle : Real.Angle) = q := by
      have hframe := inner_normalVector_smul_add_inner_tangentVector_smul
        q (Θ.angle : Real.Angle)
      rw [hqn, zero_smul, zero_add] at hframe
      exact hframe
    have hμ : 0 ≤ μ := by
      have hqy := hfan.2
      change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqy
      have hcoord := congrArg (fun p : Point ↦ p 1) hqeq
      change μ * Real.cos Θ.angle = q 1 at hcoord
      have hqy' : 0 ≤ q 1 := by
        simpa [normalVector, frame, PiLp.inner_apply] using hqy
      rw [← hcoord] at hqy'
      exact nonneg_of_mul_nonneg_left hqy' (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩)
    rw [htangent, inner_neg_right]
    simpa using neg_nonpos.mpr hμ
  have hsnd : (edgeVertices K.val.val
      ((Θ.angle + Real.pi : ℝ) : Real.Angle)).2 = C := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hCedge
    intro q hq
    have hqL := inner_le_supportValue K.val.val hq.1
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
    rw [show ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
      (Θ.angle : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) by rfl,
      normalVector_add_pi_div_two] at hqL
    change inner ℝ q (tangentVector (Θ.angle : Real.Angle)) ≤ L at hqL
    rw [htangent, hCeq, inner_neg_right, inner_neg_right, real_inner_smul_left,
      inner_tangentVector_self]
    linarith
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd, segment_symm]

private theorem exposedEdge_bottom_eq_segment_left_right {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      segment ℝ (capVertices K.val Θ.angle).2.1 (capVertices K.val 0).1.2 := by
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have htangent : tangentVector ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      normalVector (0 : Real.Angle) := by
    ext i
    fin_cases i <;>
      simp [tangentVector, normalVector, frame,
        show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add]
  have hAK : A ∈ (K.val.val : Set Point) := by
    rw [hAeq]
    exact supportValue_zero_smul_normalVector_mem K.val
  have hCK : C ∈ (K.val.val : Set Point) := by
    exact (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
  have hAedge : A ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hAeq, inner_normalVector_three_pi_div_two]
    simp [normalVector, frame]
  have hCedge : C ∈ exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hCK, ?_⟩
    change inner ℝ C (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.2.2.1, hCeq, inner_normalVector_three_pi_div_two]
    simp [hω, tangentVector, frame]
  have hfst : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).1 = A := by
    apply edgeVertices_fst_eq_of_tangent_isGreatest K.val.val _ hAedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ A (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    rw [htangent]
    exact hqx.trans_eq hA.symm
  have hsnd : (edgeVertices K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)).2 = C := by
    apply edgeVertices_snd_eq_of_tangent_isLeast K.val.val _ hCedge
    intro q hq
    have hqx := inner_le_supportValue K.val.val hq.1 (Real.pi : Real.Angle)
    have hC := (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).2
    change inner ℝ C
      (normalVector ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) at hC
    have hang : ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) =
        (Real.pi : Real.Angle) := by
      congr 1
      rw [hω]
      ring
    rw [hang] at hC
    rw [htangent]
    simpa [normalVector, frame, PiLp.inner_apply] using hqx.trans_eq hC.symm
  rw [exposedEdge_eq_segment_edgeVertices, hfst, hsnd]

private theorem XMonotonePolylineData.carrier_fst_mem_Icc
    (p : XMonotonePolylineData) {q : Point} (hq : q ∈ p.carrier) :
    q 0 ∈ Set.Icc ((p.vertices 0) 0) ((p.vertices (Fin.last p.edges)) 0) := by
  rw [XMonotonePolylineData.carrier] at hq
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hq
  have hi := fst_mem_Icc_of_mem_segment (p.increasing i.castSucc_lt_succ).le hqi
  exact ⟨(p.increasing.monotone (Fin.zero_le i.castSucc)).trans hi.1,
    hi.2.trans (p.increasing.monotone (Fin.le_last i.succ))⟩

private theorem mem_segment_of_fst_mem_Icc_of_mem_normalLine
    {a b q : Point} {t c : ℝ} (hab : a 0 < b 0)
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (ha : a ∈ normalLine (t : Real.Angle) c)
    (hb : b ∈ normalLine (t : Real.Angle) c)
    (hq : q ∈ normalLine (t : Real.Angle) c)
    (hx : q 0 ∈ Set.Icc (a 0) (b 0)) : q ∈ segment ℝ a b := by
  let r := (q 0 - a 0) / (b 0 - a 0)
  have hden : 0 < b 0 - a 0 := sub_pos.mpr hab
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · exact (div_le_one hden).2 (by linarith [hx.2])
  rw [segment_eq_image']
  refine ⟨r, hr, ?_⟩
  change a + r • (b - a) = q
  have hxcoord : (a + r • (b - a)) 0 = q 0 := by
    dsimp [r]
    field_simp
    ring
  have hline : a + r • (b - a) ∈ normalLine (t : Real.Angle) c := by
    change inner ℝ (a + r • (b - a)) (normalVector (t : Real.Angle)) = c
    change inner ℝ a (normalVector (t : Real.Angle)) = c at ha
    change inner ℝ b (normalVector (t : Real.Angle)) = c at hb
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb, sub_self,
      mul_zero, add_zero]
  ext i
  fin_cases i
  · exact hxcoord
  · change (a + r • (b - a)) 1 = q 1
    change inner ℝ (a + r • (b - a)) (normalVector (t : Real.Angle)) = c at hline
    change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hline hq
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hxcoord ⊢
    apply mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    linear_combination hline - hq - Real.cos t * hxcoord

private theorem eq_of_fst_eq_of_mem_normalLine {p q : Point} {t c : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (hp : p ∈ normalLine (t : Real.Angle) c)
    (hq : q ∈ normalLine (t : Real.Angle) c) (hx : p 0 = q 0) : p = q := by
  ext i
  fin_cases i
  · exact hx
  · change p 1 = q 1
    change inner ℝ p (normalVector (t : Real.Angle)) = c at hp
    change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
    simp [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two] at hp hq
    apply mul_left_cancel₀ (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2).ne'
    linear_combination hp - hq - Real.cos t * hx

private theorem polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hC0 : C 0 ≤ 0 := by
    rw [hCeq]
    simp [tangentVector, frame]
    simpa only [Real.Angle.coe_add] using mul_nonneg hL
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos])))
  have hA0support : 0 < supportValue K.val.val (0 : Real.Angle) := by
    obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
      (Θ.angle : Real.Angle)
    have huy : u 1 ≤ 1 := by
      have huy' := inner_le_supportValue K.val.val huK
        ((Real.pi / 2 : ℝ) : Real.Angle)
      rw [K.val.property.2.2.2.1] at huy'
      simpa [normalVector, frame, PiLp.inner_apply] using huy'
    rw [K.val.property.2.2.1] at hu
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hsin_lt : Real.sin Θ.angle < 1 := by
      nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
    have hux : 0 < u 0 := by
      simp [normalVector, frame, PiLp.inner_apply] at hu
      have hsin : 0 ≤ Real.sin Θ.angle :=
        (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
      have hmul := mul_le_mul_of_nonneg_left huy hsin
      nlinarith
    exact hux.trans_le (by
      have := inner_le_supportValue K.val.val huK (0 : Real.Angle)
      simpa [normalVector, frame, PiLp.inner_apply] using this)
  have hA0 : 0 < A 0 := by
    rw [hAeq]
    simpa [normalVector, frame] using hA0support
  intro q hq
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine hA0
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · change inner ℝ (capVertices K.val 0).1.2
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [capVertices_zero_snd_eq K]
    simp [normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · have hxbounds := p.carrier_fst_mem_Icc hq.1
    rw [hp.2.1, hp.2.2.1] at hxbounds
    refine ⟨?_, hxbounds.2⟩
    have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      rw [hp.2.2.2.2.2.1]
      exact Or.inl (Or.inr hq.1)
    have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
    have hfan : q ∈ capFan Θ.angle :=
      (hclosed.closure_eq ▸ frontier_subset_closure hfront).1
    have hqy : q 1 = 0 := by
      have h := hq.2
      change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at h
      simpa [normalVector, frame, PiLp.inner_apply] using h
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have h := hfan.1
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at h
    simp [normalVector, frame, PiLp.inner_apply, hqy] at h
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using h) hcos

private theorem polygonCapPolyline_carrier_inter_left_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩ normalLine (Θ.angle : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hC0 : C 0 ≤ 0 := by
    rw [hCeq]
    simp [tangentVector, frame]
    simpa only [Real.Angle.coe_add] using mul_nonneg hL
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos])))
  intro q hq
  rw [exposedEdge_left_eq_segment_zero_left K hω, segment_symm]
  have hfront : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
    rw [hp.2.2.2.2.2.1]
    exact Or.inl (Or.inr hq.1)
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  have hfan : q ∈ capFan Θ.angle :=
    (hclosed.closure_eq ▸ frontier_subset_closure hfront).1
  have hxbounds := p.carrier_fst_mem_Icc hq.1
  rw [hp.2.1, hp.2.2.1] at hxbounds
  have hq0 : q 0 ≤ 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hline
    have hqy := hfan.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hqy
    have hqy' : 0 ≤ q 1 := by
      simpa [normalVector, frame, PiLp.inner_apply] using hqy
    simp [normalVector, frame, PiLp.inner_apply] at hline
    have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hsin : 0 < Real.sin Θ.angle := Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (by linarith [Θ.angle_le, Real.pi_pos])
    nlinarith
  have hCline : C ∈ normalLine (Θ.angle : Real.Angle) 0 := by
    change inner ℝ C (normalVector (Θ.angle : Real.Angle)) = 0
    rw [hCeq, real_inner_smul_left, real_inner_comm, inner_normalVector_tangentVector]
    simp
  have h0line : (0 : Point) ∈ normalLine (Θ.angle : Real.Angle) 0 := by
    simp [normalLine]
  by_cases hCstrict : C 0 < 0
  · exact mem_segment_of_fst_mem_Icc_of_mem_normalLine hCstrict
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
      hCline h0line hq.2 ⟨hxbounds.1, hq0⟩
  · have hCzero : C 0 = 0 := le_antisymm hC0 (le_of_not_gt hCstrict)
    have hqzero : q 0 = C 0 := by linarith [hxbounds.1, hq0]
    have hqC := eq_of_fst_eq_of_mem_normalLine
      ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
      hq.2 hCline hqzero
    rw [hqC]
    exact left_mem_segment ℝ C 0

private theorem polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hAeq := capVertices_zero_snd_eq K
  change A = supportValue K.val.val (0 : Real.Angle) •
    normalVector (0 : Real.Angle) at hAeq
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
    tangentVector (Θ.angle : Real.Angle) at hCeq
  intro q hq
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine (polygonCap_left_x_lt_right_x K)
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · change inner ℝ C (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [hCeq]
    simp [hω, tangentVector, normalVector, frame, PiLp.inner_apply]
  · change inner ℝ A (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0
    rw [hAeq]
    simp [normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · have hxbounds := p.carrier_fst_mem_Icc hq.1
    simpa [hp.2.1, hp.2.2.1] using hxbounds

private theorem IsCapPolyline.edge_subset_fanLine_of_orthogonal
    {Θ : AngleSet} {K : PolygonCapSpace Θ} {p : XMonotonePolylineData}
    (hp : IsCapPolyline K p) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (i : Fin p.edges)
    (hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector (t : Real.Angle)) = 0) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
      normalLine (t : Real.Angle) 0 := by
  classical
  obtain ⟨l, hl, hline⟩ := hp.edge_subset_boundaryLine i
  have hleft := hline (left_mem_segment ℝ _ _)
  have hright := hline (right_mem_segment ℝ _ _)
  have hlorth : inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
      (normalVector l.1) = 0 := by
    change inner ℝ (p.vertices i.castSucc) (normalVector l.1) = l.2 at hleft
    change inner ℝ (p.vertices i.succ) (normalVector l.1) = l.2 at hright
    rw [inner_sub_left, hright, hleft, sub_self]
  have hωI : Θ.angle ∈ Set.Ioo 0 Real.pi :=
    ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
  have hTI : Real.pi / 2 ∈ Set.Ioo 0 Real.pi :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
    rcases hl with hl | hl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · exact hline
      · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hTI hωI hlorth hi
        simpa [heq] using hline
    · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
      rcases hsl with rfl | rfl
      · have hsI : s ∈ Set.Ioo 0 Real.pi :=
          ⟨(Θ.interior s hs).1,
            ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
              (by linarith [Real.pi_pos])⟩
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hωI hlorth hi
        linarith [(Θ.interior s hs).2]
      · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
          constructor
          · linarith [(Θ.interior s hs).1, Real.pi_pos]
          · linarith [(Θ.interior s hs).2, Θ.angle_le]
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hωI hlorth hi
        linarith [(Θ.interior s hs).1, Θ.angle_le, Real.pi_pos]
  · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
    subst t
    simp only [polygonCapBoundaryLines, Finset.mem_union] at hl
    rcases hl with hl | hl
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hωI hTI hlorth hi
        simpa [heq] using hline
      · exact hline
    · obtain ⟨s, hs, hsl⟩ := Finset.mem_biUnion.mp hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsl
      rcases hsl with rfl | rfl
      · have hsI : s ∈ Set.Ioo 0 Real.pi :=
          ⟨(Θ.interior s hs).1,
            ((Θ.interior s hs).2.trans_le Θ.angle_le).trans
              (by linarith [Real.pi_pos])⟩
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hTI hlorth hi
        linarith [(Θ.interior s hs).2, Θ.angle_le]
      · have hsI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
          constructor
          · linarith [(Θ.interior s hs).1, Real.pi_pos]
          · linarith [(Θ.interior s hs).2, Θ.angle_le]
        have heq := real_eq_of_normal_orthogonal_of_mem_Ioo_zero_pi
          (edge_direction_ne_zero p i) hsI hTI hlorth hi
        linarith [(Θ.interior s hs).1]

private theorem polygonCapPolyline_fanLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (Measure.hausdorffMeasure 1
      ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)).toReal =
      polygonPolylineLengthAt K t := by
  let p := polygonCapPolyline K
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hmeasure := p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (normalVector (t : Real.Angle)) 0
    (fun i hi ↦ hp.edge_subset_fanLine_of_orthogonal ht i hi)
  have htDomain : t ∈ angleDomain Θ := Or.inr ht
  rw [show normalLine (t : Real.Angle) 0 =
      {q | inner ℝ q (normalVector (t : Real.Angle)) = 0} by rfl,
    hmeasure]
  simp [polygonPolylineLengthAt, htDomain, polygonCapPolylineLength, p]

private theorem polygonNiche_inter_bottom_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgap : 0 < (wedgeGaps K.val t).1 := hgapBounds.2.1.trans_le hgapBounds.1
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hb
    simp only [wedgeEndpoints]
    simp [normalVector, frame]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hendpoint_A : (wedgeEndpoints K.val t).1 0 < (capVertices K.val 0).1.2 0 := by
    simpa [wedgeGaps, inner_sub_left, normalVector, frame, PiLp.inner_apply] using hgap
  have hqx_nonneg : 0 ≤ q 0 := by
    have hfan := hq.1.1.1
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hfan
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hfan
    have hcosω : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfan) hcosω
  have hApos : 0 < (capVertices K.val 0).1.2 0 :=
    hqx_nonneg.trans_lt (hqx_endpoint.trans hendpoint_A)
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine hApos
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · exact ⟨hqx_nonneg, (hqx_endpoint.trans hendpoint_A).le⟩

private theorem mem_segment_of_inner_tangent_mem_Icc_of_mem_normalLine
    {a b q : Point} {t : Real.Angle} {c : ℝ}
    (hab : inner ℝ a (tangentVector t) < inner ℝ b (tangentVector t))
    (ha : a ∈ normalLine t c) (hb : b ∈ normalLine t c)
    (hq : q ∈ normalLine t c)
    (hx : inner ℝ q (tangentVector t) ∈
      Set.Icc (inner ℝ a (tangentVector t)) (inner ℝ b (tangentVector t))) :
    q ∈ segment ℝ a b := by
  let r := (inner ℝ q (tangentVector t) - inner ℝ a (tangentVector t)) /
    (inner ℝ b (tangentVector t) - inner ℝ a (tangentVector t))
  have hden : 0 < inner ℝ b (tangentVector t) - inner ℝ a (tangentVector t) :=
    sub_pos.mpr hab
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hden.le
    · exact (div_le_one hden).2 (by linarith [hx.2])
  rw [segment_eq_image']
  refine ⟨r, hr, ?_⟩
  change a + r • (b - a) = q
  have hn : inner ℝ (a + r • (b - a)) (normalVector t) =
      inner ℝ q (normalVector t)
      := by
    change inner ℝ a (normalVector t) = c at ha
    change inner ℝ b (normalVector t) = c at hb
    change inner ℝ q (normalVector t) = c at hq
    rw [inner_add_left, real_inner_smul_left, inner_sub_left, ha, hb, sub_self,
      mul_zero, add_zero, hq]
  have htangent : inner ℝ (a + r • (b - a)) (tangentVector t) =
      inner ℝ q (tangentVector t)
      := by
    rw [inner_add_left, real_inner_smul_left, inner_sub_left]
    dsimp [r]
    field_simp
    ring
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      (a + r • (b - a)) t,
    ← inner_normalVector_smul_add_inner_tangentVector_smul q t, hn, htangent]

private theorem polygonNiche_inter_left_subset_exposedEdge_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine (Θ.angle : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_left_eq_segment_zero_left K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgap : 0 < (wedgeGaps K.val t).2 :=
    hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
  have hqcoord_endpoint : inner ℝ q (tangentVector (Θ.angle : Real.Angle)) <
      inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector (Θ.angle : Real.Angle)) := by
    have hd := hqt.2
    change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hd
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q (Θ.angle : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hd
    have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.cos (Θ.angle - t) := by
      rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_sub]
      ring_nf
    rw [hinner] at hd
    have hendpoint : inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector (Θ.angle : Real.Angle)) =
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (Θ.angle - t) := by
      simp only [wedgeEndpoints, real_inner_smul_left]
      rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (tangentVector (Θ.angle : Real.Angle)) = 1 by
          exact inner_tangentVector_self Θ.angle, mul_one]
    rw [hendpoint]
    exact (lt_div_iff₀ hcosδ).2 (by linarith [hd])
  have hendpoint_C : inner ℝ (wedgeEndpoints K.val t).2
      (tangentVector (Θ.angle : Real.Angle)) <
      inner ℝ (capVertices K.val Θ.angle).2.1
        (tangentVector (Θ.angle : Real.Angle)) := by
    simpa [wedgeGaps, inner_sub_left] using hgap
  have hqcoord_nonneg : 0 ≤ inner ℝ q (tangentVector (Θ.angle : Real.Angle)) := by
    have hfan := hq.1.1.2
    change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hfan
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q (Θ.angle : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector (Θ.angle : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hfan
    have hcosω : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
    have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = Real.cos Θ.angle := by
      simp [tangentVector, normalVector, frame, PiLp.inner_apply,
        Fin.sum_univ_two]
    rw [hinner] at hfan
    exact nonneg_of_mul_nonneg_left hfan hcosω
  have hCpos : 0 < inner ℝ (capVertices K.val Θ.angle).2.1
      (tangentVector (Θ.angle : Real.Angle)) :=
    hqcoord_nonneg.trans_lt (hqcoord_endpoint.trans hendpoint_C)
  apply mem_segment_of_inner_tangent_mem_Icc_of_mem_normalLine
    (t := (Θ.angle : Real.Angle)) (c := 0) (by simpa using hCpos)
  · simp [normalLine]
  · have hCeq := capVertices_angle_fst_eq K
    change inner ℝ (capVertices K.val Θ.angle).2.1
      (normalVector (Θ.angle : Real.Angle)) = 0
    rw [hCeq, real_inner_smul_left, real_inner_comm,
      inner_normalVector_tangentVector, mul_zero]
  · exact hq.2
  · exact ⟨by simpa using hqcoord_nonneg, (hqcoord_endpoint.trans hendpoint_C).le⟩

private theorem polygonNiche_inter_bottom_subset_exposedEdge_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  rcases Set.mem_iUnion.mp hq.1.2 with ⟨t, ht⟩
  rcases Set.mem_iUnion.mp ht with ⟨htΘ, hqt⟩
  have htt := Θ.interior t htΘ
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
  have hcosδ : 0 < Real.cos (Θ.angle - t) := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.2, Real.pi_pos], by linarith [htt.1, Θ.angle_le]⟩
  have hgapBounds := wedgeGaps_positive_lower_bound K.val t htt
  have hgapA : 0 < (wedgeGaps K.val t).1 := hgapBounds.2.1.trans_le hgapBounds.1
  have hgapC : 0 < (wedgeGaps K.val t).2 :=
    hgapBounds.2.2.2.trans_le hgapBounds.2.2.1
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  have hqx_endpoint : q 0 < (wedgeEndpoints K.val t).1 0 := by
    have hb := hqt.1
    change inner ℝ q (normalVector (t : Real.Angle)) <
      supportValue K.val.val (t : Real.Angle) - 1 at hb
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hb
    simp only [wedgeEndpoints]
    simp [normalVector, frame]
    exact (lt_div_iff₀ hcost).2 (by simpa [mul_comm] using hb)
  have hendpoint_A : (wedgeEndpoints K.val t).1 0 < (capVertices K.val 0).1.2 0 := by
    simpa [wedgeGaps, inner_sub_left, normalVector, frame, PiLp.inner_apply] using hgapA
  have hqcoord_endpoint : inner ℝ q
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
      inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    have hd := hqt.2
    change inner ℝ q (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hd
    have hqdecomp := inner_normalVector_smul_add_inner_tangentVector_smul
      q ((Real.pi / 2 : ℝ) : Real.Angle)
    have hqnormal := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hqnormal
    rw [hqnormal, zero_smul, zero_add] at hqdecomp
    rw [← hqdecomp, real_inner_smul_left] at hd
    have hinner : inner ℝ (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.cos (Real.pi / 2 - t) := by
      rw [Real.Angle.coe_add, normalVector_add_pi_div_two]
      simp [tangentVector, frame, PiLp.inner_apply, Fin.sum_univ_two,
        Real.cos_sub]
    rw [hinner] at hd
    have hcosEq : Real.cos (Θ.angle - t) = Real.cos (Real.pi / 2 - t) := by
      rw [hω]
    have hendpoint : inner ℝ (wedgeEndpoints K.val t).2
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
          Real.cos (Real.pi / 2 - t) := by
      calc
        _ = (supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) /
            Real.cos (Θ.angle - t) := by
          rw [show tangentVector ((Real.pi / 2 : ℝ) : Real.Angle) =
              tangentVector (Θ.angle : Real.Angle) by rw [hω]]
          simp only [wedgeEndpoints, real_inner_smul_left]
          rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
            (tangentVector (Θ.angle : Real.Angle)) = 1 by
              exact inner_tangentVector_self Θ.angle, mul_one]
        _ = _ := by rw [hcosEq]
    rw [hendpoint]
    have hcosT : 0 < Real.cos (Real.pi / 2 - t) := by simpa [hω] using hcosδ
    exact (lt_div_iff₀ hcosT).2 (by linarith [hd])
  have hendpoint_C : inner ℝ (wedgeEndpoints K.val t).2
      (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) <
      inner ℝ (capVertices K.val Θ.angle).2.1
        (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) := by
    rw [← hω]
    simpa [wedgeGaps, inner_sub_left] using hgapC
  have hCx_lt_qx : (capVertices K.val Θ.angle).2.1 0 < q 0 := by
    have h := hqcoord_endpoint.trans hendpoint_C
    simp [tangentVector, frame, PiLp.inner_apply, hω] at h
    simpa [hω] using h
  have hqx_lt_Ax : q 0 < (capVertices K.val 0).1.2 0 :=
    hqx_endpoint.trans hendpoint_A
  apply mem_segment_of_fst_mem_Icc_of_mem_normalLine (polygonCap_left_x_lt_right_x K)
    (t := Real.pi / 2) (c := 0)
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  · rw [capVertices_angle_fst_eq K]
    simp [normalLine, normalVector, tangentVector, frame, PiLp.inner_apply, hω]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]
  · exact hq.2
  · exact ⟨hCx_lt_qx.le, hqx_lt_Ax.le⟩

private theorem mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
    (t : ℝ) (c : ℝ) {q : Point} (hq : q ∈ normalLine (t : Real.Angle) c) :
    q ∈ frontier (normalHalfPlane (t : Real.Angle) c true false) := by
  have hqH : q ∈ normalHalfPlane (t : Real.Angle) c true false := by
    change c ≤ inner ℝ q (normalVector (t : Real.Angle))
    exact hq.ge
  apply (mem_frontier_iff_notMem_interior hqH).mpr
  intro hqInt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hqInt
  let e := ε / 2
  let z := q - e • normalVector (t : Real.Angle)
  have he : 0 < e := half_pos hε
  have hzball : z ∈ Metric.ball q ε := by
    change dist z q < ε
    simp [z, norm_smul, norm_normalVector_real, abs_of_pos he]
    dsimp [e]
    linarith
  have hz := interior_subset (hball hzball)
  change c ≤ inner ℝ z (normalVector (t : Real.Angle)) at hz
  change inner ℝ q (normalVector (t : Real.Angle)) = c at hq
  dsimp [z] at hz
  rw [inner_sub_left, real_inner_smul_left, inner_normalVector_self, mul_one, hq] at hz
  linarith

private theorem capFan_inter_fanLine_subset_frontier {Θ : AngleSet} {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    capFan Θ.angle ∩ normalLine (t : Real.Angle) 0 ⊆ frontier (capFan Θ.angle) := by
  intro q hq
  apply (mem_frontier_iff_notMem_interior hq.1).mpr
  intro hqInt
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · have hInt := interior_mono Set.inter_subset_left hqInt
    have hfront := mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
      Θ.angle 0 hq.2
    exact (mem_frontier_iff_notMem_interior hq.1.1).mp hfront hInt
  · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
    subst t
    have hInt := interior_mono Set.inter_subset_right hqInt
    have hfront := mem_frontier_normalHalfPlane_upper_closed_of_mem_normalLine
      (Real.pi / 2) 0 hq.2
    exact (mem_frontier_iff_notMem_interior hq.1.2).mp hfront hInt

private theorem frontier_innerQuadrant_inter_fanLine_countable
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {s t : ℝ}
    (hs : s ∈ Θ.directions) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (frontier (innerQuadrant K.val.val s) ∩ normalLine (t : Real.Angle) 0).Countable := by
  have hsI : s ∈ Set.Ioo 0 Real.pi :=
    ⟨(Θ.interior s hs).1,
      ((Θ.interior s hs).2.trans_le Θ.angle_le).trans (by linarith [Real.pi_pos])⟩
  have hsTI : s + Real.pi / 2 ∈ Set.Ioo 0 Real.pi := by
    constructor
    · linarith [(Θ.interior s hs).1, Real.pi_pos]
    · linarith [(Θ.interior s hs).2, Θ.angle_le]
  have htI : t ∈ Set.Ioo 0 Real.pi := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ⟨Θ.angle_pos, Θ.angle_le.trans_lt (by linarith [Real.pi_pos])⟩
    · rw [Set.mem_singleton_iff.mp ht]
      exact ⟨by positivity, by linarith [Real.pi_pos]⟩
  have hst : s ≠ t := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact ne_of_lt (Θ.interior s hs).2
    · rw [Set.mem_singleton_iff.mp ht]
      exact ne_of_lt ((Θ.interior s hs).2.trans_le Θ.angle_le)
  have hsTt : s + Real.pi / 2 ≠ t := by
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · intro heq
      linarith [(Θ.interior s hs).1, Θ.angle_le]
    · rw [Set.mem_singleton_iff.mp ht]
      exact ne_of_gt (by linarith [(Θ.interior s hs).1])
  refine ((normalLine_inter_normalLine_subsingleton hsI htI hst
      (c := supportValue K.val.val (s : Real.Angle) - 1) (d := 0)).countable.union
    (normalLine_inter_normalLine_subsingleton hsTI htI hsTt
      (c := supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
      (d := 0)).countable).mono ?_
  rintro q ⟨hqfront, hqline⟩
  have hfront := frontier_inter_subset
    (normalHalfPlane (s : Real.Angle) (supportValue K.val.val (s : Real.Angle) - 1)
      false true)
    (normalHalfPlane ((s + Real.pi / 2 : ℝ) : Real.Angle)
      (supportValue K.val.val ((s + Real.pi / 2 : ℝ) : Real.Angle) - 1)
      false true) hqfront
  rcases hfront with hfront | hfront
  · exact Or.inl ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hfront.1,
      hqline⟩
  · exact Or.inr ⟨frontier_normalHalfPlane_lower_strict_subset_normalLine _ _ hfront.2,
      hqline⟩

private theorem frontier_polygonNiche_inter_fanLine_eq_niche_inter
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    Measure.hausdorffMeasure 1
        (frontier (polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0) := by
  let X : Set Point := ⋃ s ∈ Θ.directions, innerQuadrant K.val.val s
  have hN : polygonNiche Θ K.val = capFan Θ.angle ∩ X := by simp [polygonNiche, X]
  rw [hN]
  apply measure_eq_of_symmDiff_subset_null (E := frontier X ∩ normalLine (t : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · refine ⟨?_, hq.1.2⟩
      rw [← closure_sdiff_interior]
      refine ⟨closure_mono Set.inter_subset_right (frontier_subset_closure hq.1.1), ?_⟩
      intro hqInt
      have hqX : q ∈ X := interior_subset hqInt
      have hqF : q ∈ capFan Θ.angle := by
        have hqcl := frontier_subset_closure hq.1.1
        exact (isClosed_capFan Θ.angle).closure_eq ▸
          closure_mono Set.inter_subset_left hqcl
      exact hq.2 ⟨⟨hqF, hqX⟩, hq.1.2⟩
    · have hqFront : q ∈ frontier (capFan Θ.angle ∩ X) := by
        apply (mem_frontier_iff_notMem_interior hq.1.1).mpr
        intro hqInt
        have hqFInt := interior_mono Set.inter_subset_left hqInt
        exact (mem_frontier_iff_notMem_interior hq.1.1.1).mp
          (capFan_inter_fanLine_subset_frontier ht ⟨hq.1.1.1, hq.1.2⟩) hqFInt
      exact (hq.2 ⟨hqFront, hq.1.2⟩).elim
  · have hcount : (frontier X ∩ normalLine (t : Real.Angle) 0).Countable := by
      refine (Set.Countable.biUnion Θ.directions.countable_toSet fun s hs ↦
        frontier_innerQuadrant_inter_fanLine_countable K hs ht).mono ?_
      rintro q ⟨hqX, hqline⟩
      have hqUnion := Finset.frontier_biUnion_subset Θ.directions
        (fun s ↦ innerQuadrant K.val.val s) hqX
      obtain ⟨s, hs, hqs⟩ := Set.mem_iUnion₂.mp hqUnion
      exact Set.mem_iUnion₂.mpr ⟨s, hs, ⟨hqs, hqline⟩⟩
    have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
    exact hcount.measure_zero (Measure.hausdorffMeasure 1)

private theorem capVertices_zero_fst_pos_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    0 < (capVertices K.val 0).1.2 0 := by
  obtain ⟨u, huK, hu⟩ := exists_mem_inner_eq_supportValue K.val.val
    (Θ.angle : Real.Angle)
  have huy : u 1 ≤ 1 := by
    have huy' := inner_le_supportValue K.val.val huK
      ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.val.property.2.2.2.1] at huy'
    simpa [normalVector, frame, PiLp.inner_apply] using huy'
  have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
  have hsin_lt : Real.sin Θ.angle < 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq Θ.angle, sq_pos_of_pos hcos]
  have hux : 0 < u 0 := by
    rw [K.val.property.2.2.1] at hu
    simp [normalVector, frame, PiLp.inner_apply] at hu
    have hsin : 0 ≤ Real.sin Θ.angle :=
      (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
        (Θ.angle_le.trans_lt (by linarith [Real.pi_pos]))).le
    have hmul := mul_le_mul_of_nonneg_left huy hsin
    nlinarith
  have hsupport : 0 < supportValue K.val.val (0 : Real.Angle) :=
    hux.trans_le (by
      have := inner_le_supportValue K.val.val huK (0 : Real.Angle)
      simpa [normalVector, frame, PiLp.inner_apply] using this)
  rw [capVertices_zero_snd_eq K]
  simpa [normalVector, frame] using hsupport

private theorem hausdorffMeasure_bottom_exposedEdge_sdiff_niche_eq_carrier_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩
          normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  let L := openRay C (tangentVector (Θ.angle : Real.Angle))
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  apply measure_eq_of_symmDiff_subset_null (E :=
    L ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1.1
      have hqFrontF := capFan_inter_fanLine_subset_frontier
        (Θ := Θ) (t := Real.pi / 2) (by simp) ⟨hqF, hq.1.2⟩
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.1.2⟩
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        apply (mem_frontier_iff_notMem_interior hqC).mpr
        intro hqInt
        exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
          (interior_mono Set.sdiff_subset hqInt)
      rw [hp.2.2.2.2.2.1] at hqFrontC
      rcases hqFrontC with hqL | hqR
      · rcases hqL with hqL | hqcarrier
        · exact ⟨hqL, hq.1.2⟩
        · exact (hq.2 ⟨hqcarrier, hq.1.2⟩).elim
      · rcases hqR with ⟨r, hr, hqr⟩
        have hD := hq.1.1.1
        rw [exposedEdge_bottom_eq_segment_zero_right K hω] at hD
        have hApos : 0 < A 0 := capVertices_zero_fst_pos_of_lt K hω
        have hqx := (fst_mem_Icc_of_mem_segment hApos.le hD).2
        have hqx' : A 0 < q 0 := by
          rw [hqr]
          simp [A, normalVector, frame]
          linarith
        linarith
    · have hD := polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_lt
        K hω hq.1
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1)
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
        hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
      exact (hq.2 ⟨⟨hD, hqC.2⟩, hq.1.2⟩).elim
  · have hinner : inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≠ 0 := by
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
      simpa [tangentVector, normalVector, frame, PiLp.inner_apply,
        Fin.sum_univ_two] using hcos.ne'
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hinner

private theorem hausdorffMeasure_left_exposedEdge_sdiff_niche_eq_carrier_of_lt
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine (Θ.angle : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (Θ.angle : Real.Angle) 0) := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  let R := openRay A (normalVector 0)
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  have hCeq := capVertices_angle_fst_eq K
  change C = supportValue K.val.val
    ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) •
      tangentVector (Θ.angle : Real.Angle) at hCeq
  have hL : 0 ≤ supportValue K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) :=
    supportValue_nonneg_of_mem_capUpperAngles K.val hω
      (Or.inr ⟨by linarith [Θ.angle_pos, Real.pi_pos], le_rfl⟩)
  have hCcoord : 0 ≤ inner ℝ C (tangentVector (Θ.angle : Real.Angle)) := by
    rw [hCeq, real_inner_smul_left]
    rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
      (tangentVector (Θ.angle : Real.Angle)) = 1 by
        exact inner_tangentVector_self Θ.angle, mul_one]
    exact hL
  apply measure_eq_of_symmDiff_subset_null (E :=
    R ∩ normalLine (Θ.angle : Real.Angle) 0)
  · intro q hq
    rcases hq with hq | hq
    · have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1.1
      have hqFrontF := capFan_inter_fanLine_subset_frontier
        (Θ := Θ) (t := Θ.angle) (by simp) ⟨hqF, hq.1.2⟩
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.1.2⟩
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        apply (mem_frontier_iff_notMem_interior hqC).mpr
        intro hqInt
        exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
          (interior_mono Set.sdiff_subset hqInt)
      rw [hp.2.2.2.2.2.1] at hqFrontC
      rcases hqFrontC with hqL | hqR
      · rcases hqL with hqL | hqcarrier
        · rcases hqL with ⟨r, hr, hqr⟩
          have hD := hq.1.1.1
          rw [exposedEdge_left_eq_segment_zero_left K hω] at hD
          rcases hD with ⟨u, v, hu, hv, huv, hqseg⟩
          have hvle : v ≤ 1 := by linarith
          have hqcoord_le : inner ℝ q (tangentVector (Θ.angle : Real.Angle)) ≤
              inner ℝ C (tangentVector (Θ.angle : Real.Angle)) := by
            rw [← hqseg, inner_add_left, real_inner_smul_left,
              real_inner_smul_left, inner_zero_left, mul_zero, zero_add]
            exact mul_le_of_le_one_left hCcoord hvle
          have hqcoord_gt : inner ℝ C (tangentVector (Θ.angle : Real.Angle)) <
              inner ℝ q (tangentVector (Θ.angle : Real.Angle)) := by
            change inner ℝ (capVertices K.val Θ.angle).2.1
                (tangentVector (Θ.angle : Real.Angle)) <
              inner ℝ q (tangentVector (Θ.angle : Real.Angle))
            rw [hqr, inner_add_left, real_inner_smul_left]
            rw [show inner ℝ (tangentVector (Θ.angle : Real.Angle))
              (tangentVector (Θ.angle : Real.Angle)) = 1 by
                exact inner_tangentVector_self Θ.angle]
            simp
            exact hr
          exact (not_lt_of_ge hqcoord_le hqcoord_gt).elim
        · exact (hq.2 ⟨hqcarrier, hq.1.2⟩).elim
      · exact ⟨hqR, hq.1.2⟩
    · have hD := polygonCapPolyline_carrier_inter_left_subset_exposedEdge_of_lt
        K hω hq.1
      have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
        rw [hp.2.2.2.2.2.1]
        exact Or.inl (Or.inr hq.1.1)
      have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
        hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
      exact (hq.2 ⟨⟨hD, hqC.2⟩, hq.1.2⟩).elim
  · have hinner : inner ℝ (normalVector 0)
        (normalVector (Θ.angle : Real.Angle)) ≠ 0 := by
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩
      rw [show (0 : Real.Angle) = ((0 : ℝ) : Real.Angle) by rfl,
        inner_normalVector_normalVector, zero_sub, Real.cos_neg]
      exact hcos.ne'
    exact hausdorffMeasure_openRay_inter_hyperplane_eq_zero hinner

private theorem bottom_exposedEdge_sdiff_niche_inter_eq_carrier_of_eq
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    (exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) \
        polygonNiche Θ K.val) ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 =
      (polygonCapPolyline K).carrier ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  let p := polygonCapPolyline K
  let A := (capVertices K.val 0).1.2
  let C := (capVertices K.val Θ.angle).2.1
  have hp : IsCapPolyline K p := polygonCapPolyline_spec K
  have hclosed : IsClosed (capFan Θ.angle \ polygonNiche Θ K.val) := hp.2.2.2.2.1
  ext q
  constructor
  · intro hq
    have hqF : q ∈ capFan Θ.angle := K.val.subset_capFan hq.1.1.1
    have hqFrontF := capFan_inter_fanLine_subset_frontier
      (Θ := Θ) (t := Real.pi / 2) (by simp) ⟨hqF, hq.2⟩
    have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val := ⟨hqF, hq.1.2⟩
    have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      apply (mem_frontier_iff_notMem_interior hqC).mpr
      intro hqInt
      exact (mem_frontier_iff_notMem_interior hqF).mp hqFrontF
        (interior_mono Set.sdiff_subset hqInt)
    rw [hp.2.2.2.2.2.1] at hqFrontC
    rcases hqFrontC with hqL | hqR
    · rcases hqL with hqL | hqcarrier
      · rcases hqL with ⟨r, hr, hqr⟩
        have hD := hq.1.1
        rw [exposedEdge_bottom_eq_segment_left_right K hω] at hD
        have hqx := fst_mem_Icc_of_mem_segment
          (polygonCap_left_x_lt_right_x K).le hD
        have hqx' : q 0 < C 0 := by
          rw [hqr]
          simp [C, tangentVector, frame, hω]
          exact hr
        exact (not_lt_of_ge (by simpa [C] using hqx.1) hqx').elim
      · exact ⟨hqcarrier, hq.2⟩
    · rcases hqR with ⟨r, hr, hqr⟩
      have hD := hq.1.1
      rw [exposedEdge_bottom_eq_segment_left_right K hω] at hD
      have hqx := fst_mem_Icc_of_mem_segment
        (polygonCap_left_x_lt_right_x K).le hD
      have hqx' : A 0 < q 0 := by
        rw [hqr]
        simp [A, normalVector, frame]
        exact hr
      exact (not_lt_of_ge (by simpa [A] using hqx.2) hqx').elim
  · intro hq
    have hD := polygonCapPolyline_carrier_inter_bottom_subset_exposedEdge_of_eq
      K hω hq
    have hqFrontC : q ∈ frontier (capFan Θ.angle \ polygonNiche Θ K.val) := by
      rw [hp.2.2.2.2.2.1]
      exact Or.inl (Or.inr hq.1)
    have hqC : q ∈ capFan Θ.angle \ polygonNiche Θ K.val :=
      hclosed.closure_eq ▸ frontier_subset_closure hqFrontC
    exact ⟨⟨hD, hqC.2⟩, hq.2⟩

private theorem segment_subset_normalLine {a b : Point} {t : Real.Angle} {c : ℝ}
    (ha : a ∈ normalLine t c) (hb : b ∈ normalLine t c) :
    segment ℝ a b ⊆ normalLine t c := by
  rintro q ⟨u, v, hu, hv, huv, rfl⟩
  change inner ℝ (u • a + v • b) (normalVector t) = c
  change inner ℝ a (normalVector t) = c at ha
  change inner ℝ b (normalVector t) = c at hb
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, ha, hb]
  linear_combination c * huv

private theorem hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier
    {Θ : AngleSet} (K : PolygonCapSpace Θ) {t : ℝ}
    (hDline : exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle) ⊆
      normalLine (t : Real.Angle) 0)
    (hNsub : polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))
    (hcomp : Measure.hausdorffMeasure 1
        ((exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle) \
          polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0) =
      Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)) :
    (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0)).toReal =
      (Measure.hausdorffMeasure 1
        (exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))).toReal -
      (Measure.hausdorffMeasure 1
        ((polygonCapPolyline K).carrier ∩ normalLine (t : Real.Angle) 0)).toReal := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let D := exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle)
  let M := polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0
  have hdiff : D \ M =
      (D \ polygonNiche Θ K.val) ∩ normalLine (t : Real.Angle) 0 := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨hq.1, fun hqN ↦ hq.2 ⟨hqN, hDline hq.1⟩⟩, hDline hq.1⟩
    · intro hq
      exact ⟨hq.1.1, fun hqM ↦ hq.1.2 hqM.1⟩
  have hNMeas : MeasurableSet (polygonNiche Θ K.val) := by
    exact (isClosed_capFan Θ.angle).measurableSet.inter
      (isOpen_iUnion fun s ↦ isOpen_iUnion fun _ ↦
        isOpen_innerQuadrant K.val.val s).measurableSet
  have hMMeas : MeasurableSet M :=
    hNMeas.inter (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hDfinite : μ D ≠ ⊤ := by
    dsimp [μ, D]
    rw [exposedEdge_eq_segment_edgeVertices, MeasureTheory.hausdorffMeasure_segment,
      edist_dist]
    simp
  have hreal := MeasureTheory.measureReal_sdiff (μ := μ) hNsub hMMeas hDfinite
  change (μ (D \ M)).toReal = (μ D).toReal - (μ M).toReal at hreal
  rw [hdiff] at hreal
  have hcompReal := congrArg ENNReal.toReal hcomp
  dsimp [μ, D, M] at hreal hcompReal ⊢
  rw [hcompReal] at hreal
  linarith

private theorem bottom_exposedEdge_subset_fanLine_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) ⊆
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  rw [exposedEdge_bottom_eq_segment_zero_right K hω]
  apply segment_subset_normalLine
  · simp [normalLine]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]

private theorem left_exposedEdge_subset_fanLine_of_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    exposedEdge K.val.val ((Θ.angle + Real.pi : ℝ) : Real.Angle) ⊆
      normalLine (Θ.angle : Real.Angle) 0 := by
  rw [exposedEdge_left_eq_segment_zero_left K hω]
  apply segment_subset_normalLine
  · simp [normalLine]
  · change inner ℝ (capVertices K.val Θ.angle).2.1
      (normalVector (Θ.angle : Real.Angle)) = 0
    rw [capVertices_angle_fst_eq K, real_inner_smul_left,
      show inner ℝ (tangentVector (Θ.angle : Real.Angle))
        (normalVector (Θ.angle : Real.Angle)) = 0 by
          rw [real_inner_comm, inner_normalVector_tangentVector], mul_zero]

private theorem bottom_exposedEdge_subset_fanLine_of_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle = Real.pi / 2) :
    exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) ⊆
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 := by
  rw [exposedEdge_bottom_eq_segment_left_right K hω]
  apply segment_subset_normalLine
  · rw [capVertices_angle_fst_eq K]
    simp [normalLine, normalVector, tangentVector, frame, PiLp.inner_apply, hω]
  · rw [capVertices_zero_snd_eq K]
    simp [normalLine, normalVector, frame, PiLp.inner_apply]

private theorem polygonNiche_fanLine_length {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩ normalLine (t : Real.Angle) 0)).toReal =
      (Measure.hausdorffMeasure 1
        (exposedEdge K.val.val ((t + Real.pi : ℝ) : Real.Angle))).toReal -
      polygonPolylineLengthAt K t := by
  by_cases hω : Θ.angle < Real.pi / 2
  · rcases Set.mem_insert_iff.mp ht with rfl | ht
    · rw [← polygonCapPolyline_fanLine_length K (by simp)]
      exact hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
        (left_exposedEdge_subset_fanLine_of_lt K hω)
        (polygonNiche_inter_left_subset_exposedEdge_of_lt K hω)
        (hausdorffMeasure_left_exposedEdge_sdiff_niche_eq_carrier_of_lt K hω)
    · have ht : t = Real.pi / 2 := Set.mem_singleton_iff.mp ht
      subst t
      rw [← polygonCapPolyline_fanLine_length K (by simp)]
      apply hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
      · convert bottom_exposedEdge_subset_fanLine_of_lt K hω using 1 ; ring_nf
      · convert polygonNiche_inter_bottom_subset_exposedEdge_of_lt K hω using 1 ; ring_nf
      · convert hausdorffMeasure_bottom_exposedEdge_sdiff_niche_eq_carrier_of_lt
          K hω using 1 ; ring_nf
  · have hωeq : Θ.angle = Real.pi / 2 := le_antisymm Θ.angle_le (le_of_not_gt hω)
    have htT : t = Real.pi / 2 := by
      rcases Set.mem_insert_iff.mp ht with ht | ht
      · exact ht.trans hωeq
      · exact Set.mem_singleton_iff.mp ht
    subst t
    rw [← polygonCapPolyline_fanLine_length K (by simp)]
    apply hausdorffMeasure_niche_inter_eq_exposedEdge_sub_carrier K
    · convert bottom_exposedEdge_subset_fanLine_of_eq K hωeq using 1 ; ring_nf
    · convert polygonNiche_inter_bottom_subset_exposedEdge_of_eq K hωeq using 1 ; ring_nf
    · convert congrArg (Measure.hausdorffMeasure 1)
        (bottom_exposedEdge_sdiff_niche_inter_eq_carrier_of_eq K hωeq) using 1 ;
        ring_nf

/-- The niche trace on a fan line is the lower face length minus polyline length. -/
theorem polygonNiche_fanLine_lengths {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {t : ℝ} (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    nicheBoundaryLength K (normalLine t 0) =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t ∧
      (Measure.hausdorffMeasure 1
        (polygonNiche Θ K.val ∩ normalLine t 0)).toReal =
        (surfaceAreaMeasure K.val.val {((t + Real.pi : ℝ) : Real.Angle)}).toReal -
          polygonPolylineLengthAt K t := by
  have hN := polygonNiche_fanLine_length K ht
  have hatom := congrArg ENNReal.toReal
    (surfaceAreaMeasure_atom_length K.val.val
      ((t + Real.pi : ℝ) : Real.Angle)).1
  rw [← hatom] at hN
  refine ⟨?_, hN⟩
  unfold nicheBoundaryLength
  rw [frontier_polygonNiche_inter_fanLine_eq_niche_inter K ht]
  exact hN

/-- Inner-wall and inner-ray niche lengths agree with the corresponding polyline lengths. -/
theorem polygonNiche_wall_lengths {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {t : ℝ} (ht : t ∈ Θ.directions) :
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).b =
      polygonPolylineLengthAt K t ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).bRay =
      polygonPolylineLengthAt K t ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).d =
      polygonPolylineLengthAt K (t + Real.pi / 2) ∧
    nicheBoundaryLength K (rotatingHallwayParts (K.val.val : Set Point) t).dRay =
      polygonPolylineLengthAt K (t + Real.pi / 2) := by
  have hf := rotatingHallwayParts_formulas
    (K.val.val : Set Point) (t : Real.Angle)
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold nicheBoundaryLength
    rw [hf.2.2.2.2.1]
    exact polygonNiche_bLine_length K ht
  · unfold nicheBoundaryLength
    exact polygonNiche_bRay_length K ht
  · unfold nicheBoundaryLength
    rw [hf.2.2.2.2.2.2.1]
    exact polygonNiche_dLine_length K ht
  · unfold nicheBoundaryLength
    exact polygonNiche_dRay_length K ht

end MovingSofa
