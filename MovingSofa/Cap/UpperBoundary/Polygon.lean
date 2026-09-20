import MovingSofa.Cap.AngleDomain
import MovingSofa.Cap.PolylineBoundary
import MovingSofa.Geometry.Convex.HorizontalExtrema
import MovingSofa.Polygon.Polyline.Measure
import MovingSofa.Polygon.Polyline.Displacement

noncomputable section

namespace MovingSofa

open MeasureTheory

private lemma PolygonCapSpace.eq_of_mem_of_fst_eq_of_fst_extremal {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : Point}
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hab : a 0 = b 0)
    (hext : (∀ q ∈ (K.val.val : Set Point), q 0 ≤ a 0) ∨
      (∀ q ∈ (K.val.val : Set Point), a 0 ≤ q 0)) : a = b := by
  apply ConvexBody.eq_of_mem_of_fst_eq_of_fst_extremal K.val.val
    (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle)
    _ K.property _ ha hb hab hext
  · have hfinite : (angleDomain Θ).Finite := by
      unfold angleDomain
      exact (Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
          (Set.toFinite _)
    exact (hfinite.image _).union (by simp [capLowerNormals])
  · intro t ht
    rcases ht with ⟨r, hr, rfl⟩ | ht
    · exact (Real.sin_pos_of_pos_of_lt_pi
        (angleDomain_subset_Ioo Θ hr).1 (angleDomain_subset_Ioo Θ hr).2).ne'
    · simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl
      · change Real.sin (Θ.angle + Real.pi) ≠ 0
        rw [Real.sin_add_pi]
        exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
          (by linarith [Θ.angle_le, Real.pi_pos])).ne'
      · change Real.sin (3 * Real.pi / 2) ≠ 0
        norm_num [show 3 * Real.pi / 2 = Real.pi + Real.pi / 2 by ring,
          Real.sin_add]



private def upperSupportAffine (K : ConvexBody Point) (t : ℝ) : ℝ × ℝ :=
  (-Real.cos t / Real.sin t, supportValue K (t : Real.Angle) / Real.sin t)

private def upperSupportHeight (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) (x : ℝ) : ℝ :=
  D.inf' hne (fun t ↦ affineValue (upperSupportAffine K t) x)

private lemma continuous_upperSupportHeight (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) : Continuous (upperSupportHeight K D hne) := by
  apply Continuous.finset_inf'_apply hne
  intro t ht
  exact continuous_affineValue _

private lemma upperSupportHeight_eq_affineValue (K : ConvexBody Point) (D : Finset ℝ)
    (hne : D.Nonempty) (x : ℝ) :
    ∃ c ∈ D.image (upperSupportAffine K),
      upperSupportHeight K D hne x = affineValue c x := by
  obtain ⟨t, ht, heq⟩ := Finset.exists_mem_eq_inf' hne
    (fun t ↦ affineValue (upperSupportAffine K t) x)
  exact ⟨upperSupportAffine K t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, heq⟩

private lemma inner_le_support_iff_snd_le_affine (K : ConvexBody Point)
    {t : ℝ} (ht : 0 < Real.sin t) (q : Point) :
    inner ℝ q (normalVector (t : Real.Angle)) ≤ supportValue K (t : Real.Angle) ↔
      q 1 ≤ affineValue (upperSupportAffine K t) (q 0) := by
  have hformula : affineValue (upperSupportAffine K t) (q 0) =
      (supportValue K (t : Real.Angle) - q 0 * Real.cos t) / Real.sin t := by
    simp only [affineValue, upperSupportAffine]
    ring
  rw [hformula, le_div_iff₀ ht]
  simp only [normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  simp
  constructor <;> intro h <;> nlinarith

private lemma snd_le_upperSupportHeight_iff (K : ConvexBody Point)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : ∀ t ∈ D, 0 < Real.sin t) (q : Point) :
    q 1 ≤ upperSupportHeight K D hne (q 0) ↔
      ∀ t ∈ D, inner ℝ q (normalVector (t : Real.Angle)) ≤
        supportValue K (t : Real.Angle) := by
  rw [upperSupportHeight, Finset.le_inf'_iff]
  exact forall_congr' fun t ↦ forall_congr' fun ht ↦
    (inner_le_support_iff_snd_le_affine K (hD t ht) q).symm

private lemma PolygonCapSpace.mem_iff_mem_capFan_and_support_le {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (p : Point) :
    p ∈ (K.val.val : Set Point) ↔ p ∈ capFan Θ.angle ∧
      ∀ t ∈ angleDomain Θ,
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val.val (t : Real.Angle) := by
  constructor
  · intro hp
    exact ⟨K.val.subset_capFan hp, fun t _ ↦ inner_le_supportValue K.val.val hp _⟩
  · rintro ⟨hp, hupper⟩
    rw [K.property.eq_iInter_supportValue]
    simp only [Set.mem_iInter]
    intro a ha
    rcases ha with ⟨t, ht, rfl⟩ | ha
    · exact hupper t ht
    rcases ha with rfl | rfl
    · change inner ℝ p (normalVector ((Θ.angle + Real.pi : ℝ) : Real.Angle)) ≤ _
      rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
      exact neg_nonpos.mpr hp.1
    · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
          (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
      rw [K.val.property.2.2.2.2.2.1, hang, normalVector_add_pi, inner_neg_right]
      exact neg_nonpos.mpr hp.2

private lemma mem_capFan_of_fst_eq_of_snd_le {ω : ℝ} (hω : 0 ≤ Real.sin ω)
    {p q : Point} (hp : p ∈ capFan ω) (hx : p 0 = q 0) (hy : p 1 ≤ q 1) :
    q ∈ capFan ω := by
  change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle)) ∧
    0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
  change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) ∧
    0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hp
  simp [normalVector, frame, PiLp.inner_apply] at hp ⊢
  rw [hx] at hp
  constructor
  · nlinarith [hp.1, mul_nonneg hω (sub_nonneg.mpr hy)]
  · exact hp.2.trans hy

private lemma pointOnGraph_upperSupportHeight_mem {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : (D : Set ℝ) = angleDomain Θ)
    (hsin : ∀ t ∈ D, 0 < Real.sin t) {x : ℝ}
    (hx : ∃ q ∈ (K.val.val : Set Point), q 0 = x) :
    pointOnGraph (upperSupportHeight K.val.val D hne) x ∈ (K.val.val : Set Point) := by
  obtain ⟨q, hq, hqx⟩ := hx
  have hqle : q 1 ≤ upperSupportHeight K.val.val D hne x := by
    rw [← hqx, snd_le_upperSupportHeight_iff K.val.val D hne hsin]
    exact fun t _ ↦ inner_le_supportValue K.val.val hq _
  apply (K.mem_iff_mem_capFan_and_support_le _).mpr
  constructor
  · apply mem_capFan_of_fst_eq_of_snd_le
      (Real.sin_nonneg_of_nonneg_of_le_pi Θ.angle_pos.le
        (Θ.angle_le.trans (by linarith [Real.pi_pos]))) (K.val.subset_capFan hq)
    · exact hqx
    · exact hqle
  · intro t ht
    have htD : t ∈ D := by change t ∈ (D : Set ℝ); rwa [hD]
    apply (inner_le_support_iff_snd_le_affine K.val.val (hsin t htD) _).mpr
    change upperSupportHeight K.val.val D hne x ≤
      affineValue (upperSupportAffine K.val.val t) x
    exact Finset.inf'_le _ htD

private lemma exists_upperSupportHeight_polyline {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (D : Finset ℝ) (hne : D.Nonempty) (hD : (D : Set ℝ) = angleDomain Θ)
    (hsin : ∀ t ∈ D, 0 < Real.sin t) {a b : ℝ} (hab : a < b)
    (hfeasible : ∀ x ∈ Set.Icc a b, ∃ q ∈ (K.val.val : Set Point), q 0 = x) :
    ∃ p : XMonotonePolylineData,
      0 < p.edges ∧
      p.vertices 0 = pointOnGraph (upperSupportHeight K.val.val D hne) a ∧
      p.vertices (Fin.last p.edges) = pointOnGraph (upperSupportHeight K.val.val D hne) b ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) '' Set.Icc a b ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  obtain ⟨p, hp, hpa, hpb, hcarrier, hvertices, hpieces⟩ :=
    exists_graphPolyline_of_finite_affine_selector hab (D.image (upperSupportAffine K.val.val))
      (continuous_upperSupportHeight K.val.val D hne).continuousOn
      (fun x _ ↦ upperSupportHeight_eq_affineValue K.val.val D hne x)
  refine ⟨p, hp, hpa, hpb, hcarrier, ?_, ?_⟩
  · rw [hcarrier]
    rintro q ⟨x, hx, rfl⟩
    exact pointOnGraph_upperSupportHeight_mem K D hne hD hsin (hfeasible x hx)
  · intro i
    obtain ⟨c, hc, heq⟩ := hpieces i
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hc
    refine ⟨t, ht, ?_, ?_⟩
    · rw [hvertices i.succ, hvertices i.castSucc]
      apply inner_pointOnGraph_sub_normalVector_eq_zero heq
        (p.increasing i.castSucc_lt_succ).le
      dsimp [upperSupportAffine]
      field_simp [(hsin t ht).ne']
      ring
    · have hstart := heq ⟨le_rfl, (p.increasing i.castSucc_lt_succ).le⟩
      rw [hvertices i.castSucc]
      simp only [pointOnGraph, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
      simp only [Real.Angle.cos_coe, Real.Angle.sin_coe]
      change Real.cos t * (p.vertices i.castSucc) 0 +
        Real.sin t * upperSupportHeight K.val.val D hne ((p.vertices i.castSucc) 0) = _
      rw [hstart]
      dsimp [upperSupportAffine, affineValue]
      field_simp [(hsin t ht).ne']
      ring

private lemma exists_upperSupportHeight_polyline_with_endpoints {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) {a b : Point}
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hab : a 0 < b 0)
    (hmin : ∀ q ∈ (K.val.val : Set Point), a 0 ≤ q 0)
    (hmax : ∀ q ∈ (K.val.val : Set Point), q 0 ≤ b 0) :
    ∃ p : XMonotonePolylineData, 0 < p.edges ∧ p.vertices 0 = a ∧
      p.vertices (Fin.last p.edges) = b ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) '' Set.Icc (a 0) (b 0) ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  have hsin : ∀ t ∈ D, 0 < Real.sin t := by
    intro t ht
    have ht' : t ∈ angleDomain Θ := hD ▸ ht
    exact Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ ht').1
      (angleDomain_subset_Ioo Θ ht').2
  obtain ⟨p, hp, hpa, hpb, hc, hK, hn⟩ :=
    exists_upperSupportHeight_polyline K D hne hD hsin hab
      (fun _ hx ↦ ConvexBody.exists_mem_fst_eq_of_mem_Icc K.val.val ha hb hab hx)
  refine ⟨p, hp, ?_, ?_, hc, hK, hn⟩
  · rw [hpa]
    apply K.eq_of_mem_of_fst_eq_of_fst_extremal
      (pointOnGraph_upperSupportHeight_mem K D hne hD hsin ⟨a, ha, rfl⟩) ha rfl
    exact Or.inr hmin
  · rw [hpb]
    apply K.eq_of_mem_of_fst_eq_of_fst_extremal
      (pointOnGraph_upperSupportHeight_mem K D hne hD hsin ⟨b, hb, rfl⟩) hb rfl
    exact Or.inl hmax

/-- The terminal cap contacts bound every horizontal coordinate of a polygon cap. -/
lemma PolygonCapSpace.capVertices_fst_bounds {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {q : Point} (hq : q ∈ (K.val.val : Set Point)) :
    ((capVertices K.val Θ.angle).2.1) 0 ≤ q 0 ∧
      q 0 ≤ ((capVertices K.val 0).1.2) 0 := by
  constructor
  · rw [capVertices_angle_fst_eq]
    have hu := (K.val.subset_capFan hq).1
    have hv := inner_le_supportValue K.val.val hq
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)
    have hs : 0 ≤ Real.sin Θ.angle := (Real.sin_pos_of_pos_of_lt_pi Θ.angle_pos
      (by linarith [Θ.angle_le, Real.pi_pos])).le
    have hc : 0 ≤ Real.cos Θ.angle := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Θ.angle_pos, Real.pi_pos], Θ.angle_le⟩
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hu
    simp [normalVector, tangentVector, frame, PiLp.inner_apply,
      Real.Angle.cos_add_pi_div_two, Real.Angle.sin_add_pi_div_two] at hu hv ⊢
    nlinarith [congrArg (fun z : ℝ ↦ z * q 0) (Real.sin_sq_add_cos_sq Θ.angle),
      mul_nonneg hu hc, mul_le_mul_of_nonneg_right hv hs,
      sq_nonneg (Real.sin Θ.angle), sq_nonneg (Real.cos Θ.angle)]
  · have hq' := inner_le_supportValue K.val.val hq (0 : Real.Angle)
    have hA := (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).2
    change inner ℝ ((capVertices K.val 0).1.2) (normalVector (0 : Real.Angle)) =
      supportValue K.val.val (0 : Real.Angle) at hA
    simp [normalVector, frame, PiLp.inner_apply] at hq' hA
    linarith

private lemma PolygonCapSpace.exists_upperBoundary_polyline {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) :
    ∃ p : XMonotonePolylineData, 0 < p.edges ∧
      p.vertices 0 = (capVertices K.val Θ.angle).2.1 ∧
      p.vertices (Fin.last p.edges) = (capVertices K.val 0).1.2 ∧
      p.carrier = pointOnGraph (upperSupportHeight K.val.val D hne) ''
        Set.Icc (((capVertices K.val Θ.angle).2.1) 0)
          (((capVertices K.val 0).1.2) 0) ∧
      p.carrier ⊆ (K.val.val : Set Point) ∧
      ∀ i : Fin p.edges, ∃ t ∈ D,
        inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 ∧
        inner ℝ (p.vertices i.castSucc) (normalVector (t : Real.Angle)) =
          supportValue K.val.val (t : Real.Angle) := by
  apply exists_upperSupportHeight_polyline_with_endpoints K D hne hD
    (edgeVertices_fst_mem K.val.val
      ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
    (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
    (polygonCap_left_x_lt_right_x K)
  · exact fun q hq ↦ (K.capVertices_fst_bounds hq).1
  · exact fun q hq ↦ (K.capVertices_fst_bounds hq).2

private lemma PolygonCapSpace.exposedEdge_eq_upperSupportGraph_inter {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) {t : ℝ} (ht : t ∈ D) :
    exposedEdge K.val.val (t : Real.Angle) =
      (pointOnGraph (upperSupportHeight K.val.val D hne) ''
        Set.Icc (((capVertices K.val Θ.angle).2.1) 0)
          (((capVertices K.val 0).1.2) 0)) ∩
      {q | inner ℝ q (normalVector (t : Real.Angle)) =
        supportValue K.val.val (t : Real.Angle)} := by
  have hsin : ∀ r ∈ D, 0 < Real.sin r := by
    intro r hr
    have hr' : r ∈ angleDomain Θ := hD ▸ hr
    exact Real.sin_pos_of_pos_of_lt_pi (angleDomain_subset_Ioo Θ hr').1
      (angleDomain_subset_Ioo Θ hr').2
  ext q
  constructor
  · rintro ⟨hq, heq⟩
    refine ⟨⟨q 0, K.capVertices_fst_bounds hq, ?_⟩, heq⟩
    have hle : q 1 ≤ upperSupportHeight K.val.val D hne (q 0) :=
      (snd_le_upperSupportHeight_iff K.val.val D hne hsin q).mpr
        (fun r _ ↦ inner_le_supportValue K.val.val hq _)
    have hge := Finset.inf'_le (fun r ↦ affineValue (upperSupportAffine K.val.val r) (q 0)) ht
    have haff : affineValue (upperSupportAffine K.val.val t) (q 0) = q 1 := by
      change inner ℝ q (normalVector (t : Real.Angle)) =
        supportValue K.val.val (t : Real.Angle) at heq
      simp [normalVector, frame, PiLp.inner_apply] at heq
      dsimp [affineValue, upperSupportAffine]
      field_simp [(hsin t ht).ne']
      nlinarith [heq]
    have hy : upperSupportHeight K.val.val D hne (q 0) = q 1 :=
      le_antisymm (haff ▸ hge) hle
    ext i
    fin_cases i
    · rfl
    · exact hy
  · rintro ⟨⟨x, hx, rfl⟩, heq⟩
    refine ⟨pointOnGraph_upperSupportHeight_mem K D hne hD hsin ?_, heq⟩
    exact ConvexBody.exists_mem_fst_eq_of_mem_Icc K.val.val
      (edgeVertices_fst_mem K.val.val
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle)).1
      (edgeVertices_snd_mem K.val.val (0 : Real.Angle)).1
      (polygonCap_left_x_lt_right_x K) hx

/-- The sine-weighted exposed-face lengths equal the horizontal separation of cap contacts. -/
lemma PolygonCapSpace.sum_hausdorffMeasure_exposedEdge_mul_sin {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (D : Finset ℝ) (hne : D.Nonempty)
    (hD : (D : Set ℝ) = angleDomain Θ) :
    ∑ t ∈ D, (Measure.hausdorffMeasure 1 (exposedEdge K.val.val (t : Real.Angle))).toReal *
      Real.sin t = ((capVertices K.val 0).1.2) 0 - ((capVertices K.val Θ.angle).2.1) 0 := by
  classical
  obtain ⟨p, hp, hpa, hpb, hc, hK, hn⟩ := K.exists_upperBoundary_polyline D hne hD
  have hangle : ∀ t ∈ D, t ∈ Set.Ioo 0 Real.pi := by
    intro t ht
    exact angleDomain_subset_Ioo Θ (hD ▸ ht)
  have hface (t : ℝ) (ht : t ∈ D) :
      (Measure.hausdorffMeasure 1 (exposedEdge K.val.val (t : Real.Angle))).toReal =
        ∑ i : Fin p.edges,
          if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
            (normalVector (t : Real.Angle)) = 0 then
            dist (p.vertices i.castSucc) (p.vertices i.succ) else 0 := by
    rw [K.exposedEdge_eq_upperSupportGraph_inter D hne hD ht, ← hc]
    apply p.toReal_hausdorffMeasure_carrier_inter_hyperplane
    intro i hi
    obtain ⟨r, hr, horth, hstart⟩ := hn i
    have hrt := eq_of_inner_sub_normalVector_eq_zero (hangle r hr) (hangle t ht)
      (p.increasing i.castSucc_lt_succ) horth hi
    subst r
    intro q hq
    rw [segment_eq_image'] at hq
    obtain ⟨c, hcoef, rfl⟩ := hq
    change inner ℝ (p.vertices i.castSucc + c •
      (p.vertices i.succ - p.vertices i.castSucc)) (normalVector (t : Real.Angle)) = _
    rw [inner_add_left, real_inner_smul_left, hi, mul_zero, add_zero, hstart]
  calc
    _ = ∑ t ∈ D, (∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc)
          (normalVector (t : Real.Angle)) = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0) * Real.sin t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hface t ht]
    _ = _ := by
      rw [p.sum_normal_lengths_mul_sin D hangle
        (fun i ↦ by obtain ⟨t, ht, ho, _⟩ := hn i; exact ⟨t, ht, ho⟩), hpa, hpb]

end MovingSofa
