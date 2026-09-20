import MovingSofa.Geometry.HallwayPartsProperties
import MovingSofa.Cap.HalfPlanes
import MovingSofa.Bounds.Niche

noncomputable section

namespace MovingSofa

/-- Membership in a polygon cap is given by the strip and selected support inequalities. -/
theorem mem_angleCap_iff (Θ : AngleSet) (K : CapSpace Θ.angle) (p : Point) :
    p ∈ angleCap Θ K ↔
      ((0 ≤ p 1 ∧ p 1 ≤ 1) ∧
        (0 ≤ inner ℝ p (normalVector (Θ.angle : Real.Angle)) ∧
          inner ℝ p (normalVector (Θ.angle : Real.Angle)) ≤ 1)) ∧
      ∀ t ∈ Θ.directions,
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle) ∧
        inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  simp only [angleCap, Set.mem_inter_iff, Set.mem_iInter, mem_stripParallelogram_iff]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro t
  apply forall_congr'
  intro _
  rw [(rotatingHallwayParts_formulas (K.val : Set Point) (t : Real.Angle)).2.2.2.2.2.2.2.1]
  rfl

/-- The polygon-cap approximation contains the original cap. -/
theorem subset_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    (K.val : Set Point) ⊆ angleCap Θ K := by
  intro p hp
  apply (mem_angleCap_iff Θ K p).mpr
  refine ⟨(mem_stripParallelogram_iff _ _).mp (K.subset_stripParallelogram hp), ?_⟩
  intro t _
  exact ⟨inner_le_supportValue K.val hp _, inner_le_supportValue K.val hp _⟩

/-- A polygon cap is the intersection of its selected support half-planes. -/
theorem angleCap_eq_iInter_supportValue (Θ : AngleSet) (K : CapSpace Θ.angle) :
    angleCap Θ K = ⋂ t ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle,
        normalHalfPlane t (supportValue K.val t) false false := by
  ext p
  simp only [Set.mem_iInter, mem_angleCap_iff]
  constructor
  · rintro ⟨⟨hy, hw⟩, ht⟩ u hu
    change inner ℝ p (normalVector u) ≤ supportValue K.val u
    rcases hu with ⟨u, hu, rfl⟩ | hu
    · rcases hu with (hu | ⟨t, ht', rfl⟩) | hu
      · exact (ht u hu).1
      · exact (ht t ht').2
      · rcases hu with rfl | hu
        · rw [K.property.2.2.1]
          exact hw.2
        · have heq : u = Real.pi / 2 := hu
          subst u
          rw [K.property.2.2.2.1]
          simpa [normalVector, frame, PiLp.inner_apply] using hy.2
    · rcases hu with rfl | hu
      · rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right]
        exact neg_nonpos.mpr hw.1
      · have heq : u = ((3 * Real.pi / 2 : ℝ) : Real.Angle) := hu
        subst u
        rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two]
        exact neg_nonpos.mpr hy.1
  · intro hp
    have ht (t : ℝ) (ht : t ∈ Θ.directions) :=
      hp (t : Real.Angle) (Or.inl ⟨t, Or.inl (Or.inl ht), rfl⟩)
    have ht' (t : ℝ) (ht : t ∈ Θ.directions) :=
      hp ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (Or.inl ⟨t + Real.pi / 2, Or.inl (Or.inr ⟨t, ht, rfl⟩), rfl⟩)
    have hw := hp (Θ.angle : Real.Angle)
      (Or.inl ⟨Θ.angle, Or.inr (Or.inl rfl), rfl⟩)
    have hy := hp ((Real.pi / 2 : ℝ) : Real.Angle)
      (Or.inl ⟨Real.pi / 2, Or.inr (Or.inr rfl), rfl⟩)
    have hl := hp ((Θ.angle + Real.pi : ℝ) : Real.Angle) (Or.inr (Or.inl rfl))
    have hb := hp ((3 * Real.pi / 2 : ℝ) : Real.Angle) (Or.inr (Or.inr rfl))
    change inner ℝ p (normalVector _) ≤ supportValue K.val _ at hw hy hl hb
    rw [K.property.2.2.1] at hw
    rw [K.property.2.2.2.1] at hy
    rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hl
    rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hb
    have hy' : p 1 ≤ 1 := by simpa [normalVector, frame, PiLp.inner_apply] using hy
    exact ⟨⟨⟨by linarith, hy'⟩, by linarith, hw⟩, fun t h ↦ ⟨ht t h, ht' t h⟩⟩

/-- Polygon-cap approximations are closed. -/
theorem isClosed_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    IsClosed (angleCap Θ K) := by
  rw [angleCap_eq_iInter_supportValue]
  apply isClosed_iInter
  intro t
  apply isClosed_iInter
  intro _
  exact isClosed_le (by fun_prop) continuous_const

/-- Polygon-cap approximations are convex. -/
theorem convex_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    Convex ℝ (angleCap Θ K) := by
  rw [angleCap_eq_iInter_supportValue]
  apply convex_iInter
  intro t
  apply convex_iInter
  intro _
  apply convex_halfSpace_le
  exact ⟨fun x y ↦ inner_add_left x y _, fun a x ↦ by simp [real_inner_smul_left]⟩

/-- Polygon-cap approximation preserves support at every selected normal. -/
theorem supportValue_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle)
    {t : Real.Angle}
    (ht : t ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) :
    supportValue (angleCap Θ K) t = supportValue K.val t := by
  have hbound : ∀ p ∈ angleCap Θ K, inner ℝ p (normalVector t) ≤ supportValue K.val t := by
    intro p hp
    rw [angleCap_eq_iInter_supportValue] at hp
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hp t) ht
  have hbd : BddAbove ((fun p ↦ inner ℝ p (normalVector t)) '' angleCap Θ K) := by
    refine ⟨supportValue K.val t, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  apply le_antisymm
  · apply csSup_le ((K.val.nonempty.mono (subset_angleCap Θ K)).image _)
    rintro _ ⟨p, hp, rfl⟩
    exact hbound p hp
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    exact le_csSup hbd ⟨p, subset_angleCap Θ K hp, rfl⟩

/-- Polygon-cap approximation fixes caps with the prescribed normals. -/
theorem angleCap_eq_self (Θ : AngleSet) (P : PolygonCapSpace Θ) :
    angleCap Θ P.val = (P.val.val : Set Point) := by
  rw [angleCap_eq_iInter_supportValue, ← P.property.eq_iInter_supportValue]

/-- An interior selected direction bounds the polygon cap, including at right angle. -/
theorem isBounded_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    Bornology.IsBounded (angleCap Θ K) := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  let l := -supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) / Real.sin t
  let r := supportValue K.val (t : Real.Angle) / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨M + 1, ?_⟩
  intro p hp
  obtain ⟨⟨hy, _⟩, hnormals⟩ := (mem_angleCap_iff Θ K p).mp hp
  obtain ⟨ha, hb⟩ := hnormals t ht
  simp [normalVector, frame, PiLp.inner_apply, Real.cos_add, Real.sin_add,
    -Real.Angle.coe_add] at ha hb
  have hl : l ≤ p 0 := by
    apply (div_le_iff₀ hs).mpr
    nlinarith [mul_nonneg hc.le hy.1]
  have hr : p 0 ≤ r := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [mul_nonneg hs.le hy.1]
  have hx : |p 0| ≤ M := by
    apply abs_le.mpr
    dsimp [M]
    constructor <;> linarith [neg_abs_le l, le_abs_self r, abs_nonneg l, abs_nonneg r]
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hM).mpr hx
  have hy2 : (p 1) ^ 2 ≤ 1 := by nlinarith [hy.1, hy.2]
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
  nlinarith [norm_nonneg p]

/-- Polygon-cap approximations are compact. -/
theorem isCompact_angleCap (Θ : AngleSet) (K : CapSpace Θ.angle) :
    IsCompact (angleCap Θ K) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨isClosed_angleCap Θ K, isBounded_angleCap Θ K⟩

theorem angleCap_properties (Θ : AngleSet) (K : CapSpace Θ.angle) :
    (∃ P : PolygonCapSpace Θ, (P.val.val : Set Point) = angleCap Θ K) ∧
    (K.val : Set Point) ⊆ angleCap Θ K ∧
    (∀ t ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle,
      supportValue (angleCap Θ K) t = supportValue (K.val : Set Point) t) ∧
    (∀ P : PolygonCapSpace Θ, angleCap Θ P.val = (P.val.val : Set Point)) := by
  refine ⟨?_, subset_angleCap Θ K, fun _ ht ↦ supportValue_angleCap Θ K ht,
    angleCap_eq_self Θ⟩
  let L : ConvexBody Point := ⟨angleCap Θ K, convex_angleCap Θ K,
    isCompact_angleCap Θ K, K.val.nonempty.mono (subset_angleCap Θ K)⟩
  let N := ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  have hrepr : HasHalfPlaneRepresentation L N := by
    refine ⟨(fun t ↦ (t, supportValue K.val t)) '' N, ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact ht
    · simp only [Set.biInter_image]
      exact angleCap_eq_iInter_supportValue Θ K
  have hdomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
    rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
    · exact Or.inl ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
    · right
      constructor <;> linarith [(Θ.interior s hs).1, (Θ.interior s hs).2]
    · rcases ht with rfl | rfl
      · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, le_add_of_nonneg_left Θ.angle_pos.le⟩
  have hrepr' : HasHalfPlaneRepresentation L
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪ capLowerNormals Θ.angle) := by
    obtain ⟨C, hC, hLC⟩ := hrepr
    refine ⟨C, ?_, hLC⟩
    intro c hc
    rcases hC c hc with ⟨t, ht, heq⟩ | ht
    · exact Or.inl ⟨t, hdomain ht, heq⟩
    · exact Or.inr ht
  have hsupp (t : Real.Angle) (ht : t ∈ N) : supportValue L t = supportValue K.val t :=
    supportValue_angleCap Θ K ht
  have hcap : IsCap Θ.angle L := by
    refine ⟨Θ.angle_pos, Θ.angle_le, ?_, ?_, ?_, ?_, hrepr'⟩
    · rw [hsupp _ (Or.inl ⟨Θ.angle, Or.inr (Or.inl rfl), rfl⟩)]
      exact K.property.2.2.1
    · rw [hsupp _ (Or.inl ⟨Real.pi / 2, Or.inr (Or.inr rfl), rfl⟩)]
      exact K.property.2.2.2.1
    · rw [hsupp _ (Or.inr (Or.inl rfl))]
      exact K.property.2.2.2.2.1
    · rw [hsupp _ (Or.inr (Or.inr rfl))]
      exact K.property.2.2.2.2.2.1
  exact ⟨⟨⟨L, hcap⟩, hrepr⟩, rfl⟩

theorem polygonNiche_angleCap (Θ : AngleSet) (K P : CapSpace Θ.angle)
    (hP : (P.val : Set Point) = angleCap Θ K) :
    polygonNiche Θ K = polygonNiche Θ P ∧ polygonNiche Θ K ⊆ capNiche K := by
  refine ⟨?_, polygonNiche_subset_capNiche Θ K⟩
  have hs := (angleCap_properties Θ K).2.2.1
  have hq (t : ℝ) (ht : t ∈ Θ.directions) :
      innerQuadrant (K.val : Set Point) t = innerQuadrant (P.val : Set Point) t := by
    unfold innerQuadrant
    rw [hP, hs (t : Real.Angle) (Or.inl ⟨t, Or.inl (Or.inl ht), rfl⟩),
      hs ((t + Real.pi / 2 : ℝ) : Real.Angle)
        (Or.inl ⟨t + Real.pi / 2, Or.inl (Or.inr ⟨t, ht, rfl⟩), rfl⟩)]
  unfold polygonNiche
  congr 1
  exact Set.iUnion_congr fun t ↦ Set.iUnion_congr fun ht ↦ hq t ht

theorem polygonArea_upperBound (Θ : AngleSet) :
    (∀ K : PolygonCapSpace Θ, polygonAreaFunctional Θ K.val =
      ClassicalResults.area (K.val.val : Set Point) -
        ClassicalResults.area (polygonNiche Θ K.val)) ∧
    (∀ K : CapSpace Θ.angle, capAreaFunctional K ≤ polygonAreaFunctional Θ K) := by
  constructor
  · intro K
    unfold polygonAreaFunctional
    rw [(angleCap_properties Θ K.val).2.2.2 K]
  · intro K
    obtain ⟨P, hP⟩ := (angleCap_properties Θ K).1
    have hcap : ClassicalResults.area (K.val : Set Point) ≤
        ClassicalResults.area (angleCap Θ K) := by
      apply ENNReal.toReal_mono
      · rw [← hP]
        exact P.val.val.isCompact.measure_ne_top
      · exact MeasureTheory.measure_mono (angleCap_properties Θ K).2.1
    have hniche : ClassicalResults.area (polygonNiche Θ K) ≤
        ClassicalResults.area (capNiche K) := by
      apply ENNReal.toReal_mono (niche_uniform_bounds.1 Θ.angle K).2.2.1.ne
      exact MeasureTheory.measure_mono (polygonNiche_angleCap Θ K P.val hP).2
    exact sub_le_sub hcap hniche

/-- A maximum polygon cap dominates every cap under the polygon area functional. -/
theorem polygonAreaFunctional_le_maximum (Θ : AngleSet) (P : PolygonCapSpace Θ)
    (hP : IsMaximumPolygonCap Θ P) (K : CapSpace Θ.angle) :
    polygonAreaFunctional Θ K ≤ polygonAreaFunctional Θ P.val := by
  obtain ⟨Q, hQ⟩ := (angleCap_properties Θ K).1
  have hn := (polygonNiche_angleCap Θ K Q.val hQ).1
  have harea : polygonAreaFunctional Θ Q.val = polygonAreaFunctional Θ K := by
    unfold polygonAreaFunctional
    rw [(angleCap_properties Θ Q.val).2.2.2 Q, hQ, hn]
  rw [← harea]
  exact hP.2 Q

end MovingSofa
