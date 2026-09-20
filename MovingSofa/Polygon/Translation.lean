import MovingSofa.Polygon.Height.Bounds
import MovingSofa.Polygon.Height.Properties

noncomputable section

namespace MovingSofa

theorem polygonCapTranslate_iff (Θ : AngleSet) (K : ConvexBody Point) :
    (∃ K' : PolygonCapTranslateSpace Θ, K'.val = (K : Set Point)) ↔
      (supportValue K (Θ.angle : Real.Angle) +
        supportValue K ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 1) ∧
      (supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) +
        supportValue K ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 1) ∧
      ∃ constraints : Set (Real.Angle × ℝ), constraints.Finite ∧
        (∀ c ∈ constraints, c.1 ∈
          ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) ∧
        (K : Set Point) = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false := by
  classical
  let N : Set Real.Angle :=
    ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle
  have hNfinite : N.Finite := by
    apply Set.Finite.union
    · apply Set.Finite.image
      simp only [angleDomain]
      exact ((Θ.directions.finite_toSet.union
        (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
          ((Set.finite_singleton (Real.pi / 2)).insert Θ.angle))
    · simp [capLowerNormals]
  constructor
  · rintro ⟨K', hK'eq⟩
    obtain ⟨P, q, hPq⟩ := K'.property
    have hKeq : (K : Set Point) = (fun p ↦ p + q) '' (P.val.val : Set Point) := by
      rw [← hK'eq, hPq]
    have hsupp (t : Real.Angle) :
        supportValue K t = supportValue P.val.val t + inner ℝ q (normalVector t) := by
      rw [show (K : Set Point) = (ConvexBody.translate P.val.val q : Set Point) from hKeq]
      exact supportValue_image_add P.val.val q t
    have hopen := P.val.property
    refine ⟨?_, ?_, ?_⟩
    · rw [hsupp, hsupp, hopen.2.2.1, hopen.2.2.2.2.1, normalVector_add_pi]
      simp only [inner_neg_right]
      ring
    · have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
        congr 1
        ring
      rw [hsupp]
      rw [← hang]
      rw [hsupp, hopen.2.2.2.1]
      rw [show supportValue P.val.val (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) = 0 by
        rw [hang]; exact hopen.2.2.2.2.2.1]
      rw [normalVector_add_pi]
      simp only [inner_neg_right]
      ring
    · have hrepr : HasHalfPlaneRepresentation K N := by
        rw [show (K : Set Point) = (ConvexBody.translate P.val.val q : Set Point) from hKeq]
        exact P.property.translate q
      exact hrepr.finite_constraints hNfinite
  · rintro ⟨hwidthω, hwidthT, C, hCfinite, hCN, hKC⟩
    let v : Point := if h : Θ.angle = Real.pi / 2 then
      !₂[0, 1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)]
    else
      !₂[(1 - supportValue K (Θ.angle : Real.Angle) -
          (1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)) * Real.sin Θ.angle) /
          Real.cos Θ.angle,
        1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle)]
    have hvT : inner ℝ v (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        1 - supportValue K ((Real.pi / 2 : ℝ) : Real.Angle) := by
      by_cases h : Θ.angle = Real.pi / 2
      · simp [v, h, normalVector, frame, PiLp.inner_apply]
      · simp [v, h, normalVector, frame, PiLp.inner_apply]
    have hvω : inner ℝ v (normalVector (Θ.angle : Real.Angle)) =
        1 - supportValue K (Θ.angle : Real.Angle) := by
      by_cases h : Θ.angle = Real.pi / 2
      · simpa [h] using hvT
      · have hlt : Θ.angle < Real.pi / 2 := lt_of_le_of_ne Θ.angle_le h
        have hcos : Real.cos Θ.angle ≠ 0 := (Real.cos_pos_of_mem_Ioo
          ⟨lt_trans (neg_neg_of_pos (by positivity : 0 < Real.pi / 2)) Θ.angle_pos,
            hlt⟩).ne'
        simp [v, h, normalVector, frame, PiLp.inner_apply]
        field_simp [hcos]
        ring
    let L := ConvexBody.translate K v
    have hsupp (t : Real.Angle) :
        supportValue L t = supportValue K t + inner ℝ v (normalVector t) :=
      supportValue_image_add K v t
    have htopω : supportValue L (Θ.angle : Real.Angle) = 1 := by
      rw [hsupp, hvω]
      ring
    have htopT : supportValue L ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
      rw [hsupp, hvT]
      ring
    have hbotω : supportValue L ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 0 := by
      rw [hsupp, normalVector_add_pi, inner_neg_right]
      rw [hvω]
      linarith
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    have hbotT : supportValue L ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
      rw [← hang, hsupp, normalVector_add_pi, inner_neg_right]
      rw [hang, hvT]
      linarith
    have hKrepr : HasHalfPlaneRepresentation K N := ⟨C, hCN, hKC⟩
    have hLrepr : HasHalfPlaneRepresentation L N := hKrepr.translate v
    have hangleDomain : angleDomain Θ ⊆ capUpperAngles Θ.angle := by
      rintro t ((ht | ⟨s, hs, rfl⟩) | ht)
      · left
        exact ⟨(Θ.interior t ht).1.le, (Θ.interior t ht).2.le⟩
      · right
        constructor <;> linarith [(Θ.interior s hs).1, (Θ.interior s hs).2]
      · rcases ht with (rfl | rfl)
        · exact Or.inl ⟨Θ.angle_pos.le, le_rfl⟩
        · exact Or.inr ⟨le_rfl, le_add_of_nonneg_left Θ.angle_pos.le⟩
    have hNsubset : N ⊆
        ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
          capLowerNormals Θ.angle := by
      rintro t (ht | ht)
      · obtain ⟨s, hs, rfl⟩ := ht
        exact Or.inl ⟨s, hangleDomain hs, rfl⟩
      · exact Or.inr ht
    have hLcapRepr : HasHalfPlaneRepresentation L
        (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles Θ.angle) ∪
          capLowerNormals Θ.angle) := by
      obtain ⟨D, hDN, hLD⟩ := hLrepr
      exact ⟨D, fun c hc ↦ hNsubset (hDN c hc), hLD⟩
    have hLcap : IsCap Θ.angle L :=
      ⟨Θ.angle_pos, Θ.angle_le, htopω, htopT, hbotω, hbotT, hLcapRepr⟩
    let P : PolygonCapSpace Θ := ⟨⟨L, hLcap⟩, hLrepr⟩
    refine ⟨⟨(K : Set Point), ?_⟩, rfl⟩
    refine ⟨P, -v, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨x + v, ⟨x, hx, rfl⟩, by simp⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy

theorem polygonHeightArea_le_translateArea {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    (K : PolygonCapTranslateSpace Θ) (hK : polygonHeightCap h = K.val) :
    polygonHeightArea h ≤ (polygonTranslateExtensions K).2 := by
  obtain ⟨P, q, hPq⟩ := K.property
  let C := ConvexBody.translate P.val.val q
  have hC : (C : Set Point) = K.val := hPq.symm
  have hBody : polygonHeightCap h = (C : Set Point) := hK.trans hC.symm
  have hw := (polygonCapTranslate_iff Θ C).1 ⟨K, hC.symm⟩
  let g := polygonTranslateHeight K
  have hle : ∀ t, g t ≤ h t := by
    intro t
    change supportValue K.val (t.val : Real.Angle) ≤ h t
    rw [← hC]
    simpa only [polygonHeightValue, dite_eq_left t.property] using
      supportValue_le_polygonHeightValue h C hBody t.property
  have heq : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      polygonHeightValue g t = polygonHeightValue h t := by
    intro t ht
    have htD : t ∈ angleDomain Θ := Or.inr ht
    have hg : polygonHeightValue g t = supportValue C (t : Real.Angle) := by
      simp only [g, polygonTranslateHeight, polygonHeightValue, dite_eq_left htD]
      rw [hC]
    rw [hg]
    apply supportValue_eq_polygonHeightValue_of_width_one h C hBody ht
    rcases ht with rfl | ht
    · exact hw.1
    · have ht : t = Real.pi / 2 := ht
      subst t
      simpa only [show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring] using hw.2.1
  have hsub := polygonHeightNiche_mono_of_eq_endpoints hle heq
  have harea : ClassicalResults.area (polygonHeightNiche g) ≤
      ClassicalResults.area (polygonHeightNiche h) := by
    apply ENNReal.toReal_mono (isBounded_polygonHeightNiche h).measure_lt_top.ne
    exact MeasureTheory.measure_mono hsub
  change ClassicalResults.area (polygonHeightCap h) -
      ClassicalResults.area (polygonHeightNiche h) ≤
    ClassicalResults.area (polygonHeightCap g) - ClassicalResults.area (polygonHeightNiche g)
  rw [hK, polygonHeightCap_of_translate K]
  exact sub_le_sub_left harea _

end MovingSofa
