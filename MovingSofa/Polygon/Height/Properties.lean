import MovingSofa.Polygon.Height.Space
import MovingSofa.Polygon.Approximation

noncomputable section

namespace MovingSofa

private theorem polygonHeightValue_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ)
    {t : ℝ} (ht : t ∈ angleDomain Θ) :
    polygonHeightValue (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) t =
      supportValue K.val.val (t : Real.Angle) := by
  simp [polygonHeightValue, ht]

private theorem polygonHeightFan_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightFan (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      capFan Θ.angle := by
  have hω : Θ.angle ∈ angleDomain Θ := by simp [angleDomain]
  have hT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  ext q
  simp only [polygonHeightFan, Set.mem_iInter, Set.mem_insert_iff, Set.mem_singleton_iff,
    forall_eq_or_imp, forall_eq]
  rw [polygonHeightValue_supportValue K hω, polygonHeightValue_supportValue K hT,
    K.val.property.2.2.1, K.val.property.2.2.2.1]
  simp [capFan]

private theorem polygonHeightNiche_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      polygonNiche Θ K.val := by
  unfold polygonHeightNiche polygonNiche
  rw [polygonHeightFan_supportValue K]
  congr 1
  apply Set.iUnion_congr
  intro t
  apply Set.iUnion_congr
  intro ht
  have htD : t ∈ angleDomain Θ := by simp [angleDomain, ht]
  have htTD : t + Real.pi / 2 ∈ angleDomain Θ := by
    exact Or.inl (Or.inr ⟨t, ht, rfl⟩)
  rw [polygonHeightValue_supportValue K htD, polygonHeightValue_supportValue K htTD]
  rfl

private theorem polygonHeightParallelogram_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightParallelogram (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      (stripParallelogram Θ.angle).1 := by
  have hω : Θ.angle ∈ angleDomain Θ := by simp [angleDomain]
  have hT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  ext p
  simp only [polygonHeightParallelogram, Set.mem_iInter, Set.mem_insert_iff,
    Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [polygonHeightValue_supportValue K hω, polygonHeightValue_supportValue K hT,
    K.val.property.2.2.1, K.val.property.2.2.2.1, mem_stripParallelogram_iff]
  simp [normalHalfPlane, normalVector, frame, PiLp.inner_apply, Fin.sum_univ_two]
  tauto

private theorem polygonHeightCap_supportValue {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightCap (Θ := Θ)
      (fun s ↦ supportValue (K.val.val : Set Point) (s.val : Real.Angle)) =
      angleCap Θ K.val := by
  unfold polygonHeightCap
  rw [polygonHeightParallelogram_supportValue K]
  ext p
  rw [mem_angleCap_iff]
  simp only [Set.mem_inter_iff, mem_stripParallelogram_iff, Set.mem_iInter]
  apply and_congr_right
  intro _
  constructor
  · intro h t ht
    have htD : t ∈ angleDomain Θ := Or.inl (Or.inl ht)
    have htTD : t + Real.pi / 2 ∈ angleDomain Θ := Or.inl (Or.inr ⟨t, ht, rfl⟩)
    have h₁ := h t (Or.inl ht)
    have h₂ := h (t + Real.pi / 2) (Or.inr ⟨t, ht, rfl⟩)
    rw [polygonHeightValue_supportValue K htD] at h₁
    rw [polygonHeightValue_supportValue K htTD] at h₂
    exact ⟨h₁, h₂⟩
  · intro h t ht
    have htD : t ∈ angleDomain Θ := Or.inl ht
    rw [polygonHeightValue_supportValue K htD]
    rcases ht with ht | ⟨s, hs, rfl⟩
    · exact (h t ht).1
    · exact (h s hs).2

private theorem mem_polygonHeightCap_supportValue_image_add {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (q p : Point) :
    p + q ∈ polygonHeightCap (Θ := Θ)
      (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
        (t.val : Real.Angle)) ↔
    p ∈ polygonHeightCap (Θ := Θ)
      (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
          (t.val : Real.Angle)) t =
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) t +
          inner ℝ q (normalVector (t : Real.Angle)) := by
    simp only [polygonHeightValue, dite_eq_left ht]
    exact supportValue_image_add K.val.val q (t : Real.Angle)
  simp only [polygonHeightCap, polygonHeightParallelogram, Set.mem_inter_iff,
    Set.mem_iInter]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inr ht)]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inl ht)]
    simp [normalHalfPlane, inner_add_left]

private theorem polygonHeightNiche_supportValue_image_add {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (q : Point) :
    polygonHeightNiche (Θ := Θ)
      (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
        (t.val : Real.Angle)) =
      (fun p ↦ p + q) '' polygonNiche Θ K.val := by
  have hval (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue ((fun x ↦ x + q) '' (K.val.val : Set Point))
          (t.val : Real.Angle)) t =
      polygonHeightValue (Θ := Θ)
        (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) t +
          inner ℝ q (normalVector (t : Real.Angle)) := by
    simp only [polygonHeightValue, dite_eq_left ht]
    exact supportValue_image_add K.val.val q (t : Real.Angle)
  ext x
  obtain ⟨p, rfl⟩ : ∃ p : Point, x = p + q := ⟨x - q, by simp⟩
  rw [← polygonHeightNiche_supportValue K]
  simp only [Set.mem_image, add_left_inj, exists_eq_right]
  simp only [polygonHeightNiche, polygonHeightFan, Set.mem_inter_iff,
    Set.mem_iInter, Set.mem_iUnion]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    rw [hval t (Or.inr ht)]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]
  · apply exists_congr
    intro t
    apply exists_congr
    intro ht
    rw [hval t (Or.inl (Or.inl ht)),
      hval (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))]
    simp [normalHalfPlane, inner_add_left, add_sub_right_comm]


theorem polygonHeightCap_of_translate {Θ : AngleSet} (K : PolygonCapTranslateSpace Θ) :
    polygonHeightCap (polygonTranslateHeight K) = K.val := by
  obtain ⟨P, q, hK⟩ := K.property
  unfold polygonTranslateHeight
  rw [hK]
  ext x
  obtain ⟨p, rfl⟩ : ∃ p : Point, x = p + q := ⟨x - q, by simp⟩
  rw [mem_polygonHeightCap_supportValue_image_add, polygonHeightCap_supportValue, angleCap_eq_self]
  simp

theorem polygonTranslateHeight_injective (Θ : AngleSet) :
    Function.Injective (polygonTranslateHeight (Θ := Θ)) := by
  intro K L h
  apply Subtype.ext
  rw [← polygonHeightCap_of_translate K, ← polygonHeightCap_of_translate L, h]

theorem polygonHeightNiche_of_cap {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    polygonHeightNiche (Θ := Θ) (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) =
      polygonNiche Θ K.val ∧
    polygonHeightArea (Θ := Θ) (fun t ↦ supportValue (K.val.val : Set Point) (t.val : Real.Angle)) =
      polygonAreaFunctional Θ K.val := by
  refine ⟨polygonHeightNiche_supportValue K, ?_⟩
  unfold polygonHeightArea polygonAreaFunctional
  rw [polygonHeightCap_supportValue K, polygonHeightNiche_supportValue K]

theorem polygonTranslateExtensions_eq {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (q : Point) (K' : PolygonCapTranslateSpace Θ)
    (hK : K'.val = (fun p ↦ p + q) '' (K.val.val : Set Point)) :
    (polygonTranslateExtensions K').1 = (fun p ↦ p + q) '' polygonNiche Θ K.val ∧
    (polygonTranslateExtensions K').2 = polygonAreaFunctional Θ K.val := by
  have hn : polygonHeightNiche (polygonTranslateHeight K') =
      (fun p ↦ p + q) '' polygonNiche Θ K.val := by
    unfold polygonTranslateHeight
    rw [hK]
    exact polygonHeightNiche_supportValue_image_add K q
  refine ⟨hn, ?_⟩
  change ClassicalResults.area (polygonHeightCap (polygonTranslateHeight K')) -
    ClassicalResults.area (polygonHeightNiche (polygonTranslateHeight K')) = _
  rw [polygonHeightCap_of_translate K', hn, hK, ClassicalResults.area_image_add,
    ClassicalResults.area_image_add]
  unfold polygonAreaFunctional
  rw [angleCap_eq_self]

end MovingSofa
