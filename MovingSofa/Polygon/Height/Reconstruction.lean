import MovingSofa.Polygon.Translation

noncomputable section

namespace MovingSofa

private theorem isClosed_polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    IsClosed (polygonHeightCap h) := by
  unfold polygonHeightCap polygonHeightParallelogram
  apply IsClosed.inter
  · exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      (isClosed_normalHalfPlane _ _ false).inter (isClosed_normalHalfPlane _ _ true)
  · exact isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦
      isClosed_normalHalfPlane _ _ false

private theorem convex_polygonHeightCap {Θ : AngleSet} (h : PolygonHeightSpace Θ) :
    Convex ℝ (polygonHeightCap h) := by
  unfold polygonHeightCap polygonHeightParallelogram
  apply Convex.inter
  · exact convex_iInter fun t ↦ convex_iInter fun _ ↦
      (convex_normalHalfPlane _ _ false).inter (convex_normalHalfPlane _ _ true)
  · exact convex_iInter fun t ↦ convex_iInter fun _ ↦
      convex_normalHalfPlane _ _ false

private theorem normalHalfPlane_upper_eq_lower_add_pi (t c : ℝ) :
    normalHalfPlane (t : Real.Angle) c true false =
      normalHalfPlane ((t + Real.pi : ℝ) : Real.Angle) (-c) false false := by
  ext p
  change c ≤ inner ℝ p (normalVector (t : Real.Angle)) ↔
    inner ℝ p (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤ -c
  rw [normalVector_add_pi, inner_neg_right]
  constructor <;> intro h <;> linarith

private theorem polygonHeightCap_halfPlaneRepresentation {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    HasHalfPlaneRepresentation (polygonHeightCap h)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) := by
  let C : Set (Real.Angle × ℝ) :=
    ((fun t : ℝ ↦ ((t : Real.Angle), polygonHeightValue h t)) '' angleDomain Θ) ∪
      ((fun t : ℝ ↦ (((t + Real.pi : ℝ) : Real.Angle),
        -(polygonHeightValue h t - 1))) '' ({Θ.angle, Real.pi / 2} : Set ℝ))
  refine ⟨C, ?_, ?_⟩
  · rintro c (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact Or.inl ⟨t, ht, rfl⟩
    · right
      rcases ht with rfl | rfl
      · exact Or.inl rfl
      · change (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) ∈ capLowerNormals Θ.angle
        rw [show Real.pi / 2 + Real.pi = 3 * Real.pi / 2 by ring]
        simp [capLowerNormals]
  · ext p
    simp only [polygonHeightCap, polygonHeightParallelogram, Set.mem_inter_iff,
      Set.mem_iInter, C, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hendpoint, hinterior⟩ c (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
      · rcases ht with (ht | ht) | ht
        · exact (hinterior t (Or.inl ht))
        · obtain ⟨s, hs, rfl⟩ := ht
          exact hinterior (s + Real.pi / 2) (Or.inr ⟨s, hs, rfl⟩)
        · exact (hendpoint t ht).1
      · rw [← normalHalfPlane_upper_eq_lower_add_pi]
        exact (hendpoint t ht).2
    · intro hall
      constructor
      · intro t ht
        constructor
        · exact hall ((t : Real.Angle), polygonHeightValue h t)
            (Or.inl ⟨t, Or.inr ht, rfl⟩)
        · rw [normalHalfPlane_upper_eq_lower_add_pi]
          exact hall (((t + Real.pi : ℝ) : Real.Angle), -(polygonHeightValue h t - 1))
            (Or.inr ⟨t, ht, rfl⟩)
      · intro t ht
        exact hall ((t : Real.Angle), polygonHeightValue h t)
          (Or.inl ⟨t, Or.inl ht, rfl⟩)

private theorem polygonHeightCap_upper_bound {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {p : Point} (hp : p ∈ polygonHeightCap h) {t : ℝ} (ht : t ∈ angleDomain Θ) :
    inner ℝ p (normalVector (t : Real.Angle)) ≤ polygonHeightValue h t := by
  exact polygonHeightCap_subset_normalHalfPlane h ht hp

private theorem polygonHeightCap_lower_bound {Θ : AngleSet} (h : PolygonHeightSpace Θ)
    {p : Point} (hp : p ∈ polygonHeightCap h) {t : ℝ}
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    polygonHeightValue h t - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
  change p ∈ polygonHeightParallelogram h ∩ _ at hp
  exact (Set.mem_iInter.mp (Set.mem_iInter.mp hp.1 t) ht).2

/-- Attainment of both endpoint strip bounds reconstructs a translated polygon cap. -/
theorem exists_polygonCapTranslate_eq_polygonHeightCap {Θ : AngleSet}
    (h : PolygonHeightSpace Θ)
    (hbounded : Bornology.IsBounded (polygonHeightCap h))
    (hupper : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap h,
        inner ℝ p (normalVector (t : Real.Angle)) = polygonHeightValue h t)
    (hlower : ∀ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap h,
        inner ℝ p (normalVector (t : Real.Angle)) = polygonHeightValue h t - 1) :
    ∃ K' : PolygonCapTranslateSpace Θ, K'.val = polygonHeightCap h := by
  obtain ⟨p, hp, _⟩ := hupper (Real.pi / 2) (by simp)
  let L : ConvexBody Point := {
    carrier := polygonHeightCap h
    convex' := convex_polygonHeightCap h
    isCompact' := Metric.isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_polygonHeightCap h, hbounded⟩
    nonempty' := ⟨p, hp⟩ }
  have hsuppUpper (t : ℝ) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      supportValue L (t : Real.Angle) = polygonHeightValue h t := by
    obtain ⟨q, hq, hqeq⟩ := hupper t ht
    apply le_antisymm
    · apply supportValue_le_of_subset_normalHalfPlane
      intro x hx
      exact polygonHeightCap_upper_bound h hx (Or.inr ht)
    · simpa only [hqeq] using inner_le_supportValue L hq (t : Real.Angle)
  have hsuppLower (t : ℝ) (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      supportValue L ((t + Real.pi : ℝ) : Real.Angle) =
        -(polygonHeightValue h t - 1) := by
    obtain ⟨q, hq, hqeq⟩ := hlower t ht
    apply le_antisymm
    · apply supportValue_le_of_subset_normalHalfPlane
      intro x hx
      change inner ℝ x (normalVector ((t + Real.pi : ℝ) : Real.Angle)) ≤
        -(polygonHeightValue h t - 1)
      rw [normalVector_add_pi, inner_neg_right]
      exact neg_le_neg (polygonHeightCap_lower_bound h hx ht)
    · have hle := inner_le_supportValue L hq ((t + Real.pi : ℝ) : Real.Angle)
      rw [normalVector_add_pi, inner_neg_right, hqeq] at hle
      exact hle
  have hwidthω : supportValue L (Θ.angle : Real.Angle) +
      supportValue L ((Θ.angle + Real.pi : ℝ) : Real.Angle) = 1 := by
    rw [hsuppUpper Θ.angle (by simp), hsuppLower Θ.angle (by simp)]
    ring
  have hangle : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    congr 1
    ring
  have hwidthT : supportValue L ((Real.pi / 2 : ℝ) : Real.Angle) +
      supportValue L ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    rw [← hangle, hsuppUpper (Real.pi / 2) (by simp),
      hsuppLower (Real.pi / 2) (by simp)]
    ring
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t : ℝ ↦ t + Real.pi / 2))).union
        (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)
  have hlowerNormals : (capLowerNormals Θ.angle).Finite := by
    simp [capLowerNormals]
  have hrepr : HasHalfPlaneRepresentation (L : Set Point)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle) := by
    exact polygonHeightCap_halfPlaneRepresentation h
  obtain ⟨C, hCfinite, hCN, hLC⟩ :=
    hrepr.finite_constraints
      (hdomain.image _ |>.union hlowerNormals)
  exact (polygonCapTranslate_iff Θ L).mpr
    ⟨hwidthω, hwidthT, C, hCfinite, hCN, hLC⟩

end MovingSofa
