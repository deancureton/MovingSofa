import MovingSofa.Cap.ReflectionGeometry
import MovingSofa.Polygon.Approximation

noncomputable section

namespace MovingSofa

def mirrorReflection (ω : ℝ) (p : Point) : Point :=
  (2 * inner ℝ p (stripParallelogram ω).2.2 /
    inner ℝ (stripParallelogram ω).2.2 (stripParallelogram ω).2.2) •
      (stripParallelogram ω).2.2 - p

def reflectedAngleSet (Θ : AngleSet) : AngleSet where
  angle := Θ.angle
  angle_pos := Θ.angle_pos
  angle_le := Θ.angle_le
  directions := Θ.directions.image (fun t ↦ Θ.angle - t)
  nonempty := Θ.nonempty.image _
  interior := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hs0, hsω⟩ := Θ.interior s hs
    constructor <;> linarith

private theorem mirrorReflection_eq_capReflection (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    mirrorReflection ω = capReflection ω := by
  change stripTopReflection ω = capReflection ω
  exact stripTopReflection_eq_capReflection ω hω0 hωle

private theorem reflectedAngle_mem_polygonNormals (Θ : AngleSet) (a : Real.Angle)
    (ha : a ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain Θ) ∪
      capLowerNormals Θ.angle) :
    reflectedAngle Θ.angle a ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain (reflectedAngleSet Θ)) ∪
        capLowerNormals Θ.angle := by
  rcases ha with ha | ha
  · obtain ⟨t, ht, rfl⟩ := ha
    left
    rw [reflectedAngle_coe]
    refine ⟨Θ.angle + Real.pi / 2 - t, ?_, rfl⟩
    simp only [angleDomain, Set.mem_union, Set.mem_image, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_coe] at ht ⊢
    rcases ht with (ht | ht) | ht
    · left
      right
      refine ⟨Θ.angle - t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, by ring⟩
    · obtain ⟨s, hs, rfl⟩ := ht
      left
      left
      exact Finset.mem_image.mpr ⟨s, hs, by ring⟩
    · rcases ht with rfl | rfl
      · exact Or.inr (Or.inr (by simp))
      · apply Or.inr
        apply Or.inl
        change Θ.angle + Real.pi / 2 - Real.pi / 2 = Θ.angle
        ring
  · right
    simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · right
      exact reflectedAngle_at_omega_add_pi Θ.angle
    · left
      exact reflectedAngle_at_three_pi_div_two Θ.angle

private theorem reflectedBody_polygonRepresentation (Θ : AngleSet)
    (K : PolygonCapSpace Θ) :
    HasHalfPlaneRepresentation (reflectedBody Θ.angle K.val.val)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' angleDomain (reflectedAngleSet Θ)) ∪
        capLowerNormals Θ.angle) := by
  exact K.property.reflectedBody fun a ha ↦ reflectedAngle_mem_polygonNormals Θ a ha

private def reflectedPolygonCap (Θ : AngleSet) (K : PolygonCapSpace Θ) :
    PolygonCapSpace (reflectedAngleSet Θ) :=
  ⟨⟨reflectedBody Θ.angle K.val.val, reflectedBody_isCap K.val⟩,
    reflectedBody_polygonRepresentation Θ K⟩

private theorem polygonNiche_reflection (Θ : AngleSet) (K : PolygonCapSpace Θ) :
    polygonNiche (reflectedAngleSet Θ) (reflectedPolygonCap Θ K).val =
      capReflection Θ.angle '' polygonNiche Θ K.val := by
  unfold polygonNiche
  rw [Set.image_inter (capReflection Θ.angle).injective,
    capReflection_image_capFan]
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    change p ∈ innerQuadrant (reflectedBody Θ.angle K.val.val) (Θ.angle - s) at hp
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨s, hs, ?_⟩, rfl⟩
    simpa only [sub_sub_cancel] using hq
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    apply Set.mem_iUnion₂.mpr
    refine ⟨Θ.angle - s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    change capReflection Θ.angle q ∈
      innerQuadrant (reflectedBody Θ.angle K.val.val) (Θ.angle - s)
    rw [innerQuadrant_reflection]
    exact ⟨q, by simpa only [sub_sub_cancel], rfl⟩

private theorem polygonAreaFunctional_reflectedPolygonCap
    (Θ : AngleSet) (K : PolygonCapSpace Θ) :
    polygonAreaFunctional (reflectedAngleSet Θ) (reflectedPolygonCap Θ K).val =
      polygonAreaFunctional Θ K.val := by
  unfold polygonAreaFunctional
  rw [angleCap_eq_self, angleCap_eq_self, polygonNiche_reflection]
  change ClassicalResults.area (capReflection Θ.angle '' (K.val.val : Set Point)) -
      ClassicalResults.area (capReflection Θ.angle '' polygonNiche Θ K.val) = _
  rw [area_image_capReflection Θ.angle (K.val.val : Set Point)
      K.val.val.isCompact.measurableSet,
    area_image_capReflection Θ.angle (polygonNiche Θ K.val)
      (measurableSet_polygonNiche Θ K.val)]

private def reflectedPolygonCapBack (Θ : AngleSet)
    (L : PolygonCapSpace (reflectedAngleSet Θ)) : PolygonCapSpace Θ :=
  ⟨⟨reflectedBody Θ.angle L.val.val, reflectedBody_isCap L.val⟩, by
    simpa [reflectedAngleSet, Finset.image_image] using
      reflectedBody_polygonRepresentation (reflectedAngleSet Θ) L⟩

private theorem polygonNiche_reflection_back (Θ : AngleSet)
    (L : PolygonCapSpace (reflectedAngleSet Θ)) :
    polygonNiche Θ (reflectedPolygonCapBack Θ L).val =
      capReflection Θ.angle '' polygonNiche (reflectedAngleSet Θ) L.val := by
  unfold polygonNiche
  change capFan Θ.angle ∩
      (⋃ t ∈ Θ.directions, innerQuadrant (reflectedBody Θ.angle L.val.val) t) =
    capReflection Θ.angle ''
      (capFan Θ.angle ∩
        ⋃ t ∈ (reflectedAngleSet Θ).directions, innerQuadrant L.val.val t)
  rw [Set.image_inter (capReflection Θ.angle).injective,
    capReflection_image_capFan]
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    change p ∈ innerQuadrant (reflectedBody Θ.angle L.val.val) t at hp
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨Θ.angle - t, ?_, hq⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_⟩
    rw [innerQuadrant_reflection]
    exact ⟨q, hq, rfl⟩

private theorem polygonAreaFunctional_reflectedPolygonCapBack (Θ : AngleSet)
    (L : PolygonCapSpace (reflectedAngleSet Θ)) :
    polygonAreaFunctional Θ (reflectedPolygonCapBack Θ L).val =
      polygonAreaFunctional (reflectedAngleSet Θ) L.val := by
  unfold polygonAreaFunctional
  rw [angleCap_eq_self, angleCap_eq_self, polygonNiche_reflection_back]
  change ClassicalResults.area (capReflection Θ.angle '' (L.val.val : Set Point)) -
      ClassicalResults.area
        (capReflection Θ.angle '' polygonNiche (reflectedAngleSet Θ) L.val) = _
  rw [area_image_capReflection Θ.angle (L.val.val : Set Point)
      L.val.val.isCompact.measurableSet,
    area_image_capReflection Θ.angle (polygonNiche (reflectedAngleSet Θ) L.val)
      (measurableSet_polygonNiche (reflectedAngleSet Θ) L.val)]

private theorem mirrorReflection_stripTop (ω : ℝ) :
    mirrorReflection ω (stripParallelogram ω).2.2 =
      (stripParallelogram ω).2.2 := by
  change stripTopReflection ω (stripParallelogram ω).2.2 = _
  exact stripTopReflection_stripTop ω

theorem maximumPolygonCap_mirror (Θ : AngleSet) (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) :
    ∃ P : PolygonCapSpace (reflectedAngleSet Θ),
      (P.val.val : Set Point) = mirrorReflection Θ.angle '' (K.val.val : Set Point) ∧
      IsMaximumPolygonCap (reflectedAngleSet Θ) P := by
  let P := reflectedPolygonCap Θ K
  refine ⟨P, ?_, ?_⟩
  · change capReflection Θ.angle '' (K.val.val : Set Point) =
      mirrorReflection Θ.angle '' (K.val.val : Set Point)
    rw [mirrorReflection_eq_capReflection Θ.angle Θ.angle_pos Θ.angle_le]
  · constructor
    · change (stripParallelogram Θ.angle).2.2 ∈
        capReflection Θ.angle '' (K.val.val : Set Point)
      refine ⟨(stripParallelogram Θ.angle).2.2, hK.1, ?_⟩
      rw [← mirrorReflection_eq_capReflection Θ.angle Θ.angle_pos Θ.angle_le,
        mirrorReflection_stripTop]
    · intro L
      calc
        polygonAreaFunctional (reflectedAngleSet Θ) L.val =
            polygonAreaFunctional Θ (reflectedPolygonCapBack Θ L).val :=
          (polygonAreaFunctional_reflectedPolygonCapBack Θ L).symm
        _ ≤ polygonAreaFunctional Θ K.val := hK.2 (reflectedPolygonCapBack Θ L)
        _ = polygonAreaFunctional (reflectedAngleSet Θ) P.val :=
          (polygonAreaFunctional_reflectedPolygonCap Θ K).symm

private def castPolygonCap {Θ Φ : AngleSet} (h : Θ = Φ)
    (K : PolygonCapSpace Θ) : PolygonCapSpace Φ :=
  cast (congrArg PolygonCapSpace h) K

@[simp] private theorem castPolygonCap_coe {Θ Φ : AngleSet} (h : Θ = Φ)
    (K : PolygonCapSpace Θ) :
    ((castPolygonCap h K).val.val : Set Point) = (K.val.val : Set Point) := by
  subst h
  rfl

private theorem isMaximumPolygonCap_castPolygonCap {Θ Φ : AngleSet} (h : Θ = Φ)
    {K : PolygonCapSpace Θ} (hK : IsMaximumPolygonCap Θ K) :
    IsMaximumPolygonCap Φ (castPolygonCap h K) := by
  subst h
  exact hK

private theorem reflectedAngleSet_uniformAngleSet (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ) (hn : 2 ≤ n) :
    reflectedAngleSet (uniformAngleSet ω hω hω' n hn) =
      uniformAngleSet ω hω hω' n hn := by
  unfold reflectedAngleSet uniformAngleSet
  congr 1
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.mp hj
    apply Finset.mem_image.mpr
    refine ⟨n - j, Finset.mem_Ioo.mpr ⟨Nat.sub_pos_of_lt hjn, ?_⟩, ?_⟩
    · omega
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hjn.le]
    field_simp
  · intro ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hj0, hjn⟩ := Finset.mem_Ioo.mp hj
    apply Finset.mem_image.mpr
    refine ⟨ω - (j : ℝ) / n * ω, ?_, by ring⟩
    apply Finset.mem_image.mpr
    refine ⟨n - j, Finset.mem_Ioo.mpr ⟨Nat.sub_pos_of_lt hjn, by omega⟩, ?_⟩
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_sub hjn.le]
    field_simp

theorem balancedMaximumCap_mirror {ω : ℝ} (K : CapSpace ω)
    (hK : IsBalancedMaximumCap K) :
    ∃ P : CapSpace ω,
      (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) ∧
      IsBalancedMaximumCap P := by
  obtain ⟨n, hn, hmono, hdyadic, Q, hQmax, hQlim⟩ := hK
  let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
  have hM : mirrorReflection ω = capReflection ω :=
    mirrorReflection_eq_capReflection ω K.property.1 K.property.2.1
  have hmirror : (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) := by
    change capReflection ω '' (K.val : Set Point) = mirrorReflection ω '' (K.val : Set Point)
    rw [hM]
  refine ⟨P, hmirror, n, hn, hmono, hdyadic, ?_⟩
  have hR (i : ℕ) : ∃ R : PolygonCapSpace
      (uniformAngleSet ω P.property.1 P.property.2.1 (n i) (hn i)),
      (R.val.val : Set Point) = mirrorReflection ω '' (Q i).val.val ∧
        IsMaximumPolygonCap _ R := by
    have heq := reflectedAngleSet_uniformAngleSet ω K.property.1 K.property.2.1
      (n i) (hn i)
    let W := maximumPolygonCap_mirror _ (Q i) (hQmax i)
    let R := castPolygonCap heq W.choose
    refine ⟨R, ?_, ?_⟩
    · rw [castPolygonCap_coe]
      simpa [W, uniformAngleSet] using W.choose_spec.1
    · exact isMaximumPolygonCap_castPolygonCap heq W.choose_spec.2
  let R : ∀ i, PolygonCapSpace
      (uniformAngleSet ω P.property.1 P.property.2.1 (n i) (hn i)) :=
    fun i ↦ (hR i).choose
  refine ⟨R, ?_, ?_⟩
  · exact fun i ↦ (hR i).choose_spec.2
  · apply hQlim.congr'
    filter_upwards [] with i
    rw [(hR i).choose_spec.1, hmirror, hM]
    exact (Metric.hausdorffDist_image (capReflection ω).isometry).symm

end MovingSofa
