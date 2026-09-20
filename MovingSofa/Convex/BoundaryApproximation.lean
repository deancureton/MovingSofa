import MovingSofa.Convex.BoundaryVariation
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

namespace MovingSofa

theorem positiveVertex_boundedVariation (K : ConvexBody Point) (a b : ℝ) (hab : a ≤ b) :
    BoundedVariationOn (fun t : ℝ ↦ (edgeVertices K (t : Real.Angle)).1) (Set.Icc a b) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact BoundedVariationOn.of_subsingleton (Set.subsingleton_Icc_of_ge le_rfl)
  · exact boundedVariationOn_of_mem_exposedEdge K _ (fun t ↦ edgeVertices_fst_mem K _) a b

private theorem exists_facePreserving_polygon (K : ConvexBody Point)
    (F : Finset Real.Angle) {ε : ℝ} (hε : 0 < ε) :
    ∃ (V : Finset Point) (P : ConvexBody Point),
      V.Nonempty ∧
      (P : Set Point) = convexHull ℝ (V : Set Point) ∧
      (P : Set Point) ⊆ (K : Set Point) ∧
      (∀ t ∈ F, exposedEdge P t = exposedEdge K t) ∧
      Metric.hausdorffDist (P : Set Point) (K : Set Point) ≤ ε := by
  obtain ⟨S, hSK, hSfinite, hcover⟩ :=
    Metric.finite_approx_of_totallyBounded K.isCompact.totallyBounded ε hε
  let N : Finset Point := hSfinite.toFinset
  let E : Finset Point :=
    F.image (fun t ↦ (edgeVertices K t).1) ∪
      F.image (fun t ↦ (edgeVertices K t).2)
  let p₀ : Point := Classical.choose K.nonempty
  let V : Finset Point := insert p₀ (N ∪ E)
  have hp₀ : p₀ ∈ K := Classical.choose_spec K.nonempty
  have hVnonempty : V.Nonempty := by
    exact ⟨p₀, Finset.mem_insert_self p₀ _⟩
  have hVsubset : (V : Set Point) ⊆ (K : Set Point) := by
    intro p hp
    simp only [V, E, Finset.mem_coe, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image] at hp
    rcases hp with rfl | hpN | hpE
    · exact hp₀
    · exact hSK (hSfinite.mem_toFinset.mp hpN)
    · rcases hpE with hpE | hpE
      · obtain ⟨t, ht, rfl⟩ := hpE
        exact (edgeVertices_fst_mem K t).1
      · obtain ⟨t, ht, rfl⟩ := hpE
        exact (edgeVertices_snd_mem K t).1
  let P : ConvexBody Point :=
    { carrier := convexHull ℝ (V : Set Point)
      convex' := convex_convexHull ℝ _
      isCompact' := V.finite_toSet.isCompact_convexHull ℝ
      nonempty' := ⟨p₀, subset_convexHull ℝ _ (Finset.mem_coe.mpr
        (Finset.mem_insert_self p₀ _))⟩ }
  have hPcarrier : (P : Set Point) = convexHull ℝ (V : Set Point) := rfl
  have hPK : (P : Set Point) ⊆ (K : Set Point) := by
    change convexHull ℝ (V : Set Point) ⊆ (K : Set Point)
    exact convexHull_min hVsubset K.convex
  have hfaces : ∀ t ∈ F, exposedEdge P t = exposedEdge K t := by
    intro t ht
    have hfstV : (edgeVertices K t).1 ∈ V := by
      simp only [V, E, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inl ⟨t, ht, rfl⟩))
    have hsndV : (edgeVertices K t).2 ∈ V := by
      simp only [V, E, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      exact Or.inr (Or.inr (Or.inr ⟨t, ht, rfl⟩))
    have hfstP : (edgeVertices K t).1 ∈ P := by
      exact subset_convexHull ℝ (V : Set Point) hfstV
    have hsndP : (edgeVertices K t).2 ∈ P := by
      exact subset_convexHull ℝ (V : Set Point) hsndV
    have hsupport : supportValue P t = supportValue K t := by
      apply le_antisymm
      · apply csSup_le (P.nonempty.image _)
        rintro _ ⟨p, hp, rfl⟩
        exact inner_le_supportValue K (hPK hp) t
      · have h := inner_le_supportValue P hfstP t
        rw [(edgeVertices_fst_mem K t).2] at h
        exact h
    ext p
    constructor
    · intro hp
      exact ⟨hPK hp.1, hp.2.trans hsupport⟩
    · intro hp
      have hpseg : p ∈ segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
        rw [← exposedEdge_eq_segment_edgeVertices]
        exact hp
      have hpP : p ∈ P := P.convex.segment_subset hsndP hfstP hpseg
      exact ⟨hpP, hp.2.trans hsupport.symm⟩
  have hdist : Metric.hausdorffDist (P : Set Point) (K : Set Point) ≤ ε := by
    apply Metric.hausdorffDist_le_of_mem_dist hε.le
    · intro p hp
      exact ⟨p, hPK hp, dist_self p ▸ hε.le⟩
    · intro p hp
      have hpcover := hcover hp
      simp only [Set.mem_iUnion, Metric.mem_ball] at hpcover
      obtain ⟨q, hqS, hpq⟩ := hpcover
      have hqN : q ∈ N := hSfinite.mem_toFinset.mpr hqS
      have hqV : q ∈ V := by
        simp only [V, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl hqN)
      have hqP : q ∈ P := subset_convexHull ℝ (V : Set Point) hqV
      exact ⟨q, hqP, hpq.le⟩
  exact ⟨V, P, hVnonempty, hPcarrier, hPK, hfaces, hdist⟩

theorem exists_facePreserving_polygonApproximation (K : ConvexBody Point)
    (F : Finset Real.Angle) :
    ∃ (V : ℕ → Finset Point) (P : ℕ → ConvexBody Point),
      (∀ n, (V n).Nonempty ∧
        (P n : Set Point) = convexHull ℝ (V n : Set Point) ∧
        (P n : Set Point) ⊆ (K : Set Point) ∧
        ∀ t ∈ F, exposedEdge (P n) t = exposedEdge K t) ∧
      ∀ n : ℕ, 1 ≤ n → Metric.hausdorffDist (P n : Set Point) (K : Set Point) ≤ 1 / (n : ℝ) := by
  let m : ℕ → ℕ := fun n ↦ max n 1
  let V : ℕ → Finset Point := fun n ↦
    Classical.choose (exists_facePreserving_polygon K F
      (show 0 < 1 / (m n : ℝ) by positivity))
  let P : ℕ → ConvexBody Point := fun n ↦
    Classical.choose (Classical.choose_spec (exists_facePreserving_polygon K F
      (show 0 < 1 / (m n : ℝ) by positivity)))
  have hdata (n : ℕ) := Classical.choose_spec (Classical.choose_spec
    (exists_facePreserving_polygon K F (show 0 < 1 / (m n : ℝ) by positivity)))
  refine ⟨V, P, ?_, ?_⟩
  · intro n
    exact ⟨(hdata n).1, (hdata n).2.1, (hdata n).2.2.1, (hdata n).2.2.2.1⟩
  · intro n hn
    have hmn : m n = n := max_eq_left hn
    simpa only [P, m, hmn] using (hdata n).2.2.2.2

end MovingSofa
