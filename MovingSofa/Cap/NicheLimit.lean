import MovingSofa.Bounds.NicheLimits

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- Containment of uniformly approximating polygon niches persists in the cap limit. -/
theorem capNiche_subset_of_uniform_polygonNiche_subset {ω : ℝ} (K : CapSpace ω)
    (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i) (hmono : StrictMono n)
    (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    (P : ∀ i, PolygonCapSpace
      (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)))
    (hcontain : ∀ i, polygonNiche
      (uniformAngleSet ω K.property.1 K.property.2.1 (n i) (hn i)) (P i).val ⊆
        ((P i).val.val : Set Point))
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point)
      (K.val : Set Point)) atTop (𝓝 0)) : capNiche K ⊆ (K.val : Set Point) := by
  intro p hp
  obtain ⟨m, hm⟩ := (eventually_mem_polygonNiche_of_mem_capNiche ω K.property.1
    K.property.2.1 n hn hmono K hp).exists
  obtain ⟨hfan, hquad⟩ := hm
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hquad
  change inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val (t : Real.Angle) - 1 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 at hpt
  have htend := tendsto_supportValue_of_hausdorff (fun i ↦ (P i).val) K hlim t
  have htend' := tendsto_supportValue_of_hausdorff (fun i ↦ (P i).val) K hlim
    (t + Real.pi / 2)
  apply ConvexBody.mem_of_tendsto_hausdorffDist p (fun i ↦ (P i).val.val) K.val _ hlim
  filter_upwards [(htend.sub_const 1).eventually_const_lt hpt.1,
    (htend'.sub_const 1).eventually_const_lt hpt.2, eventually_ge_atTop m] with i hi hi' hmi
  apply hcontain i
  refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨t, ?_, ?_⟩⟩
  · exact uniformAngleSet_directions_mono_of_dyadic ω K.property.1 K.property.2.1
      n hn hmono.monotone hdyadic hmi ht
  · exact ⟨hi, hi'⟩

end MovingSofa
