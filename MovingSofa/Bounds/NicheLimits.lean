import MovingSofa.Convex.Limits
import MovingSofa.Polygon.Approximation
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- Support values converge under Hausdorff convergence of caps. -/
theorem tendsto_supportValue_of_hausdorff {ω : ℝ}
    (K : ℕ → CapSpace ω) (L : CapSpace ω)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun i ↦ supportValue (K i).val (t : Real.Angle)) atTop
      (𝓝 (supportValue L.val (t : Real.Angle))) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro i
  simpa only [Real.dist_eq, vectorSupport, supportValue] using
    (compactSet_support_continuity (K i).val L.val (K i).val.nonempty
      (K i).val.isCompact L.val.nonempty L.val.isCompact).2.1
        (normalVector (t : Real.Angle)) (norm_normalVector_real t)

private theorem volume_normalLine_eq_zero (t c : ℝ) :
    volume {p : Point | inner ℝ p (normalVector (t : Real.Angle)) = c} = 0 := by
  let u := normalVector (t : Real.Angle)
  let f : Point →ᵃ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.toAffineMap
  let A := (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f
  have hA : (A : Set Point) = {p : Point | inner ℝ p u = c} := by
    ext p
    simp [A, f, AffineSubspace.mem_mk', real_inner_comm, sub_eq_zero]
  rw [← hA]
  apply Measure.addHaar_affineSubspace
  intro htop
  have hp : (c + 1) • u ∈ A := by rw [htop]; trivial
  rw [← SetLike.mem_coe, hA] at hp
  have hu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_normalVector_real]
    norm_num
  change inner ℝ ((c + 1) • u) u = c at hp
  rw [real_inner_smul_left, hu, mul_one] at hp
  linarith

private theorem eventually_lt_iff_of_ne {f : ℕ → ℝ} {a x : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hxa : x ≠ a) :
    ∀ᶠ i in atTop, (x < f i ↔ x < a) := by
  rcases lt_or_gt_of_ne hxa with h | h
  · filter_upwards [hf.eventually_const_lt h] with i hi
    exact iff_of_true hi h
  · filter_upwards [hf.eventually_lt_const h] with i hi
    exact iff_of_false (not_lt_of_ge hi.le) (not_lt_of_ge h.le)

private theorem ae_eventually_mem_polygonNiche_iff (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume, ∀ᶠ i in atTop, (p ∈ polygonNiche Θ (K i) ↔ p ∈ polygonNiche Θ L) := by
  have hae (t : ℝ) : ∀ᵐ p ∂volume,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) - 1 := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_normalLine_eq_zero t
      (supportValue L.val (t : Real.Angle) - 1)
  have hall : ∀ᵐ p ∂volume, ∀ t ∈ Θ.directions,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) - 1 ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 :=
    Θ.directions.eventually_all.mpr fun t _ ↦ (hae t).and (hae (t + Real.pi / 2))
  filter_upwards [hall] with p hp
  have hq (t : ℝ) (ht : t ∈ Θ.directions) : ∀ᶠ i in atTop,
      (p ∈ innerQuadrant (K i).val t ↔ p ∈ innerQuadrant L.val t) := by
    have h₁ := eventually_lt_iff_of_ne
      ((tendsto_supportValue_of_hausdorff K L hlim t).sub_const 1) (hp t ht).1
    have h₂ := eventually_lt_iff_of_ne
      ((tendsto_supportValue_of_hausdorff K L hlim (t + Real.pi / 2)).sub_const 1)
      (hp t ht).2
    filter_upwards [h₁, h₂] with i h₁ h₂
    exact and_congr h₁ h₂
  filter_upwards [Θ.directions.eventually_all.mpr hq] with i hi
  simp only [polygonNiche, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hf, t, ht, hqt⟩
    exact ⟨hf, t, ht, (hi t ht).mp hqt⟩
  · rintro ⟨hf, t, ht, hqt⟩
    exact ⟨hf, t, ht, (hi t ht).mpr hqt⟩

private theorem eventually_le_iff_of_ne {f : ℕ → ℝ} {a x : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hxa : x ≠ a) :
    ∀ᶠ i in atTop, (x ≤ f i ↔ x ≤ a) := by
  rcases lt_or_gt_of_ne hxa with h | h
  · filter_upwards [hf.eventually_const_lt h] with i hi
    exact iff_of_true hi.le h.le
  · filter_upwards [hf.eventually_lt_const h] with i hi
    exact iff_of_false (not_le_of_gt hi) (not_le_of_gt h)

private theorem ae_eventually_mem_angleCap_iff (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∀ᵐ p ∂volume, ∀ᶠ i in atTop, (p ∈ angleCap Θ (K i) ↔ p ∈ angleCap Θ L) := by
  have hae (t : ℝ) : ∀ᵐ p ∂volume,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) := by
    apply ae_iff.mpr
    simpa only [not_not] using volume_normalLine_eq_zero t
      (supportValue L.val (t : Real.Angle))
  have hall : ∀ᵐ p ∂volume, ∀ t ∈ Θ.directions,
      inner ℝ p (normalVector (t : Real.Angle)) ≠ supportValue L.val (t : Real.Angle) ∧
      inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≠
        supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle) :=
    Θ.directions.eventually_all.mpr fun t _ ↦ (hae t).and (hae (t + Real.pi / 2))
  filter_upwards [hall] with p hp
  have hq (t : ℝ) (ht : t ∈ Θ.directions) : ∀ᶠ i in atTop,
      (inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue (K i).val (t : Real.Angle) ↔
        inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue L.val (t : Real.Angle)) ∧
      (inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue (K i).val ((t + Real.pi / 2 : ℝ) : Real.Angle) ↔
        inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
          supportValue L.val ((t + Real.pi / 2 : ℝ) : Real.Angle)) :=
    (eventually_le_iff_of_ne (tendsto_supportValue_of_hausdorff K L hlim t) (hp t ht).1).and
      (eventually_le_iff_of_ne (tendsto_supportValue_of_hausdorff K L hlim
        (t + Real.pi / 2)) (hp t ht).2)
  filter_upwards [Θ.directions.eventually_all.mpr hq] with i hi
  simp only [mem_angleCap_iff]
  apply and_congr_right
  intro _
  exact forall_congr' fun t ↦ forall_congr' fun ht ↦ and_congr (hi t ht).1 (hi t ht).2

private theorem exists_angleCap_norm_bound (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    ∃ R : ℝ, ∀ i p, p ∈ angleCap Θ (K i) → ‖p‖ ≤ R := by
  obtain ⟨t, ht⟩ := Θ.nonempty
  have hti := Θ.interior t ht
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, hti.1], hti.2.trans_le Θ.angle_le⟩
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hti.1
    (by linarith [hti.2, Θ.angle_le, Real.pi_pos])
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_supportValue_of_hausdorff K L hlim t)).exists_norm_le
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _
    (tendsto_supportValue_of_hausdorff K L hlim (t + Real.pi / 2))).exists_norm_le
  let l := -|B| / Real.sin t
  let r := |A| / Real.cos t
  let M := |l| + |r|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M + 1, fun i p hp ↦ ?_⟩
  have haBound : supportValue (K i).val (t : Real.Angle) ≤ |A| :=
    (le_abs_self _).trans ((hA _ (Set.mem_range_self i)).trans (le_abs_self A))
  have hbBound : supportValue (K i).val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤ |B| :=
    (le_abs_self _).trans ((hB _ (Set.mem_range_self i)).trans (le_abs_self B))
  obtain ⟨⟨hy, _⟩, hnormals⟩ := (mem_angleCap_iff Θ (K i) p).mp hp
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

private theorem tendsto_polygonNiche_area (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (polygonNiche Θ (K i))) atTop
      (𝓝 (ClassicalResults.area (polygonNiche Θ L))) := by
  obtain ⟨R, hR, _, hpoly⟩ := niche_uniform_bounds.2.2 (fun _ ↦ Θ.angle) K L.val hlim
  let C := Metric.closedBall (0 : Point) (2 * R)
  have hcompact : IsCompact C := isCompact_closedBall _ _
  have hsubset (i : ℕ) : polygonNiche Θ (K i) ⊆ C := by
    intro p hp
    obtain ⟨hx, hy, hh⟩ := hpoly i Θ (K i) rfl hp
    change dist p 0 ≤ 2 * R
    rw [dist_zero_right]
    have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) hR).mpr hx
    have hy2 := (sq_le_sq₀ hy hR).mpr hh
    have hn := EuclideanSpace.norm_sq_eq p
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2
    nlinarith [norm_nonneg p, sq_nonneg R]
  have hCint : Integrable (C.indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hcompact.measurableSet
  have hpointwise : ∀ᵐ p ∂volume,
      Tendsto (fun i ↦ (polygonNiche Θ (K i)).indicator (fun _ ↦ (1 : ℝ)) p)
        atTop (𝓝 ((polygonNiche Θ L).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    filter_upwards [ae_eventually_mem_polygonNiche_iff Θ K L hlim] with p hp
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hp] with i hi
    by_cases h : p ∈ polygonNiche Θ L
    · simp [h, hi.mpr h]
    · have hn : p ∉ polygonNiche Θ (K i) := fun hk ↦ h (hi.mp hk)
      simp [h, hn]
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i ↦ (polygonNiche Θ (K i)).indicator fun _ ↦ (1 : ℝ))
    (f := (polygonNiche Θ L).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun i ↦
      (measurable_const.indicator (measurableSet_polygonNiche Θ (K i))).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ polygonNiche Θ (K i)
      · simp [hp, hsubset i hp]
      · by_cases hpc : p ∈ C <;> simp [hp, hpc]) hCint hpointwise
  have harea (P : CapSpace Θ.angle) :
      (∫ p, (polygonNiche Θ P).indicator (fun _ ↦ (1 : ℝ)) p) =
        ClassicalResults.area (polygonNiche Θ P) := by
    exact integral_indicator_one (measurableSet_polygonNiche Θ P)
  simpa only [harea] using hconv

private theorem tendsto_angleCap_area (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (angleCap Θ (K i))) atTop
      (𝓝 (ClassicalResults.area (angleCap Θ L))) := by
  obtain ⟨R, hR⟩ := exists_angleCap_norm_bound Θ K L hlim
  let C := Metric.closedBall (0 : Point) R
  have hcompact : IsCompact C := isCompact_closedBall _ _
  have hsubset (i : ℕ) : angleCap Θ (K i) ⊆ C := by
    intro p hp
    simpa only [C, Metric.mem_closedBall, dist_zero_right] using hR i p hp
  have hCint : Integrable (C.indicator fun _ ↦ (1 : ℝ)) :=
    (integrableOn_const hcompact.measure_lt_top.ne).integrable_indicator hcompact.measurableSet
  have hpointwise : ∀ᵐ p ∂volume,
      Tendsto (fun i ↦ (angleCap Θ (K i)).indicator (fun _ ↦ (1 : ℝ)) p)
        atTop (𝓝 ((angleCap Θ L).indicator (fun _ ↦ (1 : ℝ)) p)) := by
    filter_upwards [ae_eventually_mem_angleCap_iff Θ K L hlim] with p hp
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [hp] with i hi
    by_cases h : p ∈ angleCap Θ L
    · simp [h, hi.mpr h]
    · have hn : p ∉ angleCap Θ (K i) := fun hk ↦ h (hi.mp hk)
      simp [h, hn]
  have hconv := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun i ↦ (angleCap Θ (K i)).indicator fun _ ↦ (1 : ℝ))
    (f := (angleCap Θ L).indicator fun _ ↦ (1 : ℝ))
    (C.indicator fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun i ↦
      (measurable_const.indicator (isClosed_angleCap Θ (K i)).measurableSet).aestronglyMeasurable)
    (Eventually.of_forall fun i ↦ Eventually.of_forall fun p ↦ by
      by_cases hp : p ∈ angleCap Θ (K i)
      · simp [hp, hsubset i hp]
      · by_cases hpc : p ∈ C <;> simp [hp, hpc]) hCint hpointwise
  have harea (P : CapSpace Θ.angle) :
      (∫ p, (angleCap Θ P).indicator (fun _ ↦ (1 : ℝ)) p) =
        ClassicalResults.area (angleCap Θ P) := by
    exact integral_indicator_one (isClosed_angleCap Θ P).measurableSet
  simpa only [harea] using hconv

theorem polygonArea_continuity (Θ : AngleSet)
    (K : ℕ → CapSpace Θ.angle) (L : CapSpace Θ.angle)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((K i).val : Set Point)
      (L.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area (polygonNiche Θ (K i)))
      atTop (𝓝 (ClassicalResults.area (polygonNiche Θ L))) ∧
    Tendsto (fun i ↦ polygonAreaFunctional Θ (K i))
      atTop (𝓝 (polygonAreaFunctional Θ L)) := by
  exact ⟨tendsto_polygonNiche_area Θ K L hlim,
    (tendsto_angleCap_area Θ K L hlim).sub (tendsto_polygonNiche_area Θ K L hlim)⟩

private theorem polygonNiche_mono_directions (Θ Ψ : AngleSet)
    (K : CapSpace Θ.angle) (L : CapSpace Ψ.angle)
    (hangle : Θ.angle = Ψ.angle) (hcarrier : (K.val : Set Point) = (L.val : Set Point))
    (hsub : Θ.directions ⊆ Ψ.directions) :
    polygonNiche Θ K ⊆ polygonNiche Ψ L := by
  rintro p ⟨hp, hq⟩
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hq
  refine ⟨?_, Set.mem_iUnion₂.mpr ⟨t, hsub ht, ?_⟩⟩
  · simpa only [hangle] using hp
  · simpa only [hcarrier] using hpt

/-- Every niche point belongs to all sufficiently fine uniform polygon niches. -/
theorem eventually_mem_polygonNiche_of_mem_capNiche (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (K : CapSpace ω) {p : Point} (hp : p ∈ capNiche K) :
    ∀ᶠ i in atTop, p ∈ polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K := by
  obtain ⟨hfan, hq⟩ := hp
  obtain ⟨t, ht, hpt⟩ := Set.mem_iUnion₂.mp hq
  have hopen : IsOpen {s : ℝ | p ∈ innerQuadrant K.val s} := by
    apply IsOpen.inter
    · exact isOpen_lt (continuous_const.inner continuous_normalVector_real)
        ((continuous_supportValue_real K.val).sub continuous_const)
    · exact isOpen_lt
        (continuous_const.inner (continuous_normalVector_real.comp
          (continuous_id.add continuous_const)))
        (((continuous_supportValue_real K.val).comp
          (continuous_id.add continuous_const)).sub continuous_const)
  obtain ⟨a, b, ⟨hat, htb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds hpt)
  have hat' : max 0 a < t := max_lt ht.1 hat
  have htb' : t < min ω b := lt_min ht.2 htb
  filter_upwards [eventually_exists_uniformAngleSet_mem_Ioo ω hω hω' n hn hmono
    (le_max_left 0 a) (hat'.trans htb') (min_le_left ω b)] with i hi
  obtain ⟨s, hs, hsa, hsb⟩ := hi
  refine ⟨hfan, Set.mem_iUnion₂.mpr ⟨s, hs, hab ?_⟩⟩
  exact ⟨(le_max_right 0 a).trans_lt hsa, hsb.trans_le (min_le_right ω b)⟩

private theorem iUnion_uniform_polygonNiche (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (K : CapSpace ω) :
    (⋃ i, polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K) = capNiche K := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i ↦
      polygonNiche_subset_capNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K
  · intro p hp
    obtain ⟨i, hi⟩ := (eventually_mem_polygonNiche_of_mem_capNiche ω hω hω' n hn hmono K hp).exists
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

private theorem tendsto_uniform_polygonNiche_area (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k) (K : CapSpace ω) :
    Tendsto (fun i ↦ ClassicalResults.area
      (polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K)) atTop
      (𝓝 (ClassicalResults.area (capNiche K))) := by
  have hmon : Monotone (fun i ↦ polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) K) := by
    intro i j hij
    exact polygonNiche_mono_directions
      (uniformAngleSet ω hω hω' (n i) (hn i))
      (uniformAngleSet ω hω hω' (n j) (hn j)) K K rfl rfl
      (uniformAngleSet_directions_mono_of_dyadic ω hω hω' n hn hmono.monotone hdyadic hij)
  have hlim := tendsto_measure_iUnion_atTop (μ := volume) hmon
  rw [iUnion_uniform_polygonNiche ω hω hω' n hn hmono K] at hlim
  exact (ENNReal.tendsto_toReal (niche_uniform_bounds.1 ω K).2.2.1.ne).comp hlim

theorem maximizingPolygon_nicheArea_limit (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    (P : ∀ i, PolygonCapSpace (uniformAngleSet ω hω hω' (n i) (hn i)))
    (hmax : ∀ i, IsMaximumPolygonCap _ (P i)) (K : CapSpace ω)
    (hlim : Tendsto (fun i ↦ Metric.hausdorffDist ((P i).val.val : Set Point)
      (K.val : Set Point)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ ClassicalResults.area
      (polygonNiche (uniformAngleSet ω hω hω' (n i) (hn i)) (P i).val))
      atTop (𝓝 (ClassicalResults.area (capNiche K))) := by
  let Θ (i : ℕ) := uniformAngleSet ω hω hω' (n i) (hn i)
  have hupper (i : ℕ) :
      ClassicalResults.area (polygonNiche (Θ i) (P i).val) ≤
        ClassicalResults.area ((P i).val.val : Set Point) - capAreaFunctional K := by
    have hmax' := polygonAreaFunctional_le_maximum (Θ i) (P i) (hmax i) K
    have hbound := (polygonArea_upperBound (Θ i)).2 K
    have harea := (polygonArea_upperBound (Θ i)).1 (P i)
    have h := hbound.trans hmax'
    rw [harea] at h
    exact le_sub_comm.mp h
  have hupperlim : Tendsto
      (fun i ↦ ClassicalResults.area ((P i).val.val : Set Point) - capAreaFunctional K)
      atTop (𝓝 (ClassicalResults.area (capNiche K))) := by
    convert (convexArea_hausdorff_continuity (fun i ↦ (P i).val.val) K.val hlim).sub_const
      (capAreaFunctional K) using 1
    simp only [capAreaFunctional, sub_sub_cancel]
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hex := (tendsto_uniform_polygonNiche_area ω hω hω' n hn hmono hdyadic K).eventually_const_lt ha
    obtain ⟨m, hm⟩ := hex.exists
    have hfixed := (polygonArea_continuity (Θ m) (fun i ↦ (P i).val) K hlim).1
    filter_upwards [hfixed.eventually_const_lt hm, eventually_ge_atTop m] with i hi hmi
    have hsub : polygonNiche (Θ m) (P i).val ⊆ polygonNiche (Θ i) (P i).val :=
      polygonNiche_mono_directions (Θ m) (Θ i) (P i).val (P i).val rfl rfl
        (uniformAngleSet_directions_mono_of_dyadic ω hω hω' n hn hmono.monotone hdyadic hmi)
    have hle : ClassicalResults.area (polygonNiche (Θ m) (P i).val) ≤
        ClassicalResults.area (polygonNiche (Θ i) (P i).val) :=
      ENNReal.toReal_mono (niche_uniform_bounds.2.1 (Θ i) (P i).val).2.2.1.ne (measure_mono hsub)
    exact hi.trans_le hle
  · intro b hb
    filter_upwards [hupperlim.eventually_lt_const hb] with i hi
    exact (hupper i).trans_lt hi


end MovingSofa
