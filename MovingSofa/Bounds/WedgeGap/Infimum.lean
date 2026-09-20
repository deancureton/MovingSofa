import MovingSofa.Polygon.Balancing

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace MovingSofa

def wedgeGapInfimum {ω : ℝ} (K : CapSpace ω) : ℝ × ℝ :=
  (sInf ((fun t ↦ (wedgeGaps K t).1) '' Set.Ioo 0 ω),
    sInf ((fun t ↦ (wedgeGaps K t).2) '' Set.Ioo 0 ω))

private theorem bddBelow_wedgeGaps_fst {ω : ℝ} (K : CapSpace ω) :
    BddBelow ((fun t ↦ (wedgeGaps K t).1) '' Ioo 0 ω) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  have h := wedgeGaps_positive_lower_bound K t ht
  exact h.2.1.le.trans h.1

private theorem wedgeGapInfimum_fst_nonneg {ω : ℝ} (K : CapSpace ω) :
    0 ≤ (wedgeGapInfimum K).1 := by
  rw [wedgeGapInfimum]
  apply le_csInf
  · exact (nonempty_Ioo.mpr K.property.1).image _
  · rintro _ ⟨t, ht, rfl⟩
    have h := wedgeGaps_positive_lower_bound K t ht
    exact h.2.1.le.trans h.1

private theorem wedgeGapInfimum_fst_le_supportValue_zero {ω : ℝ}
    (K : CapSpace ω) (hω : ω < Real.pi / 2) :
    (wedgeGapInfimum K).1 ≤ supportValue K.val (0 : Real.Angle) := by
  let f := fun t : ℝ ↦ supportValue K.val (0 : Real.Angle) -
    (supportValue K.val (t : Real.Angle) - 1) / Real.cos t
  have hcos : Real.cos ω ≠ 0 := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [K.property.1, Real.pi_pos], hω⟩).ne'
  have hf : ContinuousAt f ω := continuousAt_const.sub
    (((continuous_supportValue_real K.val).continuousAt.sub continuousAt_const).div
      Real.continuous_cos.continuousAt hcos)
  have hf' : Tendsto f (𝓝[<] ω) (𝓝 (f ω)) :=
    hf.tendsto.mono_left inf_le_left
  have hlim : Tendsto f (𝓝[<] ω)
      (𝓝 (supportValue K.val (0 : Real.Angle))) := by
    convert hf' using 1
    simp [f, K.property.2.2.1]
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsLT K.property.1] with t ht
  rw [wedgeGapInfimum]
  have hle := csInf_le (bddBelow_wedgeGaps_fst K) ⟨t, ht, rfl⟩
  simpa only [f, wedgeGaps_fst_eq_supportValue] using hle

private def bottomGapSegment {ω : ℝ} (K : CapSpace ω) : Set Point :=
  let a := supportValue K.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K).1
  segment ℝ ((a - w) • normalVector (0 : Real.Angle))
    (a • normalVector (0 : Real.Angle))

private theorem point_eq_fst_smul_normalVector_zero_of_mem_normalLine
    {p : Point} (hp : p ∈ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) :
    p = p 0 • normalVector (0 : Real.Angle) := by
  have hpy : p 1 = 0 := by
    change inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hp
    simpa [normalVector, frame, PiLp.inner_apply] using hp
  ext i
  fin_cases i <;> simp [normalVector, frame, hpy]

private theorem bottomGapSegment_subset_exposedEdge {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    bottomGapSegment K.val ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  let a := supportValue K.val.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K.val).1
  let A := a • normalVector (0 : Real.Angle)
  let B := (a - w) • normalVector (0 : Real.Angle)
  have hzeroK : (0 : Point) ∈ (K.val.val : Set Point) := zero_mem_cap_of_lt K.val hω
  have hAK : A ∈ (K.val.val : Set Point) := by
    exact supportValue_zero_smul_normalVector_mem K.val
  have hw0 : 0 ≤ w := wedgeGapInfimum_fst_nonneg K.val
  have hwa : w ≤ a := wedgeGapInfimum_fst_le_supportValue_zero K.val hω
  have hBK : B ∈ (K.val.val : Set Point) := by
    exact K.val.val.convex.smul_mem_of_nonneg_of_le hzeroK hAK
      (sub_nonneg.mpr hwa) (by linarith)
  have hbottom : supportValue K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := K.val.property.2.2.2.2.2.1
  have hAedge : A ∈ exposedEdge K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hAK, ?_⟩
    change inner ℝ A (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hbottom]
    rw [inner_normalVector_three_pi_div_two]
    simp [A, normalVector, frame]
  have hBedge : B ∈ exposedEdge K.val.val
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    refine ⟨hBK, ?_⟩
    change inner ℝ B (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) = _
    rw [hbottom]
    rw [inner_normalVector_three_pi_div_two]
    simp [B, normalVector, frame]
  exact (convex_exposedEdge K.val.val _).segment_subset hBedge hAedge

private theorem polygonNiche_fanLine_fst_lt_gapStart {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {q : Point}
    (hq : q ∈ polygonNiche Θ K.val ∩
      normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) :
    q 0 < supportValue K.val.val (0 : Real.Angle) -
      (wedgeGapInfimum K.val).1 := by
  obtain ⟨t, ht, hqt⟩ := Set.mem_iUnion₂.mp hq.1.2
  have htt := Θ.interior t ht
  have hcost : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [htt.1, Real.pi_pos], htt.2.trans_le Θ.angle_le⟩
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
  have hinf : (wedgeGapInfimum K.val).1 ≤ (wedgeGaps K.val t).1 := by
    rw [wedgeGapInfimum]
    exact csInf_le (bddBelow_wedgeGaps_fst K.val) ⟨t, htt, rfl⟩
  have hgap : (wedgeGaps K.val t).1 =
      supportValue K.val.val (0 : Real.Angle) - (wedgeEndpoints K.val t).1 0 := by
    rw [wedgeGaps_fst_eq_supportValue]
    simp [wedgeEndpoints, normalVector, frame]
  rw [hgap] at hinf
  linarith

private theorem polygonNiche_fanLine_subset_bottom_exposedEdge {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2) :
    polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0 ⊆
      exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  intro q hq
  let a := supportValue K.val.val (0 : Real.Angle)
  let A := a • normalVector (0 : Real.Angle)
  have hzeroK : (0 : Point) ∈ (K.val.val : Set Point) := zero_mem_cap_of_lt K.val hω
  have hAK : A ∈ (K.val.val : Set Point) := supportValue_zero_smul_normalVector_mem K.val
  have hqx0 : 0 ≤ q 0 := by
    have hfan := hq.1.1.1
    have hqy : q 1 = 0 := by
      have hline := hq.2
      change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
      simpa [normalVector, frame, PiLp.inner_apply] using hline
    change 0 ≤ inner ℝ q (normalVector (Θ.angle : Real.Angle)) at hfan
    simp [normalVector, frame, PiLp.inner_apply, hqy] at hfan
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hfan)
      (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hω⟩)
  have hqxa : q 0 ≤ a := by
    have hlt := polygonNiche_fanLine_fst_lt_gapStart K hq
    have hw0 := wedgeGapInfimum_fst_nonneg K.val
    dsimp only [a]
    linarith
  have hqeq := point_eq_fst_smul_normalVector_zero_of_mem_normalLine hq.2
  have hqK : q ∈ (K.val.val : Set Point) := by
    rw [hqeq]
    exact K.val.val.convex.smul_mem_of_nonneg_of_le hzeroK hAK hqx0 hqxa
  refine ⟨hqK, ?_⟩
  change inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) =
    supportValue K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.val.property.2.2.2.2.2.1]
  have hqy : q 1 = 0 := by
    have hline := hq.2
    change inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 at hline
    simpa [normalVector, frame, PiLp.inner_apply] using hline
  rw [inner_normalVector_three_pi_div_two]
  simp [hqy]

private theorem bottomGapSegment_disjoint_polygonNiche_fanLine {Θ : AngleSet}
    (K : PolygonCapSpace Θ) :
    Disjoint (bottomGapSegment K.val)
      (polygonNiche Θ K.val ∩ normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0) := by
  rw [Set.disjoint_left]
  intro q hqS hqN
  let a := supportValue K.val.val (0 : Real.Angle)
  let w := (wedgeGapInfimum K.val).1
  let B := (a - w) • normalVector (0 : Real.Angle)
  let A := a • normalVector (0 : Real.Angle)
  have hw0 : 0 ≤ w := wedgeGapInfimum_fst_nonneg K.val
  have hqx : a - w ≤ q 0 := by
    change q ∈ segment ℝ B A at hqS
    rw [segment_eq_image'] at hqS
    obtain ⟨r, hr, rfl⟩ := hqS
    have heq : (B + r • (A - B)) 0 = a - w + r * w := by
      simp [B, A, normalVector, frame]
    rw [heq]
    nlinarith [hr.1]
  have hlt := polygonNiche_fanLine_fst_lt_gapStart K hqN
  exact (not_lt_of_ge hqx) (by simpa only [a, w] using hlt)

private theorem hausdorffMeasure_bottomGapSegment {ω : ℝ} (K : CapSpace ω) :
    (Measure.hausdorffMeasure 1 (bottomGapSegment K)).toReal =
      (wedgeGapInfimum K).1 := by
  have hw0 := wedgeGapInfimum_fst_nonneg K
  rw [show bottomGapSegment K =
      segment ℝ
        ((supportValue K.val (0 : Real.Angle) - (wedgeGapInfimum K).1) •
          normalVector (0 : Real.Angle))
        (supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle)) by rfl,
    MeasureTheory.hausdorffMeasure_segment, edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    dist_eq_norm]
  have hdiff :
      (supportValue K.val (0 : Real.Angle) - (wedgeGapInfimum K).1) •
          normalVector (0 : Real.Angle) -
        supportValue K.val (0 : Real.Angle) • normalVector (0 : Real.Angle) =
      (-(wedgeGapInfimum K).1) • normalVector (0 : Real.Angle) := by module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hw0,
    norm_normalVector, mul_one]

private theorem wedgeGapInfimum_fst_le_surface_of_balanced {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hω : Θ.angle < Real.pi / 2)
    (hbal : IsBalancedPolygonCap K) :
    (wedgeGapInfimum K.val).1 ≤
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
  let μ : Measure Point := Measure.hausdorffMeasure 1
  let S := bottomGapSegment K.val
  let M := polygonNiche Θ K.val ∩
    normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0
  let E := exposedEdge K.val.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  have hSsub : S ⊆ E := bottomGapSegment_subset_exposedEdge K hω
  have hMsub : M ⊆ E := polygonNiche_fanLine_subset_bottom_exposedEdge K hω
  have hSMsub : S ∪ M ⊆ E := Set.union_subset hSsub hMsub
  have hdisj : Disjoint S M := bottomGapSegment_disjoint_polygonNiche_fanLine K
  have hMMeas : MeasurableSet M := by
    apply (measurableSet_polygonNiche Θ K.val).inter
    exact (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hSne : μ S ≠ ⊤ := by
    dsimp only [μ, S]
    rw [show bottomGapSegment K.val =
        segment ℝ
          ((supportValue K.val.val (0 : Real.Angle) - (wedgeGapInfimum K.val).1) •
            normalVector (0 : Real.Angle))
          (supportValue K.val.val (0 : Real.Angle) • normalVector (0 : Real.Angle)) by rfl,
      MeasureTheory.hausdorffMeasure_segment, edist_dist]
    exact ENNReal.ofReal_ne_top
  have hatom := surfaceAreaMeasure_atom_length K.val.val
    ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  have hEne : μ E ≠ ⊤ := by
    dsimp only [μ, E]
    rw [← hatom.1, hatom.2.1]
    exact ENNReal.ofReal_ne_top
  have hMne : μ M ≠ ⊤ := measure_ne_top_of_subset hMsub hEne
  have hunion := measureReal_union hdisj hMMeas hSne hMne
  have hmono : μ.real (S ∪ M) ≤ μ.real E :=
    ENNReal.toReal_mono hEne (measure_mono hSMsub)
  have hSreal : μ.real S = (wedgeGapInfimum K.val).1 := by
    exact hausdorffMeasure_bottomGapSegment K.val
  have hMreal : μ.real M =
      (surfaceAreaMeasure K.val.val
        {((3 * Real.pi / 2 : ℝ) : Real.Angle)}).toReal -
        polygonPolylineLengthAt K (Real.pi / 2) := by
    have h := (polygonCap_polyline_lengths K).2 (Real.pi / 2) (by simp)
    dsimp only [μ, M]
    change (Measure.hausdorffMeasure 1
      (polygonNiche Θ K.val ∩
        normalLine ((Real.pi / 2 : ℝ) : Real.Angle) 0)).toReal = _
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    simpa only [hang] using h.2
  have hEreal : μ.real E =
      (surfaceAreaMeasure K.val.val
        {((3 * Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    exact (congrArg ENNReal.toReal hatom.1).symm
  have htT : Real.pi / 2 ∈ angleDomain Θ := by simp [angleDomain]
  let tT : angleDomain Θ := ⟨Real.pi / 2, htT⟩
  have hpoly0 : 0 ≤ polygonCapPolylineLength K tT := by
    unfold polygonCapPolylineLength
    exact Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
  have hbalReal :
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal =
        polygonCapPolylineLength K tT := by
    simpa only [tT, ENNReal.toReal_ofReal hpoly0] using
      congrArg ENNReal.toReal (hbal tT)
  have hlength : polygonPolylineLengthAt K (Real.pi / 2) =
      (surfaceAreaMeasure K.val.val
        {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal := by
    simp only [polygonPolylineLengthAt, dite_eq_left htT]
    exact hbalReal.symm
  rw [hunion, hSreal, hMreal, hEreal, hlength] at hmono
  linarith

theorem maximumPolygonCap_gap_le_surface {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (hK : IsMaximumPolygonCap Θ K) (hω : Θ.angle < Real.pi / 2) :
    (wedgeGapInfimum K.val).1 ≤
      (surfaceAreaMeasure K.val.val {((Real.pi / 2 : ℝ) : Real.Angle)}).toReal ∧
    (wedgeGapInfimum K.val).2 ≤
      (surfaceAreaMeasure K.val.val {(Θ.angle : Real.Angle)}).toReal := by
  have hbal := maximumPolygonCap_balanced K hK
  refine ⟨wedgeGapInfimum_fst_le_surface_of_balanced K hω hbal, ?_⟩
  obtain ⟨Q, hQcarrier, hQmax⟩ := maximumPolygonCap_mirror Θ K hK
  obtain ⟨P, hPcarrier, _hHall, hgap, _hupper, _hniche, hsurface⟩ :=
    cap_mirror_features K.val
  have hPQ : P = Q.val := by
    apply Subtype.ext
    apply ConvexBody.ext
    exact hPcarrier.trans hQcarrier.symm
  have hQbal := maximumPolygonCap_balanced Q hQmax
  have hQright := wedgeGapInfimum_fst_le_surface_of_balanced Q hω hQbal
  have himage :
      (fun t ↦ (wedgeGaps Q.val t).1) '' Ioo 0 Θ.angle =
        (fun t ↦ (wedgeGaps K.val t).2) '' Ioo 0 Θ.angle := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨ht0, htω⟩
      refine ⟨Θ.angle - t, ⟨by linarith, by linarith⟩, ?_⟩
      have hg := (hgap t ⟨ht0, htω⟩).2.2.1
      rw [hPQ] at hg
      change (wedgeGaps Q.val t).1 = (wedgeGaps K.val (Θ.angle - t)).2 at hg
      exact hg.symm
    · rintro ⟨t, ht, rfl⟩
      rcases ht with ⟨ht0, htω⟩
      have hcomp : Θ.angle - t ∈ Ioo 0 Θ.angle := ⟨by linarith, by linarith⟩
      refine ⟨Θ.angle - t, hcomp, ?_⟩
      have hg := (hgap (Θ.angle - t) hcomp).2.2.1
      rw [hPQ] at hg
      change (wedgeGaps Q.val (Θ.angle - t)).1 =
        (wedgeGaps K.val (Θ.angle - (Θ.angle - t))).2 at hg
      simpa only [sub_sub_cancel] using hg
  have hinf : (wedgeGapInfimum Q.val).1 = (wedgeGapInfimum K.val).2 := by
    change sInf ((fun t ↦ (wedgeGaps Q.val t).1) '' Ioo 0 Θ.angle) =
      sInf ((fun t ↦ (wedgeGaps K.val t).2) '' Ioo 0 Θ.angle)
    exact congrArg sInf himage
  have hsurface' :
      surfaceAreaMeasure Q.val.val {((Real.pi / 2 : ℝ) : Real.Angle)} =
        surfaceAreaMeasure K.val.val {(Θ.angle : Real.Angle)} := by
    have hs := hsurface {((Real.pi / 2 : ℝ) : Real.Angle)}
      (measurableSet_singleton _)
    rw [hPQ] at hs
    rw [Set.image_singleton] at hs
    have hang :
        ((Θ.angle + Real.pi / 2 : ℝ) : Real.Angle) -
            ((Real.pi / 2 : ℝ) : Real.Angle) =
          (Θ.angle : Real.Angle) := by
      rw [← Real.Angle.coe_sub]
      congr 1
      ring
    simpa only [hang] using hs
  rw [hinf, hsurface'] at hQright
  exact hQright

end MovingSofa
