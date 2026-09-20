import MovingSofa.Analysis.SurfaceMeasure.Construction
import MovingSofa.Convex.Limits
import MovingSofa.ForMathlib.MeasureTheory.Integral.MovingIntervals

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

namespace MovingSofa

/-- The angle of a planar vector varies continuously away from zero. -/
theorem continuousAt_vectorNormalAngle {p : Point} (hp : p ≠ 0) :
    ContinuousAt vectorNormalAngle p := by
  have hz : (⟨p 0, p 1⟩ : ℂ) ≠ 0 := by
    intro h
    apply hp
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hc : Continuous (fun q : Point ↦ (⟨q 0, q 1⟩ : ℂ)) := by
    have h : Continuous (fun q : Point ↦ (q 0 : ℂ) + (q 1 : ℂ) * Complex.I) := by
      fun_prop
    convert h using 1
    funext q
    apply Complex.ext <;> simp
  exact (Complex.continuousAt_arg_coe_angle hz).comp
    (f := fun q : Point ↦ (⟨q 0, q 1⟩ : ℂ)) hc.continuousAt

/-- The weighted upper-graph surface density is continuous as a function of slope. -/
theorem continuous_surfaceDensity_of_slope (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) :
    Continuous (fun r : ℝ ↦ ψ (vectorNormalAngle (e.symm !₂[-r, 1])) *
      Real.sqrt (1 + r ^ 2)) := by
  have hv : Continuous (fun r : ℝ ↦ vectorNormalAngle (e.symm !₂[-r, 1])) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    have hne : e.symm !₂[-r, 1] ≠ 0 := by
      intro h
      have h1 := congrArg (fun p : Point ↦ e p 1) h
      simp at h1
    apply (continuousAt_vectorNormalAngle hne).comp
      (f := fun r : ℝ ↦ e.symm !₂[-r, 1])
    fun_prop
  exact (hψ.comp hv).mul (by fun_prop)


private theorem ae_differentiableAt_upperGraphHeight (K : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (horizontalBounds K o e).1 (horizontalBounds K o e).2 →
      DifferentiableAt ℝ (upperGraphHeight K o e) x := by
  let a := (horizontalBounds K o e).1
  let b := (horizontalBounds K o e).2
  let δ : ℕ → ℝ := fun m ↦ 1 / ((m : ℝ) + 1)
  have hδpos (m : ℕ) : 0 < δ m := by positivity
  have hcompact (m : ℕ) : IsCompact (Set.Icc (a + δ m) (b - δ m)) := isCompact_Icc
  have hsub (m : ℕ) : Set.Icc (a + δ m) (b - δ m) ⊆ Set.Ioo a b := by
    intro x hx
    exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a (hδpos m)) hx.1,
      lt_of_le_of_lt hx.2 (sub_lt_self b (hδpos m))⟩
  have hae (m : ℕ) : ∀ᵐ x : ℝ,
      x ∈ Set.Ioo (a + δ m) (b - δ m) →
        DifferentiableAt ℝ (upperGraphHeight K o e) x := by
    obtain ⟨C, hC⟩ :=
      ((locallyLipschitzOn_upperGraphHeight K o e).mono (hsub m)).exists_lipschitzOnWith_of_compact
        (hcompact m)
    filter_upwards [hC.ae_differentiableWithinAt_of_mem_of_real] with x hdiff hx
    exact (hdiff ⟨hx.1.le, hx.2.le⟩).differentiableAt (Icc_mem_nhds hx.1 hx.2)
  have hall : ∀ᵐ x : ℝ, ∀ m, x ∈ Set.Ioo (a + δ m) (b - δ m) →
      DifferentiableAt ℝ (upperGraphHeight K o e) x :=
    MeasureTheory.ae_all_iff.mpr hae
  filter_upwards [hall] with x hxall hx
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hevent : ∀ᶠ m in atTop, δ m < x - a ∧ δ m < b - x :=
    ((hδ.eventually_lt_const (sub_pos.mpr hx.1)).and
      (hδ.eventually_lt_const (sub_pos.mpr hx.2)))
  obtain ⟨m, hm⟩ := hevent.exists
  apply hxall m
  constructor <;> linarith [hm.1, hm.2]

private theorem exists_tendsto_points_of_mem_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) {p : Point} (hp : p ∈ L) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) := by
  have hnear (n : ℕ) : ∃ q ∈ (K n : Set Point),
      dist p q < Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1) := by
    obtain ⟨q, hq, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt'
      (r := Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1)) hp
      (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact ⟨q, hq, by simpa [dist_comm] using hd⟩
  choose q hqK hqdist using hnear
  refine ⟨q, hqK, ?_⟩
  have hsum : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hsum
  intro n
  simpa [dist_comm] using (hqdist n).le

private theorem exists_horizontal_side_points (L : ConvexBody Point) (o : Point)
    (e : Point ≃ₗᵢ[ℝ] Point) {x : ℝ}
    (hx : x ∈ Set.Ioo (horizontalBounds L o e).1 (horizontalBounds L o e).2) :
    ∃ l ∈ (L : Set Point), ∃ r ∈ (L : Set Point),
      e (l - o) 0 < x ∧ x < e (r - o) 0 := by
  let a := (horizontalBounds L o e).1
  let b := (horizontalBounds L o e).2
  have hlcoord : (a + x) / 2 ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    dsimp [a, b]
    constructor <;> linarith [hx.1, hx.2]
  have hrcoord : (x + b) / 2 ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    dsimp [a, b]
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨l, hl, hleq⟩ := hlcoord
  obtain ⟨r, hr, hreq⟩ := hrcoord
  refine ⟨l, hl, r, hr, ?_, ?_⟩
  · change e (l - o) 0 = (a + x) / 2 at hleq
    rw [hleq]
    dsimp [a]
    linarith [hx.1]
  · change e (r - o) 0 = (x + b) / 2 at hreq
    rw [hreq]
    dsimp [b]
    linarith [hx.2]

/-- Points on an interior horizontal fiber can be approximated within the same fibers. -/
theorem exists_tendsto_points_with_horizontal_coordinate
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {p : Point} (hp : p ∈ L)
    (hpint : e (p - o) 0 ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ K n) ∧ Tendsto q atTop (𝓝 p) ∧
      ∀ᶠ n in atTop, e (q n - o) 0 = e (p - o) 0 := by
  let c : Point → ℝ := fun z ↦ e (z - o) 0
  have hc : Continuous c := by
    exact (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp
      (e.continuous.comp (continuous_id.sub continuous_const))
  have hc_lineMap (a b : Point) (t : ℝ) :
      c (AffineMap.lineMap a b t) = (1 - t) * c a + t * c b := by
    dsimp [c]
    rw [AffineMap.lineMap_apply_module]
    simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply,
      PiLp.smul_apply, smul_eq_mul]
    ring
  obtain ⟨l, hlL, r, hrL, hl, hr⟩ := exists_horizontal_side_points L o e hpint
  obtain ⟨pn, hpnK, hpn⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hp
  obtain ⟨ln, hlnK, hln⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hlL
  obtain ⟨rn, hrnK, hrn⟩ := exists_tendsto_points_of_mem_of_hausdorffDist K L hlim hrL
  let x := c p
  let tR : ℕ → ℝ := fun n ↦ (x - c (pn n)) / (c (rn n) - c (pn n))
  let tL : ℕ → ℝ := fun n ↦ (c (pn n) - x) / (c (pn n) - c (ln n))
  let qR : ℕ → Point := fun n ↦ AffineMap.lineMap (pn n) (rn n) (tR n)
  let qL : ℕ → Point := fun n ↦ AffineMap.lineMap (pn n) (ln n) (tL n)
  let corrected : ℕ → Point := fun n ↦ if c (pn n) ≤ x then qR n else qL n
  let good : ℕ → Prop := fun n ↦ c (ln n) < x ∧ x < c (rn n)
  let q : ℕ → Point := fun n ↦ if good n then corrected n else pn n
  have hcp : Tendsto (fun n ↦ c (pn n)) atTop (𝓝 (c p)) := (hc.tendsto p).comp hpn
  have hcl : Tendsto (fun n ↦ c (ln n)) atTop (𝓝 (c l)) := (hc.tendsto l).comp hln
  have hcr : Tendsto (fun n ↦ c (rn n)) atTop (𝓝 (c r)) := (hc.tendsto r).comp hrn
  have htR : Tendsto tR atTop (𝓝 0) := by
    have hden : c r - c p ≠ 0 := by
      dsimp [c] at hr
      linarith
    have hxlim : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    change Tendsto ((fun n ↦ x - c (pn n)) /
      fun n ↦ c (rn n) - c (pn n)) atTop (𝓝 0)
    simpa [x] using (hxlim.sub hcp).div (hcr.sub hcp) hden
  have htL : Tendsto tL atTop (𝓝 0) := by
    have hden : c p - c l ≠ 0 := by
      dsimp [c] at hl
      linarith
    have hxlim : Tendsto (fun _ : ℕ ↦ x) atTop (𝓝 x) := tendsto_const_nhds
    change Tendsto ((fun n ↦ c (pn n) - x) /
      fun n ↦ c (pn n) - c (ln n)) atTop (𝓝 0)
    simpa [x] using (hcp.sub hxlim).div (hcp.sub hcl) hden
  have hqR : Tendsto qR atTop (𝓝 p) := by
    simpa [qR] using hpn.lineMap hrn htR
  have hqL : Tendsto qL atTop (𝓝 p) := by
    simpa [qL] using hpn.lineMap hln htL
  have hcorrected : Tendsto corrected atTop (𝓝 p) := by
    exact hqR.if' hqL
  have hq : Tendsto q atTop (𝓝 p) := by
    exact hcorrected.if' hpn
  have hgood : ∀ᶠ n in atTop, good n := by
    filter_upwards [hcl.eventually_lt tendsto_const_nhds hl,
      tendsto_const_nhds.eventually_lt hcr hr] with n hnl hnr
    exact ⟨hnl, hnr⟩
  refine ⟨q, ?_, hq, ?_⟩
  · intro n
    by_cases hgn : good n
    · simp only [q, hgn, ite_true, corrected]
      dsimp [good] at hgn
      by_cases hpnx : c (pn n) ≤ x
      · simp only [hpnx, ite_true, qR]
        apply (K n).convex.lineMap_mem (hpnK n) (hrnK n)
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpnx) (sub_nonneg.mpr (le_trans hpnx hgn.2.le))
        · apply (div_le_one (sub_pos.mpr (lt_of_le_of_lt hpnx hgn.2))).mpr
          linarith
      · simp only [hpnx, ite_false, qL]
        apply (K n).convex.lineMap_mem (hpnK n) (hlnK n)
        constructor
        · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge hpnx))
            (sub_nonneg.mpr (le_trans hgn.1.le (le_of_not_ge hpnx)))
        · apply (div_le_one (sub_pos.mpr (lt_of_lt_of_le hgn.1 (le_of_not_ge hpnx)))).mpr
          linarith
    · simp [q, hgn, hpnK n]
  · filter_upwards [hgood] with n hgn
    simp only [q, hgn, ite_true, corrected]
    dsimp [good] at hgn
    by_cases hpnx : c (pn n) ≤ x
    · simp only [hpnx, ite_true, qR, tR]
      rw [show e (AffineMap.lineMap (pn n) (rn n)
          ((x - c (pn n)) / (c (rn n) - c (pn n))) - o) 0 =
          c (AffineMap.lineMap (pn n) (rn n)
            ((x - c (pn n)) / (c (rn n) - c (pn n)))) by rfl]
      rw [hc_lineMap]
      change _ = x
      field_simp [ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hpnx hgn.2))]
      ring
    · simp only [hpnx, ite_false, qL, tL]
      rw [show e (AffineMap.lineMap (pn n) (ln n)
          ((c (pn n) - x) / (c (pn n) - c (ln n))) - o) 0 =
          c (AffineMap.lineMap (pn n) (ln n)
            ((c (pn n) - x) / (c (pn n) - c (ln n)))) by rfl]
      rw [hc_lineMap]
      change _ = x
      field_simp [ne_of_gt (sub_pos.mpr (lt_of_lt_of_le hgn.1 (le_of_not_ge hpnx)))]
      ring

/-- A varying point of the approximating bodies is asymptotically close to the limit body. -/
private theorem exists_points_in_limit_tendsto_dist_zero
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (p : ℕ → Point) (hp : ∀ n, p n ∈ K n) :
    ∃ q : ℕ → Point, (∀ n, q n ∈ L) ∧
      Tendsto (fun n ↦ dist (p n) (q n)) atTop (𝓝 0) := by
  have hnear (n : ℕ) : ∃ q ∈ (L : Set Point),
      dist (p n) q < Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1) := by
    obtain ⟨q, hq, hd⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (r := Metric.hausdorffDist (K n : Set Point) (L : Set Point) +
        1 / ((n : ℝ) + 1)) (hp n)
      (by linarith [show 0 < 1 / ((n : ℝ) + 1) by positivity])
      (Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
        (K n).nonempty L.nonempty (K n).isCompact.isBounded L.isCompact.isBounded)
    exact ⟨q, hq, hd⟩
  choose q hqL hqdist using hnear
  refine ⟨q, hqL, ?_⟩
  have hsum : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point) + 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [add_zero] using hlim.add tendsto_one_div_add_atTop_nhds_zero_nat
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hsum
  exact fun n ↦ (hqdist n).le

/-- Upper graph heights converge at every interior point of the limit projection. -/
theorem tendsto_upperGraphHeight_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    Tendsto (fun n ↦ upperGraphHeight (K n) o e x) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
  classical
  let cx : Point → ℝ := fun p ↦ e (p - o) 0
  let cy : Point → ℝ := fun p ↦ e (p - o) 1
  have reconstruct (p : Point) : o + e.symm !₂[cx p, cy p] = p := by
    dsimp [cx, cy]
    rw [← e.injective.eq_iff]
    ext i
    fin_cases i <;> simp
  have hxproj : x ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  let pTop := o + e.symm !₂[x, upperGraphHeight L o e x]
  have hpTop : pTop ∈ L := upperGraphHeight_mem L o e hxproj
  have hcxTop : cx pTop = x := by simp [cx, pTop]
  have hcyTop : cy pTop = upperGraphHeight L o e x := by simp [cy, pTop]
  have hpTopInt : cx pTop ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by simpa [hcxTop] using hx
  obtain ⟨q, hqK, hq, hqx⟩ :=
    exists_tendsto_points_with_horizontal_coordinate K L hlim o e hpTop hpTopInt
  have hcyq : Tendsto (fun n ↦ cy (q n)) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
    have hcy : Continuous cy := by
      exact (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp
        (e.continuous.comp (continuous_id.sub continuous_const))
    change Tendsto (cy ∘ q) atTop (𝓝 (upperGraphHeight L o e x))
    simpa [hcyTop] using (hcy.tendsto pTop).comp hq
  have hqcx : ∀ᶠ n in atTop, cx (q n) = x := by
    filter_upwards [hqx] with n hnx
    dsimp [cx]
    rw [hnx]
    exact hcxTop
  have hqproj : ∀ᶠ n in atTop, x ∈ horizontalProjection (K n) o e := by
    filter_upwards [hqcx] with n hnx
    refine ⟨q n, hqK n, ?_⟩
    exact hnx
  let z : ℕ → Point := fun n ↦ if hn : x ∈ horizontalProjection (K n) o e then
    o + e.symm !₂[x, upperGraphHeight (K n) o e x] else q n
  have hzK (n : ℕ) : z n ∈ K n := by
    dsimp [z]
    split_ifs with hn
    · exact upperGraphHeight_mem (K n) o e hn
    · exact hqK n
  have hzeq : z =ᶠ[atTop]
      fun n ↦ o + e.symm !₂[x, upperGraphHeight (K n) o e x] := by
    filter_upwards [hqproj] with n hn
    simp [z, hn]
  obtain ⟨w, hwL, hd⟩ := exists_points_in_limit_tendsto_dist_zero K L hlim z hzK
  have hsub : Tendsto (fun n ↦ z n - w n) atTop (𝓝 0) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    simpa [dist_eq_norm] using hd
  have hdx : Tendsto (fun n ↦ cx (z n) - cx (w n)) atTop (𝓝 0) := by
    have heval : Continuous (fun v : Point ↦ e v 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp e.continuous
    rw [show (fun n ↦ cx (z n) - cx (w n)) =
        fun n ↦ e (z n - w n) 0 by
      funext n
      simp [cx]]
    change Tendsto ((fun v : Point ↦ e v 0) ∘ fun n ↦ z n - w n) atTop (𝓝 0)
    simpa only [map_zero, PiLp.zero_apply] using (heval.tendsto 0).comp hsub
  have hdy : Tendsto (fun n ↦ cy (z n) - cy (w n)) atTop (𝓝 0) := by
    have heval : Continuous (fun v : Point ↦ e v 1) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 1).comp e.continuous
    rw [show (fun n ↦ cy (z n) - cy (w n)) =
        fun n ↦ e (z n - w n) 1 by
      funext n
      simp [cy]]
    change Tendsto ((fun v : Point ↦ e v 1) ∘ fun n ↦ z n - w n) atTop (𝓝 0)
    simpa only [map_zero, PiLp.zero_apply] using (heval.tendsto 0).comp hsub
  have hcxz : Tendsto (fun n ↦ cx (z n)) atTop (𝓝 x) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hzeq] with n hn
    rw [hn]
    simp [cx]
  have hcxw : Tendsto (fun n ↦ cx (w n)) atTop (𝓝 x) := by
    have h := hcxz.sub hdx
    convert h using 1 <;> simp
  have hgL : Tendsto (fun n ↦ upperGraphHeight L o e (cx (w n))) atTop
      (𝓝 (upperGraphHeight L o e x)) := by
    have hcont : ContinuousAt (upperGraphHeight L o e) x :=
      (locallyLipschitzOn_upperGraphHeight L o e).continuousOn.continuousAt
        (isOpen_Ioo.mem_nhds hx)
    exact hcont.tendsto.comp hcxw
  have hlower : ∀ᶠ n in atTop,
      cy (q n) ≤ upperGraphHeight (K n) o e x := by
    filter_upwards [hqcx] with n hnx
    apply (upperGraphHeight_isGreatest (K n) o e (by
      exact ⟨q n, hqK n, hnx⟩)).2
    change o + e.symm !₂[x, cy (q n)] ∈ K n
    rw [show o + e.symm !₂[x, cy (q n)] = q n by
      calc
        o + e.symm !₂[x, cy (q n)] = o + e.symm !₂[cx (q n), cy (q n)] := by
          rw [hnx]
        _ = q n := reconstruct (q n)]
    exact hqK n
  have hupper : ∀ᶠ n in atTop,
      upperGraphHeight (K n) o e x ≤
        upperGraphHeight L o e (cx (w n)) + (cy (z n) - cy (w n)) := by
    filter_upwards [hzeq] with n hzn
    have hwproj : cx (w n) ∈ horizontalProjection L o e :=
      ⟨w n, hwL n, rfl⟩
    have hwy : cy (w n) ≤ upperGraphHeight L o e (cx (w n)) := by
      apply (upperGraphHeight_isGreatest L o e hwproj).2
      change o + e.symm !₂[cx (w n), cy (w n)] ∈ L
      rw [reconstruct (w n)]
      exact hwL n
    have hzy : cy (z n) = upperGraphHeight (K n) o e x := by
      rw [hzn]
      simp [cy]
    rw [← hzy]
    linarith
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hcyq
    (by simpa using hgL.add hdy) hlower hupper

private theorem eventually_mem_horizontalProjection_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {x : ℝ} (hx : x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2) :
    ∀ᶠ n in atTop, x ∈ horizontalProjection (K n) o e := by
  have hxproj : x ∈ horizontalProjection L o e := by
    rw [horizontalProjection_eq_Icc]
    exact ⟨hx.1.le, hx.2.le⟩
  let p := o + e.symm !₂[x, upperGraphHeight L o e x]
  have hp : p ∈ L := upperGraphHeight_mem L o e hxproj
  have hpcoord : e (p - o) 0 = x := by simp [p]
  have hpint : e (p - o) 0 ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    rw [hpcoord]
    exact hx
  obtain ⟨q, hqK, -, hqx⟩ :=
    exists_tendsto_points_with_horizontal_coordinate K L hlim o e hp hpint
  filter_upwards [hqx] with n hn
  exact ⟨q n, hqK n, hn.trans hpcoord⟩

/-- Upper graph surface densities converge almost everywhere on the interior limit projection. -/
theorem ae_tendsto_upperGraphSurfaceIntegrand_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) :
    ∀ᵐ x : ℝ, x ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 →
        Tendsto (fun n ↦ upperGraphSurfaceIntegrand (K n) o e ψ x) atTop
          (𝓝 (upperGraphSurfaceIntegrand L o e ψ x)) := by
  have haeK : ∀ᵐ x : ℝ, ∀ n,
      x ∈ Set.Ioo (horizontalBounds (K n) o e).1 (horizontalBounds (K n) o e).2 →
        DifferentiableAt ℝ (upperGraphHeight (K n) o e) x :=
    MeasureTheory.ae_all_iff.mpr fun n ↦ ae_differentiableAt_upperGraphHeight (K n) o e
  have haeL := ae_differentiableAt_upperGraphHeight L o e
  filter_upwards [haeK, haeL] with x hdiffK hdiffL hx
  let left := (horizontalBounds L o e).1
  let right := (horizontalBounds L o e).2
  let a := (left + x) / 2
  let b := (x + right) / 2
  have hax : a < x := by dsimp [a, left]; linarith [hx.1]
  have hxb : x < b := by dsimp [b, right]; linarith [hx.2]
  have haL : a ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    dsimp [a, left]
    constructor <;> linarith [hx.1, hx.2]
  have hbL : b ∈ Set.Ioo (horizontalBounds L o e).1
      (horizontalBounds L o e).2 := by
    dsimp [b, right]
    constructor <;> linarith [hx.1, hx.2]
  have haK := eventually_mem_horizontalProjection_of_hausdorffDist K L hlim o e haL
  have hbK := eventually_mem_horizontalProjection_of_hausdorffDist K L hlim o e hbL
  have hconc : ∀ᶠ n in atTop,
      ConcaveOn ℝ (Set.Ioo a b) (upperGraphHeight (K n) o e) := by
    filter_upwards [haK, hbK] with n han hbn
    apply (concaveOn_upperGraphHeight (K n) o e).subset _ (convex_Ioo a b)
    intro y hy
    rw [horizontalProjection_eq_Icc] at han hbn ⊢
    exact ⟨han.1.trans hy.1.le, hy.2.le.trans hbn.2⟩
  have hdiffEventually : ∀ᶠ n in atTop,
      DifferentiableAt ℝ (upperGraphHeight (K n) o e) x := by
    filter_upwards [haK, hbK] with n han hbn
    apply hdiffK n
    rw [horizontalProjection_eq_Icc] at han hbn
    exact ⟨han.1.trans_lt hax, hxb.trans_le hbn.2⟩
  have hpointwise (y : ℝ) (hy : y ∈ Set.Ioo a b) :
      Tendsto (fun n ↦ upperGraphHeight (K n) o e y) atTop
        (𝓝 (upperGraphHeight L o e y)) := by
    apply tendsto_upperGraphHeight_of_hausdorffDist K L hlim o e
    exact ⟨haL.1.trans hy.1, hy.2.trans hbL.2⟩
  have hderiv : Tendsto (fun n ↦ deriv (upperGraphHeight (K n) o e) x) atTop
      (𝓝 (deriv (upperGraphHeight L o e) x)) :=
    ConcaveOn.tendsto_deriv_of_tendsto_Ioo ⟨hax, hxb⟩ hconc hpointwise hdiffEventually
      (hdiffL hx)
  have hdensity := (continuous_surfaceDensity_of_slope e hψ).continuousAt.tendsto.comp hderiv
  change Tendsto ((fun r : ℝ ↦ ψ (vectorNormalAngle (e.symm !₂[-r, 1])) *
    Real.sqrt (1 + r ^ 2)) ∘ fun n ↦ deriv (upperGraphHeight (K n) o e) x)
      atTop (𝓝 (upperGraphSurfaceIntegrand L o e ψ x))
  simpa only [upperGraphSurfaceIntegrand] using hdensity

private theorem tendsto_vectorSupport_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) {u : Point} (hu : ‖u‖ = 1) :
    Tendsto (fun n ↦ vectorSupport (K n) u) atTop (𝓝 (vectorSupport L u)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hlim
  intro n
  simpa only [Real.dist_eq] using
    (compactSet_support_continuity (K n) L (K n).nonempty
      (K n).isCompact L.nonempty L.isCompact).2.1 u hu

private theorem horizontalBounds_snd_eq_vectorSupport (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).2 =
      vectorSupport K (e.symm !₂[1, 0]) - inner ℝ o (e.symm !₂[1, 0]) := by
  let u : Point := e.symm !₂[1, 0]
  have hu (p : Point) : e (p - o) 0 = inner ℝ p u - inner ℝ o u := by
    rw [← inner_sub_left, ← e.inner_map_map]
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
  obtain ⟨p, hp, hsup, hge⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty
    (show Continuous (fun p : Point ↦ inner ℝ p u) from
      continuous_id.inner continuous_const).continuousOn
  change sSup ((fun p : Point ↦ e (p - o) 0) '' (K : Set Point)) = _
  rw [show vectorSupport K u = inner ℝ p u by exact hsup]
  apply le_antisymm
  · apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    change e (q - o) 0 ≤ inner ℝ p u - inner ℝ o u
    rw [hu q]
    exact sub_le_sub_right (hge q hq) _
  · apply le_csSup
    · have hc : Continuous (fun p : Point ↦ e (p - o)) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      exact K.isCompact.bddAbove_image
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp hc).continuousOn
    · exact ⟨p, hp, hu p⟩

private theorem horizontalBounds_fst_eq_vectorSupport (K : ConvexBody Point)
    (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    (horizontalBounds K o e).1 =
      -vectorSupport K (-(e.symm !₂[1, 0])) - inner ℝ o (e.symm !₂[1, 0]) := by
  let u : Point := e.symm !₂[1, 0]
  have hu (p : Point) : e (p - o) 0 = inner ℝ p u - inner ℝ o u := by
    rw [← inner_sub_left, ← e.inner_map_map]
    simp [u, PiLp.inner_apply, Fin.sum_univ_two]
  obtain ⟨p, hp, hsup, hge⟩ := K.isCompact.exists_sSup_image_eq_and_ge K.nonempty
    (show Continuous (fun p : Point ↦ inner ℝ p (-u)) from
      continuous_id.inner continuous_const).continuousOn
  change sInf ((fun p : Point ↦ e (p - o) 0) '' (K : Set Point)) = _
  rw [show vectorSupport K (-u) = inner ℝ p (-u) by exact hsup]
  apply le_antisymm
  · apply csInf_le
    · have hc : Continuous (fun p : Point ↦ e (p - o)) :=
        e.continuous.comp (continuous_id.sub continuous_const)
      exact K.isCompact.bddBelow_image
        ((PiLp.continuous_apply 2 (fun _ : Fin 2 ↦ ℝ) 0).comp hc).continuousOn
    · refine ⟨p, hp, ?_⟩
      change e (p - o) 0 = -inner ℝ p (-u) - inner ℝ o u
      rw [hu p]
      simp
  · apply le_csInf (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    change -inner ℝ p (-u) - inner ℝ o u ≤ e (q - o) 0
    rw [hu q]
    have h := hge q hq
    simp only [inner_neg_right] at h ⊢
    linarith

/-- Horizontal projection endpoints converge with their convex bodies. -/
private theorem tendsto_horizontalBounds_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point) :
    Tendsto (fun n ↦ horizontalBounds (K n) o e) atTop
      (𝓝 (horizontalBounds L o e)) := by
  let u : Point := e.symm !₂[1, 0]
  have hu : ‖u‖ = 1 := by
    rw [show ‖u‖ = ‖(!₂[1, 0] : Point)‖ by exact e.symm.norm_map _]
    rw [EuclideanSpace.norm_eq]
    norm_num [Fin.sum_univ_two]
  rw [show (fun n ↦ horizontalBounds (K n) o e) =
      fun n ↦ (-vectorSupport (K n) (-u) - inner ℝ o u,
        vectorSupport (K n) u - inner ℝ o u) by
      funext n
      ext <;> simp [horizontalBounds_fst_eq_vectorSupport,
        horizontalBounds_snd_eq_vectorSupport, u]]
  rw [show horizontalBounds L o e =
      (-vectorSupport L (-u) - inner ℝ o u,
        vectorSupport L u - inner ℝ o u) by
      ext <;> simp [horizontalBounds_fst_eq_vectorSupport,
        horizontalBounds_snd_eq_vectorSupport, u]]
  apply Tendsto.prodMk_nhds
  · exact (tendsto_vectorSupport_of_hausdorffDist K L hlim (by simpa using hu)).neg.sub_const _
  · exact (tendsto_vectorSupport_of_hausdorffDist K L hlim hu).sub_const _

private theorem weightedSurfaceIntegral_eq_upperGraphIntegral
    (K : ConvexBody Point) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    (ψ : Real.Angle → ℝ) (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    (∫ t, ψ t ∂surfaceAreaMeasure K) =
      ∫ x in Set.Icc (horizontalBounds K o e).1 (horizontalBounds K o e).2,
        upperGraphSurfaceIntegrand K o e ψ x := by
  have hformula := (surfaceAreaMeasure_construction K).2.2.2.2 o e ψ hψ ε hε hsupport
  have hle : (horizontalBounds K o e).1 ≤ (horizontalBounds K o e).2 := by
    obtain ⟨x, hx⟩ := K.nonempty.image (fun p : Point ↦ e (p - o) 0)
    change x ∈ horizontalProjection K o e at hx
    rw [horizontalProjection_eq_Icc] at hx
    exact hx.1.trans hx.2
  rcases hle.lt_or_eq with hlt | heq
  · exact (hformula.1 hlt).2
  · rw [hformula.2 heq, heq]
    simp

/-- Weighted upper-normal surface integrals are continuous under Hausdorff convergence. -/
theorem tendsto_integral_surfaceAreaMeasure_of_hausdorffDist
    (K : ℕ → ConvexBody Point) (L : ConvexBody Point)
    (hlim : Tendsto (fun n ↦ Metric.hausdorffDist (K n : Set Point)
      (L : Set Point)) atTop (𝓝 0)) (o : Point) (e : Point ≃ₗᵢ[ℝ] Point)
    {ψ : Real.Angle → ℝ} (hψ : Continuous ψ) {ε : ℝ} (hε : 0 < ε)
    (hsupport : ∀ t, e (normalVector t) 1 < ε → ψ t = 0) :
    Tendsto (fun n ↦ ∫ t, ψ t ∂surfaceAreaMeasure (K n)) atTop
      (𝓝 (∫ t, ψ t ∂surfaceAreaMeasure L)) := by
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hψ.norm.continuousOn
  let M := ‖ψ t‖
  have hM (u : Real.Angle) : ‖ψ u‖ ≤ M := ht trivial
  have hM0 : 0 ≤ M := norm_nonneg _
  have hb := tendsto_horizontalBounds_of_hausdorffDist K L hlim o e
  have ha : Tendsto (fun n ↦ (horizontalBounds (K n) o e).1) atTop
      (𝓝 (horizontalBounds L o e).1) := continuousAt_fst.tendsto.comp hb
  have hb' : Tendsto (fun n ↦ (horizontalBounds (K n) o e).2) atTop
      (𝓝 (horizontalBounds L o e).2) := continuousAt_snd.tendsto.comp hb
  have hgraph := tendsto_integral_Icc_of_tendsto_endpoints_of_bound ha hb'
    (Eventually.of_forall fun n ↦
      (integrable_upperGraphSurfaceIntegrand (K n) o e ψ hψ hε hsupport _ _).1)
    (mul_nonneg hM0 (inv_nonneg.mpr hε.le))
    (Eventually.of_forall fun n ↦ Eventually.of_forall fun x _ ↦
      norm_upperGraphSurfaceIntegrand_le (K n) o e ψ hε hsupport hM x)
    (ae_tendsto_upperGraphSurfaceIntegrand_of_hausdorffDist K L hlim o e hψ)
  rw [weightedSurfaceIntegral_eq_upperGraphIntegral L o e ψ hψ hε hsupport]
  apply hgraph.congr'
  filter_upwards [] with n
  exact (weightedSurfaceIntegral_eq_upperGraphIntegral (K n) o e ψ hψ hε hsupport).symm

end MovingSofa
