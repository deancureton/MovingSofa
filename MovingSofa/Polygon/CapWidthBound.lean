import MovingSofa.Cap.Contacts
import MovingSofa.Polygon.Approximation

noncomputable section

namespace MovingSofa

open MeasureTheory
open scoped Pointwise

private theorem directionalWidth_zero (K : ConvexBody Point) :
    directionalWidth K 0 = horizontalMax K - horizontalMin K := by
  simp only [directionalWidth, zero_add]
  rw [← Real.Angle.coe_zero, supportValue_zero_eq_horizontalMax,
    supportValue_pi_eq_neg_horizontalMin, ← sub_eq_add_neg]

private theorem volume_coordinate_open_rectangle (l r b t : ℝ) :
    volume {p : Point | p 0 ∈ Set.Ioo l r ∧ p 1 ∈ Set.Ioo b t} =
      ENNReal.ofReal (r - l) * ENNReal.ofReal (t - b) := by
  have h := EuclideanSpace.volume_preserving_finTwoCoordinates.measure_preimage
    ((measurableSet_Ioo.prod measurableSet_Ioo).nullMeasurableSet :
      NullMeasurableSet (Set.Ioo l r ×ˢ Set.Ioo b t) (volume : Measure (ℝ × ℝ)))
  simpa [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Set.preimage, Set.prod] using h

private theorem cap_horizontalWidth_le_of_cos_pos {ω : ℝ} (K : CapSpace ω)
    (hc : 0 < Real.cos ω) :
    directionalWidth (K.val : Set Point) 0 ≤ (1 + Real.sin ω) / Real.cos ω := by
  have hs : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi K.property.1.le
    (K.property.2.1.trans (by linarith [Real.pi_pos]))
  have hx (p : Point) (hp : p ∈ (K.val : Set Point)) :
      -Real.sin ω / Real.cos ω ≤ p 0 ∧ p 0 ≤ 1 / Real.cos ω := by
    obtain ⟨hy, hv⟩ := (mem_stripParallelogram_iff ω p).mp (K.subset_stripParallelogram hp)
    simp [normalVector, frame, PiLp.inner_apply] at hv
    constructor
    · apply (div_le_iff₀ hc).mpr
      nlinarith [mul_nonneg hs (sub_nonneg.mpr hy.2)]
    · apply (le_div_iff₀ hc).mpr
      nlinarith [mul_nonneg hs hy.1]
  have hmax : horizontalMax K.val ≤ 1 / Real.cos ω :=
    csSup_le (K.val.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact (hx p hp).2)
  have hmin : -Real.sin ω / Real.cos ω ≤ horizontalMin K.val :=
    le_csInf (K.val.nonempty.image _) (by rintro _ ⟨p, hp, rfl⟩; exact (hx p hp).1)
  rw [directionalWidth_zero]
  calc
    horizontalMax K.val - horizontalMin K.val ≤
        1 / Real.cos ω - -Real.sin ω / Real.cos ω := sub_le_sub hmax hmin
    _ = (1 + Real.sin ω) / Real.cos ω := by ring

private theorem wedge_rectangle_inequalities {s c a b x y : ℝ}
    (hs : 0 < s) (hc : 0 < c) (hs1 : s ≤ 1) (hc1 : c ≤ 1)
    (hL : 0 < a / c + b / s)
    (hx : x ∈ Set.Ioo (-b / s + (a / c + b / s) / 4)
      (a / c - (a / c + b / s) / 4))
    (hy : y ∈ Set.Ioo 0 ((a / c + b / s) * s * c / 4)) :
    0 ≤ y ∧ c * x + s * y < a ∧ -s * x + c * y < b := by
  let L := a / c + b / s
  have hLc : 0 ≤ L * c / 4 := by dsimp [L]; positivity
  have hLs : 0 ≤ L * s / 4 := by dsimp [L]; positivity
  have hyc : y < L * c / 4 := by
    apply hy.2.trans_le
    calc
      L * s * c / 4 = s * (L * c / 4) := by ring
      _ ≤ 1 * (L * c / 4) := mul_le_mul_of_nonneg_right hs1 hLc
      _ = L * c / 4 := one_mul _
  have hys : y < L * s / 4 := by
    apply hy.2.trans_le
    calc
      L * s * c / 4 = c * (L * s / 4) := by ring
      _ ≤ 1 * (L * s / 4) := mul_le_mul_of_nonneg_right hc1 hLs
      _ = L * s / 4 := one_mul _
  have hsy : s * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hy.1.le]
  have hcy : c * y ≤ y := by nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hy.1.le]
  have hright : (x + L / 4) * c < a :=
    (lt_div_iff₀ hc).mp (by dsimp [L]; linarith [hx.2])
  have hleft : -b < (x - L / 4) * s :=
    (div_lt_iff₀ hs).mp (by dsimp [L]; linarith [hx.1])
  exact ⟨hy.1.le, by nlinarith, by nlinarith⟩

private theorem polygonNiche_area_ge_rectangle (Θ : AngleSet)
    (hΘ : Θ.angle = Real.pi / 2) {t : ℝ} (ht : t ∈ Θ.directions)
    (K : CapSpace Θ.angle) (hs : 0 < Real.sin t) (hc : 0 < Real.cos t)
    (hL : 0 < (supportValue K.val (t : Real.Angle) - 1) / Real.cos t +
      (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) :
    ((supportValue K.val (t : Real.Angle) - 1) / Real.cos t +
      (supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1) / Real.sin t) ^ 2 *
      Real.sin t * Real.cos t / 8 ≤ ClassicalResults.area (polygonNiche Θ K) := by
  let a := supportValue K.val (t : Real.Angle) - 1
  let b := supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
  let L := a / Real.cos t + b / Real.sin t
  let R : Set Point := {p | p 0 ∈ Set.Ioo (-b / Real.sin t + L / 4)
    (a / Real.cos t - L / 4) ∧ p 1 ∈ Set.Ioo 0 (L * Real.sin t * Real.cos t / 4)}
  have hsub : R ⊆ polygonNiche Θ K := by
    intro p hp
    have hineq := wedge_rectangle_inequalities hs hc (Real.sin_le_one t) (Real.cos_le_one t)
      hL hp.1 hp.2
    refine ⟨?_, Set.mem_iUnion₂.mpr ⟨t, ht, ?_⟩⟩
    · rw [hΘ]
      simpa [capFan, normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hineq.1
    · simpa [innerQuadrant, normalHalfPlane, normalVector, frame, PiLp.inner_apply,
        Real.sin_add, Real.cos_add, -Real.Angle.coe_add, a, b] using hineq.2
  have hwidth : a / Real.cos t - L / 4 - (-b / Real.sin t + L / 4) = L / 2 := by
    dsimp [L]
    ring
  have harea : ClassicalResults.area R = L ^ 2 * Real.sin t * Real.cos t / 8 := by
    change (volume R).toReal = _
    rw [volume_coordinate_open_rectangle, hwidth, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (show 0 ≤ L / 2 by dsimp [L, a, b]; positivity),
      ENNReal.toReal_ofReal (show 0 ≤ L * Real.sin t * Real.cos t / 4 by
        dsimp [L, a, b]; positivity)]
    ring
  rw [← harea]
  exact ENNReal.toReal_mono (niche_uniform_bounds.2.1 Θ K).2.2.1.ne (measure_mono hsub)

theorem polygonCap_width_bound (ω t : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (ht : t ∈ Set.Ioo 0 ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Θ : AngleSet), Θ.angle = ω → t ∈ Θ.directions →
      ∀ K : PolygonCapSpace Θ, 0 ≤ polygonAreaFunctional Θ K.val →
        directionalWidth (K.val.val : Set Point) (0 : Real.Angle) ≤ c := by
  rcases lt_or_eq_of_le hω' with hlt | rfl
  · have hc : 0 < Real.cos ω := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hlt⟩
    have hs : 0 ≤ Real.sin ω := Real.sin_nonneg_of_nonneg_of_le_pi hω.le
      (by linarith [Real.pi_pos])
    refine ⟨(1 + Real.sin ω) / Real.cos ω, div_pos (by linarith) hc, ?_⟩
    intro Θ hΘ _ K _
    have hcΘ : 0 < Real.cos Θ.angle := by simpa only [hΘ] using hc
    simpa only [hΘ] using cap_horizontalWidth_le_of_cos_pos K.val hcΘ
  · have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (by linarith [ht.2, Real.pi_pos])
    have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    let D := 1 / Real.cos t + 1 / Real.sin t
    let C := max (2 * D) (32 / (Real.sin t * Real.cos t))
    have hC : 0 < C := lt_of_lt_of_le (div_pos (by norm_num) (mul_pos hs hc)) (le_max_right _ _)
    refine ⟨C, hC, ?_⟩
    intro Θ hΘ htΘ K hnonneg
    by_contra hwidth
    have hdC : C < directionalWidth (K.val.val : Set Point) 0 := lt_of_not_ge hwidth
    rw [directionalWidth_zero] at hdC
    let d := horizontalMax K.val.val - horizontalMin K.val.val
    have hd0 : 0 < d := hC.trans hdC
    let a := supportValue K.val.val (t : Real.Angle) - 1
    let b := supportValue K.val.val ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1
    let L := a / Real.cos t + b / Real.sin t
    have hsupport := CapSpace.horizontal_le_supportValue K.val hs.le hc.le
    simp only [Real.Angle.coe_add] at hsupport
    have ha : horizontalMax K.val.val - 1 / Real.cos t ≤ a / Real.cos t := by
      apply (le_div_iff₀ hc).mpr
      rw [sub_mul, div_mul_cancel₀ _ hc.ne']
      dsimp [a]
      linarith [hsupport.1]
    have hb : -horizontalMin K.val.val - 1 / Real.sin t ≤ b / Real.sin t := by
      apply (le_div_iff₀ hs).mpr
      rw [sub_mul, div_mul_cancel₀ _ hs.ne']
      dsimp [b]
      linarith [hsupport.2]
    have hLd : d - D ≤ L := by dsimp [L, d, D]; linarith
    have hdD : 2 * D < d := (le_max_left _ _).trans_lt hdC
    have hdlarge : 32 / (Real.sin t * Real.cos t) < d := (le_max_right _ _).trans_lt hdC
    have hhalf : d / 2 < L := by linarith
    have hL : 0 < L := (half_pos hd0).trans hhalf
    have hlower := polygonNiche_area_ge_rectangle Θ hΘ htΘ K.val hs hc hL
    have hsq : (d / 2) ^ 2 < L ^ 2 := (sq_lt_sq₀ (half_pos hd0).le hL.le).mpr hhalf
    have hsq' := mul_lt_mul_of_pos_right hsq (mul_pos hs hc)
    have hdlarge' : 32 < d * (Real.sin t * Real.cos t) :=
      (div_lt_iff₀ (mul_pos hs hc)).mp hdlarge
    have hquad : d < L ^ 2 * Real.sin t * Real.cos t / 8 := by
      nlinarith [mul_pos hd0 (sub_pos.mpr hdlarge')]
    have harea := K.val.area_le_horizontalWidth
    have hidentity := (polygonArea_upperBound Θ).1 K
    change L ^ 2 * Real.sin t * Real.cos t / 8 ≤ _ at hlower
    change ClassicalResults.area (K.val.val : Set Point) ≤ d at harea
    rw [hidentity] at hnonneg
    linarith

end MovingSofa
