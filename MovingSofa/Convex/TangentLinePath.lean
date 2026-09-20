import MovingSofa.Analysis.Stieltjes.Affine
import MovingSofa.Curve.Area
import MovingSofa.Curve.SegmentArea
import MovingSofa.Convex.Linearity

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace MovingSofa

def tangentLinePath (K : ConvexBody Point) (t : ℝ) (s : Set.Ioc (t - Real.pi) t) : Point :=
  if s.val < t then supportingIntersection K (s.val : Real.Angle) (t : Real.Angle)
  else (edgeVertices K (t : Real.Angle)).2

def tangentLineRestriction (K : ConvexBody Point) (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (s : Set.Icc a b) : Point :=
  tangentLinePath K t ⟨s.val, lt_of_lt_of_le ha.1 s.property.1,
    le_trans s.property.2 hb.2⟩

private def tangentLineCoordinate (K : ConvexBody Point) (t s : ℝ) : ℝ :=
  (supportValue K (s : Real.Angle) - supportValue K (t : Real.Angle) * Real.cos (s - t)) /
    Real.sin (s - t)

private theorem tangentLineCoordinate_le (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) {p : Point} (hp : p ∈ K) :
    tangentLineCoordinate K t s ≤ inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t)) := by
  have hsin : Real.sin (s - t) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])
  have hbound := inner_le_supportValue K hp (s : Real.Angle)
  have hn : normalVector (s : Real.Angle) =
      Real.cos (s - t) • normalVector (t : Real.Angle) +
        Real.sin (s - t) • tangentVector (t : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real t (s - t)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right] at hbound
  dsimp [tangentLineCoordinate]
  apply (div_le_iff_of_neg hsin).mpr
  have hc : (inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t))) * Real.sin (s - t) =
      inner ℝ p (tangentVector (t : Real.Angle)) * Real.sin (s - t) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        Real.cos (s - t) := by
    field_simp [hsin.ne]
  rw [hc]
  nlinarith

private theorem tangentLineCoordinate_eq_of_mem_support (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) {p : Point}
    (hp : inner ℝ p (normalVector (s : Real.Angle)) = supportValue K (s : Real.Angle)) :
    tangentLineCoordinate K t s = inner ℝ p (tangentVector (t : Real.Angle)) +
      (inner ℝ p (normalVector (t : Real.Angle)) - supportValue K (t : Real.Angle)) *
        (Real.cos (s - t) / Real.sin (s - t)) := by
  have hsin : Real.sin (s - t) ≠ 0 :=
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])).ne
  have hn : normalVector (s : Real.Angle) =
      Real.cos (s - t) • normalVector (t : Real.Angle) +
        Real.sin (s - t) • tangentVector (t : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real t (s - t)
  dsimp [tangentLineCoordinate]
  rw [← hp, hn, inner_add_right, inner_smul_right, inner_smul_right]
  field_simp
  ring

private theorem monotoneOn_tangentLineCoordinate (K : ConvexBody Point) (t : ℝ) :
    MonotoneOn (tangentLineCoordinate K t) (Ioo (t - Real.pi) t) := by
  intro x hx y hy hxy
  obtain ⟨p, hp, hmax⟩ := exists_mem_inner_eq_supportValue K (y : Real.Angle)
  rw [tangentLineCoordinate_eq_of_mem_support K hy hmax]
  apply (tangentLineCoordinate_le K hx hp).trans
  apply add_le_add_right
  exact mul_le_mul_of_nonpos_left
    (Real.antitoneOn_cos_div_sin_Ioo_neg_pi_zero ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩ (by linarith))
    (sub_nonpos.mpr (inner_le_supportValue K hp (t : Real.Angle)))

private theorem supportingIntersection_eq_tangentLineCoordinate (K : ConvexBody Point)
    {t s : ℝ} (hs : s ∈ Ioo (t - Real.pi) t) :
    supportingIntersection K (s : Real.Angle) (t : Real.Angle) =
      supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
        tangentLineCoordinate K t s • tangentVector (t : Real.Angle) := by
  rw [supportingIntersection_comm K s t
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hs.2]) (by linarith [hs.1])).ne']
  simp only [supportingIntersection, tangentLineCoordinate, ← Real.Angle.coe_sub,
    Real.Angle.cos_coe, Real.Angle.sin_coe]

private theorem continuousAt_tangentLineCoordinate (K : ConvexBody Point) {t s : ℝ}
    (hs : s ∈ Ioo (t - Real.pi) t) : ContinuousAt (tangentLineCoordinate K t) s := by
  have hsin : Real.sin (s - t) ≠ 0 :=
    (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hs.2]) (by linarith [hs.1])).ne
  exact ((continuous_supportValue_real K).continuousAt.sub
    (continuousAt_const.mul (Real.continuous_cos.continuousAt.comp
      (continuousAt_id.sub continuousAt_const)))).div
    (Real.continuous_sin.continuousAt.comp (continuousAt_id.sub continuousAt_const)) hsin

private theorem tendsto_tangentLineCoordinate_left (K : ConvexBody Point) (t : ℝ) :
    Tendsto (tangentLineCoordinate K t) (𝓝[<] t)
      (𝓝 (inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)))) := by
  have h := (contact_oneSided_limits K t).2.2.2.2.2.inner
    (𝕜 := ℝ) (tendsto_const_nhds (x := tangentVector (t : Real.Angle)))
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : t - Real.pi < t)] with s hs
  rw [supportingIntersection_eq_tangentLineCoordinate K hs]
  simp only [inner_add_left, real_inner_smul_left, inner_normalVector_tangentVector,
    inner_tangentVector_self, mul_zero, mul_one, zero_add]

private def closedTangentLineCoordinate (K : ConvexBody Point) (t s : ℝ) : ℝ :=
  if s = t then inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle))
  else tangentLineCoordinate K t s

private theorem continuousOn_closedTangentLineCoordinate (K : ConvexBody Point) {t a : ℝ}
    (ha : a ∈ Ioo (t - Real.pi) t) :
    ContinuousOn (closedTangentLineCoordinate K t) (Icc a t) := by
  exact continuousOn_replace_right_endpoint ha.2 _ _
    (fun s hs ↦
      (continuousAt_tangentLineCoordinate K ⟨ha.1.trans_le hs.1, hs.2⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    (fun s hs ↦
      (continuousAt_tangentLineCoordinate K ⟨ha.1.trans hs.1, hs.2⟩).tendsto.mono_left
      nhdsWithin_le_nhds)
    (tendsto_tangentLineCoordinate_left K t)

private theorem monotoneOn_closedTangentLineCoordinate (K : ConvexBody Point) (t : ℝ) :
    MonotoneOn (closedTangentLineCoordinate K t) (Ioc (t - Real.pi) t) := by
  intro x hx y hy hxy
  by_cases hyEq : y = t
  · subst y
    by_cases hxEq : x = t
    · subst x
      rfl
    · have hxt : x < t := lt_of_le_of_ne hx.2 hxEq
      change (if x = t then _ else _) ≤ (if t = t then _ else _)
      simp only [ite_eq_right hxEq, ite_true]
      apply ge_of_tendsto (tendsto_tangentLineCoordinate_left K t)
      filter_upwards [Ioo_mem_nhdsLT hxt] with u hu
      exact monotoneOn_tangentLineCoordinate K t ⟨hx.1, hxt⟩
        ⟨hx.1.trans hu.1, hu.2⟩ hu.1.le
  · have hyt : y < t := lt_of_le_of_ne hy.2 hyEq
    have hxt : x < t := hxy.trans_lt hyt
    simp only [closedTangentLineCoordinate, ite_eq_right hxt.ne, ite_eq_right hyEq]
    exact monotoneOn_tangentLineCoordinate K t ⟨hx.1, hxt⟩ ⟨hy.1, hyt⟩ hxy

private theorem tangentLinePath_eq_coordinate (K : ConvexBody Point) (t : ℝ)
    (s : Ioc (t - Real.pi) t) :
    tangentLinePath K t s = supportValue K (t : Real.Angle) • normalVector (t : Real.Angle) +
      closedTangentLineCoordinate K t s • tangentVector (t : Real.Angle) := by
  dsimp [tangentLinePath]
  split_ifs with hs
  · rw [supportingIntersection_eq_tangentLineCoordinate K ⟨s.property.1, hs⟩]
    simp only [closedTangentLineCoordinate, ite_eq_right hs.ne]
  · have heq : (s : ℝ) = t := le_antisymm s.property.2 (le_of_not_gt hs)
    simp only [closedTangentLineCoordinate, heq]
    have hp := (edgeVertices_snd_mem K (t : Real.Angle)).2
    change inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
      supportValue K (t : Real.Angle) at hp
    rw [← hp]
    exact (inner_normalVector_smul_add_inner_tangentVector_smul _ _).symm

/-- Every value of a tangent-line path lies on the supporting line at its own path parameter. -/
theorem tangentLinePath_mem_supportingLine (K : ConvexBody Point) (t : ℝ)
    (s : Set.Ioc (t - Real.pi) t) :
    tangentLinePath K t s ∈
      (supportingLineHalfPlane (K : Set Point) ((s : ℝ) : Real.Angle)).1 := by
  unfold tangentLinePath
  split_ifs with hs
  · exact supportingIntersection_inner_left K (s : ℝ) t
  · have hst : (s : ℝ) = t := le_antisymm s.property.2 (le_of_not_gt hs)
    rw [hst]
    exact (edgeVertices_snd_mem K (t : Real.Angle)).2

theorem tangentLinePath_segment_area (K : ConvexBody Point) (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a ≤ b) :
    ∃ γ : ContinuousBVPaths a b,
      γ.val = tangentLineRestriction K t a b ha hb ∧
      Set.range γ.val = segment ℝ (tangentLinePath K t ⟨a, ha⟩)
        (tangentLinePath K t ⟨b, hb⟩) ∧
      Set.range γ.val ⊆ (supportingLineHalfPlane (K : Set Point) (t : Real.Angle)).1 ∧
      curveAreaFunctional γ =
        segmentArea (tangentLinePath K t ⟨a, ha⟩) (tangentLinePath K t ⟨b, hb⟩) := by
  let Q : Set.Icc a b → ℝ := fun s ↦ closedTangentLineCoordinate K t s
  have hQmono : Monotone Q := by
    intro x y hxy
    exact monotoneOn_closedTangentLineCoordinate K t
      ⟨ha.1.trans_le x.property.1, x.property.2.trans hb.2⟩
      ⟨ha.1.trans_le y.property.1, y.property.2.trans hb.2⟩ hxy
  have hQcont : Continuous Q := by
    change Continuous (Set.domRestrict (Set.Icc a b) (closedTangentLineCoordinate K t))
    by_cases hat : a < t
    · exact continuousOn_iff_continuous_domRestrict.mp
        ((continuousOn_closedTangentLineCoordinate K ⟨ha.1, hat⟩).mono
          (Icc_subset_Icc_right hb.2))
    · have heq : a = b := le_antisymm hab (hb.2.trans (le_of_not_gt hat))
      have hc : ContinuousOn (closedTangentLineCoordinate K t) ({a} : Set ℝ) :=
        (show ({a} : Set ℝ).Subsingleton from Set.subsingleton_singleton).continuousOn _
      exact continuousOn_iff_continuous_domRestrict.mp (hc.mono (by simp [heq]))
  have hQbv : BoundedVariationOn Q Set.univ := by
    apply MonotoneOn.boundedVariationOn (f := Q) (s := Set.univ)
      (fun _ _ _ _ hxy ↦ hQmono hxy)
      (C := |Q ⟨a, le_rfl, hab⟩| + |Q ⟨b, hab, le_rfl⟩|)
    intro s _
    have hlo := hQmono (show (⟨a, le_rfl, hab⟩ : Set.Icc a b) ≤ s from s.property.1)
    have hhi := hQmono (show s ≤ (⟨b, hab, le_rfl⟩ : Set.Icc a b) from s.property.2)
    exact abs_le.mpr ⟨by
      linarith [neg_abs_le (Q ⟨a, le_rfl, hab⟩), abs_nonneg (Q ⟨b, hab, le_rfl⟩)], by
      linarith [le_abs_self (Q ⟨b, hab, le_rfl⟩), abs_nonneg (Q ⟨a, le_rfl, hab⟩)]⟩
  let h := supportValue K (t : Real.Angle)
  let γ : ContinuousBVPaths a b := {
    val := fun s ↦ h • normalVector (t : Real.Angle) + Q s • tangentVector (t : Real.Angle)
    property := ⟨continuous_const.add (hQcont.smul continuous_const), fun i ↦ by
      let C : NNReal := ⟨|tangentVector (t : Real.Angle) i|, abs_nonneg _⟩
      have hLip : LipschitzWith C (fun r : ℝ ↦
          h * normalVector (t : Real.Angle) i + r * tangentVector (t : Real.Angle) i) := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        simp only [Real.dist_eq]
        rw [show (h * normalVector (t : Real.Angle) i + x * tangentVector (t : Real.Angle) i) -
          (h * normalVector (t : Real.Angle) i + y * tangentVector (t : Real.Angle) i) =
            (x - y) * tangentVector (t : Real.Angle) i by ring, abs_mul, mul_comm]
        rfl
      have hcomp := hLip.comp_boundedVariationOn hQbv
      change BoundedVariationOn (fun t_1 ↦
        h * normalVector (t : Real.Angle) i + Q t_1 * tangentVector (t : Real.Angle) i) Set.univ
      exact hcomp⟩ }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · funext s
    unfold tangentLineRestriction
    exact (tangentLinePath_eq_coordinate K t
      ⟨s, lt_of_lt_of_le ha.1 s.property.1, s.property.2.trans hb.2⟩).symm
  · rw [show γ.val = fun s ↦ h • normalVector (t : Real.Angle) +
        Q s • tangentVector (t : Real.Angle) from rfl]
    let A := Q ⟨a, le_rfl, hab⟩
    let B := Q ⟨b, hab, le_rfl⟩
    have hAB : A ≤ B := hQmono hab
    have hQrange : Set.range Q = Set.Icc (Q ⟨a, le_rfl, hab⟩) (Q ⟨b, hab, le_rfl⟩) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨s, rfl⟩
        exact ⟨hQmono s.property.1, hQmono s.property.2⟩
      · intro y hy
        let _ : PreconnectedSpace (Set.Icc a b) :=
          Subtype.preconnectedSpace isPreconnected_Icc
        exact intermediate_value_univ ⟨a, le_rfl, hab⟩ ⟨b, hab, le_rfl⟩ hQcont hy
    have haeq := tangentLinePath_eq_coordinate K t ⟨a, ha⟩
    have hbeq := tangentLinePath_eq_coordinate K t ⟨b, hb⟩
    have hAa : closedTangentLineCoordinate K t a = A := rfl
    have hBb : closedTangentLineCoordinate K t b = B := rfl
    change Set.range (fun s ↦ h • normalVector (t : Real.Angle) +
      Q s • tangentVector (t : Real.Angle)) = _
    rw [haeq, hbeq]
    rw [hAa, hBb]
    rw [segment_eq_image_lineMap]
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      have hs : Q s ∈ Set.Icc A B := by
        exact ⟨hQmono s.property.1, hQmono s.property.2⟩
      by_cases hABeq : A = B
      · refine ⟨0, by simp, ?_⟩
        have : Q s = A := le_antisymm (hs.2.trans_eq hABeq.symm) hs.1
        ext i
        simp [h, hABeq, this]
      · let u := (Q s - A) / (B - A)
        have hpos : 0 < B - A := sub_pos.mpr (lt_of_le_of_ne hAB hABeq)
        refine ⟨u, ⟨div_nonneg (sub_nonneg.mpr hs.1) hpos.le,
          (div_le_one hpos).2 (by linarith [hs.2])⟩, ?_⟩
        ext i
        simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
          smul_eq_mul]
        dsimp [u]
        field_simp [hpos.ne']
        ring
    · rintro ⟨u, hu, rfl⟩
      let r := A + u * (B - A)
      have hr : r ∈ Set.Icc A B := by
        dsimp [r]
        constructor
        · exact le_add_of_nonneg_right (mul_nonneg hu.1 (sub_nonneg.mpr hAB))
        · nlinarith [mul_le_mul_of_nonneg_right hu.2 (sub_nonneg.mpr hAB)]
      have hrange : r ∈ Set.range Q := by simpa [A, B, hQrange] using hr
      obtain ⟨s, hs⟩ := hrange
      refine ⟨s, ?_⟩
      ext i
      simp only [AffineMap.lineMap_apply_module, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul]
      rw [hs]
      ring
  · intro p hp
    obtain ⟨s, rfl⟩ := hp
    change inner ℝ (γ.val s) (normalVector (t : Real.Angle)) = supportValue K _
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_normalVector_self, real_inner_comm, inner_normalVector_tangentVector]
    simp [h]
  · let Qbv : RightContinuousIntervalBV a b := {
      toFun := Q
      boundedVariation := hQbv
      right_continuous := fun s ↦ hQcont.continuousAt.continuousWithinAt }
    have hcoord (i : Fin 2) (s : Set.Icc a b) :
        (continuousBVCoordinate γ i).toFun s =
          h * normalVector (t : Real.Angle) i +
            tangentVector (t : Real.Angle) i * Qbv.toFun s := by
      change (h • normalVector (t : Real.Angle) + Q s • tangentVector (t : Real.Angle)) i = _
      simp [Qbv, mul_comm]
    unfold curveAreaFunctional
    change (intervalStieltjesIntegral (continuousBVCoordinate γ 1)
        (continuousBVCoordinate γ 0).toFun Set.univ -
      intervalStieltjesIntegral (continuousBVCoordinate γ 0)
        (continuousBVCoordinate γ 1).toFun Set.univ) / 2 = _
    rw [intervalStieltjesIntegral_affine_driver_cross hab Qbv
      (continuousBVCoordinate γ 0) (continuousBVCoordinate γ 1) hQcont
      (h * normalVector (t : Real.Angle) 0) (tangentVector (t : Real.Angle) 0)
      (h * normalVector (t : Real.Angle) 1) (tangentVector (t : Real.Angle) 1)
      (hcoord 0) (hcoord 1)]
    have haeq := tangentLinePath_eq_coordinate K t ⟨a, ha⟩
    have hbeq := tangentLinePath_eq_coordinate K t ⟨b, hb⟩
    rw [haeq, hbeq]
    simp only [Qbv]
    simp [segmentArea, planeCrossProduct, normalVector, tangentVector, frame, h]
    simp only [Q]
    ring

theorem tangentLinePath_convexLinear (t a b : ℝ)
    (ha : a ∈ Set.Ioc (t - Real.pi) t) (hb : b ∈ Set.Ioc (t - Real.pi) t)
    (hab : a ≤ b) :
    ∃ F : ConvexBody Point → ContinuousBVPaths a b,
      (∀ K, (F K).val = tangentLineRestriction K t a b ha hb) ∧
      IsConvexLinear convexBodyCombination
        (fun r x y ↦ (1 - (r : ℝ)) • x + (r : ℝ) • y) F := by
  let F : ConvexBody Point → ContinuousBVPaths a b := fun K ↦
    (tangentLinePath_segment_area K t a b ha hb hab).choose
  have hF (K : ConvexBody Point) :
      (F K).val = tangentLineRestriction K t a b ha hb :=
    (tangentLinePath_segment_area K t a b ha hb hab).choose_spec.1
  refine ⟨F, hF, ?_⟩
  intro r K L
  apply Subtype.ext
  funext s
  change (F (convexBodyCombination r K L)).val s =
    ((1 - (r : ℝ)) • (F K).val + (r : ℝ) • (F L).val) s
  rw [hF, hF, hF]
  unfold tangentLineRestriction tangentLinePath
  by_cases hs : (s : ℝ) < t
  · simp only [hs, ↓reduceIte, Pi.add_apply, Pi.smul_apply]
    exact (convexBody_maps_linear r K L).2.2.1 (s : ℝ) t hs
      (by linarith [ha.1, s.property.1])
  · have hst : (s : ℝ) = t := by
      apply le_antisymm
      · exact le_trans s.property.2 hb.2
      · exact le_of_not_gt hs
    simp only [hs, ↓reduceIte, Pi.add_apply, Pi.smul_apply]
    simpa [hst] using (convexBody_maps_linear r K L).2.1 (t : Real.Angle) |>.2

end MovingSofa
