import MovingSofa.Analysis.MeasureProducts
import MovingSofa.Cap.Regularity
import MovingSofa.ForMathlib.Analysis.Calculus.FirstReturn

/-!
# Endpoint contacts for the canonical cap tails

The right and left canonical tails of a special cap are cut out of the cap by the upper
half-planes of its inner supporting walls. This file supplies the contact points that make the
tail support values meet their endpoint bounds.

The mathematical content is the frame-free lemma
`exists_mem_inner_eq_sub_one_of_deriv_signs`: let `s` be a nonempty compact convex planar set
lying above the horizontal axis with `h_s(pi/2) = 1`, whose support function `h` is
differentiable on the two quarter-turn families with the strict corner velocity signs
`h'(t) - h(t + pi/2) + 1 < 0` and `h'(t + pi/2) + h(t) - 1 > 0` for `t` in `(0, pi/2)`. Then
every interior cut line `{q | inner q (normalVector t) = h(t) - 1}` meets `s` in a point that
stays above the whole cut family on `[t, pi/2]`.

The proof selects the transverse maximum `p` of the first cut section and studies the
deficiency `g(t) = h(t) - inner p (normalVector t)`. Wherever `g(t) = 1`, the chord joining the
two frame contacts has nonpositive signed area (`planeCrossProduct_nonpos_of_isMaxOn`), which
forces `g` to decrease strictly at the cut angle; at a first return of `g` to level one the
same determinant is strictly positive, a contradiction.

The left tail follows from the same lemma applied to `reflectedBody (pi/2) K`, whose support
derivatives are the negated right-hand ones read backwards; see `exists_left_tail_contact`.

This argument replaces the step in the paper's proof of `lem:right-left-body` which infers that the
upper boundary avoids the niche; that inference fails for the stated class of caps (P46 in
`NOTES.md`).
-/

noncomputable section

namespace MovingSofa

/-- Lowering a right-angle cap point vertically to the base line keeps it inside the cap. -/
theorem basePoint_mem_of_rightAngleCap (K : RightAngleCapSpace) {q : Point}
    (hq : q ∈ (K.1 : Set Point)) : (!₂[q 0, 0] : Point) ∈ (K.1 : Set Point) := by
  have hq0 : (!₂[q 0, 0] : Point) 0 = q 0 := rfl
  have hq1 : (!₂[q 0, 0] : Point) 1 = 0 := rfl
  have hqy : 0 ≤ q 1 := by
    have h := K.inner_normalVector_pi_div_two_nonneg hq
    rwa [inner_normalVector_pi_div_two] at h
  have hzero : inner ℝ (!₂[q 0, 0] : Point)
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [inner_normalVector_pi_div_two, hq1]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨le_of_eq hzero.symm, le_of_eq hzero.symm⟩ ?_
  intro t ht
  have htI : 0 ≤ t ∧ t ≤ Real.pi := by
    rcases ht with h | h
    · exact ⟨h.1, by linarith only [h.2, Real.pi_pos]⟩
    · exact ⟨by linarith only [h.1, Real.pi_pos], by linarith only [h.2]⟩
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1 htI.2
  have hqt := inner_le_supportValue_of_isCompact K.1.isCompact hq (t : Real.Angle)
  rw [inner_normalVector_real] at hqt
  rw [inner_normalVector_real, hq0, hq1]
  nlinarith only [hqt, hsin, hqy]

/-- The two frame contacts at an interior angle, with their derivative coordinates. -/
theorem exists_frame_contacts {s : Set Point} (hcomp : IsCompact s) (hne : s.Nonempty)
    {t dh dj : ℝ}
    (hdh : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) dh t)
    (hdj : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) dj (t + Real.pi / 2)) :
    ∃ A ∈ s, ∃ C ∈ s,
      inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) ∧
      inner ℝ A (tangentVector (t : Real.Angle)) = dh ∧
      inner ℝ C (normalVector (t : Real.Angle)) = -dj ∧
      inner ℝ C (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  obtain ⟨A, hA, hA1, hA2⟩ := exists_contact_of_hasDerivAt hcomp hne hdh
  obtain ⟨C, hC, hC1, hC2⟩ := exists_contact_of_hasDerivAt hcomp hne hdj
  have hnv : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      tangentVector (t : Real.Angle) := by
    rw [Real.Angle.coe_add]
    exact normalVector_add_pi_div_two (t : Real.Angle)
  have htv : tangentVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      -normalVector (t : Real.Angle) := tangentVector_add_pi_div_two t
  rw [hnv] at hC1
  rw [htv, inner_neg_right] at hC2
  exact ⟨A, hA, C, hC, hA1, hA2, by linarith, hC1⟩

/-- A transverse chord through a maximizing section point has nonpositive signed area. -/
theorem planeCrossProduct_nonpos_of_isMaxOn {s : Set Point} (hconv : Convex ℝ s)
    {r c₀ : ℝ} {p : Point}
    (hpline : inner ℝ p (normalVector (r : Real.Angle)) = c₀)
    (hmax : ∀ q ∈ s, inner ℝ q (normalVector (r : Real.Angle)) = c₀ →
      inner ℝ q (tangentVector (r : Real.Angle)) ≤ inner ℝ p (tangentVector (r : Real.Angle)))
    {A C : Point} (hA : A ∈ s) (hC : C ∈ s)
    (hApos : 0 < inner ℝ (A - p) (normalVector (r : Real.Angle)))
    (hCneg : inner ℝ (C - p) (normalVector (r : Real.Angle)) < 0) :
    planeCrossProduct (A - p) (C - p) ≤ 0 := by
  set u := normalVector (r : Real.Angle) with hu
  set v := tangentVector (r : Real.Angle) with hv
  set mu : ℝ := inner ℝ (A - p) u with hmu
  set la : ℝ := -inner ℝ (C - p) u with hla
  have hlapos : 0 < la := by simp only [hla]; linarith
  have hsum : 0 < la + mu := by linarith
  set w : ℝ := la / (la + mu) with hw
  have hw0 : 0 ≤ w := div_nonneg hlapos.le hsum.le
  have hw1 : 0 ≤ 1 - w := by
    rw [hw, sub_nonneg, div_le_one hsum]
    linarith
  set q : Point := w • A + (1 - w) • C with hq
  have hqs : q ∈ s := hconv hA hC hw0 hw1 (by ring)
  have hwmu : w * mu + (1 - w) * (-la) = 0 := by
    rw [hw]; field_simp; ring
  have hqu : inner ℝ q u = c₀ := by
    have h1 : inner ℝ q u - inner ℝ p u = w * mu + (1 - w) * (-la) := by
      simp only [hq, hmu, hla, inner_add_left, real_inner_smul_left, inner_sub_left]
      ring
    rw [hwmu] at h1
    rw [hpline] at h1
    linarith
  have hqv := hmax q hqs hqu
  have h2 : inner ℝ q v - inner ℝ p v =
      w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v := by
    simp only [hq, inner_add_left, real_inner_smul_left, inner_sub_left]
    ring
  have hnum : w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v ≤ 0 := by
    rw [← h2]; linarith
  have hcross : planeCrossProduct (A - p) (C - p) =
      mu * inner ℝ (C - p) v - inner ℝ (A - p) v * (-la) := by
    rw [planeCrossProduct_eq_inner_frame (A - p) (C - p) r, ← hu, ← hv, ← hmu]
    simp only [hla]
    ring
  rw [hcross]
  have hwid : (1 - w) * (la + mu) = mu := by rw [hw]; field_simp; ring
  have hwid2 : w * (la + mu) = la := by rw [hw]; field_simp
  have hexp : (w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v) * (la + mu) =
      la * inner ℝ (A - p) v + mu * inner ℝ (C - p) v := by
    calc (w * inner ℝ (A - p) v + (1 - w) * inner ℝ (C - p) v) * (la + mu)
        = (w * (la + mu)) * inner ℝ (A - p) v +
          ((1 - w) * (la + mu)) * inner ℝ (C - p) v := by ring
      _ = la * inner ℝ (A - p) v + mu * inner ℝ (C - p) v := by rw [hwid, hwid2]
  have hmul := mul_nonpos_of_nonpos_of_nonneg hnum hsum.le
  rw [hexp] at hmul
  linarith

/-- The three chord signs at a first return time, in the frame coordinates at that time. -/
private theorem chord_signs {r t d al be : ℝ} (hr : 0 < r) (hrt : r < t)
    (ht : t < Real.pi / 2) (hd : 0 ≤ d) (hal : al < 0) (hbe : 0 < be)
    (hstrip : Real.sin t + Real.cos t * d ≤ 1) :
    0 < Real.cos (t - r) - Real.sin (t - r) * d ∧
      Real.cos (t - r) * (-be) - Real.sin (t - r) * (1 - al + d) < 0 ∧
      0 < 1 - al + d + be * d := by
  have hpi := Real.pi_pos
  have hδpos : 0 < t - r := by linarith only [hrt]
  have hδlt : t - r < Real.pi / 2 := by linarith only [hr, ht]
  have hsinδ : 0 < Real.sin (t - r) :=
    Real.sin_pos_of_pos_of_lt_pi hδpos (by linarith only [hpi, hδlt])
  have hcosδ : 0 < Real.cos (t - r) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hpi, hδpos], hδlt⟩
  have hcost : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith only [hpi, hr, hrt], ht⟩
  have hcosr : Real.cos (t - r) * Real.cos t + Real.sin (t - r) * Real.sin t = Real.cos r := by
    rw [← Real.cos_sub, show t - r - t = -r by ring, Real.cos_neg]
  have hcosrgt : Real.sin (t - r) < Real.cos r := by
    rw [← Real.sin_pi_div_two_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith only [hpi, hδpos])
      (by linarith only [hr]) (by linarith only [ht])
  refine ⟨?_, ?_, by nlinarith only [hal, hbe, hd]⟩
  · have hmul := mul_le_mul_of_nonneg_left hstrip hsinδ.le
    have hstep : Real.cos r - Real.sin (t - r) ≤
        Real.cos t * (Real.cos (t - r) - Real.sin (t - r) * d) := by
      nlinarith only [hmul, hcosr]
    by_contra hc
    push Not at hc
    nlinarith only [hstep, hc, hcost, hcosrgt]
  · nlinarith only [hcosδ, hsinδ, hbe, hal, hd]

/-- Contradiction sign lemma at the cut angle: a nonpositive determinant forces a negative slope. -/
private theorem neg_of_det_nonpos {d al be : ℝ} (hal : al < 0) (hbe : 0 < be)
    (hdet : 1 - al + d + be * d ≤ 0) : d < 0 := by
  by_contra h
  push Not at h
  nlinarith only [hal, hbe, hdet, h]

/-- Endpoint contact for the upper cut family of a strip body with strict corner velocities. -/
theorem exists_mem_inner_eq_sub_one_of_deriv_signs
    {s : Set Point} (hcomp : IsCompact s) (hconv : Convex ℝ s) (hne : s.Nonempty)
    (dh dj : ℝ → ℝ)
    (hdh : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) (dh t) t)
    (hdj : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) (dj t) (t + Real.pi / 2))
    (halpha : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      dh t - supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) + 1 < 0)
    (hbeta : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < dj t + supportValue s (t : Real.Angle) - 1)
    (htop : supportValue s ((Real.pi / 2 : ℝ) : Real.Angle) = 1)
    (hlow : ∀ q ∈ s, 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ s, inner ℝ p (normalVector (r : Real.Angle)) =
        supportValue s (r : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc r (Real.pi / 2),
        supportValue s (t : Real.Angle) - 1 ≤ inner ℝ p (normalVector (t : Real.Angle)) := by
  -- the cut line at `r` meets the body, between the two frame contacts
  obtain ⟨A₀, hA₀, C₀, hC₀, hA₀n, hA₀t, hC₀n, hC₀t⟩ :=
    exists_frame_contacts hcomp hne (hdh r hr) (hdj r hr)
  have hC₀le : inner ℝ C₀ (normalVector (r : Real.Angle)) ≤
      supportValue s (r : Real.Angle) - 1 := by
    rw [hC₀n]; linarith only [hbeta r hr]
  have hA₀ge : supportValue s (r : Real.Angle) - 1 ≤
      inner ℝ A₀ (normalVector (r : Real.Angle)) := by rw [hA₀n]; linarith only []
  obtain ⟨p₀, hp₀, hp₀line⟩ :=
    exists_mem_inner_eq_of_convex hconv hA₀ hC₀ hC₀le hA₀ge
  -- the transverse maximizer on that cut section
  have hcontinner : Continuous (fun q : Point ↦ inner ℝ q (normalVector (r : Real.Angle))) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hScomp : IsCompact (s ∩ {q : Point |
      inner ℝ q (normalVector (r : Real.Angle)) = supportValue s (r : Real.Angle) - 1}) :=
    hcomp.inter_right (isClosed_eq hcontinner continuous_const)
  have hconttang : Continuous (fun q : Point ↦ inner ℝ q (tangentVector (r : Real.Angle))) :=
    continuous_inner.comp (continuous_id.prodMk continuous_const)
  obtain ⟨p, hpS, hpmax⟩ :=
    hScomp.exists_isMaxOn ⟨p₀, hp₀, hp₀line⟩ hconttang.continuousOn
  have hps : p ∈ s := hpS.1
  have hpline : inner ℝ p (normalVector (r : Real.Angle)) =
    supportValue s (r : Real.Angle) - 1 := hpS.2
  have hmaxq : ∀ q ∈ s, inner ℝ q (normalVector (r : Real.Angle)) =
      supportValue s (r : Real.Angle) - 1 →
      inner ℝ q (tangentVector (r : Real.Angle)) ≤
        inner ℝ p (tangentVector (r : Real.Angle)) := fun q hq hq2 => hpmax ⟨hq, hq2⟩
  -- the deficiency function
  set g : ℝ → ℝ := fun u ↦ supportValue s (u : Real.Angle) -
    inner ℝ p (normalVector (u : Real.Angle)) with hgdef
  have hgval : ∀ u : ℝ, g u = supportValue s (u : Real.Angle) -
      inner ℝ p (normalVector (u : Real.Angle)) := fun _ => rfl
  have hgr : g r = 1 := by rw [hgval, hpline]; ring
  have hgderiv : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt g (dh t - inner ℝ p (tangentVector (t : Real.Angle))) t :=
    fun t ht => (hdh t ht).sub (hasDerivAt_inner_normalVector p t)
  have hgT : g (Real.pi / 2) ≤ 1 := by
    rw [hgval, htop]
    linarith only [hlow p hps]
  -- coordinates of the two contact chords relative to the maximizer
  have hcoords : ∀ t : ℝ, g t = 1 → ∀ A C : Point,
      inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) →
      inner ℝ A (tangentVector (t : Real.Angle)) = dh t →
      inner ℝ C (normalVector (t : Real.Angle)) = -dj t →
      inner ℝ C (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) →
      inner ℝ (A - p) (normalVector (t : Real.Angle)) = 1 ∧
      inner ℝ (A - p) (tangentVector (t : Real.Angle)) =
        dh t - inner ℝ p (tangentVector (t : Real.Angle)) ∧
      inner ℝ (C - p) (normalVector (t : Real.Angle)) =
        -dj t - (supportValue s (t : Real.Angle) - 1) ∧
      inner ℝ (C - p) (tangentVector (t : Real.Angle)) =
        supportValue s ((t + Real.pi / 2 : ℝ) : Real.Angle) -
          inner ℝ p (tangentVector (t : Real.Angle)) := by
    intro t hgt A C e1 e2 e3 e4
    have hpu : inner ℝ p (normalVector (t : Real.Angle)) =
        supportValue s (t : Real.Angle) - 1 := by
      have h := hgval t
      rw [hgt] at h
      linarith only [h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [inner_sub_left, e1, hpu]; ring
    · simp only [inner_sub_left, e2]
    · simp only [inner_sub_left, e3, hpu]
    · simp only [inner_sub_left, e4]
  -- the deficiency decreases strictly at the cut angle
  have hdgr : dh r - inner ℝ p (tangentVector (r : Real.Angle)) < 0 := by
    obtain ⟨k1, k2, k3, k4⟩ := hcoords r hgr A₀ C₀ hA₀n hA₀t hC₀n hC₀t
    have hApos : 0 < inner ℝ (A₀ - p) (normalVector (r : Real.Angle)) := by
      rw [k1]; norm_num
    have hCneg : inner ℝ (C₀ - p) (normalVector (r : Real.Angle)) < 0 := by
      rw [k3]; linarith only [hbeta r hr]
    have hcr := planeCrossProduct_nonpos_of_isMaxOn hconv hpline hmaxq hA₀ hC₀ hApos hCneg
    rw [planeCrossProduct_eq_inner_frame (A₀ - p) (C₀ - p) r, k1, k2, k3, k4] at hcr
    exact neg_of_det_nonpos (halpha r hr) (hbeta r hr) (by linarith only [hcr])
  -- the deficiency never exceeds one on the cut range
  have hmain : ∀ t ∈ Set.Icc r (Real.pi / 2), g t ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t₁, ht₁mem, ht₁gt⟩ := hcon
    have ht₁r : r < t₁ :=
      lt_of_le_of_ne ht₁mem.1 (by rintro rfl; rw [hgr] at ht₁gt; exact lt_irrefl 1 ht₁gt)
    have ht₁T : t₁ < Real.pi / 2 :=
      lt_of_le_of_ne ht₁mem.2 (by rintro rfl; exact absurd hgT (not_le.mpr ht₁gt))
    -- a time just to the right of the cut where the deficiency is below one
    have hev : ∀ᶠ y in nhdsWithin r (Set.Ioi r), slope g r y < 0 := by
      refine (((hasDerivAt_iff_tendsto_slope.mp (hgderiv r hr)).mono_left
        (nhdsWithin_mono r fun x hx => ne_of_gt hx)).eventually_lt_const hdgr)
    obtain ⟨r', hr'slope, hr'mem⟩ :=
      (hev.and (Filter.eventually_of_mem (Ioo_mem_nhdsGT ht₁r) fun y hy => hy)).exists
    have hrr' : r < r' := hr'mem.1
    have hr't₁ : r' < t₁ := hr'mem.2
    have hgr'lt : g r' < 1 := by
      rw [slope_def_field] at hr'slope
      have hnum : g r' - g r < 0 := by
        by_contra hcc
        push Not at hcc
        have h0 : 0 ≤ (g r' - g r) / (r' - r) := div_nonneg hcc (by linarith only [hrr'])
        linarith only [h0, hr'slope]
      linarith only [hnum, hgr]
    -- the first return to level one
    have hgcontOn : ContinuousOn g (Set.Icc r' t₁) := fun u hu =>
      ((hgderiv u ⟨by linarith only [hu.1, hrr', hr.1],
        by linarith only [hu.2, ht₁T]⟩).continuousAt).continuousWithinAt
    obtain ⟨t₂, ht₂mem', hgt₂, hleft⟩ :=
      exists_first_return hr't₁ hgcontOn hgr'lt ht₁gt.le
    have ht₂gt : r' < t₂ := ht₂mem'.1
    have ht₂mem : t₂ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith only [hr.1, hrr', ht₂gt], lt_of_le_of_lt ht₂mem'.2 ht₁T⟩
    have hdgt₂ : 0 ≤ dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle)) :=
      nonneg_of_first_return ht₂gt (hgderiv t₂ ht₂mem) hgt₂ hleft
    -- the transverse signs at the first return
    obtain ⟨A, hA, C, hC, e1, e2, e3, e4⟩ :=
      exists_frame_contacts hcomp hne (hdh t₂ ht₂mem) (hdj t₂ ht₂mem)
    obtain ⟨k1, k2, k3, k4⟩ := hcoords t₂ hgt₂ A C e1 e2 e3 e4
    have hframeR : normalVector (r : Real.Angle) =
        Real.cos (t₂ - r) • normalVector (t₂ : Real.Angle) -
          Real.sin (t₂ - r) • tangentVector (t₂ : Real.Angle) := by
      have hrew : ((r : ℝ) : Real.Angle) = ((t₂ + -(t₂ - r) : ℝ) : Real.Angle) := by
        congr 1; ring
      rw [hrew, normalVector_add_real t₂ (-(t₂ - r)), Real.cos_neg, Real.sin_neg]
      module
    have hframeT : normalVector ((Real.pi / 2 : ℝ) : Real.Angle) =
        Real.sin t₂ • normalVector (t₂ : Real.Angle) +
          Real.cos t₂ • tangentVector (t₂ : Real.Angle) := by
      have hrew : ((Real.pi / 2 : ℝ) : Real.Angle) =
          ((t₂ + (Real.pi / 2 - t₂) : ℝ) : Real.Angle) := by norm_num
      rw [hrew, normalVector_add_real t₂ (Real.pi / 2 - t₂), Real.cos_pi_div_two_sub,
        Real.sin_pi_div_two_sub]
    have hAT : inner ℝ (A - p) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
        Real.sin t₂ * 1 + Real.cos t₂ *
          (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeT, inner_add_right, real_inner_smul_right, real_inner_smul_right, k1, k2]
    have hstrip : Real.sin t₂ + Real.cos t₂ *
        (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) ≤ 1 := by
      have h1 := inner_le_supportValue_of_isCompact hcomp hA ((Real.pi / 2 : ℝ) : Real.Angle)
      rw [htop] at h1
      have h2 : inner ℝ (A - p) (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1 := by
        rw [inner_sub_left]
        linarith only [h1, hlow p hps]
      rw [hAT] at h2
      linarith only [h2]
    obtain ⟨hs1, hs2, hs3⟩ := chord_signs hr.1 (by linarith only [hrr', ht₂gt])
      ht₂mem.2 hdgt₂ (halpha t₂ ht₂mem) (hbeta t₂ ht₂mem) hstrip
    have hAr : inner ℝ (A - p) (normalVector (r : Real.Angle)) =
        Real.cos (t₂ - r) * 1 - Real.sin (t₂ - r) *
          (dh t₂ - inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeR, inner_sub_right, real_inner_smul_right, real_inner_smul_right, k1, k2]
    have hCr : inner ℝ (C - p) (normalVector (r : Real.Angle)) =
        Real.cos (t₂ - r) * (-dj t₂ - (supportValue s (t₂ : Real.Angle) - 1)) -
          Real.sin (t₂ - r) * (supportValue s ((t₂ + Real.pi / 2 : ℝ) : Real.Angle) -
            inner ℝ p (tangentVector (t₂ : Real.Angle))) := by
      rw [hframeR, inner_sub_right, real_inner_smul_right, real_inner_smul_right, k3, k4]
    have hApos : 0 < inner ℝ (A - p) (normalVector (r : Real.Angle)) := by
      rw [hAr]; linarith only [hs1]
    have hCneg : inner ℝ (C - p) (normalVector (r : Real.Angle)) < 0 := by
      rw [hCr]; linarith only [hs2]
    have hcr := planeCrossProduct_nonpos_of_isMaxOn hconv hpline hmaxq hA hC hApos hCneg
    rw [planeCrossProduct_eq_inner_frame (A - p) (C - p) t₂, k1, k2, k3, k4] at hcr
    linarith only [hcr, hs3]
  refine ⟨p, hps, hpline, fun t ht => ?_⟩
  have hle := hmain t ht
  rw [hgval] at hle
  linarith only [hle]

/-- The lowered horizontal extremes of a right-angle cap lie under all right and left cuts. -/
theorem exists_cap_base_points (K : RightAngleCapSpace) :
    ∃ pR ∈ (K.1 : Set Point), ∃ pL ∈ (K.1 : Set Point),
      inner ℝ pR (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∧
      inner ℝ pL (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ pR (normalVector (t : Real.Angle))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ pL (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle))) := by
  have hheight : ∀ q ∈ (K.1 : Set Point), 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    intro q hq
    have hlo := K.inner_normalVector_pi_div_two_nonneg hq
    have hhi := inner_le_supportValue_of_isCompact K.1.isCompact hq
      ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.1] at hhi
    rw [inner_normalVector_pi_div_two] at hlo hhi
    exact ⟨hlo, hhi⟩
  obtain ⟨A, hA, hAeq⟩ := exists_mem_inner_eq_supportValue K.1 ((0 : ℝ) : Real.Angle)
  obtain ⟨C, hC, hCeq⟩ := exists_mem_inner_eq_supportValue K.1 ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero] at hAeq
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hCeq
  have hAmax : ∀ q ∈ (K.1 : Set Point), q 0 ≤ A 0 := by
    intro q hq
    have h := inner_le_supportValue_of_isCompact K.1.isCompact hq ((0 : ℝ) : Real.Angle)
    rw [inner_normalVector_real, Real.cos_zero, Real.sin_zero] at h
    linarith only [h, hAeq]
  have hCmin : ∀ q ∈ (K.1 : Set Point), C 0 ≤ q 0 := by
    intro q hq
    have h := inner_le_supportValue_of_isCompact K.1.isCompact hq ((Real.pi : ℝ) : Real.Angle)
    rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at h
    linarith only [h, hCeq]
  refine ⟨!₂[A 0, 0], basePoint_mem_of_rightAngleCap K hA, !₂[C 0, 0],
    basePoint_mem_of_rightAngleCap K hC, ?_, ?_, ?_, ?_⟩
  · rw [inner_normalVector_pi_div_two]; rfl
  · rw [inner_normalVector_pi_div_two]; rfl
  · intro t ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
    have hbound : supportValue (K.1 : Set Point) (t : Real.Angle) ≤ A 0 * Real.cos t + 1 := by
      refine csSup_le (K.1.nonempty.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      dsimp only
      rw [inner_normalVector_real]
      nlinarith only [hAmax q hq, (hheight q hq).2, hcos, hsin, hsin1]
    rw [inner_normalVector_real]
    show supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤ A 0 * Real.cos t + 0 * Real.sin t
    linarith only [hbound]
  · intro t ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith only [ht.1, Real.pi_pos], ht.2⟩
    have hcos1 : Real.cos t ≤ 1 := Real.cos_le_one t
    have hsin : 0 ≤ Real.sin t :=
      Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith only [ht.2, Real.pi_pos])
    have hbound : supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
        -(C 0) * Real.sin t + 1 := by
      refine csSup_le (K.1.nonempty.image _) ?_
      rintro _ ⟨q, hq, rfl⟩
      dsimp only
      rw [inner_normalVector_real, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
      nlinarith only [hCmin q hq, (hheight q hq).2, hcos, hcos1, hsin]
    rw [inner_normalVector_real, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
    show supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
      C 0 * -Real.sin t + 0 * Real.cos t
    linarith only [hbound]

/-- The right cut line meets the cap, below the whole right cut family. -/
theorem exists_right_tail_contact (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ (K.1 : Set Point),
      inner ℝ p (normalVector (r : Real.Angle)) =
        supportValue (K.1 : Set Point) (r : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc r (Real.pi / 2),
        supportValue (K.1 : Set Point) (t : Real.Angle) - 1 ≤
          inner ℝ p (normalVector (t : Real.Angle)) := by
  obtain ⟨dh, dj, h1, h2, h3, h4⟩ := capSupport_hasDerivAt K hinj
  exact exists_mem_inner_eq_sub_one_of_deriv_signs K.1.isCompact K.1.convex K.1.nonempty
    dh dj h1 h2 h3 h4 K.property.2.2.2.1
    (fun q hq => K.inner_normalVector_pi_div_two_nonneg hq) hr

/-- The left cut line meets the cap, below the whole left cut family. -/
theorem exists_left_tail_contact (K : RightAngleCapSpace)
    (hinj : SatisfiesInjectivityCondition K) {l : ℝ}
    (hl : l ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∃ p ∈ (K.1 : Set Point),
      inner ℝ p (normalVector ((l + Real.pi / 2 : ℝ) : Real.Angle)) =
        supportValue (K.1 : Set Point) ((l + Real.pi / 2 : ℝ) : Real.Angle) - 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) l,
        supportValue (K.1 : Set Point) ((t + Real.pi / 2 : ℝ) : Real.Angle) - 1 ≤
          inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) := by
  obtain ⟨dh, dj, h1, h2, h3, h4⟩ := capSupport_hasDerivAt K hinj
  have hcast : ∀ a b : ℝ, a = b → ((a : ℝ) : Real.Angle) = ((b : ℝ) : Real.Angle) :=
    fun a b h => by rw [h]
  have hsv : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point) (u : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi - u : ℝ) : Real.Angle) :=
    supportValue_reflectedBody_pi_div_two K.1
  have hfunS : (fun w : ℝ ↦ supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point)
      (w : Real.Angle)) =
      fun w : ℝ ↦ supportValue (K.1 : Set Point) ((Real.pi - w : ℝ) : Real.Angle) :=
    funext hsv
  have hrefl : ∀ u : ℝ, u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Real.pi / 2 - u ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun u hu => ⟨by linarith only [hu.2], by linarith only [hu.1]⟩
  have hsvL : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point)
          ((u + Real.pi / 2 : ℝ) : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi / 2 - u : ℝ) : Real.Angle) := by
    intro u
    rw [hsv (u + Real.pi / 2),
      hcast _ _ (show Real.pi - (u + Real.pi / 2) = Real.pi / 2 - u by ring)]
  have hsvR : ∀ u : ℝ,
      supportValue (reflectedBody (Real.pi / 2) K.1 : Set Point) (u : Real.Angle) =
        supportValue (K.1 : Set Point) ((Real.pi / 2 - u + Real.pi / 2 : ℝ) : Real.Angle) := by
    intro u
    rw [hsv u, hcast _ _ (show Real.pi - u = Real.pi / 2 - u + Real.pi / 2 by ring)]
  obtain ⟨q0, hq0s, hq0line, hq0bound⟩ :=
    exists_mem_inner_eq_sub_one_of_deriv_signs
      (reflectedBody (Real.pi / 2) K.1).isCompact (reflectedBody (Real.pi / 2) K.1).convex
      (reflectedBody (Real.pi / 2) K.1).nonempty
      (fun u ↦ -dj (Real.pi / 2 - u)) (fun u ↦ -dh (Real.pi / 2 - u))
      (by
        intro u hu
        have hF : HasDerivAt (fun w : ℝ ↦ supportValue (K.1 : Set Point) (w : Real.Angle))
            (dj (Real.pi / 2 - u)) (Real.pi - u) := by
          rw [show Real.pi - u = Real.pi / 2 - u + Real.pi / 2 by ring]
          exact h2 _ (hrefl u hu)
        rw [hfunS]
        exact HasDerivAt.comp_const_sub Real.pi u hF)
      (by
        intro u hu
        have hF : HasDerivAt (fun w : ℝ ↦ supportValue (K.1 : Set Point) (w : Real.Angle))
            (dh (Real.pi / 2 - u)) (Real.pi - (u + Real.pi / 2)) := by
          rw [show Real.pi - (u + Real.pi / 2) = Real.pi / 2 - u by ring]
          exact h1 _ (hrefl u hu)
        rw [hfunS]
        exact HasDerivAt.comp_const_sub Real.pi (u + Real.pi / 2) hF)
      (by
        intro u hu
        rw [hsvL u]
        linarith only [h4 _ (hrefl u hu)])
      (by
        intro u hu
        rw [hsvR u]
        linarith only [h3 _ (hrefl u hu)])
      (by
        rw [hsv (Real.pi / 2), hcast _ _ (show Real.pi - Real.pi / 2 = Real.pi / 2 by ring)]
        exact K.property.2.2.2.1)
      (by
        rintro q ⟨v, hv, rfl⟩
        rw [inner_capReflection_pi_div_two,
          hcast _ _ (show Real.pi - Real.pi / 2 = Real.pi / 2 by ring)]
        exact K.inner_normalVector_pi_div_two_nonneg hv)
      (show Real.pi / 2 - l ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) from hrefl l hl)
  obtain ⟨p, hpK, rfl⟩ : ∃ p ∈ (K.1 : Set Point), capReflection (Real.pi / 2) p = q0 := hq0s
  refine ⟨p, hpK, ?_, ?_⟩
  · rw [inner_capReflection_pi_div_two,
      hcast _ _ (show Real.pi - (Real.pi / 2 - l) = l + Real.pi / 2 by ring)] at hq0line
    rw [hsv (Real.pi / 2 - l),
      hcast _ _ (show Real.pi - (Real.pi / 2 - l) = l + Real.pi / 2 by ring)] at hq0line
    exact hq0line
  · intro t ht
    have hw : Real.pi / 2 - t ∈ Set.Icc (Real.pi / 2 - l) (Real.pi / 2) :=
      ⟨by linarith only [ht.2], by linarith only [ht.1]⟩
    have hb := hq0bound (Real.pi / 2 - t) hw
    rw [inner_capReflection_pi_div_two,
      hcast _ _ (show Real.pi - (Real.pi / 2 - t) = t + Real.pi / 2 by ring)] at hb
    rw [hsv (Real.pi / 2 - t),
      hcast _ _ (show Real.pi - (Real.pi / 2 - t) = t + Real.pi / 2 by ring)] at hb
    exact hb

end MovingSofa
