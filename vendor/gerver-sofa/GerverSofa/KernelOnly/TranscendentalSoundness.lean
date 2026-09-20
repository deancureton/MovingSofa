import GerverSofa.KernelOnly.AlternatingSeries
import GerverSofa.KernelOnly.ReplayConsequences
import GerverSofa.KernelOnly.SoundnessInterfaces
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Soundness of the exact transcendental interval evaluator

This file proves the analytic trust bridge omitted by the executable replay:

* the alternating rational arctangent sums enclose the two Machin terms;
* the computed Machin interval encloses `Real.pi` and lies in the declared
  interval;
* fixed-decimal rounding is outward;
* the small-argument Taylor intervals enclose `Real.sin` and `Real.cos`;
* complementary-angle reduction is sound on `[0, π/2]`;
* externally over-wide intervals fail closed to `[-1,1]` rather than silently
  violating the Taylor precondition.

No project axiom and no floating-point literal occurs in this file.
-/

noncomputable section

namespace GerverSofa.ExactReplay

open RatInterval

/-! ## Partial-sum interval consequences -/

/-- The executable sine Taylor hull contains the exact real sine value on
`[0,1]`. -/
theorem sinBound_contains {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains (sinBound x) (Real.sin (x : ℝ)) := by
  have h := sine_between_partials hx0 hx1
  constructor
  · have hmin : min (sinPartial x 19) (sinPartial x 20) ≤ sinPartial x 20 :=
      min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax : sinPartial x 19 ≤ max (sinPartial x 19) (sinPartial x 20) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-- The executable cosine Taylor hull contains the exact real cosine value on
`[0,1]`. -/
theorem cosBound_contains {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Contains (cosBound x) (Real.cos (x : ℝ)) := by
  have h := cosine_between_partials hx0 hx1
  constructor
  · have hmin : min (cosPartial x 19) (cosPartial x 20) ≤ cosPartial x 20 :=
      min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax : cosPartial x 19 ≤ max (cosPartial x 19) (cosPartial x 20) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-- Consecutive odd/even arctangent sums form a semantic interval. -/
theorem atanBound_contains {x : ℚ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (k : ℕ) :
    Contains (atanBound x (2 * k + 1) (2 * k + 2))
      (Real.arctan (x : ℝ)) := by
  have h := arctan_between_partials hx0 hx1 k
  constructor
  · have hmin :
        min (atanPartial x (2 * k + 1)) (atanPartial x (2 * k + 2)) ≤
          atanPartial x (2 * k + 2) := min_le_right _ _
    exact le_trans (by exact_mod_cast hmin) h.1
  · have hmax :
        atanPartial x (2 * k + 1) ≤
          max (atanPartial x (2 * k + 1)) (atanPartial x (2 * k + 2)) :=
      le_max_left _ _
    exact le_trans h.2 (by exact_mod_cast hmax)

/-! ## Machin identity and the declared interval for π -/

/-- The interval computed from the two exact arctangent Taylor certificates
contains the true value of `π`. -/
theorem machinPi_contains_pi : Contains machinPi Real.pi := by
  have h5 : Contains (atanBound (1 / 5) 43 44)
      (Real.arctan ((1 / 5 : ℚ) : ℝ)) := by
    simpa using (atanBound_contains (x := (1 / 5 : ℚ)) (by norm_num) (by norm_num) 21)
  have h239 : Contains (atanBound (1 / 239) 13 14)
      (Real.arctan ((1 / 239 : ℚ) : ℝ)) := by
    simpa using (atanBound_contains (x := (1 / 239 : ℚ)) (by norm_num) (by norm_num) 6)
  have h16 := RatInterval.contains_scale (a := (16 : ℚ)) h5
  have h4 := RatInterval.contains_scale (a := (4 : ℚ)) h239
  have hsub := RatInterval.contains_sub h16 h4
  have hMachin :
      (16 : ℝ) * Real.arctan (1 / 5) -
          4 * Real.arctan (1 / 239) = Real.pi := by
    nlinarith [Real.four_mul_arctan_inv_5_sub_arctan_inv_239]
  have hsub' : Contains machinPi
      ((16 : ℝ) * Real.arctan (1 / 5) -
        4 * Real.arctan (1 / 239)) := by
    simpa [machinPi, scale] using hsub
  exact hMachin ▸ hsub'

/-- The executable and proof-carrying manifests contain byte-for-byte equal
Machin intervals.  This is a finite rational normalization, not a numerical
assumption. -/
private theorem ratInterval_eq_of_endpoints {a b : RatInterval}
    (hlo : a.lo = b.lo) (hhi : a.hi = b.hi) : a = b := by
  cases a
  cases b
  simp_all

/-- Exact lower endpoint agreement between the executable Machin evaluation
and the frozen manifest.  This is a small bounded kernel computation (two
arctangent sums), deliberately separated from the old monolithic replay. -/
private theorem machinPi_lo_eq_manifest :
    machinPi.lo = CertificateManifest.machinPi.lo := by
  set_option maxRecDepth 100000 in
    decide +kernel

/-- Exact upper endpoint agreement between the executable Machin evaluation
and the frozen manifest. -/
private theorem machinPi_hi_eq_manifest :
    machinPi.hi = CertificateManifest.machinPi.hi := by
  set_option maxRecDepth 100000 in
    decide +kernel

theorem machinPi_eq_manifest :
    machinPi = CertificateManifest.machinPi :=
  ratInterval_eq_of_endpoints machinPi_lo_eq_manifest machinPi_hi_eq_manifest

/-- The executable declared interval agrees with the frozen manifest. -/
theorem piI_eq_manifest : piI = CertificateManifest.declaredPi := by
  apply ratInterval_eq_of_endpoints
  · set_option maxRecDepth 100000 in
      norm_num [piI, q, CertificateManifest.declaredPi, CertificateManifest.q]
  · set_option maxRecDepth 100000 in
      norm_num [piI, q, CertificateManifest.declaredPi, CertificateManifest.q]

/-- The exact interval used by every transcendental call encloses `Real.pi`. -/
theorem piI_contains_pi : Contains piI Real.pi := by
  have hm : Contains CertificateManifest.machinPi Real.pi := by
    simpa [machinPi_eq_manifest] using machinPi_contains_pi
  have hd : Contains CertificateManifest.declaredPi Real.pi :=
    RatInterval.contains_of_strictInsideB
      CertificateManifest.machin_inside_declared hm
  simpa [piI_eq_manifest] using hd

/-! ## Outward decimal rounding -/

/-- Fixed-decimal floor rounding never exceeds the input rational. -/
theorem floorDecimal_le (x : ℚ) (digits : ℕ := 60) :
    floorDecimal x digits ≤ x := by
  let s : ℚ := (10 : ℚ) ^ digits
  have hs : 0 < s := by positivity
  apply (div_le_iff₀ hs).2
  have hf : (((⌊x * s⌋ : ℤ) : ℚ)) ≤ x * s := Int.floor_le _
  simpa [floorDecimal, s] using hf

/-- Fixed-decimal ceiling rounding never lies below the input rational. -/
theorem le_ceilDecimal (x : ℚ) (digits : ℕ := 60) :
    x ≤ ceilDecimal x digits := by
  let s : ℚ := (10 : ℚ) ^ digits
  have hs : 0 < s := by positivity
  apply (le_div_iff₀ hs).2
  have hc : x * s ≤ (((⌈x * s⌉ : ℤ) : ℚ)) := Int.le_ceil _
  simpa [ceilDecimal, s] using hc

/-- The exact 60-decimal conversion is outward in real semantics. -/
theorem outwardDecimal_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) : Contains (outwardDecimal z) x := by
  constructor
  · exact le_trans (by exact_mod_cast floorDecimal_le z.lo (digits := 60)) hx.1
  · exact le_trans hx.2 (by exact_mod_cast le_ceilDecimal z.hi (digits := 60))

/-! ## Small-argument sine and cosine -/

/-- The small sine evaluator is sound whenever its whole input lies in
`[0, 9/10]`. -/
theorem sinSmall_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) (hz0 : 0 ≤ z.lo) (hz9 : z.hi ≤ 9 / 10) :
    Contains (sinSmall z) (Real.sin x) := by
  have hzvalid : z.lo ≤ z.hi := by exact_mod_cast RatInterval.valid_of_contains hx
  have hlo1 : z.lo ≤ 1 := le_trans hzvalid (le_trans hz9 (by norm_num))
  have hhi0 : 0 ≤ z.hi := le_trans hz0 hzvalid
  have hhi1 : z.hi ≤ 1 := le_trans hz9 (by norm_num)
  have hloBound := sinBound_contains hz0 hlo1
  have hhiBound := sinBound_contains hhi0 hhi1
  have hpi : (9 / 10 : ℝ) ≤ Real.pi / 2 := by
    nlinarith [Real.pi_gt_three]
  have hloMem : -(Real.pi / 2) ≤ (z.lo : ℝ) := by
    have : (0 : ℝ) ≤ (z.lo : ℝ) := by exact_mod_cast hz0
    nlinarith [Real.pi_pos]
  have hhiMem : (z.hi : ℝ) ≤ Real.pi / 2 := by
    have hz9R0 : (z.hi : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) :=
      (Rat.cast_le).2 hz9
    have hz9R : (z.hi : ℝ) ≤ (9 / 10 : ℝ) := by
      norm_num at hz9R0 ⊢
      exact hz9R0
    exact le_trans hz9R hpi
  have hmonoLo : Real.sin (z.lo : ℝ) ≤ Real.sin x :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hloMem (le_trans hx.2 hhiMem) hx.1
  have hxLower : -(Real.pi / 2) ≤ x := by
    have hneg : -(Real.pi / 2) ≤ (0 : ℝ) := by
      nlinarith [Real.pi_pos]
    exact le_trans hneg (le_trans (by exact_mod_cast hz0) hx.1)
  have hmonoHi : Real.sin x ≤ Real.sin (z.hi : ℝ) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hxLower hhiMem hx.2
  apply outwardDecimal_contains
  constructor
  · exact le_trans hloBound.1 hmonoLo
  · exact le_trans hmonoHi hhiBound.2

/-- The small cosine evaluator is sound whenever its whole input lies in
`[0, 9/10]`. -/
theorem cosSmall_contains {z : RatInterval} {x : ℝ}
    (hx : Contains z x) (hz0 : 0 ≤ z.lo) (hz9 : z.hi ≤ 9 / 10) :
    Contains (cosSmall z) (Real.cos x) := by
  have hzvalid : z.lo ≤ z.hi := by exact_mod_cast RatInterval.valid_of_contains hx
  have hlo1 : z.lo ≤ 1 := le_trans hzvalid (le_trans hz9 (by norm_num))
  have hhi0 : 0 ≤ z.hi := le_trans hz0 hzvalid
  have hhi1 : z.hi ≤ 1 := le_trans hz9 (by norm_num)
  have hloBound := cosBound_contains hz0 hlo1
  have hhiBound := cosBound_contains hhi0 hhi1
  have hpi : (9 / 10 : ℝ) ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hlo0 : (0 : ℝ) ≤ (z.lo : ℝ) := by exact_mod_cast hz0
  have hhiPi : (z.hi : ℝ) ≤ Real.pi := by
    have hz9R0 : (z.hi : ℝ) ≤ (((9 / 10 : ℚ) : ℝ)) :=
      (Rat.cast_le).2 hz9
    have hz9R : (z.hi : ℝ) ≤ (9 / 10 : ℝ) := by
      norm_num at hz9R0 ⊢
      exact hz9R0
    exact le_trans hz9R hpi
  have hx0 : (0 : ℝ) ≤ x := le_trans hlo0 hx.1
  have hxPi : x ≤ Real.pi := le_trans hx.2 hhiPi
  have hcosLower : Real.cos (z.hi : ℝ) ≤ Real.cos x :=
    Real.cos_le_cos_of_nonneg_of_le_pi hx0 hhiPi hx.2
  have hcosUpper : Real.cos x ≤ Real.cos (z.lo : ℝ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hlo0 hxPi hx.1
  apply outwardDecimal_contains
  constructor
  · exact le_trans hhiBound.1 hcosLower
  · exact le_trans hcosUpper hloBound.2

/-! ## Range reduction and fail-closed totality -/

/-- Physical clamping preserves every enclosed angle in `[0,π/2]`. -/
theorem physicalClamp_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (physicalClamp z) x := by
  have hpi := piI_contains_pi
  constructor
  · simpa [physicalClamp] using (max_le hx0 hz.1)
  · have hupper : x ≤ ((piI.hi / 2 : ℚ) : ℝ) := by
      have hhi : Real.pi ≤ (piI.hi : ℝ) := hpi.2
      have hxhi : x ≤ (piI.hi : ℝ) / 2 := by
        linarith [hxpi, hhi]
      have hcast : (((piI.hi / 2 : ℚ) : ℝ)) = (piI.hi : ℝ) / 2 := by
        norm_num
      rw [hcast]
      exact hxhi
    simpa [physicalClamp] using (le_min hupper hz.2)

/-- Complementary-angle range reduction encloses `π/2-x`. -/
theorem complementInterval_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (complementInterval z) (Real.pi / 2 - x) := by
  have hpi := piI_contains_pi
  constructor
  · have hzero : 0 ≤ Real.pi / 2 - x := by linarith
    have hdiff : ((piI.lo / 2 - z.hi : ℚ) : ℝ) ≤ Real.pi / 2 - x := by
      have hlo : (piI.lo : ℝ) ≤ Real.pi := hpi.1
      have hdiff' : (piI.lo : ℝ) / 2 - (z.hi : ℝ) ≤ Real.pi / 2 - x := by
        linarith [hlo, hz.2]
      have hcast : (((piI.lo / 2 - z.hi : ℚ) : ℝ)) =
          (piI.lo : ℝ) / 2 - (z.hi : ℝ) := by
        norm_num
      rw [hcast]
      exact hdiff'
    simpa [complementInterval] using (max_le hzero hdiff)
  · have hdiff : Real.pi / 2 - x ≤ ((piI.hi / 2 - z.lo : ℚ) : ℝ) := by
      have hhi : Real.pi ≤ (piI.hi : ℝ) := hpi.2
      have hdiff' : Real.pi / 2 - x ≤ (piI.hi : ℝ) / 2 - (z.lo : ℝ) := by
        linarith [hhi, hz.1]
      have hcast : (((piI.hi / 2 - z.lo : ℚ) : ℝ)) =
          (piI.hi : ℝ) / 2 - (z.lo : ℝ) := by
        norm_num
      rw [hcast]
      exact hdiff'
    simpa [complementInterval] using hdiff

/-- Universal fallback for sine. -/
theorem universal_contains_sin (x : ℝ) :
    Contains universalTrigInterval (Real.sin x) := by
  simpa [Contains, universalTrigInterval] using Real.sin_mem_Icc x

/-- Universal fallback for cosine. -/
theorem universal_contains_cos (x : ℝ) :
    Contains universalTrigInterval (Real.cos x) := by
  simpa [Contains, universalTrigInterval] using Real.cos_mem_Icc x

/-- Full soundness of the executable sine interval on the physical angular
range. -/
theorem sinI_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (sinI z) (Real.sin x) := by
  let w := physicalClamp z
  have hw : Contains w x := physicalClamp_contains hz hx0 hxpi
  have hw0 : 0 ≤ w.lo := by simp [w, physicalClamp]
  simp only [sinI]
  split_ifs with hsmall hcomp
  · exact sinSmall_contains hw hw0 hsmall
  · let y := complementInterval w
    have hy : Contains y (Real.pi / 2 - x) :=
      complementInterval_contains hw hx0 hxpi
    have hy0 : 0 ≤ y.lo := by simp [y, complementInterval]
    have hcy := cosSmall_contains hy hy0 hcomp
    simpa [Real.cos_pi_div_two_sub] using hcy
  · exact universal_contains_sin x

/-- Full soundness of the executable cosine interval on the physical angular
range. -/
theorem cosI_contains {z : RatInterval} {x : ℝ}
    (hz : Contains z x) (hx0 : 0 ≤ x) (hxpi : x ≤ Real.pi / 2) :
    Contains (cosI z) (Real.cos x) := by
  let w := physicalClamp z
  have hw : Contains w x := physicalClamp_contains hz hx0 hxpi
  have hw0 : 0 ≤ w.lo := by simp [w, physicalClamp]
  simp only [cosI]
  split_ifs with hsmall hcomp
  · exact cosSmall_contains hw hw0 hsmall
  · let y := complementInterval w
    have hy : Contains y (Real.pi / 2 - x) :=
      complementInterval_contains hw hx0 hxpi
    have hy0 : 0 ≤ y.lo := by simp [y, complementInterval]
    have hsy := sinSmall_contains hy hy0 hcomp
    simpa [Real.sin_pi_div_two_sub] using hsy
  · exact universal_contains_cos x

end GerverSofa.ExactReplay

namespace GerverSofa

open RatInterval

end GerverSofa
