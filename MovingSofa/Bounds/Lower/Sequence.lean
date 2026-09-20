import MovingSofa.Bounds.Arm.Regularity
import MovingSofa.Bounds.Lower.Profile

noncomputable section

namespace MovingSofa

def nonnegativeLowerBoundProfile (c : Set.Icc (0 : ℝ) 1) :
    C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal) where
  toFun x := Real.toNNReal (lowerBoundProfile c x)
  continuous_toFun := continuous_real_toNNReal.comp (lowerBoundProfile c).continuous

theorem armIntegralOperator_monotone
    (f g : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal))
    (hfg : ∀ x, f x ≤ g x) :
    ∀ x, armIntegralOperator f x ≤ armIntegralOperator g x := by
  have hc (k : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal)) :
      Continuous (fun u : ℝ ↦ magicFunctions.2
        (k (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))) := by
    unfold magicFunctions
    fun_prop
  intro x
  change (1 : ℝ) + _ ≤ 1 + _
  apply add_le_add le_rfl
  exact intervalIntegral.integral_mono x.property.1
    ((hc f).intervalIntegrable _ _) ((hc g).intervalIntegrable _ _)
    (fun u ↦ magicFunctions_snd_monotone (hfg _))

private theorem magicFunction_eq_affine_of_mem_Icc (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    magicFunctions.2 (Real.toNNReal y) = 3 / 2 * y - 1 := by
  simp [magicFunctions, abs_of_nonpos (by linarith : y - 1 ≤ 0),
    Real.toNNReal_of_nonneg hy0]
  rw [max_eq_right (by linarith)]
  ring

private theorem armIntegralOperator_nonnegativeLowerBoundProfile_eq
    (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 2 / 3)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
  armIntegralOperator (nonnegativeLowerBoundProfile ⟨c, ⟨hc, by linarith⟩⟩) x =
    1 - (x : ℝ) + (3 / 2) *
      (∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c) := by
  have hintegrand (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) (x : ℝ)) :
      magicFunctions.2
          ((nonnegativeLowerBoundProfile ⟨c, hc, by linarith⟩)
            (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u))) =
        3 / 2 * max (1 - (Real.pi / 2 - u)) c - 1 := by
    rw [Set.uIcc_of_le x.property.1] at hu
    have hu0 : 0 ≤ u := hu.1
    have huT : Real.pi / 2 - u ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [hu.2, x.property.2, Real.pi_pos]
    rw [Set.projIcc_of_mem (by positivity) huT]
    apply magicFunction_eq_affine_of_mem_Icc
    · exact le_max_of_le_right hc
    · apply max_le
      · linarith [huT.1]
      · linarith
  change
    (1 + ∫ u in (0 : ℝ)..(x : ℝ),
        magicFunctions.2
          ((nonnegativeLowerBoundProfile ⟨c, ⟨hc, by linarith⟩⟩)
            (Set.projIcc 0 (Real.pi / 2) (by positivity) (Real.pi / 2 - u)))) = _
  have hcont : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := by
    fun_prop
  rw [intervalIntegral.integral_congr (fun u hu ↦ hintegrand u hu)]
  have hsplit :
      (∫ u in (0 : ℝ)..(x : ℝ), 3 / 2 * max (1 - (Real.pi / 2 - u)) c - 1) =
        (3 / 2) * (∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c) - (x : ℝ) := by
    calc
      _ = (∫ u in (0 : ℝ)..(x : ℝ), 3 / 2 * max (1 - (Real.pi / 2 - u)) c) -
            ∫ u in (0 : ℝ)..(x : ℝ), (1 : ℝ) := by
        rw [intervalIntegral.integral_sub ((hcont.const_mul (3 / 2)).intervalIntegrable _ _)
          intervalIntegrable_const]
      _ = _ := by
        nth_rewrite 1 [intervalIntegral.integral_const_mul]
        nth_rewrite 1 [intervalIntegral.integral_const]
        simp only [smul_eq_mul, sub_zero]
        ring
  rw [hsplit]
  ring

private theorem split_le_integral_lowerBoundProfile (c : ℝ) (hc : 0 ≤ c)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) (hsx : Real.pi / 2 - 1 + c ≤ (x : ℝ)) :
    c * (Real.pi / 2 - 1 + c) + (((x : ℝ) + 1 - Real.pi / 2) ^ 2 - c ^ 2) / 2 ≤
      ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
  have hcont : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := by
    fun_prop
  have hlin (s t : ℝ) :
      (∫ u in s..t, 1 - Real.pi / 2 + u) =
        ((t + 1 - Real.pi / 2) ^ 2 - (s + 1 - Real.pi / 2) ^ 2) / 2 := by
    rw [intervalIntegral.integral_add (f := fun _ : ℝ ↦ 1 - Real.pi / 2)
      (g := fun u : ℝ ↦ u)
      (a := s) (b := t) (intervalIntegrable_const)
      (continuous_id.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, integral_id]
    ring
  let s : ℝ := Real.pi / 2 - 1 + c
  have hq : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := hcont
  have hfirst := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
    (f := fun _ : ℝ ↦ c) (g := fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c)
    (a := (0 : ℝ)) (b := s) (by dsimp [s]; linarith [Real.pi_gt_three])
    (intervalIntegrable_const (μ := MeasureTheory.volume)) (hq.intervalIntegrable _ _)
    (fun u ↦ (le_max_right _ _ : c ≤ max (1 - (Real.pi / 2 - u)) c))
  have hcontlin : Continuous (fun u : ℝ ↦ 1 - Real.pi / 2 + u) := by fun_prop
  have hsecond := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
    (f := fun u : ℝ ↦ 1 - Real.pi / 2 + u)
    (g := fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) (a := s) (b := (x : ℝ)) hsx
    (hcontlin.intervalIntegrable _ _) (hq.intervalIntegrable _ _)
    (fun u ↦ by
      change 1 - Real.pi / 2 + u ≤ max (1 - (Real.pi / 2 - u)) c
      have hu : 1 - Real.pi / 2 + u = 1 - (Real.pi / 2 - u) := by ring
      exact hu.le.trans (le_max_left _ _))
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hq.intervalIntegrable (0 : ℝ) s) (hq.intervalIntegrable s (x : ℝ))
  rw [hlin s (x : ℝ)] at hsecond
  have hfirst' : c * s ≤ ∫ u in (0 : ℝ)..s,
      max (1 - (Real.pi / 2 - u)) c := by
    convert hfirst using 1
    simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  have hsum : c * s + ∫ u in s..(x : ℝ), max (1 - (Real.pi / 2 - u)) c ≤
      ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
    calc
      _ ≤ (∫ u in (0 : ℝ)..s, max (1 - (Real.pi / 2 - u)) c) +
          ∫ u in s..(x : ℝ), max (1 - (Real.pi / 2 - u)) c :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hfirst' (∫ u in s..(x : ℝ),
              max (1 - (Real.pi / 2 - u)) c)
      _ = _ := hadd
  calc
    c * s + (((x : ℝ) + 1 - Real.pi / 2) ^ 2 - c ^ 2) / 2 ≤
        c * s + ∫ u in s..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
      dsimp [s] at *
      nlinarith [hsecond]
    _ ≤ _ := hsum

theorem armIntegralOperator_profile_step (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 2 / 3) :
    ∀ x, lowerBoundProfile ⟨c + 1 / 12, by constructor <;> linarith⟩ x ≤
      armIntegralOperator
        (nonnegativeLowerBoundProfile ⟨c, hc, by linarith⟩) x := by
  intro x
  rw [armIntegralOperator_nonnegativeLowerBoundProfile_eq c hc hc' x]
  simp only [lowerBoundProfile, ContinuousMap.coe_mk]
  have hcont : Continuous (fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) := by
    fun_prop
  have hI : c * (x : ℝ) ≤
      ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
    have h := intervalIntegral.integral_mono (μ := MeasureTheory.volume)
      (f := fun _ : ℝ ↦ c) (g := fun u : ℝ ↦ max (1 - (Real.pi / 2 - u)) c) x.property.1
      (intervalIntegrable_const (μ := MeasureTheory.volume)) (hcont.intervalIntegrable _ _)
      (fun u ↦ (le_max_right _ _ : c ≤ max (1 - (Real.pi / 2 - u)) c))
    convert h using 1
    simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  let s : ℝ := Real.pi / 2 - 1 + c
  apply max_le
  · have hnonneg : 0 ≤ ∫ u in (0 : ℝ)..(x : ℝ), max (1 - (Real.pi / 2 - u)) c := by
      exact intervalIntegral.integral_nonneg x.property.1
        (fun _ _ ↦ le_max_of_le_right hc)
    linarith
  · have hpi : Real.pi ≤ 22 / 7 := by linarith [Real.pi_lt_d20]
    have hmul : 0 ≤ (22 / 7 - Real.pi) * (2 / 3 - c) :=
      mul_nonneg (sub_nonneg.mpr hpi) (sub_nonneg.mpr hc')
    by_cases hsx : s ≤ (x : ℝ)
    · have hs := split_le_integral_lowerBoundProfile c hc x hsx
      nlinarith [sq_nonneg ((x : ℝ) - (Real.pi / 2 - 1 / 3)),
        sq_nonneg (c - 2 / 21), hmul]
    · have hxs : (x : ℝ) ≤ s := le_of_not_ge hsx
      have hprod : 0 ≤ (s - (x : ℝ)) * (1 - 3 / 2 * c) :=
        mul_nonneg (sub_nonneg.mpr hxs) (by linarith)
      dsimp [s] at hxs hprod ⊢
      nlinarith [hI, sq_nonneg (c - 7 / 6 + Real.pi / 4), hprod, hmul]

private theorem armIntegralOperator_le_sequence_succ (n : ℕ)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    armIntegralOperator (armLowerBoundSequence n) x ≤
      (armLowerBoundSequence (n + 1) x : ℝ) := by
  exact (Real.le_coe_toNNReal _).trans (NNReal.coe_le_coe.mpr (le_max_right _ _))

private theorem lowerBoundProfile_zero_le_one
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    lowerBoundProfile ⟨0, by constructor <;> norm_num⟩ x ≤
      (armLowerBoundSequence 1 x : ℝ) := by
  change max (1 - (x : ℝ)) 0 ≤ _
  simp only [armLowerBoundSequence, ContinuousMap.coe_mk, NNReal.coe_max,
    NNReal.coe_zero]
  simp [armIntegralOperator, magicFunctions, intervalIntegral.integral_const]
  by_cases hx : 1 ≤ (x : ℝ)
  · exact Or.inr hx
  · left
    rw [max_eq_left (by linarith)]
    linarith

private theorem lowerBoundProfile_le_sequence_succ (n : ℕ) (hn : n ≤ 9)
    (x : Set.Icc (0 : ℝ) (Real.pi / 2)) :
    lowerBoundProfile ⟨(n : ℝ) / 12, by
      have hnR : (n : ℝ) ≤ 9 := by exact_mod_cast hn
      constructor
      · positivity
      · linarith⟩ x ≤
      (armLowerBoundSequence (n + 1) x : ℝ) := by
  induction n generalizing x with
  | zero => simpa [lowerBoundProfile] using lowerBoundProfile_zero_le_one x
  | succ n ih =>
      have hn' : n ≤ 9 := by omega
      have hn8 : n ≤ 8 := by omega
      have hn8r : (n : ℝ) ≤ 8 := by exact_mod_cast hn8
      have hprof := armIntegralOperator_profile_step ((n : ℝ) / 12) (by positivity)
        (by nlinarith)
      have hmon := armIntegralOperator_monotone
        (nonnegativeLowerBoundProfile ⟨(n : ℝ) / 12, by
          have hnR : (n : ℝ) ≤ 9 := by exact_mod_cast hn'
          constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩)
        (armLowerBoundSequence (n + 1)) (by
          intro y
          exact Real.toNNReal_le_iff_le_coe.mpr (ih hn' y))
      have hop : lowerBoundProfile ⟨(n + 1) / 12, by
          have hnR : ((n + 1 : ℕ) : ℝ) ≤ 9 := by exact_mod_cast hn
          constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩ x ≤
          armIntegralOperator (armLowerBoundSequence (n + 1)) x := by
        have heq : (n : ℝ) / 12 + 1 / 12 = (n + 1) / 12 := by ring
        simpa only [heq] using (hprof x).trans (hmon x)
      simpa only [Nat.cast_add, Nat.cast_one] using
        hop.trans (armIntegralOperator_le_sequence_succ (n + 1) x)

theorem armLowerBoundSequence_threshold :
    ∀ x : Set.Icc (0 : ℝ) (Real.pi / 2), 0 < (x : ℝ) →
      1 < (armLowerBoundSequence 11 x : ℝ) := by
  intro x hx
  let f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal) := ⟨fun _ ↦ 3 / 4, continuous_const⟩
  have hbound (y : Set.Icc (0 : ℝ) (Real.pi / 2)) : f y ≤ armLowerBoundSequence 10 y := by
    have h := lowerBoundProfile_le_sequence_succ 9 (by omega) y
    have hreal : (3 / 4 : ℝ) ≤ (armLowerBoundSequence 10 y : ℝ) := by
      norm_num [lowerBoundProfile] at h
      exact h.2
    exact_mod_cast hreal
  have hmon := armIntegralOperator_monotone f (armLowerBoundSequence 10) hbound x
  have hconst : armIntegralOperator f x = 1 + (x : ℝ) / 8 := by
    norm_num [armIntegralOperator, f, magicFunctions, intervalIntegral.integral_const]
  rw [hconst] at hmon
  have hstep := armIntegralOperator_le_sequence_succ 10 x
  linarith

/-- The mirror reflection turns the right arm length function of a nondegenerate right-angle cap
into the reflected left arm length function of the original cap. At the two endpoints the
prescribed one-sided conventions match: `f⁺` of the mirror at `π / 2 - t = 0` is the terminal
`g⁻`, and `f⁻` of the mirror at `π / 2` is the prescribed `g⁺` at `0`. -/
private theorem nondegenerateCapData_arm_mirror (K P : RightAngleCapSpace)
    (hP : (P.val : Set Point) = mirrorReflection (Real.pi / 2) '' (K.val : Set Point))
    (hDK : ∃ r s, HasCapDensities K r s) (hDP : ∃ r s, HasCapDensities P r s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (nondegenerateCapData P hDP).2.1
        ⟨Real.pi / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩ =
      (nondegenerateCapData K hDK).2.2 ⟨t, ht⟩ := by
  have hT : Real.pi / 2 - t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨h1, h2, -, -⟩ := tangentArms_mirror K P hP (Real.pi / 2 - t) hT
  rw [show Real.pi / 2 - (Real.pi / 2 - t) = t by ring] at h1 h2
  simp only [nondegenerateCapData]
  split_ifs with hcase
  · exact h2
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 fun h ↦ hcase (by rw [← h]; ring)
    rw [h1]
    exact ((capDensities_contact_eq K hDK).2 t ⟨htpos, ht.2⟩).2.symm

/-- The integral operator is a lower bound for the right arm length function of a balanced
maximum cap, for every continuous profile `f` with `f(π / 2 - u) ≤ g_K(u)`. Absolute continuity
of `f_K` on `[0, t]` turns it into the integral of its derivative, the differential inequality
`f_K' ≥ m₀ ∘ g_K` bounds that derivative from below almost everywhere, and `m₀` is nondecreasing;
the initial value `f_K(0) = 1` supplies the constant term of the operator. -/
private theorem armIntegralOperator_le_nondegenerateCapData_right (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) (hD : ∃ r s, HasCapDensities K r s)
    (f : C(Set.Icc (0 : ℝ) (Real.pi / 2), NNReal))
    (hf : ∀ (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
      (f ⟨Real.pi / 2 - u, ⟨by linarith [hu.2], by linarith [hu.1]⟩⟩ : ℝ) ≤
        (nondegenerateCapData K hD).2.2 ⟨u, hu⟩)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    armIntegralOperator f ⟨t, ht⟩ ≤ (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ := by
  have hTle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  obtain ⟨hD', hAC, hderiv⟩ := balancedMaximumCap_arm_regularity K hK
  -- proof irrelevance retypes the regularity statement for the witness `hD`
  have hACf : AbsolutelyContinuousOnInterval
      (extendIntervalScalar (nondegenerateCapData K hD).2.1) 0 (Real.pi / 2) := hAC
  have hderivf : ∀ᵐ u ∂MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)),
      magicFunctions.2
          (Real.toNNReal (extendIntervalScalar (nondegenerateCapData K hD).2.2 u)) ≤
        deriv (extendIntervalScalar (nondegenerateCapData K hD).2.1) u := hderiv
  have hACt := hACf.mono (by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hTle]
    exact Set.Icc_subset_Icc le_rfl ht.2)
  have hFTC := hACt.integral_deriv_eq_sub
  have hF0 : extendIntervalScalar (nondegenerateCapData K hD).2.1 0 = 1 := by
    rw [extendIntervalScalar_of_mem _ ⟨le_rfl, hTle⟩]
    simp only [nondegenerateCapData,
      ite_eq_right (ne_of_lt (show (0 : ℝ) < Real.pi / 2 by positivity))]
    exact tangentArmLengths_right_zero_eq_one K hD
  have hFt : extendIntervalScalar (nondegenerateCapData K hD).2.1 t =
      (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ := extendIntervalScalar_of_mem _ ht
  have hcont : Continuous (fun u : ℝ ↦ magicFunctions.2
      (f (Set.projIcc 0 (Real.pi / 2) hTle (Real.pi / 2 - u)))) := by
    unfold magicFunctions
    fun_prop
  -- the integrand of the operator is dominated by the derivative almost everywhere
  have hae : (fun u : ℝ ↦ magicFunctions.2
        (f (Set.projIcc 0 (Real.pi / 2) hTle (Real.pi / 2 - u)))) ≤ᵐ[
      MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)]
      deriv (extendIntervalScalar (nondegenerateCapData K hD).2.1) := by
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    filter_upwards [MeasureTheory.ae_restrict_of_ae_restrict_of_subset
        (Set.Ioo_subset_Ioo le_rfl ht.2) hderivf,
      MeasureTheory.ae_restrict_mem measurableSet_Ioo] with u h1 h2
    refine le_trans ?_ h1
    have humem : u ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨h2.1.le, h2.2.le.trans ht.2⟩
    have hTu : Real.pi / 2 - u ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [humem.2], by linarith [humem.1]⟩
    apply magicFunctions_snd_monotone
    rw [Set.projIcc_of_mem hTle hTu, extendIntervalScalar_of_mem _ humem,
      Real.le_toNNReal_iff_coe_le (nondegenerateCapData_arm_nonneg K hD ⟨u, humem⟩).2]
    exact hf u humem
  have hmono := intervalIntegral.integral_mono_ae_restrict ht.1
    (hcont.intervalIntegrable _ _) hACt.intervalIntegrable_deriv hae
  have hval : armIntegralOperator f ⟨t, ht⟩ =
      1 + ∫ u in (0 : ℝ)..t, magicFunctions.2
        (f (Set.projIcc 0 (Real.pi / 2) hTle (Real.pi / 2 - u))) := rfl
  rw [hval, ← hFt]
  linarith [hFTC, hmono, hF0]

/-- The simultaneous lower bound for the two arm length functions of a balanced maximum
right-angle cap. The induction on `n` quantifies over every balanced maximum cap, because the
bound for the left arm is obtained by applying the bound for the right arm to the mirror cap. -/
private theorem armLowerBoundSequence_le_nondegenerateCapData (n : ℕ) :
    ∀ (K : RightAngleCapSpace), IsBalancedMaximumCap K →
      ∀ (hD : ∃ r s, HasCapDensities K r s) (t : ℝ)
        (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
        (armLowerBoundSequence n ⟨t, ht⟩ : ℝ) ≤
          (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ ∧
        (armLowerBoundSequence n
            ⟨Real.pi / 2 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩⟩ : ℝ) ≤
          (nondegenerateCapData K hD).2.2 ⟨t, ht⟩ := by
  induction n with
  | zero =>
      intro K hK hD t ht
      simpa only [armLowerBoundSequence, ContinuousMap.coe_mk, NNReal.coe_zero] using
        nondegenerateCapData_arm_nonneg K hD ⟨t, ht⟩
  | succ n ih =>
      -- the bound for the right arm, proved for every balanced maximum cap at once
      have hfirst : ∀ (K : RightAngleCapSpace), IsBalancedMaximumCap K →
          ∀ (hD : ∃ r s, HasCapDensities K r s) (t : ℝ)
            (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)),
            (armLowerBoundSequence (n + 1) ⟨t, ht⟩ : ℝ) ≤
              (nondegenerateCapData K hD).2.1 ⟨t, ht⟩ := by
        intro K hK hD t ht
        have hop := armIntegralOperator_le_nondegenerateCapData_right K hK hD
          (armLowerBoundSequence n) (fun u hu ↦ (ih K hK hD u hu).2) t ht
        simp only [armLowerBoundSequence, ContinuousMap.coe_mk, NNReal.coe_max,
          Real.coe_toNNReal']
        exact max_le (ih K hK hD t ht).1
          (max_le hop (nondegenerateCapData_arm_nonneg K hD ⟨t, ht⟩).1)
      intro K hK hD t ht
      refine ⟨hfirst K hK hD t ht, ?_⟩
      obtain ⟨P, hP, hPbal⟩ := balancedMaximumCap_mirror K hK
      obtain ⟨r, s, hrs, -⟩ := balancedMaximumCap_hasDensities P hPbal
      have hT : Real.pi / 2 - t ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
        ⟨by linarith [ht.2], by linarith [ht.1]⟩
      rw [← nondegenerateCapData_arm_mirror K P hP hD ⟨r, s, hrs⟩ t ht]
      exact hfirst P hPbal ⟨r, s, hrs⟩ (Real.pi / 2 - t) hT

theorem balancedMaximumCap_sequence_bound (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ hD : ∃ r s, HasCapDensities K r s,
      ∀ (n : ℕ) (t : Set.Icc (0 : ℝ) (Real.pi / 2)),
        (armLowerBoundSequence n t : ℝ) ≤ (nondegenerateCapData K hD).2.1 t ∧
        (armLowerBoundSequence n
          ⟨Real.pi / 2 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩ : ℝ) ≤
          (nondegenerateCapData K hD).2.2 t := by
  obtain ⟨r, s, hrs, -⟩ := balancedMaximumCap_hasDensities K hK
  refine ⟨⟨r, s, hrs⟩, fun n t ↦ ?_⟩
  exact armLowerBoundSequence_le_nondegenerateCapData n K hK ⟨r, s, hrs⟩ t t.property

theorem balancedMaximumCap_arm_gt_one (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ hD : ∃ r s, HasCapDensities K r s,
      (∀ t : Set.Icc (0 : ℝ) (Real.pi / 2), 0 < (t : ℝ) →
        1 < (nondegenerateCapData K hD).2.1 t) ∧
      (∀ t : Set.Icc (0 : ℝ) (Real.pi / 2), (t : ℝ) < Real.pi / 2 →
        1 < (nondegenerateCapData K hD).2.2 t) := by
  obtain ⟨hD, hbound⟩ := balancedMaximumCap_sequence_bound K hK
  refine ⟨hD, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · exact (armLowerBoundSequence_threshold t ht).trans_le (hbound 11 t).1
  · have hT : Real.pi / 2 - (t : ℝ) ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      constructor <;> linarith [t.property.1, t.property.2]
    exact (armLowerBoundSequence_threshold ⟨Real.pi / 2 - (t : ℝ), hT⟩
      (by linarith)).trans_le (hbound 11 t).2

end MovingSofa
