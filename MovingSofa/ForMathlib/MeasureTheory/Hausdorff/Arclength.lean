import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Order.Hom.Set

noncomputable section

open Filter
open scoped Topology

open MeasureTheory

namespace MeasureTheory

private theorem dist_le_hausdorffMeasure_image_Icc_of_continuousOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b) (hγ : ContinuousOn γ (Set.Icc a b)) :
    ENNReal.ofReal (dist (γ a) (γ b)) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by
  by_cases heq : γ a = γ b
  · simp [heq]
  let n : (EuclideanSpace ℝ (Fin 2)) := ‖γ b - γ a‖⁻¹ • (γ b - γ a)
  let f : (EuclideanSpace ℝ (Fin 2)) → ℝ := fun p ↦ inner ℝ (p - γ a) n
  have hnorm : ‖n‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm heq)))]
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    rw [NNReal.coe_one, one_mul, Real.dist_eq]
    change |inner ℝ (p - γ a) n - inner ℝ (q - γ a) n| ≤ dist p q
    rw [← inner_sub_left]
    have h := abs_real_inner_le_norm ((p - γ a) - (q - γ a)) n
    rw [hnorm, mul_one, show (p - γ a) - (q - γ a) = p - q by module,
      ← dist_eq_norm] at h
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hfa : f (γ a) = 0 := by simp [f]
  have hfb : f (γ b) = dist (γ a) (γ b) := by
    dsimp only [f, n]
    rw [inner_smul_right, real_inner_self_eq_norm_sq, dist_eq_norm, inv_mul_eq_div,
      norm_sub_rev]
    field_simp [norm_ne_zero_iff.mpr (sub_ne_zero.mpr (Ne.symm heq))]
  have hinterval : Set.Icc 0 (dist (γ a) (γ b)) ⊆ f '' (γ '' Set.Icc a b) := by
    rw [← hfa, ← hfb]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc hab (hf.continuous.comp_continuousOn hγ) hy
    exact ⟨γ x, ⟨x, hx, rfl⟩, hxy⟩
  calc
    ENNReal.ofReal (dist (γ a) (γ b)) =
        Measure.hausdorffMeasure 1 (Set.Icc 0 (dist (γ a) (γ b))) := by
      rw [MeasureTheory.hausdorffMeasure_real, Real.volume_Icc]
      simp
    _ ≤ Measure.hausdorffMeasure 1 (f '' (γ '' Set.Icc a b)) := measure_mono hinterval
    _ ≤ ((1 : NNReal) : ENNReal) ^ (1 : ℝ) *
        Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) :=
      hf.hausdorffMeasure_image_le (by norm_num) _
    _ = Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by simp

private theorem hausdorffMeasure_image_Icc_add_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a c) +
        Measure.hausdorffMeasure 1 (γ '' Set.Icc c b) := by
  let μ : Measure (EuclideanSpace ℝ (Fin 2)) := Measure.hausdorffMeasure 1
  have hleft : Set.Icc a c ⊆ Set.Icc a b := Set.Icc_subset_Icc_right hcb
  have hright : Set.Icc c b ⊆ Set.Icc a b := Set.Icc_subset_Icc_left hac
  have hinter : γ '' Set.Icc a c ∩ γ '' Set.Icc c b ⊆ {γ c} := by
    rintro p ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hxeq : x = y := hinj (hleft hx) (hright hy) hxy.symm
    have : x = c := le_antisymm hx.2 (hxeq ▸ hy.1)
    simp [this]
  have hnull : μ (γ '' Set.Icc a c ∩ γ '' Set.Icc c b) = 0 := by
    let _ := Measure.nullSingletonClass_hausdorff (EuclideanSpace ℝ (Fin 2)) (by norm_num : (0 : ℝ) < 1)
    exact measure_mono_null hinter (measure_singleton (γ c))
  have hmeas : MeasurableSet (γ '' Set.Icc c b) :=
    (isCompact_Icc.image_of_continuousOn (hγ.mono hright)).measurableSet
  have hunion : γ '' Set.Icc a b = γ '' Set.Icc a c ∪ γ '' Set.Icc c b := by
    rw [← Set.image_union, Set.Icc_union_Icc_eq_Icc hac hcb]
  rw [hunion]
  exact measure_union₀ hmeas.nullMeasurableSet hnull

private theorem hausdorff_partition_sum_le (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) (u : ℕ → ℝ) (n : ℕ)
    (hu : Monotone u) (hγ : ContinuousOn γ (Set.Icc (u 0) (u n)))
    (hinj : Set.InjOn γ (Set.Icc (u 0) (u n))) :
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 0) (u n)) := by
  induction n generalizing u with
  | zero => simp
  | succ n ih =>
      let v : ℕ → ℝ := fun i ↦ u (i + 1)
      have huv : u 0 ≤ u 1 := hu (Nat.zero_le 1)
      have hvn : u 1 ≤ u (n + 1) := hu (Nat.succ_le_succ (Nat.zero_le n))
      have hwhole : u 0 ≤ u (n + 1) := huv.trans hvn
      have hleft : Set.Icc (u 0) (u 1) ⊆ Set.Icc (u 0) (u (n + 1)) :=
        Set.Icc_subset_Icc_right hvn
      have hright : Set.Icc (u 1) (u (n + 1)) ⊆ Set.Icc (u 0) (u (n + 1)) :=
        Set.Icc_subset_Icc_left huv
      rw [Finset.sum_range_succ']
      have htail : (∑ i ∈ Finset.range n,
          edist (γ (u (i + 1 + 1))) (γ (u (i + 1)))) ≤
          Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 1) (u (n + 1))) := by
        simpa [v, Nat.add_assoc] using ih v (fun _ _ hij ↦ hu (Nat.add_le_add_right hij 1))
          (hγ.mono hright) (hinj.mono hright)
      have hfirst := dist_le_hausdorffMeasure_image_Icc_of_continuousOn γ huv
        (hγ.mono hleft)
      rw [edist_dist]
      rw [hausdorffMeasure_image_Icc_add_of_injectiveOn γ huv hvn hγ hinj]
      simpa [add_comm, dist_comm] using add_le_add htail hfirst

private theorem eVariationOn_le_hausdorffMeasure_image_Icc_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤
      Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) := by
  rw [eVariationOn]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨n, u, hu, hus⟩
  have hu0 := hus 0
  have hun := hus n
  have hsub : Set.Icc (u 0) (u n) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hu0.1 hun.2
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        Measure.hausdorffMeasure 1 (γ '' Set.Icc (u 0) (u n)) :=
      hausdorff_partition_sum_le γ u n hu (hγ.mono hsub) (hinj.mono hsub)
    _ ≤ Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) :=
      measure_mono (Set.image_mono hsub)

private theorem hausdorffMeasure_image_Icc_le_eVariationOn_of_injectiveOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≤
      eVariationOn γ (Set.Icc a b) := by
  let ℓ : ℝ → ℝ := variationOnFromTo γ (Set.Icc a b) a
  have hℓstrict : StrictMonoOn ℓ (Set.Icc a b) := by
    intro x hx y hy hxy
    have hnonneg : 0 ≤ variationOnFromTo γ (Set.Icc a b) x y :=
      variationOnFromTo.nonneg_of_le γ _ hxy.le
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy
    have hle : ℓ x ≤ ℓ y := by dsimp only [ℓ]; linarith
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hzero : variationOnFromTo γ (Set.Icc a b) x y = 0 := by
      dsimp only [ℓ] at heq
      linarith
    have hed := variationOnFromTo.edist_zero_of_eq_zero hBV.locallyBoundedVariationOn
      hx hy hzero
    have hxy' : γ x = γ y := edist_eq_zero.mp hed
    exact hxy.ne (hinj hx hy hxy')
  let iso := hℓstrict.orderIso ℓ (Set.Icc a b)
  let Γ : (ℓ '' Set.Icc a b) → (EuclideanSpace ℝ (Fin 2)) := fun z ↦ γ (iso.symm z)
  have hΓle : ∀ z w : (ℓ '' Set.Icc a b), z ≤ w →
      dist (Γ z) (Γ w) ≤ dist z w := by
    intro z w hzw
    have hxy : (iso.symm z : ℝ) ≤ iso.symm w := iso.symm.monotone hzw
    have hvar : dist (γ (iso.symm z)) (γ (iso.symm w)) ≤
        variationOnFromTo γ (Set.Icc a b) (iso.symm z) (iso.symm w) := by
      rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
      apply ENNReal.toReal_mono
        (hBV.locallyBoundedVariationOn _ _ (iso.symm z).property (iso.symm w).property)
      exact eVariationOn.edist_le γ
        ⟨(iso.symm z).property, le_rfl, hxy⟩
        ⟨(iso.symm w).property, hxy, le_rfl⟩
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) (iso.symm z).property (iso.symm w).property
    change dist (γ (iso.symm z)) (γ (iso.symm w)) ≤ dist (z : ℝ) (w : ℝ)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (show (z : ℝ) ≤ (w : ℝ) from hzw))]
    have hz : ℓ (iso.symm z) = z := congrArg Subtype.val (iso.apply_symm_apply z)
    have hw : ℓ (iso.symm w) = w := congrArg Subtype.val (iso.apply_symm_apply w)
    dsimp only [ℓ] at hz hw
    linarith
  have hΓ : LipschitzWith 1 Γ := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simp only [NNReal.coe_one, one_mul]
    rcases le_total z w with hzw | hwz
    · exact hΓle z w hzw
    · simpa only [dist_comm] using hΓle w z hwz
  have himage : Γ '' Set.univ = γ '' Set.Icc a b := by
    ext p
    constructor
    · rintro ⟨z, _, rfl⟩
      exact ⟨iso.symm z, (iso.symm z).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨iso ⟨x, hx⟩, Set.mem_univ _, ?_⟩
      simp [Γ]
  have hval : (Subtype.val : (ℓ '' Set.Icc a b) → ℝ) '' Set.univ =
      ℓ '' Set.Icc a b := by
    ext x
    constructor
    · rintro ⟨z, _, rfl⟩; exact z.property
    · intro hx; exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  have hdom : Measure.hausdorffMeasure 1 (Set.univ : Set (ℓ '' Set.Icc a b)) =
      Measure.hausdorffMeasure 1 (ℓ '' Set.Icc a b) := by
    conv_rhs => rw [← hval]
    have hi : Isometry (Subtype.val : (ℓ '' Set.Icc a b) → ℝ) := fun _ _ ↦ rfl
    exact (hi.hausdorffMeasure_image (Or.inl (by norm_num : (0 : ℝ) ≤ 1)) _).symm
  have hsub : ℓ '' Set.Icc a b ⊆
      Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨variationOnFromTo.nonneg_of_le γ _ hx.1,
      (le_abs_self _).trans (variationOnFromTo.abs_le_eVariationOn hBV)⟩
  calc
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
        Measure.hausdorffMeasure 1 (Γ '' Set.univ) := congrArg _ himage.symm
    _ ≤ Measure.hausdorffMeasure 1 (Set.univ : Set (ℓ '' Set.Icc a b)) := by
      simpa using hΓ.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) Set.univ
    _ = Measure.hausdorffMeasure 1 (ℓ '' Set.Icc a b) := hdom
    _ ≤ Measure.hausdorffMeasure 1
        (Set.Icc 0 (eVariationOn γ (Set.Icc a b)).toReal) := measure_mono hsub
    _ = eVariationOn γ (Set.Icc a b) := by
      rw [hausdorffMeasure_real, Real.volume_Icc, sub_zero, ENNReal.ofReal_toReal hBV]


/-- Hausdorff length of a continuous injective arc is its total variation. -/
theorem hausdorffMeasure_image_Icc_eq_eVariationOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b))
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      eVariationOn γ (Set.Icc a b) :=
  le_antisymm (hausdorffMeasure_image_Icc_le_eVariationOn_of_injectiveOn γ hab hinj hBV)
    (eVariationOn_le_hausdorffMeasure_image_Icc_of_injectiveOn γ hγ hinj)

private theorem eVariationOn_Icc_le_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ}
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ C * ENNReal.ofReal (b - a) := by
  simpa using hγ.comp_eVariationOn_le (g := id) (s := Set.Icc a b) (fun _ hx ↦ hx)

/-- Accumulated variation preserves a curve's Lipschitz bound. -/
private theorem lipschitzOnWith_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    LipschitzOnWith C (variationOnFromTo γ (Set.Icc a b) a) (Set.Icc a b) := by
  let ℓ := variationOnFromTo γ (Set.Icc a b) a
  have hBV : BoundedVariationOn γ (Set.Icc a b) :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  have hbound : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, x ≤ y →
      dist (ℓ x) (ℓ y) ≤ C * dist x y := by
    intro x hx y hy hxy
    have hsub : Set.Icc x y ⊆ Set.Icc a b := Set.Icc_subset_Icc hx.1 hy.2
    have hvar := eVariationOn_Icc_le_of_lipschitzOn (hγ.mono hsub)
    have hreal := ENNReal.toReal_mono (by finiteness) hvar
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] at hreal
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy
    have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
      (Set.left_mem_Icc.mpr hab) hx hy hxy
    rw [variationOnFromTo.eq_of_le _ _ hxy, Set.inter_eq_right.mpr hsub] at hadd
    change dist (variationOnFromTo γ (Set.Icc a b) a x)
      (variationOnFromTo γ (Set.Icc a b) a y) ≤ _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm), Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hbound x hx y hy hxy
  · simpa only [dist_comm] using hbound y hy x hx hyx

/-- Total variation of a Lipschitz curve is the integral of its accumulated variation derivative. -/
private theorem integral_deriv_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, deriv (variationOnFromTo γ (Set.Icc a b) a) x) =
      (eVariationOn γ (Set.Icc a b)).toReal := by
  have hL := lipschitzOnWith_variationOnFromTo hab hγ
  have hAC := (show LipschitzOnWith C (variationOnFromTo γ (Set.Icc a b) a)
    (Set.uIcc a b) by simpa only [Set.uIcc_of_le hab] using hL).absolutelyContinuousOnInterval
  rw [hAC.integral_deriv_eq_sub, variationOnFromTo.self,
    variationOnFromTo.eq_of_le _ _ hab, Set.inter_self, sub_zero]

private theorem norm_deriv_le_abs_deriv_of_eventually_dist_le
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {ℓ : ℝ → ℝ} {x : ℝ}
    (hγ : DifferentiableAt ℝ γ x) (hℓ : DifferentiableAt ℝ ℓ x)
    (hbound : ∀ᶠ y in nhds x, dist (γ y) (γ x) ≤ dist (ℓ y) (ℓ x)) :
    ‖deriv γ x‖ ≤ |deriv ℓ x| := by
  have hγlim := hγ.hasDerivAt.tendsto_slope.norm
  have hℓlim := hℓ.hasDerivAt.tendsto_slope.norm
  change Filter.Tendsto _ _ (nhds |deriv ℓ x|) at hℓlim
  apply le_of_tendsto_of_tendsto hγlim hℓlim
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds] with y hy
  simp only [slope, norm_smul]
  rw [dist_eq_norm, dist_eq_norm] at hy
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)

private theorem dist_le_dist_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {a b x y : ℝ} (hab : a ≤ b)
    (hBV : BoundedVariationOn γ (Set.Icc a b))
    (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    dist (γ x) (γ y) ≤
      dist (variationOnFromTo γ (Set.Icc a b) a x)
        (variationOnFromTo γ (Set.Icc a b) a y) := by
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this hy hx (le_of_not_ge hxy)
  have hvar : dist (γ x) (γ y) ≤ variationOnFromTo γ (Set.Icc a b) x y := by
    rw [variationOnFromTo.eq_of_le _ _ hxy, dist_edist]
    apply ENNReal.toReal_mono (hBV.locallyBoundedVariationOn _ _ hx hy)
    exact eVariationOn.edist_le γ ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab) hx hy
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab) hx hy hxy
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hm)]
  linarith

/-- The derivative norm of a curve is bounded by the derivative of accumulated variation. -/
private theorem norm_deriv_le_deriv_variationOnFromTo
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {a b x : ℝ}
    (hBV : BoundedVariationOn γ (Set.Icc a b)) (hx : x ∈ Set.Ioo a b)
    (hγ : DifferentiableAt ℝ γ x)
    (hℓ : DifferentiableAt ℝ (variationOnFromTo γ (Set.Icc a b) a) x) :
    ‖deriv γ x‖ ≤ deriv (variationOnFromTo γ (Set.Icc a b) a) x := by
  have hab := hx.1.le.trans hx.2.le
  have hnhds := Icc_mem_nhds hx.1 hx.2
  have hbound : ∀ᶠ y in nhds x, dist (γ y) (γ x) ≤
      dist (variationOnFromTo γ (Set.Icc a b) a y)
        (variationOnFromTo γ (Set.Icc a b) a x) := by
    filter_upwards [hnhds] with y hy
    exact dist_le_dist_variationOnFromTo hab hBV hy ⟨hx.1.le, hx.2.le⟩
  have h := norm_deriv_le_abs_deriv_of_eventually_dist_le hγ hℓ hbound
  have hm := variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn
    (Set.left_mem_Icc.mpr hab)
  have hnonneg := hm.derivWithin_nonneg (x := x)
  rw [derivWithin_of_mem_nhds hnhds] at hnonneg
  rwa [abs_of_nonneg hnonneg] at h

/-- The derivative of a planar Lipschitz curve is integrable on its interval. -/
theorem integrableOn_deriv_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ}
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    IntegrableOn (deriv γ) (Set.Icc a b) := by
  rw [IntegrableOn, ← restrict_Ioo_eq_restrict_Icc]
  apply (integrable_const (C : ℝ)).mono' (aestronglyMeasurable_deriv γ _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hγ

/-- The integral of speed is bounded by the total variation of a Lipschitz curve. -/
private theorem integral_norm_deriv_le_eVariationOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, ‖deriv γ x‖) ≤ (eVariationOn γ (Set.Icc a b)).toReal := by
  let ℓ := variationOnFromTo γ (Set.Icc a b) a
  have hL := lipschitzOnWith_variationOnFromTo hab hγ
  have hAC := (show LipschitzOnWith C ℓ (Set.uIcc a b) by
    simpa only [Set.uIcc_of_le hab] using hL).absolutelyContinuousOnInterval
  have hBV : BoundedVariationOn γ (Set.Icc a b) :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  rw [← integral_deriv_variationOnFromTo hab hγ]
  apply intervalIntegral.integral_mono_ae_restrict hab
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ).norm) hAC.intervalIntegrable_deriv
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [hγ.ae_differentiableWithinAt_of_mem,
    hL.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ x : ℝ, x ≠ a by simp [ae_iff, measure_singleton],
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff, measure_singleton]] with x hxγ hxL hxa hxb hx
  have hx' : x ∈ Set.Ioo a b := ⟨lt_of_le_of_ne hx.1 (Ne.symm hxa), lt_of_le_of_ne hx.2 hxb⟩
  have hxcc : x ∈ Set.Icc a b := ⟨hx'.1.le, hx'.2.le⟩
  exact norm_deriv_le_deriv_variationOnFromTo hBV hx'
    ((hxγ hxcc).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))
    ((hxL hxcc).differentiableAt (Icc_mem_nhds hx'.1 hx'.2))

/-- Fundamental theorem of calculus for a planar Lipschitz curve. -/
private theorem integral_deriv_eq_sub_of_lipschitzOn
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    (∫ x in a..b, deriv γ x) = γ b - γ a := by
  have hint : IntervalIntegrable (deriv γ) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ)
  ext i
  let L : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 ↦ ℝ) i
  have hcoord := L.lipschitzWith.comp_lipschitzOnWith hγ
  have hAC := (show LipschitzOnWith _ (fun x ↦ L (γ x)) (Set.uIcc a b) by
    simpa only [Set.uIcc_of_le hab, LipschitzOnWith, Function.comp_apply] using hcoord).absolutelyContinuousOnInterval
  change L (∫ x in a..b, deriv γ x) = L (γ b - γ a)
  rw [← L.intervalIntegral_comp_comm hint, map_sub, ← hAC.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hγ.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ x : ℝ, x ≠ b by simp [ae_iff, measure_singleton]] with x hx hxb hxI
  have hx' : x ∈ Set.Ioo a b := by
    rw [Set.uIoc_of_le hab] at hxI
    exact ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩
  have hd := (hx ⟨hx'.1.le, hx'.2.le⟩).differentiableAt (Icc_mem_nhds hx'.1 hx'.2)
  exact ((L.hasFDerivAt.comp_hasDerivAt x hd.hasDerivAt).deriv).symm

private theorem edist_le_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    edist (γ b) (γ a) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  rw [edist_dist, dist_eq_norm, ← integral_deriv_eq_sub_of_lipschitzOn hab hγ]
  exact ENNReal.ofReal_le_ofReal (intervalIntegral.norm_integral_le_integral_norm hab)

/-- Total variation is bounded by the integral of speed for a Lipschitz curve. -/
private theorem eVariationOn_le_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  have hint : IntervalIntegrable (fun x ↦ ‖deriv γ x‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (integrableOn_deriv_of_lipschitzOn hγ).norm
  rw [eVariationOn]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨n, u, hu, hus⟩
  have hsub (i : ℕ) : Set.Icc (u i) (u (i + 1)) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc (hus i).1 (hus (i + 1)).2
  have hints (i : ℕ) : IntervalIntegrable (fun x ↦ ‖deriv γ x‖) volume (u i) (u (i + 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (hu (Nat.le_succ i))).mpr
      (IntegrableOn.mono_set (integrableOn_deriv_of_lipschitzOn hγ).norm (hsub i))
  calc
    (∑ i ∈ Finset.range n, edist (γ (u (i + 1))) (γ (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ x in u i..u (i + 1), ‖deriv γ x‖) :=
      Finset.sum_le_sum fun i _ ↦
        edist_le_ofReal_integral_norm_deriv (hu (Nat.le_succ i)) (hγ.mono (hsub i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ x in u i..u (i + 1), ‖deriv γ x‖) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg fun i _ ↦
        intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ ↦ norm_nonneg _)
    _ = ENNReal.ofReal (∫ x in u 0..u n, ‖deriv γ x‖) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (fun i _ ↦ hints i)]
    _ ≤ ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hus 0).1 (hu (Nat.zero_le n)) (hus n).2
        (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) hint

/-- Total variation of a planar Lipschitz curve is the integral of its speed. -/
theorem eVariationOn_eq_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) :
    eVariationOn γ (Set.Icc a b) = ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  apply le_antisymm (eVariationOn_le_ofReal_integral_norm_deriv hab hγ)
  have hBV : eVariationOn γ (Set.Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)
  rw [ENNReal.ofReal_le_iff_le_toReal hBV]
  exact integral_norm_deriv_le_eVariationOn hab hγ

/-- Hausdorff length of a planar injective Lipschitz curve is the integral of its speed. -/
theorem hausdorffMeasure_image_Icc_eq_ofReal_integral_norm_deriv
    {γ : ℝ → (EuclideanSpace ℝ (Fin 2))} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hγ : LipschitzOnWith C γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b)) :
    Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) =
      ENNReal.ofReal (∫ x in a..b, ‖deriv γ x‖) := by
  rw [hausdorffMeasure_image_Icc_eq_eVariationOn γ hab hγ.continuousOn hinj
    (ne_top_of_le_ne_top (by finiteness) (eVariationOn_Icc_le_of_lipschitzOn hγ)),
    eVariationOn_eq_ofReal_integral_norm_deriv hab hγ]

/-- The image of a continuous injective planar arc of bounded variation is Lebesgue null. -/
theorem volume_image_Icc_eq_zero_of_boundedVariationOn
    (γ : ℝ → (EuclideanSpace ℝ (Fin 2))) {a b : ℝ} (hab : a ≤ b)
    (hγ : ContinuousOn γ (Set.Icc a b)) (hinj : Set.InjOn γ (Set.Icc a b))
    (hBV : BoundedVariationOn γ (Set.Icc a b)) :
    volume (γ '' Set.Icc a b) = 0 := by
  have hlength : Measure.hausdorffMeasure 1 (γ '' Set.Icc a b) ≠ ⊤ := by
    rw [hausdorffMeasure_image_Icc_eq_eVariationOn γ hab hγ hinj hBV]
    exact hBV
  have harea : Measure.hausdorffMeasure 2 (γ '' Set.Icc a b) = 0 :=
    (Measure.hausdorffMeasure_zero_or_top (by norm_num : (1 : ℝ) < 2) _).resolve_right hlength
  have habs := MeasureTheory.Measure.absolutelyContinuous_isAddHaarMeasure
    (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (Measure.hausdorffMeasure (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))))
  apply habs
  simpa [finrank_euclideanSpace_fin] using harea

end MeasureTheory
