import MovingSofa.Curve.Area
import MovingSofa.Analysis.Stieltjes.Affine

noncomputable section

namespace MovingSofa

open MeasureTheory Set

/-- A continuous monotone surjection preserves continuous bounded variation. -/
theorem continuousBVPaths_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφm : Monotone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_monotone_surjective_Icc hab (x.property.2 i) hφm hφs⟩
  exact ⟨y, rfl⟩

/-- A continuous monotone surjection preserves signed path area. -/
theorem curveArea_comp_monotone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφm : Monotone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d,
      y.val = x.val ∘ φ ∧ curveAreaFunctional y = curveAreaFunctional x := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_monotone_surjective_Icc hab (x.property.2 i) hφm hφs⟩
  refine ⟨y, rfl, ?_⟩
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_comp_monotone_surjective hab hcd
      (continuousBVCoordinate x 1)
      ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      (fun t ↦ x.val t 0) ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      φ hφc hφm hφs,
    intervalStieltjesIntegral_comp_monotone_surjective hab hcd
      (continuousBVCoordinate x 0)
      ((PiLp.continuous_apply 2 _ 0).comp x.property.1)
      (fun t ↦ x.val t 1) ((PiLp.continuous_apply 2 _ 1).comp x.property.1)
      φ hφc hφm hφs]
  rfl

/-- A continuous monotone surjective reparametrisation identifies the signed areas of two given
paths whenever one is the composite of the other with it. -/
theorem curveAreaFunctional_eq_of_comp_monotone_surjective {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b) (y : ContinuousBVPaths c d)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ) (hφm : Monotone φ)
    (hφs : Function.Surjective φ) (hy : y.val = x.val ∘ φ) :
    curveAreaFunctional y = curveAreaFunctional x := by
  obtain ⟨z, hz, hza⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hφm hφs
  rw [show y = z from Subtype.ext (hy.trans hz.symm)]
  exact hza

/-- Translating a continuous BV path shifts its signed area by the cross product of the
translation vector with the path's total displacement, halved. -/
theorem curveAreaFunctional_add_constBVPath {a b : ℝ} (hab : a ≤ b)
    (x : ContinuousBVPaths a b) (v : Point) :
    curveAreaFunctional (x + constBVPath a b v) =
      curveAreaFunctional x +
        (v 0 * (x.val ⟨b, hab, le_rfl⟩ 1 - x.val ⟨a, le_rfl, hab⟩ 1) -
          v 1 * (x.val ⟨b, hab, le_rfl⟩ 0 - x.val ⟨a, le_rfl, hab⟩ 0)) / 2 := by
  have hcont : ∀ i : Fin 2, Continuous (continuousBVCoordinate x i).toFun :=
    fun i ↦ (PiLp.continuous_apply 2 _ i).comp x.property.1
  have hval : ∀ (i : Fin 2) (t : Set.Icc a b),
      (continuousBVCoordinate (x + constBVPath a b v) i).toFun t =
        (continuousBVCoordinate x i).toFun t + v i := by
    intro i t
    show (x.val t + v) i = x.val t i + v i
    simp
  have hint : ∀ i j : Fin 2,
      intervalStieltjesIntegral (continuousBVCoordinate (x + constBVPath a b v) i)
          (fun t ↦ (x + constBVPath a b v).val t j) univ =
        intervalStieltjesIntegral (continuousBVCoordinate x i) (fun t ↦ x.val t j) univ +
          v j * (x.val ⟨b, hab, le_rfl⟩ i - x.val ⟨a, le_rfl, hab⟩ i) := by
    intro i j
    rw [show (fun t ↦ (x + constBVPath a b v).val t j) =
      fun t ↦ (continuousBVCoordinate x j).toFun t + v j from funext (hval j)]
    exact intervalStieltjesIntegral_add_const hab (continuousBVCoordinate x i) _ (hcont i)
      (v i) (hval i) _ (hcont j) (v j)
  unfold curveAreaFunctional
  rw [hint 1 0, hint 0 1]
  ring

/-- Reversing a continuous BV path negates its signed area. -/
theorem curveArea_comp_reverse
    {a b : ℝ} (hab : a ≤ b) (x : ContinuousBVPaths a b) :
    let r := Set.Icc.reverse hab
    let y : ContinuousBVPaths a b :=
      ⟨x.val ∘ r, x.property.1.comp (Set.Icc.continuous_reverse hab), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i)
          (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)⟩
    curveAreaFunctional y = -curveAreaFunctional x := by
  dsimp only
  let r := Set.Icc.reverse hab
  let y : ContinuousBVPaths a b :=
    ⟨x.val ∘ r, x.property.1.comp (Set.Icc.continuous_reverse hab), fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i)
        (Set.Icc.antitone_reverse hab) (Set.Icc.surjective_reverse hab)⟩
  have hcoord (p q : Fin 2) :
      intervalStieltjesIntegral (continuousBVCoordinate y p)
          (fun t ↦ y.val t q) Set.univ =
        -intervalStieltjesIntegral (continuousBVCoordinate x p)
          (fun t ↦ x.val t q) Set.univ := by
    have hrev := intervalStieltjesIntegral_comp_reverse hab
      (continuousBVCoordinate x p)
      ((PiLp.continuous_apply 2 _ p).comp x.property.1)
      (fun t ↦ x.val t q) ((PiLp.continuous_apply 2 _ q).comp x.property.1)
    change intervalStieltjesIntegral _ _ Set.univ = -intervalStieltjesIntegral _ _ Set.univ
    exact hrev
  unfold curveAreaFunctional
  rw [hcoord 1 0, hcoord 0 1]
  ring

/-- A continuous antitone surjection negates signed path area. -/
theorem curveArea_comp_antitone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφa : Antitone φ) (hφs : Function.Surjective φ) :
    ∃ y : ContinuousBVPaths c d,
      y.val = x.val ∘ φ ∧ curveAreaFunctional y = -curveAreaFunctional x := by
  let y : ContinuousBVPaths c d :=
    ⟨x.val ∘ φ, x.property.1.comp hφc, fun i ↦
      BoundedVariationOn.comp_antitone_surjective_Icc hab (x.property.2 i) hφa hφs⟩
  let r := Set.Icc.reverse hcd
  let ψ : Set.Icc c d → Set.Icc a b := φ ∘ r
  have hψc : Continuous ψ := hφc.comp (Set.Icc.continuous_reverse hcd)
  have hψm : Monotone ψ := fun _ _ hst ↦
    hφa ((Set.Icc.antitone_reverse hcd) hst)
  have hψs : Function.Surjective ψ :=
    hφs.comp (Set.Icc.surjective_reverse hcd)
  obtain ⟨z, hz, hzarea⟩ :=
    curveArea_comp_monotone_surjective hab hcd x ψ hψc hψm hψs
  have hyrev : curveAreaFunctional z = -curveAreaFunctional y := by
    have hz' : z.val = y.val ∘ r := by
      rw [hz]
      rfl
    let yr : ContinuousBVPaths c d :=
      ⟨y.val ∘ r, y.property.1.comp (Set.Icc.continuous_reverse hcd), fun i ↦
        BoundedVariationOn.comp_antitone_surjective_Icc hcd (y.property.2 i)
          (Set.Icc.antitone_reverse hcd) (Set.Icc.surjective_reverse hcd)⟩
    have hyr := curveArea_comp_reverse hcd y
    change curveAreaFunctional yr = -curveAreaFunctional y at hyr
    have hzy : z = yr := by
      apply Subtype.ext
      exact hz'
    simpa [hzy] using hyr
  refine ⟨y, rfl, ?_⟩
  linarith

/-- A constant path has zero signed area, including on an empty parameter interval. -/
theorem curveAreaFunctional_eq_zero_of_constant
    {a b : ℝ} (x : ContinuousBVPaths a b) (p : Point)
    (hx : ∀ t, x.val t = p) : curveAreaFunctional x = 0 := by
  have hfun : x.val = fun _ ↦ p := funext hx
  have hcoord (i : Fin 2) : (fun t ↦ x.val t i) = fun _ ↦ p i := by
    funext t
    rw [hx t]
  let _ : MeasureTheory.IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x 0)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure (x.property.2 0)
  let _ : MeasureTheory.IsFiniteMeasure
      (intervalStieltjesMeasure (continuousBVCoordinate x 1)).variation :=
    BoundedVariationOn.instIsFiniteMeasureVariationVectorMeasure (x.property.2 1)
  unfold curveAreaFunctional
  unfold intervalStieltjesIntegral
  rw [MeasureTheory.VectorMeasure.setIntegral_congr_fun
      (s := Set.univ) (f := fun t ↦ x.val t 0) (g := fun _ ↦ p 0)
      (fun _ _ ↦ congrFun (hcoord 0) _),
    MeasureTheory.VectorMeasure.setIntegral_congr_fun
      (s := Set.univ) (f := fun t ↦ x.val t 1) (g := fun _ ↦ p 1)
      (fun _ _ ↦ congrFun (hcoord 1) _)]
  rw [MeasureTheory.VectorMeasure.setIntegral_const,
    MeasureTheory.VectorMeasure.setIntegral_const]
  by_cases hab : a ≤ b
  · let _ : Fact (a ≤ b) := ⟨hab⟩
    simp [intervalStieltjesMeasure, continuousBVCoordinate, hfun, Filter.limUnder,
      Filter.map_const]
  · let _ : IsEmpty (Set.Icc a b) :=
      ⟨fun t ↦ hab (le_trans t.property.1 t.property.2)⟩
    have hfilters : (Filter.atTop : Filter (Set.Icc a b)) = Filter.atBot :=
      Subsingleton.elim _ _
    simp [intervalStieltjesMeasure, continuousBVCoordinate, hfun, Filter.limUnder, hfilters]

/-- A continuous monotone or antitone surjection transports BV paths and signed area. -/
theorem curveArea_comp_monotone_or_antitone_surjective
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (x : ContinuousBVPaths a b)
    (φ : Set.Icc c d → Set.Icc a b) (hφc : Continuous φ)
    (hφs : Function.Surjective φ) (hφ : Monotone φ ∨ Antitone φ) :
    ∃ y : ContinuousBVPaths c d, y.val = x.val ∘ φ ∧
      (Monotone φ → curveAreaFunctional y = curveAreaFunctional x) ∧
      (Antitone φ → curveAreaFunctional y = -curveAreaFunctional x) := by
  rcases hφ with hm | ha
  · obtain ⟨y, hy, harea⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hm hφs
    refine ⟨y, hy, fun _ ↦ harea, ?_⟩
    intro ha
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_antitone_surjective hab hcd x φ hφc ha hφs
    have hzy : z = y := Subtype.ext (hz.trans hy.symm)
    simpa only [hzy] using hzarea
  · obtain ⟨y, hy, harea⟩ := curveArea_comp_antitone_surjective hab hcd x φ hφc ha hφs
    refine ⟨y, hy, ?_, fun _ ↦ harea⟩
    intro hm
    obtain ⟨z, hz, hzarea⟩ := curveArea_comp_monotone_surjective hab hcd x φ hφc hm hφs
    have hzy : z = y := Subtype.ext (hz.trans hy.symm)
    simpa only [hzy] using hzarea

end MovingSofa
