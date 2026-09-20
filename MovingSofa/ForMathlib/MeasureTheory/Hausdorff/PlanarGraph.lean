import MovingSofa.ForMathlib.MeasureTheory.Hausdorff.Graph
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

private theorem lipschitzOnWith_planarGraph {g : ℝ → ℝ} {s : Set ℝ} {C : NNReal}
    (hg : LipschitzOnWith C g s) :
    LipschitzOnWith (C + 1) (fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hgxy := hg.dist_le_mul x hx y hy
  rw [dist_eq_norm, EuclideanSpace.norm_eq]
  simp only [PiLp.sub_apply, Fin.sum_univ_two, Real.norm_eq_abs, pow_two]
  have hxy : dist x y = |x - y| := Real.dist_eq x y
  have hgy : |g x - g y| ≤ (C : ℝ) * |x - y| := by
    simpa [Real.dist_eq] using hgxy
  have hnonneg : 0 ≤ ((C : ℝ) + 1) * |x - y| := mul_nonneg (by positivity) (abs_nonneg _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, NNReal.coe_add, NNReal.coe_one,
    Real.dist_eq]
  rw [Real.sqrt_le_iff]
  constructor
  · exact hnonneg
  · have hsq := mul_self_le_mul_self (abs_nonneg (g x - g y)) hgy
    nlinarith [sq_nonneg ((C : ℝ) * |x - y|), NNReal.coe_nonneg C]

private theorem hausdorffMeasure_planarGraph_eq_zero {g : ℝ → ℝ} {s t : Set ℝ}
    {C : NNReal} (hg : LipschitzOnWith C g s) (hts : t ⊆ s) (ht : volume t = 0) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' t) = 0 := by
  have hgraph := (lipschitzOnWith_planarGraph hg).mono hts
  apply le_zero_iff.mp
  calc
    Measure.hausdorffMeasure 1
        ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' t) ≤
        ((C + 1 : NNReal) : ENNReal) ^ (1 : ℝ) * Measure.hausdorffMeasure 1 t :=
      hgraph.hausdorffMeasure_image_le (by positivity)
    _ = 0 := by rw [MeasureTheory.hausdorffMeasure_real, ht, mul_zero]

private theorem hausdorffMeasure_planarGraph_nondifferentiableOn_Icc_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} {C : NNReal}
    (hg : LipschitzOnWith C g (Set.Icc a b)) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) ''
        {x | x ∈ Set.Icc a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  apply hausdorffMeasure_planarGraph_eq_zero hg (by
    intro x hx
    exact hx.1)
  rcases le_total a b with hab | hba
  · rw [MeasureTheory.measure_eq_zero_iff_ae_notMem]
    have hg' : LipschitzOnWith C g (Set.uIcc a b) := by
      rwa [Set.uIcc_of_le hab]
    have hBV := hg'.absolutelyContinuousOnInterval.boundedVariationOn
    have hdiff := hBV.ae_differentiableAt_of_mem_uIcc
    rw [Set.uIcc_of_le hab] at hdiff
    filter_upwards [hdiff] with x hx hbad
    exact hbad.2 (hx hbad.1)
  · rcases hba.eq_or_lt with rfl | hba
    · apply measure_mono_null (by aesop) (MeasureTheory.measure_singleton b)
    · rw [Set.Icc_eq_empty (not_le_of_gt hba)]
      simp

private theorem hausdorffMeasure_planarGraph_nondifferentiableOn_Ioo_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hg : LocallyLipschitzOn (Set.Ioo a b) g) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) ''
        {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  let s : ℕ → Set ℝ := fun n ↦
    Set.Icc (a + 1 / (n + 1 : ℝ)) (b - 1 / (n + 1 : ℝ))
  let bad : ℕ → Set ℝ := fun n ↦ {x | x ∈ s n ∧ ¬ DifferentiableAt ℝ g x}
  have hs (n : ℕ) : s n ⊆ Set.Ioo a b := by
    intro x hx
    dsimp only [s] at hx
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    exact ⟨lt_of_lt_of_le (lt_add_of_pos_right a hpos) hx.1,
      lt_of_le_of_lt hx.2 (sub_lt_self b hpos)⟩
  have hzero (n : ℕ) : Measure.hausdorffMeasure 1
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' bad n) = 0 := by
    obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
      isCompact_Icc (hg.mono (hs n))
    exact hausdorffMeasure_planarGraph_nondifferentiableOn_Icc_eq_zero hC
  apply measure_mono_null
    (t := ⋃ n, (fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' bad n) ?_
    (MeasureTheory.measure_iUnion_null hzero)
  rintro p ⟨x, hx, rfl⟩
  have hδ : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hx.1.1) (sub_pos.mpr hx.1.2)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  rw [Set.mem_iUnion]
  refine ⟨n, x, ?_, rfl⟩
  refine ⟨?_, hx.2⟩
  dsimp only [s]
  constructor <;> linarith [lt_of_lt_of_le hn (min_le_left _ _),
    lt_of_lt_of_le hn (min_le_right _ _)]

/-- The graph image of the nondifferentiability set of a locally Lipschitz real
function has zero one-dimensional Hausdorff measure, in isometric coordinates. -/
theorem hausdorffMeasure_coordinateGraph_nondifferentiable_eq_zero
    {g : ℝ → ℝ} {a b : ℝ} (hg : LocallyLipschitzOn (Set.Ioo a b) g)
    (o : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Measure.hausdorffMeasure 1
      ((fun x ↦ o + e.symm !₂[x, g x]) ''
        {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) = 0 := by
  let graph : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  let transform : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p ↦ o + e.symm p
  have htransform : LipschitzWith 1 transform := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simp only [transform, NNReal.coe_one, one_mul, dist_add_left]
    rw [e.symm.dist_map]
  have hzero := hausdorffMeasure_planarGraph_nondifferentiableOn_Ioo_eq_zero hg
  apply le_zero_iff.mp
  rw [show (fun x ↦ o + e.symm !₂[x, g x]) ''
      {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x} =
      transform '' (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) by
    simp only [transform, graph, Set.image_image]]
  calc
    Measure.hausdorffMeasure 1
        (transform '' (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x})) ≤
      ((1 : NNReal) : ENNReal) ^ (1 : ℝ) * Measure.hausdorffMeasure 1
        (graph '' {x | x ∈ Set.Ioo a b ∧ ¬ DifferentiableAt ℝ g x}) :=
      htransform.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [hzero, mul_zero]

private theorem norm_coordinateGraph_deriv (g : ℝ → ℝ) (x : ℝ) :
    ‖(!₂[1, deriv g x] : EuclideanSpace ℝ (Fin 2))‖ = Real.sqrt (1 + (deriv g x) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_two, Real.norm_eq_abs, pow_two]

private theorem hasDerivAt_coordinateGraph {g : ℝ → ℝ} {x : ℝ}
    (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun y ↦ !₂[y, g y] : ℝ → EuclideanSpace ℝ (Fin 2))
      !₂[1, deriv g x] x := by
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.toContinuousLinearMap
  have hpi : HasDerivAt (fun y i ↦ !₂[y, g y].ofLp i)
      (fun i ↦ !₂[1, deriv g x].ofLp i) x := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · exact hasDerivAt_id x
    · exact hg.hasDerivAt
  have hcomp := L.hasFDerivAt.comp x hpi
  have hfun : (L ∘ fun y i ↦ !₂[y, g y].ofLp i) =
      (fun y ↦ !₂[y, g y] : ℝ → EuclideanSpace ℝ (Fin 2)) := rfl
  have hder : L.comp (ContinuousLinearMap.toSpanSingleton ℝ
      (fun i ↦ !₂[1, deriv g x].ofLp i)) =
      ContinuousLinearMap.toSpanSingleton ℝ
        (!₂[1, deriv g x] : EuclideanSpace ℝ (Fin 2)) := by
    apply ContinuousLinearMap.ext
    intro r
    rw [WithLp.ext_iff]
    funext i
    fin_cases i <;> simp [L, ContinuousLinearMap.comp_apply]
  rw [hfun, hder] at hcomp
  exact hcomp

private theorem integral_restrict_planarGraph_eq_integral_sqrt_mul
    {g : ℝ → ℝ} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hg : LipschitzOnWith C g (Set.Icc a b))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b)) =
      ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) * φ !₂[x, g x] := by
  let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  rw [MeasureTheory.integral_restrict_curve_eq_integral_norm_deriv_mul hab
    (lipschitzOnWith_planarGraph hg) (fun _ _ ↦ rfl) hφ]
  apply intervalIntegral.integral_congr_ae
  have hg' : LipschitzOnWith C g (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact hg
  have hdiff := hg'.absolutelyContinuousOnInterval.boundedVariationOn
    |>.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff] with x hx hxi
  have hderiv := (hasDerivAt_coordinateGraph (hx ⟨le_of_lt hxi.1, hxi.2⟩)).deriv
  rw [hderiv, norm_coordinateGraph_deriv]

/-- Weighted Hausdorff integration over an isometric planar graph equals the
parameter integral weighted by its almost-everywhere speed. -/
theorem integral_restrict_coordinateGraph_eq_integral_sqrt_mul
    {g : ℝ → ℝ} {C : NNReal} {a b : ℝ} (hab : a ≤ b)
    (hg : LipschitzOnWith C g (Set.Icc a b)) (o : EuclideanSpace ℝ (Fin 2))
    (e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {φ : EuclideanSpace ℝ (Fin 2) → ℝ} (hφ : Measurable φ) :
    (∫ p, φ p ∂(Measure.hausdorffMeasure 1).restrict
      ((fun x ↦ o + e.symm !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b)) =
      ∫ x in a..b, Real.sqrt (1 + (deriv g x) ^ 2) * φ (o + e.symm !₂[x, g x]) := by
  let F : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) :=
    e.symm.toIsometryEquiv.trans
      (AffineIsometryEquiv.vaddConst (V := EuclideanSpace ℝ (Fin 2))
        (P := EuclideanSpace ℝ (Fin 2)) ℝ o).toIsometryEquiv
  let γ : ℝ → EuclideanSpace ℝ (Fin 2) := fun x ↦ !₂[x, g x]
  have hF : ∀ p, F p = o + e.symm p := by
    intro p
    simp [F, add_comm]
  rw [show (fun x ↦ o + e.symm !₂[x, g x] : ℝ → EuclideanSpace ℝ (Fin 2)) '' Set.Icc a b =
      F '' (γ '' Set.Icc a b) by
    rw [Set.image_image]
    congr 1
    funext x
    exact (hF _).symm]
  rw [(F.measurePreserving_hausdorffMeasure 1).setIntegral_image_emb
    F.toHomeomorph.measurableEmbedding φ (γ '' Set.Icc a b)]
  have hbase := integral_restrict_planarGraph_eq_integral_sqrt_mul hab hg
    (hφ.comp F.continuous.measurable)
  simpa only [γ, Function.comp_apply, hF] using hbase

end MeasureTheory
