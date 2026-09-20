import MovingSofa.Curve.Concatenation
import MovingSofa.Curve.Area
import MovingSofa.Analysis.Stieltjes.Transport

noncomputable section

open MeasureTheory Set
open scoped Function

namespace MovingSofa

theorem curveArea_concatenation (Γ : RectifiablePathData) {n : ℕ}
    (pieces : Fin n → RectifiablePathData) (h : IsPathConcatenation Γ pieces) :
    curveAreaFunctional Γ.path = ∑ i, curveAreaFunctional (pieces i).path := by
  rcases h with ⟨_, cuts, hcuts, hcuts_zero, hcuts_last, hpieces⟩
  have hcoord (i : Fin n) (p q : Fin 2) :
      intervalStieltjesIntegral (continuousBVCoordinate Γ.path p)
          (fun t ↦ Γ.path.val t q) (Ioc (cuts i.castSucc) (cuts i.succ)) =
        intervalStieltjesIntegral (continuousBVCoordinate (pieces i).path p)
          (fun t ↦ (pieces i).path.val t q) Set.univ := by
    obtain ⟨φ, ψ, hφc, hφm, hφs, hψc, hψm, hψs, heq⟩ := hpieces i
    let l := cuts i.castSucc
    let u := cuts i.succ
    let ι : Set.Icc (l : ℝ) u → Set.Icc Γ.a Γ.b := fun x ↦
      ⟨x, le_trans l.property.1 x.property.1, le_trans x.property.2 u.property.2⟩
    let hp : BoundedVariationOn ((continuousBVCoordinate Γ.path p).toFun ∘ ι) Set.univ :=
      ne_top_of_le_ne_top (continuousBVCoordinate Γ.path p).boundedVariation
        (eVariationOn.comp_le_of_monotoneOn _ ι
          (fun _ _ _ _ h ↦ h) (mapsTo_univ ι _))
    let Fp : RightContinuousIntervalBV (l : ℝ) u :=
      { toFun := (continuousBVCoordinate Γ.path p).toFun ∘ ι
        boundedVariation := hp
        right_continuous := fun _ ↦
          (((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1).comp
            (continuous_subtype_val.subtype_mk _)).continuousAt.continuousWithinAt }
    rw [intervalStieltjesIntegral_Ioc_eq_inclusion
      (continuousBVCoordinate Γ.path p)
      ((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t q)
      ((PiLp.continuous_apply 2 _ q).comp Γ.path.property.1) l u
      (hcuts (Fin.castSucc_le_succ i))]
    change intervalStieltjesIntegral Fp
        ((fun t ↦ Γ.path.val t q) ∘ ι) Set.univ =
      intervalStieltjesIntegral (continuousBVCoordinate (pieces i).path p)
        (fun t ↦ (pieces i).path.val t q) Set.univ
    rw [intervalStieltjesIntegral_comp_monotone_surjective
      (show (l : ℝ) ≤ u from hcuts (Fin.castSucc_le_succ i)) (by norm_num) Fp
      (((PiLp.continuous_apply 2 _ p).comp Γ.path.property.1).comp
        (continuous_subtype_val.subtype_mk _))
      ((fun t ↦ Γ.path.val t q) ∘ ι)
      (((PiLp.continuous_apply 2 _ q).comp Γ.path.property.1).comp
        (continuous_subtype_val.subtype_mk _))
      φ hφc hφm hφs,
      intervalStieltjesIntegral_comp_monotone_surjective
        (pieces i).ordered (by norm_num) (continuousBVCoordinate (pieces i).path p)
        ((PiLp.continuous_apply 2 _ p).comp (pieces i).path.property.1)
        (fun t ↦ (pieces i).path.val t q)
        ((PiLp.continuous_apply 2 _ q).comp (pieces i).path.property.1)
        ψ hψc hψm hψs]
    congr 1
    · congr 1
      funext s
      simpa [Fp, continuousBVCoordinate, ι, Function.comp_apply] using
        congrArg (fun z ↦ z p) (heq s)
    · funext s
      simpa [continuousBVCoordinate, ι, Function.comp_apply] using
        congrArg (fun z ↦ z q) (heq s)
  unfold curveAreaFunctional
  rw [intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate Γ.path 1)
      ((PiLp.continuous_apply 2 _ 1).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t 0) ((PiLp.continuous_apply 2 _ 0).comp Γ.path.property.1)
      cuts hcuts hcuts_zero hcuts_last,
    intervalStieltjesIntegral_eq_sum_Ioc (continuousBVCoordinate Γ.path 0)
      ((PiLp.continuous_apply 2 _ 0).comp Γ.path.property.1)
      (fun t ↦ Γ.path.val t 1) ((PiLp.continuous_apply 2 _ 1).comp Γ.path.property.1)
      cuts hcuts hcuts_zero hcuts_last]
  simp_rw [hcoord]
  rw [← Finset.sum_sub_distrib]
  simp_rw [div_eq_mul_inv, Finset.sum_mul]

end MovingSofa
