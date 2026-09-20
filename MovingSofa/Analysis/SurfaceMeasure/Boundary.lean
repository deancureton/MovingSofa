import MovingSofa.Analysis.SurfaceMeasure.FrameProducts
import MovingSofa.Analysis.Stieltjes.Shift
import MovingSofa.ForMathlib.MeasureTheory.Integral.Translation
import MovingSofa.Cap.ArmCoordinates

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace MovingSofa

theorem positiveArm_stieltjes_surface (K : RightAngleCapSpace) :
    ∃ f : RightContinuousIntervalBV 0 (Real.pi / 2),
      (∀ t, f.toFun t = (tangentArmLengths K t).1.1) ∧
      ∀ E : Set (Set.Icc (0 : ℝ) (Real.pi / 2)), MeasurableSet E →
        (∀ t ∈ E, 0 < (t : ℝ)) →
        intervalStieltjesMeasure f E =
          (∫ t in (fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ (s : ℝ)) '' E,
            (tangentArmLengths K t).2.1) -
          (surfaceAreaMeasure K.val
            ((fun s : Set.Icc (0 : ℝ) (Real.pi / 2) ↦ ((s : ℝ) : Real.Angle)) '' E)).toReal := by
  have hT : 0 < (Real.pi / 2) := by positivity
  obtain ⟨HA, PA, hHA, hPA, hmA⟩ := exists_positiveVertex_frame_products K.val hT
    (by linarith [Real.pi_pos])
  obtain ⟨HC, PC, hHC, hPC, hmC⟩ := exists_positiveVertex_frame_products K.val
    (a := 0 + (Real.pi / 2)) (b := (Real.pi / 2) + (Real.pi / 2)) (by linarith)
    (by linarith [Real.pi_pos])
  have hHC_support (t : Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2))) :
      HC.toFun t = supportValue K.val (((t : ℝ) : Real.Angle)) := by
    rw [hHC, (edgeVertices_fst_mem K.val (((t : ℝ) : Real.Angle))).2]
  have hHCc : Continuous HC.toFun := by
    convert (continuous_supportValue_real K.val).comp continuous_subtype_val using 1
    funext t
    exact hHC_support t
  obtain ⟨Hs, hHs, hHsm⟩ := exists_intervalBV_shift_from_zero hT.le HC hHCc
  obtain ⟨f, hf, hfm⟩ := intervalStieltjes_linear_combination 0 (Real.pi / 2) hT.le Hs PA 1 (-1)
  refine ⟨f, ?_, ?_⟩
  · intro t
    rw [hf, hHs, hHC_support, hPA, (tangentArmLengths_positive_frame K t).1]
    simp only [one_mul, neg_mul, one_mul]
    ring
  · intro E hE hE0
    change Set (Icc 0 (Real.pi / 2)) at E
    let φ : Icc 0 (Real.pi / 2) →
        Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) := fun t ↦
      ⟨(t : ℝ) + (Real.pi / 2), by constructor <;> linarith [t.property.1, t.property.2]⟩
    let R := (Subtype.val : Icc 0 (Real.pi / 2) → ℝ) '' E
    have hR : MeasurableSet R :=
      (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' hE
    have hφE : MeasurableSet (φ '' E) := by
      let ψ : Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) →
          Icc 0 (Real.pi / 2) := fun t ↦
        ⟨(t : ℝ) - (Real.pi / 2), by
          constructor
          · linarith [t.property.1]
          · linarith [t.property.2]⟩
      let e : Icc 0 (Real.pi / 2) ≃ₜ
          Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) :=
        { toFun := φ
          invFun := ψ
          left_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
          right_inv := fun x ↦ by apply Subtype.ext; simp [φ, ψ]
          continuous_toFun := (continuous_subtype_val.add_const (Real.pi / 2)).subtype_mk _
          continuous_invFun := (continuous_subtype_val.sub continuous_const).subtype_mk _ }
      exact e.measurableEmbedding.measurableSet_image' hE
    have hφleft : ∀ t ∈ φ '' E, 0 + (Real.pi / 2) < (t : ℝ) := by
      rintro t ⟨s, hs, rfl⟩
      dsimp [φ]
      linarith [hE0 s hs]
    have hreal : (Subtype.val :
        Icc (0 + (Real.pi / 2)) ((Real.pi / 2) + (Real.pi / 2)) → ℝ) '' (φ '' E) =
        (fun x : ℝ ↦ x + (Real.pi / 2)) '' R := by
      ext x
      constructor
      · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩
      · rintro ⟨-, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨φ s, ⟨s, hs, rfl⟩, rfl⟩
    have hHs_measure : intervalStieltjesMeasure Hs E =
        ∫ t in R, inner ℝ
          (edgeVertices K.val (((t + (Real.pi / 2) : ℝ) : Real.Angle))).1
          (tangentVector (((t + (Real.pi / 2) : ℝ) : Real.Angle))) := by
      rw [hHsm E hE, (hmC (φ '' E) hφE hφleft).1, hreal,
        integral_image_add_right_eq (Real.pi / 2) R hR]
    have hPA_measure := (hmA E hE hE0).2
    have hlin : intervalStieltjesMeasure f E =
        intervalStieltjesMeasure Hs E - intervalStieltjesMeasure PA E := by
      have := congrArg (fun m : SignedMeasure (Icc 0 (Real.pi / 2)) ↦ m E) hfm
      rw [add_apply, _root_.smul_apply, _root_.smul_apply] at this
      simpa only [smul_eq_mul, one_mul, neg_one_mul, sub_eq_add_neg] using this
    change intervalStieltjesMeasure f E = _
    rw [hlin, hHs_measure, hPA_measure]
    have hAint : IntegrableOn
        (fun t : ℝ ↦ inner ℝ (edgeVertices K.val (t : Real.Angle)).1
          (normalVector (t : Real.Angle))) R := by
      have hAIcc := HA.integrableOn_Icc_of_eq
        (fun t : ℝ ↦ inner ℝ (edgeVertices K.val (t : Real.Angle)).1
          (normalVector (t : Real.Angle))) (fun t ↦ (hHA t).symm)
      apply hAIcc.mono_set
      rintro x ⟨t, -, rfl⟩
      exact t.property
    have hCint : IntegrableOn
        (fun t : ℝ ↦ inner ℝ
          (edgeVertices K.val (((t + (Real.pi / 2) : ℝ) : Real.Angle))).1
          (tangentVector (((t + (Real.pi / 2) : ℝ) : Real.Angle)))) R := by
      let q : ℝ → ℝ := fun s ↦ inner ℝ (edgeVertices K.val (s : Real.Angle)).1
        (tangentVector (s : Real.Angle))
      have hqIcc := PC.integrableOn_Icc_of_eq q (fun t ↦ (hPC t).symm)
      have hqshift : IntegrableOn q
          ((fun x : ℝ ↦ x + Real.pi / 2) '' R) := by
        apply hqIcc.mono_set
        rintro x ⟨-, ⟨t, -, rfl⟩, rfl⟩
        constructor <;> linarith [t.property.1, t.property.2]
      exact (integrableOn_comp_add_right_iff (Real.pi / 2) R hR q).2 hqshift
    rw [show (∫ t in R, inner ℝ
          (edgeVertices K.val (((t + Real.pi / 2 : ℝ) : Real.Angle))).1
          (tangentVector (((t + Real.pi / 2 : ℝ) : Real.Angle)))) -
        ((surfaceAreaMeasure K.val
          ((fun t : Icc 0 (Real.pi / 2) ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal -
          ∫ t in R, inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) =
        ((∫ t in R, inner ℝ
            (edgeVertices K.val (((t + Real.pi / 2 : ℝ) : Real.Angle))).1
            (tangentVector (((t + Real.pi / 2 : ℝ) : Real.Angle)))) +
          ∫ t in R, inner ℝ (edgeVertices K.val (t : Real.Angle)).1
            (normalVector (t : Real.Angle))) -
        (surfaceAreaMeasure K.val
          ((fun t : Icc 0 (Real.pi / 2) ↦ ((t : ℝ) : Real.Angle)) '' E)).toReal by ring]
    rw [← integral_add hCint hAint]
    apply congrArg (fun z : ℝ ↦ z -
      (surfaceAreaMeasure K.val
        ((fun s : Icc (0 : ℝ) (Real.pi / 2) ↦ ((s : ℝ) : Real.Angle)) '' E)).toReal)
    apply integral_congr_ae
    filter_upwards with t
    rw [(tangentArmLengths_positive_frame K t).2]
    ring

end MovingSofa
