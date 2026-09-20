import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import MovingSofa.Analysis.SurfaceMeasure.BoundaryLimit

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace MovingSofa

/-- A sine convolution of tangent directions is the negative normal projection of their
Bochner integral. -/
private theorem integral_sin_sub_eq_neg_inner_integral_tangentVector
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (u : α → Real.Angle) (t : Real.Angle)
    (hu : Integrable (fun x ↦ tangentVector (u x)) (μ.restrict s)) :
    (∫ x in s, (u x - t).sin ∂μ) =
      -inner ℝ (normalVector t) (∫ x in s, tangentVector (u x) ∂μ) := by
  let L : Point →L[ℝ] ℝ := innerSL ℝ (normalVector t)
  calc
    (∫ x in s, (u x - t).sin ∂μ) =
        ∫ x in s, -L (tangentVector (u x)) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact sin_sub_eq_neg_inner_normalVector_tangentVector t (u x)
    _ = -(∫ x in s, L (tangentVector (u x)) ∂μ) := integral_neg _
    _ = -L (∫ x in s, tangentVector (u x) ∂μ) := by
      rw [ContinuousLinearMap.integral_comp_comm L hu]
    _ = -inner ℝ (normalVector t) (∫ x in s, tangentVector (u x) ∂μ) := rfl

theorem tangentArm_convolution (K : RightAngleCapSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    (tangentArmLengths K t).2.1 =
      ∫ u in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2),
        (u - (t : Real.Angle)).sin ∂surfaceAreaMeasure K.val := by
  let A := (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2)
  let _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hu : Integrable (fun u : Real.Angle ↦ tangentVector u)
      ((surfaceAreaMeasure K.val).restrict A) := by
    rw [← integrableOn_univ]
    apply ContinuousOn.integrableOn_compact isCompact_univ
    apply Continuous.continuousOn
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_sin.neg
    · exact Real.Angle.continuous_cos
  have hvec : (∫ u in A, tangentVector u ∂surfaceAreaMeasure K.val) =
      (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
        (edgeVertices K.val (t : Real.Angle)).1 := by
    ext i
    have hi := ContinuousLinearMap.integral_comp_comm
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 ↦ ℝ) i) hu
    change (∫ u in A, tangentVector u i ∂surfaceAreaMeasure K.val) =
      (∫ u in A, tangentVector u ∂surfaceAreaMeasure K.val) i at hi
    rw [← hi]
    symm
    simpa [A] using positiveVertex_sub_eq_integral K.val (a := t)
      (b := t + Real.pi / 2) (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos]) i
  have harm : (tangentArmLengths K t).2.1 =
      -inner ℝ (normalVector (t : Real.Angle))
        ((edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1 -
          (edgeVertices K.val (t : Real.Angle)).1) := by
    obtain ⟨hA, _, hC, _⟩ := capTangentArm_identities K t ht
    have hnt : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector t
    have hnn : inner ℝ (normalVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 1 := inner_normalVector_self t
    rw [hA] at hC
    have hproj := congrArg (fun p : Point ↦ inner ℝ p (normalVector (t : Real.Angle))) hC
    simp only [inner_add_left, real_inner_smul_left, hnt, hnn, mul_zero, add_zero,
      mul_one] at hproj
    simp only [capVertices] at hproj
    rw [inner_sub_right]
    rw [real_inner_comm
      (edgeVertices K.val ((t + Real.pi / 2 : ℝ) : Real.Angle)).1
      (normalVector (t : Real.Angle)),
      real_inner_comm (edgeVertices K.val (t : Real.Angle)).1
        (normalVector (t : Real.Angle))]
    linarith
  have hkernel := integral_sin_sub_eq_neg_inner_integral_tangentVector
    (surfaceAreaMeasure K.val) A id (t : Real.Angle) hu
  simp only [id_eq] at hkernel
  rw [show (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Ioc t (t + Real.pi / 2) = A from rfl,
    hkernel, hvec, harm]

end MovingSofa
