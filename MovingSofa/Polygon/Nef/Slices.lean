import MovingSofa.Polygon.Nef.Cells
import MovingSofa.ForMathlib.Analysis.FiniteEnvelope
import MovingSofa.Geometry.HallwayParts
import MovingSofa.ForMathlib.MeasureTheory.EuclideanSpace
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

def framePoint (a : Real.Angle) (x y : ℝ) : Point :=
  rotationMap a !₂[x, y]

lemma framePoint_eq (a : Real.Angle) (x y : ℝ) :
    framePoint a x y = x • normalVector a + y • tangentVector a := by
  ext j
  fin_cases j <;>
    simp [framePoint, rotationMap, Orientation.rotation_apply,
      rightAngleRotation_apply, normalVector, tangentVector, frame]
  <;> ring

@[simp] lemma inner_framePoint_normalVector (a : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (normalVector a) = x := by
  rw [framePoint, inner_rotationMap_normalVector]
  rfl

@[simp] lemma inner_framePoint_tangentVector (a : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (tangentVector a) = y := by
  rw [framePoint, inner_rotationMap_tangentVector]
  rfl

@[simp] lemma norm_tangentVector_angle (a : Real.Angle) : ‖tangentVector a‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]
  rw [EuclideanSpace.norm_sq_eq]
  simp [tangentVector, frame, Fin.sum_univ_two]
  nlinarith [Real.Angle.cos_sq_add_sin_sq a]

def frameNormalCoeff (a b : Real.Angle) : ℝ :=
  inner ℝ (normalVector a) (normalVector b)

def frameTangentCoeff (a b : Real.Angle) : ℝ :=
  inner ℝ (tangentVector a) (normalVector b)

lemma inner_framePoint_normalVector_eq (a b : Real.Angle) (x y : ℝ) :
    inner ℝ (framePoint a x y) (normalVector b) =
      frameNormalCoeff a b * x + frameTangentCoeff a b * y := by
  rw [framePoint_eq, inner_add_left, real_inner_smul_left,
    real_inner_smul_left]
  simp only [frameNormalCoeff, frameTangentCoeff]
  ring

def cellUpper {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Bool :=
  if P j then (H j).upper else !(H j).upper

def frameBoundaryValue (a : Real.Angle) (H : PlanarHalfPlaneData) (x : ℝ) : ℝ :=
  (H.height - frameNormalCoeff a H.angle * x) / frameTangentCoeff a H.angle

lemma frameBoundaryValue_sub (a : Real.Angle) (H : PlanarHalfPlaneData)
    (x z : ℝ) :
    frameBoundaryValue a H x - frameBoundaryValue a H z =
      -(frameNormalCoeff a H.angle / frameTangentCoeff a H.angle) * (x - z) := by
  simp only [frameBoundaryValue]
  ring

lemma abs_frameBoundaryValue_sub (a : Real.Angle) (H : PlanarHalfPlaneData)
    (x z : ℝ) :
    |frameBoundaryValue a H x - frameBoundaryValue a H z| =
      |frameNormalCoeff a H.angle / frameTangentCoeff a H.angle| * |x - z| := by
  rw [frameBoundaryValue_sub, abs_mul, abs_neg]

def isUpperEndpoint {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Prop :=
  (cellUpper H P j = false ∧ 0 < frameTangentCoeff a (H j).angle) ∨
    (cellUpper H P j = true ∧ frameTangentCoeff a (H j).angle < 0)

def isLowerEndpoint {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (j : Fin n) : Prop :=
  (cellUpper H P j = false ∧ frameTangentCoeff a (H j).angle < 0) ∨
    (cellUpper H P j = true ∧ 0 < frameTangentCoeff a (H j).angle)

def upperBoundaryFunctions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) : List (ℝ → ℝ) := by
  classical
  exact ((Finset.univ.filter (isUpperEndpoint a H P)).toList.map fun j x ↦
    frameBoundaryValue a (H j) x)

def lowerBoundaryFunctions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) : List (ℝ → ℝ) := by
  classical
  exact ((Finset.univ.filter (isLowerEndpoint a H P)).toList.map fun j x ↦
    frameBoundaryValue a (H j) x)

def upperEnvelope {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  (upperBoundaryFunctions a H P).foldr (fun f r ↦ min (f x) r) R

def lowerEnvelope {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  (lowerBoundaryFunctions a H P).foldr (fun f r ↦ max (f x) r) (-R)

def slopeBound {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData) : ℝ :=
  ∑ j, |frameNormalCoeff a (H j).angle / frameTangentCoeff a (H j).angle|

lemma slopeBound_nonneg {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) : 0 ≤ slopeBound a H := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

lemma abs_upperEnvelope_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |upperEnvelope a H P R x - upperEnvelope a H P R z| ≤
      slopeBound a H * |x - z| := by
  apply List.abs_foldr_min_apply_sub_le
  · exact slopeBound_nonneg a H
  · intro f hf
    simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨j, _, rfl⟩ := hf
    rw [abs_frameBoundaryValue_sub]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [slopeBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n ↦
          |frameNormalCoeff a (H k).angle / frameTangentCoeff a (H k).angle|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))

lemma abs_lowerEnvelope_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |lowerEnvelope a H P R x - lowerEnvelope a H P R z| ≤
      slopeBound a H * |x - z| := by
  apply List.abs_foldr_max_apply_sub_le
  · exact slopeBound_nonneg a H
  · intro f hf
    simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
      Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨j, _, rfl⟩ := hf
    rw [abs_frameBoundaryValue_sub]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    simpa only [slopeBound] using
      (Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin n ↦
          |frameNormalCoeff a (H k).angle / frameTangentCoeff a (H k).angle|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j))

def cellSliceLength {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : ℝ :=
  max (upperEnvelope a H P R x - lowerEnvelope a H P R x) 0

lemma abs_cellSliceLength_sub_le {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x z : ℝ) :
    |cellSliceLength a H P R x - cellSliceLength a H P R z| ≤
      (2 * slopeBound a H) * |x - z| := by
  unfold cellSliceLength
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · calc
      |(upperEnvelope a H P R x - lowerEnvelope a H P R x) -
          (upperEnvelope a H P R z - lowerEnvelope a H P R z)| ≤
          |upperEnvelope a H P R x - upperEnvelope a H P R z| +
            |lowerEnvelope a H P R x - lowerEnvelope a H P R z| := by
              rw [sub_sub_sub_comm]
              exact abs_sub _ _
      _ ≤ slopeBound a H * |x - z| + slopeBound a H * |x - z| :=
        add_le_add (abs_upperEnvelope_sub_le a H P R x z)
          (abs_lowerEnvelope_sub_le a H P R x z)
      _ = (2 * slopeBound a H) * |x - z| := by ring
  · simp only [sub_self, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (slopeBound_nonneg a H))
      (abs_nonneg _)

lemma continuous_cellSliceLength {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R : ℝ) :
    Continuous (cellSliceLength a H P R) := by
  let K : NNReal :=
    ⟨2 * slopeBound a H, mul_nonneg (by norm_num) (slopeBound_nonneg a H)⟩
  apply (LipschitzWith.of_dist_le_mul (K := K) fun x z ↦ ?_).continuous
  change |cellSliceLength a H P R x - cellSliceLength a H P R z| ≤
    (2 * slopeBound a H) * |x - z|
  exact abs_cellSliceLength_sub_le a H P R x z

def closedCellSlice {n : ℕ} (a : Real.Angle) (H : Fin n → PlanarHalfPlaneData)
    (P : Fin n → Bool) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ closedBooleanCell H P} ∩ Set.Icc (-R) R

def parallelCellFeasible {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (x : ℝ) : Prop :=
  ∀ j, frameTangentCoeff a (H j).angle = 0 →
    framePoint a x 0 ∈ normalHalfPlane (H j).angle (H j).height
      (cellUpper H P j) false

lemma mem_closedCellSlice_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x y : ℝ)
    (hparallel : parallelCellFeasible a H P x) :
    y ∈ closedCellSlice a H P R x ↔
      lowerEnvelope a H P R x ≤ y ∧ y ≤ upperEnvelope a H P R x := by
  classical
  rw [closedCellSlice, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc,
    lowerEnvelope, upperEnvelope, List.foldr_max_apply_le_iff, List.le_foldr_min_apply_iff]
  constructor
  · rintro ⟨hycell, hyR⟩
    simp only [closedBooleanCell, Set.mem_iInter] at hycell
    refine ⟨⟨hyR.1, ?_⟩, hyR.2, ?_⟩
    · intro f hf
      simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjcell := hycell j
      change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
        (cellUpper H P j) false at hjcell
      rcases hj with ⟨hu, hb⟩ | ⟨hu, hb⟩
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (div_le_iff_of_neg hb).2
        nlinarith
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (div_le_iff₀ hb).2
        nlinarith
    · intro f hf
      simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
        Finset.mem_filter, Finset.mem_univ, true_and] at hf
      obtain ⟨j, hj, rfl⟩ := hf
      have hjcell := hycell j
      change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
        (cellUpper H P j) false at hjcell
      rcases hj with ⟨hu, hb⟩ | ⟨hu, hb⟩
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (le_div_iff₀ hb).2
        nlinarith
      · simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hjcell
        rw [inner_framePoint_normalVector_eq] at hjcell
        simp only [frameBoundaryValue]
        apply (le_div_iff_of_neg hb).2
        nlinarith
  · rintro ⟨⟨hyRneg, hylower⟩, hyR, hyupper⟩
    refine ⟨?_, hyRneg, hyR⟩
    simp only [closedBooleanCell, Set.mem_iInter]
    intro j
    change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
      (cellUpper H P j) false
    by_cases hb0 : frameTangentCoeff a (H j).angle = 0
    · have hj := hparallel j hb0
      cases hu : cellUpper H P j <;>
        simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
          Set.mem_ofPred_eq] at hj ⊢ <;>
        rw [inner_framePoint_normalVector_eq] at hj ⊢ <;>
        simp only [hb0, mul_zero, zero_mul, add_zero] at hj ⊢ <;>
        exact hj
    · rcases lt_or_gt_of_ne hb0 with hb | hb
      · by_cases hu : cellUpper H P j = false
        · have hjindex : isLowerEndpoint a H P j := Or.inl ⟨hu, hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              lowerBoundaryFunctions a H P := by
            simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hylower _ hjfun
          simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq, inner_framePoint_normalVector_eq,
            frameBoundaryValue] at hjbound ⊢
          have := (div_le_iff_of_neg hb).mp hjbound
          nlinarith
        · have hu' : cellUpper H P j = true := Bool.eq_true_of_not_eq_false hu
          have hjindex : isUpperEndpoint a H P j := Or.inr ⟨hu', hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              upperBoundaryFunctions a H P := by
            simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hyupper _ hjfun
          simp only [normalHalfPlane, hu', Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
            inner_framePoint_normalVector_eq, frameBoundaryValue,
            ] at hjbound ⊢
          have := (le_div_iff_of_neg hb).mp hjbound
          nlinarith
      · by_cases hu : cellUpper H P j = false
        · have hjindex : isUpperEndpoint a H P j := Or.inl ⟨hu, hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              upperBoundaryFunctions a H P := by
            simp only [upperBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hyupper _ hjfun
          simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
            Set.mem_ofPred_eq, inner_framePoint_normalVector_eq,
            frameBoundaryValue] at hjbound ⊢
          have := (le_div_iff₀ hb).mp hjbound
          nlinarith
        · have hu' : cellUpper H P j = true := Bool.eq_true_of_not_eq_false hu
          have hjindex : isLowerEndpoint a H P j := Or.inr ⟨hu', hb⟩
          have hjfun : (fun x ↦ frameBoundaryValue a (H j) x) ∈
              lowerBoundaryFunctions a H P := by
            simp only [lowerBoundaryFunctions, List.mem_map, Finset.mem_toList,
              Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hjindex, rfl⟩
          have hjbound := hylower _ hjfun
          simp only [normalHalfPlane, hu', Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq,
            inner_framePoint_normalVector_eq, frameBoundaryValue,
            ] at hjbound ⊢
          have := (div_le_iff₀ hb).mp hjbound
          nlinarith

lemma volume_closedCellSlice_toReal {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : parallelCellFeasible a H P x) :
    (MeasureTheory.volume (closedCellSlice a H P R x)).toReal =
      cellSliceLength a H P R x := by
  have hset : closedCellSlice a H P R x =
      Set.Icc (lowerEnvelope a H P R x) (upperEnvelope a H P R x) := by
    ext y
    simpa [Set.mem_Icc] using mem_closedCellSlice_iff a H P R x y hparallel
  rw [hset, Real.volume_Icc]
  unfold cellSliceLength
  by_cases h : 0 ≤ upperEnvelope a H P R x - lowerEnvelope a H P R x
  · rw [ENNReal.toReal_ofReal h, max_eq_left h]
  · have h' : upperEnvelope a H P R x - lowerEnvelope a H P R x ≤ 0 := le_of_not_ge h
    rw [ENNReal.ofReal_of_nonpos h', max_eq_right h']
    rfl

def booleanCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ booleanCell (fun j ↦ (H j).carrier) P} ∩ Set.Icc (-R) R

def noParallelBoundaryAt {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) : Prop :=
  ∀ j, frameTangentCoeff a (H j).angle = 0 →
    frameNormalCoeff a (H j).angle * x ≠ (H j).height

def cellSliceBoundaryExceptions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) : Set ℝ :=
  ⋃ j, {y | inner ℝ (framePoint a x y) (normalVector (H j).angle) = (H j).height}

lemma finite_cellSliceBoundaryExceptions {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (x : ℝ) (hx : noParallelBoundaryAt a H x) :
    (cellSliceBoundaryExceptions a H x).Finite := by
  classical
  unfold cellSliceBoundaryExceptions
  apply Set.Finite.iUnion Set.finite_univ
  · intro j _
    apply Set.Subsingleton.finite
    intro y hy z hz
    simp only [Set.mem_ofPred_eq, inner_framePoint_normalVector_eq] at hy hz
    by_cases hb : frameTangentCoeff a (H j).angle = 0
    · exact (hx j hb (by simpa [hb] using hy)).elim
    · rcases lt_or_gt_of_ne hb with hb | hb <;> nlinarith
  · simp

lemma volume_booleanCellSlice_eq_closedCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hx : noParallelBoundaryAt a H x) :
    MeasureTheory.volume (booleanCellSlice a H P R x) =
      MeasureTheory.volume (closedCellSlice a H P R x) := by
  apply MeasureTheory.measure_congr
  rw [MeasureTheory.ae_eq_set]
  have hzero :=
    (finite_cellSliceBoundaryExceptions a H x hx).measure_zero MeasureTheory.volume
  constructor <;> apply MeasureTheory.measure_mono_null _ hzero
  · intro y hy
    by_contra hyexception
    have hyne : ∀ j, inner ℝ (framePoint a x y) (normalVector (H j).angle) ≠
        (H j).height := by
      intro j hj
      apply hyexception
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have heq := mem_booleanCell_iff_mem_closedBooleanCell_of_ne H P _ hyne
    rcases hy.1 with ⟨hycell, hyR⟩
    exact hy.2 ⟨heq.mp hycell, hyR⟩
  · intro y hy
    by_contra hyexception
    have hyne : ∀ j, inner ℝ (framePoint a x y) (normalVector (H j).angle) ≠
        (H j).height := by
      intro j hj
      apply hyexception
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    have heq := mem_booleanCell_iff_mem_closedBooleanCell_of_ne H P _ hyne
    rcases hy.1 with ⟨hycell, hyR⟩
    exact hy.2 ⟨heq.mpr hycell, hyR⟩

lemma volume_booleanCellSlice_toReal {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : parallelCellFeasible a H P x)
    (hx : noParallelBoundaryAt a H x) :
    (MeasureTheory.volume (booleanCellSlice a H P R x)).toReal =
      cellSliceLength a H P R x := by
  rw [volume_booleanCellSlice_eq_closedCellSlice a H P R x hx]
  exact volume_closedCellSlice_toReal a H P R x hparallel

lemma normalVector_eq_frameCombination (a b : Real.Angle) :
    normalVector b = frameNormalCoeff a b • normalVector a +
      frameTangentCoeff a b • tangentVector a := by
  symm
  simpa only [frameNormalCoeff, frameTangentCoeff, real_inner_comm] using
    inner_normalVector_smul_add_inner_tangentVector_smul (normalVector b) a

lemma normalLine_eq_of_frameTangentCoeff_eq_zero {a b : Real.Angle} {h k : ℝ}
    (hb : frameTangentCoeff a b = 0) (hk : frameNormalCoeff a b * h = k) :
    normalLine b k = normalLine a h := by
  have hvec : normalVector b = frameNormalCoeff a b • normalVector a := by
    rw [normalVector_eq_frameCombination a b, hb, zero_smul, add_zero]
  have hcoeff : frameNormalCoeff a b ≠ 0 := by
    intro hc
    have : normalVector b = 0 := by simp [hvec, hc]
    have hnorm : ‖normalVector b‖ = 1 := by
      simpa only [b.coe_toReal] using norm_normalVector_real b.toReal
    rw [this, norm_zero] at hnorm
    norm_num at hnorm
  ext p
  simp only [normalLine, Set.mem_ofPred_eq, hvec, inner_smul_right]
  rw [← hk]
  constructor <;> intro hp
  · exact (mul_left_cancel₀ hcoeff hp)
  · exact congrArg (frameNormalCoeff a b * ·) hp

@[simp] lemma frameNormalCoeff_self (a : Real.Angle) : frameNormalCoeff a a = 1 := by
  simpa only [frameNormalCoeff, a.coe_toReal] using inner_normalVector_self a.toReal

lemma measurableSet_booleanCellSlice {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) :
    MeasurableSet (booleanCellSlice a H P R x) := by
  apply MeasurableSet.inter _ measurableSet_Icc
  have hcont : Continuous (fun y ↦ framePoint a x y) := by
    simp_rw [framePoint_eq]
    fun_prop
  exact (measurableSet_booleanCell H P).preimage hcont.measurable

def actualCellSliceLength {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ) : ℝ := by
  classical
  exact if parallelCellFeasible a H P x then cellSliceLength a H P R x else 0

lemma closedCellSlice_eq_empty_of_not_parallelCellFeasible {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (hparallel : ¬parallelCellFeasible a H P x) :
    closedCellSlice a H P R x = ∅ := by
  classical
  unfold parallelCellFeasible at hparallel
  push Not at hparallel
  obtain ⟨j, hb, hj⟩ := hparallel
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hycell := hy.1
  simp only [closedBooleanCell, Set.mem_iInter] at hycell
  have hjy := hycell j
  change framePoint a x y ∈ normalHalfPlane (H j).angle (H j).height
    (cellUpper H P j) false at hjy
  cases hu : cellUpper H P j <;>
    simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
      Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, zero_mul, add_zero]
      at hj hjy
  · exact hj hjy
  · exact hj hjy

lemma volume_booleanCellSlice_toReal_eq_actual {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (P : Fin n → Bool) (R x : ℝ)
    (_hx : noParallelBoundaryAt a H x) :
    (MeasureTheory.volume (booleanCellSlice a H P R x)).toReal =
      actualCellSliceLength a H P R x := by
  by_cases hp : parallelCellFeasible a H P x
  · simp only [actualCellSliceLength, hp, ↓reduceIte]
    exact volume_booleanCellSlice_toReal a H P R x hp _hx
  · simp only [actualCellSliceLength, hp, ↓reduceIte]
    rw [volume_booleanCellSlice_eq_closedCellSlice a H P R x _hx,
      closedCellSlice_eq_empty_of_not_parallelCellFeasible a H P R x hp,
      MeasureTheory.measure_empty]
    rfl

def frameCoordinates : Point ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

lemma frameCoordinates_measurePreserving :
    MeasureTheory.MeasurePreserving frameCoordinates MeasureTheory.volume
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume) := by
  rw [← MeasureTheory.Measure.volume_eq_prod]
  convert EuclideanSpace.volume_preserving_finTwoCoordinates using 1
  funext p
  rfl

lemma framePoint_measurePreserving (a : Real.Angle) :
    MeasureTheory.MeasurePreserving (fun p : ℝ × ℝ ↦ framePoint a p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume := by
  have hcoordinates : MeasureTheory.MeasurePreserving frameCoordinates.symm
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod MeasureTheory.volume)
      MeasureTheory.volume :=
    frameCoordinates_measurePreserving.symm frameCoordinates
  have hrotation : MeasureTheory.MeasurePreserving
      (EuclideanGeometry.o.rotation a : Point → Point) :=
    LinearIsometryEquiv.measurePreserving _
  convert hrotation.comp hcoordinates using 1
  funext p
  rfl

lemma volume_toReal_eq_integral_frameSlice (a : Real.Angle) {S : Set Point}
    (hS : MeasurableSet S) (hSfinite : MeasureTheory.volume S ≠ ⊤) :
    (MeasureTheory.volume S).toReal =
      ∫ x : ℝ, (MeasureTheory.volume {y : ℝ | framePoint a x y ∈ S}).toReal := by
  let f : ℝ × ℝ → Point := fun p ↦ framePoint a p.1 p.2
  have hf := framePoint_measurePreserving a
  have hpre : MeasurableSet (f ⁻¹' S) := hS.preimage hf.measurable
  have hmeasure : MeasureTheory.volume (f ⁻¹' S) = MeasureTheory.volume S :=
    hf.measure_preimage hS.nullMeasurableSet
  have hprod : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
      MeasureTheory.volume) (f ⁻¹' S) =
      ∫⁻ x : ℝ, MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S)) :=
    MeasureTheory.Measure.prod_apply hpre
  have hsectionMeas : Measurable
      (fun x : ℝ ↦ MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))) :=
    measurable_measure_prodMk_left hpre
  have hsectionFinite : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S)) < ⊤ :=
    MeasureTheory.Measure.ae_measure_lt_top hpre (by
      rw [← MeasureTheory.Measure.volume_eq_prod, hmeasure]
      exact hSfinite)
  rw [← hmeasure]
  calc
    (MeasureTheory.volume (f ⁻¹' S)).toReal =
        (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
          MeasureTheory.volume) (f ⁻¹' S)).toReal := by
      rw [← MeasureTheory.Measure.volume_eq_prod]
    _ = (∫⁻ x : ℝ,
        MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))).toReal :=
      congrArg ENNReal.toReal hprod
    _ = ∫ x : ℝ,
        (MeasureTheory.volume (Prod.mk x ⁻¹' (f ⁻¹' S))).toReal :=
      (MeasureTheory.integral_toReal hsectionMeas.aemeasurable hsectionFinite).symm
    _ = ∫ x : ℝ,
        (MeasureTheory.volume {y : ℝ | framePoint a x y ∈ S}).toReal := by
      rfl

end MovingSofa.Nef
