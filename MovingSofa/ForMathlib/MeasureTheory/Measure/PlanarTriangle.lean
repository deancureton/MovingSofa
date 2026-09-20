import MovingSofa.ForMathlib.MeasureTheory.RegionBetween
import MovingSofa.ForMathlib.MeasureTheory.Measure.HaarNullSets
import Mathlib.Analysis.Convex.Combination

/-!
# The area of a planar triangle

The convex hull of three points of the Euclidean plane has area one half of the absolute
determinant of the two edge vectors emanating from the first point. The proof transports the
standard right triangle, whose area is computed by integration, along the linear map sending
the coordinate basis to the two edge vectors.
-/

open MeasureTheory Set
open scoped Pointwise

namespace EuclideanSpace

private def standardTriangleProd : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioc 0 1 ∧ p.2 ∈ Icc 0 (1 - p.1)}

private theorem measurableSet_standardTriangleProd : MeasurableSet standardTriangleProd := by
  have h : MeasurableSet {p : ℝ × ℝ | (0 < p.1 ∧ p.1 ≤ 1) ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 - p.1} :=
    ((measurableSet_lt measurable_const measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const)).inter
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_const.sub measurable_fst)))
  simpa only [standardTriangleProd, Set.mem_Ioc, Set.mem_Icc] using h

private theorem volume_standardTriangleProd :
    volume standardTriangleProd = ENNReal.ofReal (1 / 2) := by
  rw [show standardTriangleProd =
      {p : ℝ × ℝ | p.1 ∈ Ioc 0 1 ∧ p.2 ∈ Icc (0 : ℝ) (1 - p.1)} from rfl,
    volume_setOf_mem_Icc_eq_volume_regionBetween
      (f := fun _ : ℝ ↦ 0) (g := fun x ↦ 1 - x) (s := Ioc 0 1)
      measurable_const (measurable_const.sub measurable_id) measurableSet_Ioc]
  simpa using
    (volume_regionBetween_triangle (b := 1) (h := 1)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 1))

private def standardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ∈ Ioc 0 1 ∧ p 1 ∈ Icc 0 (1 - p 0)}

private theorem volume_standardTriangle : volume standardTriangle = ENNReal.ofReal (1 / 2) := by
  have hpre := volume_preserving_finTwoCoordinates.measure_preimage
    measurableSet_standardTriangleProd.nullMeasurableSet
  rw [show (fun p : EuclideanSpace ℝ (Fin 2) ↦ (p 0, p 1)) ⁻¹' standardTriangleProd =
      standardTriangle from rfl, volume_standardTriangleProd] at hpre
  exact hpre

private def closedStandardTriangle : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 1 - p 0}

private theorem volume_closedStandardTriangle :
    volume closedStandardTriangle = ENNReal.ofReal (1 / 2) := by
  rw [← volume_standardTriangle]
  refine (measure_eq_measure_of_null_sdiff (μ := volume) ?_ ?_).symm
  · exact fun p hp ↦ ⟨hp.1.1.le, hp.2⟩
  · refine measure_mono_null
      (t := {p : EuclideanSpace ℝ (Fin 2) | inner ℝ p (EuclideanSpace.single 0 (1 : ℝ)) = 0})
      (fun p hp ↦ ?_) ?_
    · have hp0 : p 0 = 0 := by
        refine le_antisymm (le_of_not_gt fun hpos ↦ hp.2 ⟨⟨hpos, ?_⟩, hp.1.2⟩) hp.1.1
        linarith [hp.1.2.1, hp.1.2.2]
      simpa [EuclideanSpace.inner_single_right] using hp0
    · refine volume.addHaar_setOf_real_inner_eq (fun h ↦ ?_) 0
      have hone : (1 : ℝ) = 0 := by
        simpa [PiLp.single_apply] using congrArg (fun p : EuclideanSpace ℝ (Fin 2) ↦ p 0) h
      exact one_ne_zero hone

private def standardTriangleVertices : Set (EuclideanSpace ℝ (Fin 2)) :=
  {0, EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)}

private theorem convex_closedStandardTriangle : Convex ℝ closedStandardTriangle := by
  intro p hp q hq a b ha hb hab
  simp only [closedStandardTriangle, Set.mem_ofPred_eq] at hp hq ⊢
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    nlinarith [hp.1, hq.1, hp.2.1, hq.2.1, hp.2.2, hq.2.2]

private theorem convexHull_standardTriangleVertices :
    convexHull ℝ standardTriangleVertices = closedStandardTriangle := by
  refine Set.Subset.antisymm (convexHull_min (fun p hp ↦ ?_) convex_closedStandardTriangle)
    (fun p hp ↦ ?_)
  · simp only [standardTriangleVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;>
      norm_num [closedStandardTriangle, PiLp.single_apply]
  · simp only [closedStandardTriangle, Set.mem_ofPred_eq] at hp
    refine mem_convexHull_of_exists_fintype ![1 - p 0 - p 1, p 0, p 1]
      ![0, EuclideanSpace.single 0 (1 : ℝ), EuclideanSpace.single 1 (1 : ℝ)] ?_ ?_ ?_ ?_
    · intro i
      fin_cases i <;> simp <;> linarith
    · simp [Fin.sum_univ_succ]
    · intro i
      fin_cases i <;> simp [standardTriangleVertices]
    · ext i
      fin_cases i <;> simp [Fin.sum_univ_succ]

private def triangleMap (u v : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := p 0 • u + p 1 • v
  map_add' p q := by
    ext i
    simp [add_smul, add_assoc, add_left_comm]
  map_smul' c p := by
    ext i
    simp [mul_smul]

private theorem det_triangleMap (u v : EuclideanSpace ℝ (Fin 2)) :
    LinearMap.det (triangleMap u v) = u 0 * v 1 - v 0 * u 1 := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 2)), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, PiLp.basisFun_repr, triangleMap,
    PiLp.basisFun_apply, Fin.isValue]
  norm_num

private theorem convexHull_triple_eq_image (u v : EuclideanSpace ℝ (Fin 2)) :
    convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) =
      triangleMap u v '' closedStandardTriangle := by
  have himage : triangleMap u v '' standardTriangleVertices =
      ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [standardTriangleVertices, Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl | rfl <;> simp [triangleMap]
    · intro hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl
      · exact ⟨0, by simp [standardTriangleVertices], by simp [triangleMap]⟩
      · exact ⟨EuclideanSpace.single 0 (1 : ℝ), by simp [standardTriangleVertices],
          by simp [triangleMap]⟩
      · exact ⟨EuclideanSpace.single 1 (1 : ℝ), by simp [standardTriangleVertices],
          by simp [triangleMap]⟩
  rw [← himage, ← LinearMap.image_convexHull, convexHull_standardTriangleVertices]

/-- The triangle spanned by the origin and two vectors of the Euclidean plane has area one
half of the absolute determinant of their coordinates. -/
theorem volume_convexHull_zero_pair (u v : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({0, u, v} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal (|u 0 * v 1 - v 0 * u 1| / 2) := by
  rw [convexHull_triple_eq_image, Measure.addHaar_image_linearMap, det_triangleMap,
    volume_closedStandardTriangle, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  ring

/-- The area of a planar triangle is one half of the absolute coordinate determinant of its
two edge vectors. -/
theorem volume_convexHull_triple (a b c : EuclideanSpace ℝ (Fin 2)) :
    volume (convexHull ℝ ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2)))) =
      ENNReal.ofReal (|(b - a) 0 * (c - a) 1 - (c - a) 0 * (b - a) 1| / 2) := by
  have hvertices : ({a, b, c} : Set (EuclideanSpace ℝ (Fin 2))) =
      a +ᵥ ({0, b - a, c - a} : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext p
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_vadd_set]
    constructor
    · intro hp
      rcases hp with hp | hp | hp
      · exact ⟨0, by simp, by simp [hp]⟩
      · refine ⟨b - a, by simp, ?_⟩
        rw [hp]
        change a + (b - a) = b
        abel
      · refine ⟨c - a, by simp, ?_⟩
        rw [hp]
        change a + (c - a) = c
        abel
    · rintro ⟨q, hq, hp⟩
      rcases hq with hq | hq | hq
      · subst hq
        simp at hp
        exact hp ▸ Or.inl rfl
      · refine Or.inr (Or.inl ?_)
        rw [← hp, hq]
        change a + (b - a) = b
        abel
      · refine Or.inr (Or.inr ?_)
        rw [← hp, hq]
        change a + (c - a) = c
        abel
  rw [hvertices, convexHull_vadd, measure_vadd, volume_convexHull_zero_pair]

end EuclideanSpace

