import MovingSofa.Polygon.Polyline.Basic
import MovingSofa.ForMathlib.Geometry.Euclidean.Segment
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

noncomputable section

namespace MovingSofa

private lemma fst_mem_Icc_of_mem_segment {a b q : Point}
    (hab : a 0 ≤ b 0) (hq : q ∈ segment ℝ a b) : q 0 ∈ Set.Icc (a 0) (b 0) := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  change a 0 + r * (b 0 - a 0) ∈ Set.Icc (a 0) (b 0)
  constructor <;> nlinarith [hr.1, hr.2]

private lemma eq_right_of_mem_segment_of_fst_eq {a b q : Point}
    (hab : a 0 < b 0) (hq : q ∈ segment ℝ a b) (heq : q 0 = b 0) : q = b := by
  rw [segment_eq_image'] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  have hcoord : a 0 + r * (b 0 - a 0) = b 0 := heq
  have hrone : r = 1 := by nlinarith
  simp [hrone]

/-- Distinct increasing polyline segments meet only at a possible common endpoint. -/
lemma XMonotonePolylineData.segment_inter_subset_singleton
    (p : XMonotonePolylineData) {i j : Fin p.edges} (hij : i < j) :
    segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ∩
        segment ℝ (p.vertices j.castSucc) (p.vertices j.succ) ⊆
      {p.vertices i.succ} := by
  intro q hq
  have hi := fst_mem_Icc_of_mem_segment (p.increasing i.castSucc_lt_succ).le hq.1
  have hj := fst_mem_Icc_of_mem_segment (p.increasing j.castSucc_lt_succ).le hq.2
  have hindex : i.succ ≤ j.castSucc := by
    change i.val + 1 ≤ j.val
    exact hij
  have horder := p.increasing.monotone hindex
  apply Set.mem_singleton_iff.mpr
  exact eq_right_of_mem_segment_of_fst_eq (p.increasing i.castSucc_lt_succ) hq.1
    (le_antisymm hi.2 (horder.trans hj.1))

open MeasureTheory

/-- The segments of an increasing polyline are almost disjoint for length measure. -/
lemma XMonotonePolylineData.pairwise_aedisjoint_segments
    (p : XMonotonePolylineData) :
    Pairwise (fun i j : Fin p.edges ↦ AEDisjoint (Measure.hausdorffMeasure 1)
      (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ))
      (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ))) := by
  have := Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  have hlt (i j : Fin p.edges) (hij : i < j) :
      AEDisjoint (Measure.hausdorffMeasure 1)
        (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ))
        (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ)) := by
    exact measure_mono_null (p.segment_inter_subset_singleton hij) (measure_singleton _)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hlt i j h
  · exact (hlt j i h).symm

/-- A supporting-line slice has the sum of the lengths of its parallel segments. -/
lemma XMonotonePolylineData.hausdorffMeasure_carrier_inter_hyperplane
    (p : XMonotonePolylineData) (n : Point) (c : ℝ)
    (hparallel : ∀ i : Fin p.edges,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 →
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        {q | inner ℝ q n = c}) :
    Measure.hausdorffMeasure 1 (p.carrier ∩ {q | inner ℝ q n = c}) =
      ∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 then
          ENNReal.ofReal (dist (p.vertices i.castSucc) (p.vertices i.succ)) else 0 := by
  classical
  have hd : Pairwise (fun i j : Fin p.edges ↦ AEDisjoint (Measure.hausdorffMeasure 1)
      (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ∩ {q | inner ℝ q n = c})
      (segment ℝ (p.vertices j.castSucc) (p.vertices j.succ) ∩ {q | inner ℝ q n = c})) := by
    intro i j hij
    exact (p.pairwise_aedisjoint_segments hij).mono Set.inter_subset_left Set.inter_subset_left
  rw [XMonotonePolylineData.carrier, Set.iUnion_inter, measure_iUnion₀ hd, tsum_fintype]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0
    · rw [ite_eq_left hi, Set.inter_eq_left.mpr (hparallel i hi), hausdorffMeasure_segment,
        edist_dist]
    · rw [ite_eq_right hi]
      exact EuclideanGeometry.hausdorffMeasure_segment_inter_hyperplane_eq_zero hi
  · intro i
    have hc : IsCompact (segment ℝ (p.vertices i.castSucc) (p.vertices i.succ)) := by
      rw [segment_eq_image']
      exact isCompact_Icc.image (by fun_prop)
    exact (hc.isClosed.measurableSet.inter
      (isClosed_eq (by fun_prop) continuous_const).measurableSet).nullMeasurableSet

/-- The real length of a supporting-line slice is the sum of its parallel segment lengths. -/
lemma XMonotonePolylineData.toReal_hausdorffMeasure_carrier_inter_hyperplane
    (p : XMonotonePolylineData) (n : Point) (c : ℝ)
    (hparallel : ∀ i : Fin p.edges,
      inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 →
      segment ℝ (p.vertices i.castSucc) (p.vertices i.succ) ⊆
        {q | inner ℝ q n = c}) :
    (Measure.hausdorffMeasure 1 (p.carrier ∩ {q | inner ℝ q n = c})).toReal =
      ∑ i : Fin p.edges,
        if inner ℝ (p.vertices i.succ - p.vertices i.castSucc) n = 0 then
          dist (p.vertices i.castSucc) (p.vertices i.succ) else 0 := by
  classical
  rw [p.hausdorffMeasure_carrier_inter_hyperplane n c hparallel,
    ENNReal.toReal_sum (by intro i _; split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [dist_nonneg]

end MovingSofa
