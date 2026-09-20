import MovingSofa.Polygon.Nef.Variation.LocalSlices
import Mathlib.MeasureTheory.Measure.Hausdorff

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

lemma tendsto_sub_one_div_normalVector (p : Point) (a : Real.Angle) :
    Filter.Tendsto
      (fun k : ℕ ↦ p - (1 / ((k + 1 : ℕ) : ℝ)) • normalVector a)
      Filter.atTop (𝓝 p) := by
  simpa using tendsto_const_nhds.sub
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (normalVector a))

lemma tendsto_add_one_div_normalVector (p : Point) (a : Real.Angle) :
    Filter.Tendsto
      (fun k : ℕ ↦ p + (1 / ((k + 1 : ℕ) : ℝ)) • normalVector a)
      Filter.atTop (𝓝 p) := by
  simpa using tendsto_const_nhds.add
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const
      (normalVector a))

lemma sub_smul_normalVector_mem_carrier (H : PlanarHalfPlaneData)
    (hupper : H.upper = false) {p : Point} (hp : p ∈ H.boundaryLine)
    {t : ℝ} (ht : 0 < t) :
    p - t • normalVector H.angle ∈ H.carrier := by
  change inner ℝ p (normalVector H.angle) = H.height at hp
  rw [PlanarHalfPlaneData.carrier, normalHalfPlane, hupper]
  simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  rw [inner_sub_left, real_inner_smul_left, hp]
  rw [show inner ℝ (normalVector H.angle) (normalVector H.angle) = 1 by
    simpa using inner_normalVector_self H.angle.toReal]
  cases H.strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma add_smul_normalVector_not_mem_carrier (H : PlanarHalfPlaneData)
    (hupper : H.upper = false) {p : Point} (hp : p ∈ H.boundaryLine)
    {t : ℝ} (ht : 0 < t) :
    p + t • normalVector H.angle ∉ H.carrier := by
  change inner ℝ p (normalVector H.angle) = H.height at hp
  rw [PlanarHalfPlaneData.carrier, normalHalfPlane, hupper]
  simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_ofPred_eq]
  rw [inner_add_left, real_inner_smul_left, hp]
  rw [show inner ℝ (normalVector H.angle) (normalVector H.angle) = 1 by
    simpa using inner_normalVector_self H.angle.toReal]
  cases H.strict <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma mem_frontier_booleanSet_of_active {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (p : Point)
    (hline : p ∈ (H i).boundaryLine)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine)
    (hactive : IsActiveBooleanPattern E i
      (setMembershipPattern (fun j ↦ (H j).carrier) p)) :
    p ∈ frontier (booleanSet E (fun j ↦ (H j).carrier)) := by
  let P := setMembershipPattern (fun j ↦ (H j).carrier) p
  let qminus : ℕ → Point := fun k ↦
    p - (1 / ((k + 1 : ℕ) : ℝ)) • normalVector (H i).angle
  let qplus : ℕ → Point := fun k ↦
    p + (1 / ((k + 1 : ℕ) : ℝ)) • normalVector (H i).angle
  have hminus_lim : Filter.Tendsto qminus Filter.atTop (𝓝 p) :=
    tendsto_sub_one_div_normalVector p (H i).angle
  have hplus_lim : Filter.Tendsto qplus Filter.atTop (𝓝 p) :=
    tendsto_add_one_div_normalVector p (H i).angle
  have hlocal := eventually_setMembershipPattern_eq_of_ne H i p hother
  have hminus_local : ∀ᶠ k in Filter.atTop, ∀ j, j ≠ i →
      setMembershipPattern (fun r ↦ (H r).carrier) (qminus k) j = P j :=
    hminus_lim.eventually hlocal
  have hplus_local : ∀ᶠ k in Filter.atTop, ∀ j, j ≠ i →
      setMembershipPattern (fun r ↦ (H r).carrier) (qplus k) j = P j :=
    hplus_lim.eventually hlocal
  have hminus_mem : ∀ᶠ k in Filter.atTop,
      qminus k ∈ booleanSet E (fun j ↦ (H j).carrier) := by
    filter_upwards [hminus_local] with k hk
    have hki : qminus k ∈ (H i).carrier :=
      sub_smul_normalVector_mem_carrier (H i) hupper hline (by positivity)
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) (qminus k) =
        Function.update P i true := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [setMembershipPattern, hki]
      · simpa [Function.update_of_ne hji] using hk j hji
    change E (setMembershipPattern (fun r ↦ (H r).carrier) (qminus k)) = true
    rw [hpattern]
    exact hactive.2
  have hplus_mem : ∀ᶠ k in Filter.atTop,
      qplus k ∈ (booleanSet E (fun j ↦ (H j).carrier))ᶜ := by
    filter_upwards [hplus_local] with k hk
    have hki : qplus k ∉ (H i).carrier :=
      add_smul_normalVector_not_mem_carrier (H i) hupper hline (by positivity)
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) (qplus k) =
        Function.update P i false := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [setMembershipPattern, hki]
      · simpa [Function.update_of_ne hji] using hk j hji
    change E (setMembershipPattern (fun r ↦ (H r).carrier) (qplus k)) ≠ true
    rw [hpattern, hactive.1]
    decide
  rw [frontier_eq_closure_inter_closure]
  exact ⟨mem_closure_of_tendsto hminus_lim hminus_mem,
    mem_closure_of_tendsto hplus_lim hplus_mem⟩

lemma not_mem_frontier_booleanSet_of_not_active {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (p : Point)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine)
    (hinactive : ¬IsActiveBooleanPattern E i
      (setMembershipPattern (fun j ↦ (H j).carrier) p)) :
    p ∉ frontier (booleanSet E (fun j ↦ (H j).carrier)) := by
  let P := setMembershipPattern (fun j ↦ (H j).carrier) p
  let X := booleanSet E (fun j ↦ (H j).carrier)
  have heq : E (Function.update P i false) = E (Function.update P i true) :=
    (not_isActiveBooleanPattern_iff hE i P).mp hinactive
  have hlocal := eventually_setMembershipPattern_eq_of_ne H i p hother
  have hevent : ∀ᶠ q in 𝓝 p,
      (q ∈ X ↔ E (Function.update P i false) = true) := by
    filter_upwards [hlocal] with q hq
    have hpattern : setMembershipPattern (fun r ↦ (H r).carrier) q =
        Function.update P i
          (setMembershipPattern (fun r ↦ (H r).carrier) q i) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simpa [Function.update_of_ne hji] using hq j hji
    change (E (setMembershipPattern (fun r ↦ (H r).carrier) q) = true ↔ _)
    rw [hpattern]
    cases hqi : setMembershipPattern (fun r ↦ (H r).carrier) q i
    · rfl
    · simp [heq]
  cases hvalue : E (Function.update P i false)
  · have hcompl : Xᶜ ∈ 𝓝 p := by
      filter_upwards [hevent] with q hq
      simpa [hvalue] using hq
    have hinter : p ∈ interior Xᶜ := mem_interior_iff_mem_nhds.mpr hcompl
    have hpcompl : p ∈ Xᶜ := interior_subset hinter
    have hnot : p ∉ frontier Xᶜ :=
      (mem_interior_iff_notMem_frontier hpcompl).mp hinter
    simpa [X] using hnot
  · have hset : X ∈ 𝓝 p := by
      filter_upwards [hevent] with q hq
      simpa [hvalue] using hq
    have hinter : p ∈ interior X := mem_interior_iff_mem_nhds.mpr hset
    have hp : p ∈ X := interior_subset hinter
    exact (mem_interior_iff_notMem_frontier hp).mp hinter

lemma mem_frontier_booleanSet_iff_mem_activeBooleanRegion {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (p : Point)
    (hline : p ∈ (H i).boundaryLine)
    (hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine) :
    p ∈ frontier (booleanSet E (fun j ↦ (H j).carrier)) ↔
      p ∈ activeBooleanRegion E H i := by
  rw [mem_activeBooleanRegion_iff]
  constructor
  · intro hfrontier
    by_contra hinactive
    exact (not_mem_frontier_booleanSet_of_not_active hE H i p hother hinactive)
      hfrontier
  · intro hactive
    exact mem_frontier_booleanSet_of_active E H i hupper p hline hother hactive

def frontierLineSlice {n : ℕ} (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R : ℝ) : Set ℝ :=
  {y | framePoint (H i).angle (H i).height y ∈
    frontier (booleanSet E (fun j ↦ (H j).carrier))} ∩ Set.Icc (-R) R

lemma volume_frontierLineSlice_eq_activeRegionSlice {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (M R : ℝ)
    (hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height) :
    MeasureTheory.volume (frontierLineSlice E H i R) =
      MeasureTheory.volume (activeRegionSlice (H i).angle E H i R (H i).height) := by
  apply MeasureTheory.measure_congr
  rw [MeasureTheory.ae_eq_set]
  have hzero := (finite_cellSliceBoundaryExceptions (H i).angle
    (auxiliaryHalfPlaneFamily H i M) (H i).height hno).measure_zero
      MeasureTheory.volume
  have heq : ∀ y,
      y ∉ cellSliceBoundaryExceptions (H i).angle
          (auxiliaryHalfPlaneFamily H i M) (H i).height →
        (y ∈ frontierLineSlice E H i R ↔
          y ∈ activeRegionSlice (H i).angle E H i R (H i).height) := by
    intro y hy
    let p := framePoint (H i).angle (H i).height y
    have hline : p ∈ (H i).boundaryLine := by
      change inner ℝ p (normalVector (H i).angle) = (H i).height
      exact inner_framePoint_normalVector _ _ _
    have hother : ∀ j, j ≠ i → p ∉ (H j).boundaryLine := by
      intro j hji hj
      apply hy
      apply Set.mem_iUnion.mpr
      refine ⟨j, ?_⟩
      change inner ℝ p (normalVector (H j).angle) = (H j).height at hj
      simpa [p, auxiliaryHalfPlaneFamily_of_ne H i j M hji] using hj
    have hfrontier := mem_frontier_booleanSet_iff_mem_activeBooleanRegion
      hE H i hupper p hline hother
    constructor
    · rintro ⟨hyfrontier, hyR⟩
      exact ⟨hfrontier.mp hyfrontier, hyR⟩
    · rintro ⟨hyactive, hyR⟩
      exact ⟨hfrontier.mpr hyactive, hyR⟩
  constructor <;> apply MeasureTheory.measure_mono_null _ hzero
  · intro y hy
    by_contra hyexception
    exact hy.2 ((heq y hyexception).mp hy.1)
  · intro y hy
    by_contra hyexception
    exact hy.2 ((heq y hyexception).mpr hy.1)

lemma lineMap_framePoint (a : Real.Angle) (h y : ℝ) :
    AffineMap.lineMap (framePoint a h 0) (framePoint a h 1) y =
      framePoint a h y := by
  simp only [AffineMap.lineMap_apply_module', framePoint_eq, zero_smul,
    add_zero, one_smul]
  module

lemma dist_framePoint_zero_one (a : Real.Angle) (h : ℝ) :
    dist (framePoint a h 0) (framePoint a h 1) = 1 := by
  rw [dist_eq_norm]
  simp only [framePoint_eq, zero_smul, add_zero, one_smul]
  rw [show h • normalVector a - (h • normalVector a + tangentVector a) =
      -tangentVector a by module]
  simp [norm_tangentVector_angle]

lemma frontier_booleanSet_inter_boundaryLine_eq_image_frontierLineSlice {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (R : ℝ)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R) :
    frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩ (H i).boundaryLine =
      AffineMap.lineMap
        (framePoint (H i).angle (H i).height 0)
        (framePoint (H i).angle (H i).height 1) ''
          frontierLineSlice E H i R := by
  ext p
  constructor
  · rintro ⟨hpfrontier, hpline⟩
    let y := inner ℝ p (tangentVector (H i).angle)
    have hpnormal : inner ℝ p (normalVector (H i).angle) = (H i).height := hpline
    have hparam : framePoint (H i).angle (H i).height y = p := by
      rw [framePoint_eq, ← hpnormal]
      exact inner_normalVector_smul_add_inner_tangentVector_smul p (H i).angle
    have hpball : p ∈ Metric.closedBall (0 : Point) R := by
      have hpclosure : p ∈ closure (booleanSet E (fun j ↦ (H j).carrier)) :=
        frontier_subset_closure hpfrontier
      exact (closure_minimal hBound Metric.isClosed_closedBall) hpclosure
    have hynorm := abs_real_inner_le_norm p (tangentVector (H i).angle)
    rw [norm_tangentVector_angle, mul_one] at hynorm
    have hpnorm : ‖p‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_left] using hpball
    have hyR : y ∈ Set.Icc (-R) R := abs_le.mp (hynorm.trans hpnorm)
    refine ⟨y, ⟨?_, ?_⟩⟩
    · exact ⟨by simpa [frontierLineSlice, hparam] using hpfrontier, hyR⟩
    · rw [lineMap_framePoint, hparam]
  · rintro ⟨y, hy, rfl⟩
    rw [lineMap_framePoint]
    refine ⟨hy.1, ?_⟩
    change inner ℝ (framePoint (H i).angle (H i).height y)
      (normalVector (H i).angle) = (H i).height
    exact inner_framePoint_normalVector _ _ _

lemma hausdorffMeasure_frontier_inter_boundaryLine_eq_volume_slice {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (R : ℝ)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R) :
    MeasureTheory.Measure.hausdorffMeasure 1
        (frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩ (H i).boundaryLine) =
      MeasureTheory.volume (frontierLineSlice E H i R) := by
  rw [frontier_booleanSet_inter_boundaryLine_eq_image_frontierLineSlice
    E H i R hBound, MeasureTheory.hausdorffMeasure_lineMap_image,
    MeasureTheory.hausdorffMeasure_real]
  have hdist := dist_framePoint_zero_one (H i).angle (H i).height
  have hnndist : nndist
      (framePoint (H i).angle (H i).height 0)
      (framePoint (H i).angle (H i).height 1) = 1 := by
    apply NNReal.eq
    simpa using hdist
  rw [hnndist, one_smul]

lemma hausdorffMeasure_frontier_toReal_eq_activeSliceLength {n : ℕ}
    {E : BooleanFunction n} (hE : IsMonotoneBooleanFunction E)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (hupper : (H i).upper = false) (M R : ℝ)
    (hM : (H i).height ≤ M)
    (hBound : booleanSet E (fun j ↦ (H j).carrier) ⊆ Metric.closedBall 0 R)
    (hno : noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i M) (H i).height) :
    (MeasureTheory.Measure.hausdorffMeasure 1
      (frontier (booleanSet E (fun j ↦ (H j).carrier)) ∩
        (H i).boundaryLine)).toReal =
      activeSliceLength (H i).angle E
        (auxiliaryHalfPlaneFamily H i M) i R (H i).height := by
  rw [hausdorffMeasure_frontier_inter_boundaryLine_eq_volume_slice E H i R hBound,
    volume_frontierLineSlice_eq_activeRegionSlice hE H i hupper M R hno]
  exact volume_activeRegionSlice_toReal_eq_activeSliceLength E H i M R
    (H i).height hM hno

end MovingSofa.Nef
