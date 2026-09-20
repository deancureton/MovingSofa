import MovingSofa.Polygon.Nef.Slices
import MovingSofa.Polygon.Nef.Height

noncomputable section

namespace MovingSofa.Nef

open Filter Topology

def auxiliaryHalfPlaneFamily {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (M : ℝ) : Fin n → PlanarHalfPlaneData :=
  Function.update H i
    { angle := (H i).angle, height := M, upper := false, strict := false }

@[simp] lemma auxiliaryHalfPlaneFamily_self {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (M : ℝ) :
    auxiliaryHalfPlaneFamily H i M i =
      { angle := (H i).angle, height := M, upper := false, strict := false } := by
  simp [auxiliaryHalfPlaneFamily]

lemma auxiliaryHalfPlaneFamily_of_ne {n : ℕ}
    (H : Fin n → PlanarHalfPlaneData) (i j : Fin n) (M : ℝ) (hji : j ≠ i) :
    auxiliaryHalfPlaneFamily H i M j = H j := by
  simp [auxiliaryHalfPlaneFamily, Function.update_of_ne hji]

lemma noParallelBoundaryAt_auxiliary {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hLines : Function.Injective (fun j ↦ (H j).boundaryLine))
    (R ε₀ : ℝ) (hR : 0 < R) (hε₀ : 0 < ε₀) :
    noParallelBoundaryAt (H i).angle
      (auxiliaryHalfPlaneFamily H i (|(H i).height| + ε₀ + R + 1)) (H i).height := by
  intro j hb
  by_cases hji : j = i
  · subst j
    simp only [auxiliaryHalfPlaneFamily_self, frameNormalCoeff_self]
    have hh : (H i).height < |(H i).height| + ε₀ + R + 1 := by
      linarith [le_abs_self (H i).height]
    simpa only [one_mul] using ne_of_lt hh
  · rw [auxiliaryHalfPlaneFamily_of_ne H i j _ hji] at hb ⊢
    intro heq
    have hline : (H j).boundaryLine = (H i).boundaryLine := by
      exact normalLine_eq_of_frameTangentCoeff_eq_zero hb heq
    exact hji (hLines hline)

lemma eventually_parallel_inequalities_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∀ᶠ x in 𝓝 h, ∀ j, frameTangentCoeff a (H j).angle = 0 →
      (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
          frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
        ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
          (H j).height ≤ frameNormalCoeff a (H j).angle * h) := by
  suffices ∀ᶠ x in 𝓝 h, ∀ j ∈ (Set.univ : Set (Fin n)),
      frameTangentCoeff a (H j).angle = 0 →
        (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
            frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
          ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
            (H j).height ≤ frameNormalCoeff a (H j).angle * h) by
    exact this.mono fun x hx j ↦ hx j (Set.mem_univ j)
  apply (Filter.eventually_all_finite Set.finite_univ).2
  intro j _
  by_cases hb : frameTangentCoeff a (H j).angle = 0
  · have hne := hh j hb
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hev : ∀ᶠ x in 𝓝 h,
          frameNormalCoeff a (H j).angle * x < (H j).height :=
        (continuousAt_const.mul continuousAt_id).eventually_lt continuousAt_const hlt
      filter_upwards [hev] with x hx
      intro _
      constructor <;> constructor <;> intro <;> linarith
    · have hev : ∀ᶠ x in 𝓝 h,
          (H j).height < frameNormalCoeff a (H j).angle * x :=
        continuousAt_const.eventually_lt (continuousAt_const.mul continuousAt_id) hgt
      filter_upwards [hev] with x hx
      intro _
      constructor <;> constructor <;> intro <;> linarith
  · exact Filter.Eventually.of_forall fun _ hb' ↦ (hb hb').elim

lemma eventually_parallelCellFeasible_iff {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∀ᶠ x in 𝓝 h, ∀ P : Fin n → Bool,
      parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h := by
  filter_upwards [eventually_parallel_inequalities_iff a H h hh] with x hx
  intro P
  constructor <;> intro hp j hb
  · have hj := hp j hb
    have hiff := hx j hb
    cases hu : cellUpper H P j <;>
      simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, mul_zero, add_zero]
        at hj ⊢
    · exact hiff.1.mp hj
    · exact hiff.2.mp hj
  · have hj := hp j hb
    have hiff := hx j hb
    cases hu : cellUpper H P j <;>
      simp only [normalHalfPlane, hu, Bool.false_eq_true, ↓reduceIte,
        Set.mem_ofPred_eq, inner_framePoint_normalVector_eq, hb, mul_zero, add_zero]
        at hj ⊢
    · exact hiff.1.mpr hj
    · exact hiff.2.mpr hj

lemma exists_parallel_stability_radius {n : ℕ} (a : Real.Angle)
    (H : Fin n → PlanarHalfPlaneData) (h : ℝ) (hh : noParallelBoundaryAt a H h) :
    ∃ ε > 0, ∀ x, |x - h| ≤ ε →
      noParallelBoundaryAt a H x ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) := by
  have hev : ∀ᶠ x in 𝓝 h,
      (∀ j, frameTangentCoeff a (H j).angle = 0 →
        (frameNormalCoeff a (H j).angle * x ≤ (H j).height ↔
            frameNormalCoeff a (H j).angle * h ≤ (H j).height) ∧
          ((H j).height ≤ frameNormalCoeff a (H j).angle * x ↔
            (H j).height ≤ frameNormalCoeff a (H j).angle * h)) ∧
        ∀ P : Fin n → Bool,
          (parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) :=
    (eventually_parallel_inequalities_iff a H h hh).and
      (eventually_parallelCellFeasible_iff a H h hh)
  rcases (Metric.mem_nhds_iff.mp hev) with ⟨r, hr, hball⟩
  refine ⟨r / 2, by positivity, ?_⟩
  intro x hx
  have hxr : x ∈ Metric.ball h r := by
    rw [Metric.mem_ball, Real.dist_eq]
    calc
      |x - h| ≤ r / 2 := hx
      _ < r := by linarith
  have hstable := hball hxr
  refine ⟨?_, hstable.2⟩
  intro j hb heq
  have hj := hstable.1 j hb
  apply hh j hb
  apply le_antisymm
  · exact hj.1.mp (by rw [heq])
  · exact hj.2.mp (by rw [heq])

lemma setMembershipPattern_auxiliary {n : ℕ} (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (M : ℝ) (p : Point)
    (hp : p ∈ (auxiliaryHalfPlaneFamily H i M i).carrier) :
    setMembershipPattern (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) p =
      Function.update (setMembershipPattern (fun j ↦ (H j).carrier) p) i true := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    rw [auxiliaryHalfPlaneFamily_self] at hp
    simp [setMembershipPattern, hp]
  · simp [setMembershipPattern, auxiliaryHalfPlaneFamily_of_ne H i j M hji,
      Function.update_of_ne hji]

lemma mem_activeBooleanRegion_iff_mem_booleanCell_auxiliary {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M : ℝ) (p : Point) (hp : p ∈ (auxiliaryHalfPlaneFamily H i M i).carrier) :
    p ∈ activeBooleanRegion E H i ↔
      ∃ P ∈ activeBooleanPatterns E i,
        p ∈ booleanCell (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) P := by
  classical
  rw [mem_activeBooleanRegion_iff]
  constructor
  · intro hactive
    unfold IsActiveBooleanPattern at hactive
    let P := setMembershipPattern
      (fun j ↦ (auxiliaryHalfPlaneFamily H i M j).carrier) p
    have hP : P = Function.update
        (setMembershipPattern (fun j ↦ (H j).carrier) p) i true :=
      setMembershipPattern_auxiliary H i M p hp
    refine ⟨P, ?_, (mem_booleanCell_iff _ _ _).mpr rfl⟩
    simp only [activeBooleanPatterns, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold IsActiveBooleanPattern
    rw [hP]
    simpa only [Function.update_idem] using hactive
  · rintro ⟨P, hP, hcell⟩
    simp only [activeBooleanPatterns, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP
    have hpattern := (mem_booleanCell_iff _ P p).mp hcell
    have haux := setMembershipPattern_auxiliary H i M p hp
    unfold IsActiveBooleanPattern at hP ⊢
    rw [hpattern] at haux
    rw [haux] at hP
    simpa only [Function.update_idem] using hP

def activeRegionSlice {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R x : ℝ) : Set ℝ :=
  {y | framePoint a x y ∈ activeBooleanRegion E H i} ∩ Set.Icc (-R) R

lemma frameSlice_perturbSdiff_eq {n : ℕ} {E : BooleanFunction n}
    (hE : IsMonotoneBooleanFunction E) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (hSide : (H i).upper = false) (R ε₀ δ ε x : ℝ)
    (hδ : |δ| ≤ ε₀)
    (hBound : ∀ z : ℝ, |z| ≤ ε₀ →
      perturbNefHeight E H i z ⊆ Metric.closedBall 0 R) :
    (x ∈ heightInterval (H i).strict (H i).height δ ε →
      {y : ℝ | framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε} =
        activeRegionSlice (H i).angle E H i R x) ∧
    (x ∉ heightInterval (H i).strict (H i).height δ ε →
      {y : ℝ | framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε} = ∅) := by
  constructor
  · intro hx
    rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
      inner_framePoint_normalVector, hx, true_and, activeRegionSlice]
    constructor
    · intro hy
      refine ⟨hy, ?_⟩
      have hdiff : framePoint (H i).angle x y ∈
          perturbNefHeight E H i δ \ perturbNefHeight E H i ε := by
        rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
        exact ⟨by simpa using hx, hy⟩
      have hball := hBound δ hδ hdiff.1
      have hynorm := abs_real_inner_le_norm (framePoint (H i).angle x y)
        (tangentVector (H i).angle)
      rw [inner_framePoint_tangentVector, norm_tangentVector_angle, mul_one] at hynorm
      have hpR : ‖framePoint (H i).angle x y‖ ≤ R := by
        simpa [Metric.mem_closedBall, dist_zero_left] using hball
      exact abs_le.mp (hynorm.trans hpR)
    · exact fun hy ↦ hy.1
  · intro hx
    rw [perturbNefHeight_sdiff_eq_heightInterval hE H i hSide]
    ext y
    simp [hx]

lemma activeRegionSlice_eq_biUnion_booleanCellSlice_auxiliary {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M) :
    activeRegionSlice (H i).angle E H i R x =
      ⋃ P ∈ activeBooleanPatterns E i,
        booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x := by
  classical
  ext y
  have haux : framePoint (H i).angle x y ∈
      (auxiliaryHalfPlaneFamily H i M i).carrier := by
    simp [PlanarHalfPlaneData.carrier, normalHalfPlane, hxM]
  rw [activeRegionSlice, Set.mem_inter_iff, Set.mem_ofPred_eq,
    mem_activeBooleanRegion_iff_mem_booleanCell_auxiliary E H i M _ haux]
  simp only [Set.mem_iUnion, booleanCellSlice, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨P, hP, hyP⟩, hyR⟩
    exact ⟨P, ⟨hP, hyP, hyR⟩⟩
  · rintro ⟨P, hP, hyP, hyR⟩
    exact ⟨⟨P, hP, hyP⟩, hyR⟩

lemma measure_activeRegionSlice_eq_sum {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M) :
    MeasureTheory.volume (activeRegionSlice (H i).angle E H i R x) =
      ∑ P ∈ activeBooleanPatterns E i,
        MeasureTheory.volume
          (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x) := by
  rw [activeRegionSlice_eq_biUnion_booleanCellSlice_auxiliary E H i M R x hxM]
  apply MeasureTheory.measure_biUnion_finset
  · intro P hP Q hQ hPQ
    change Disjoint
      (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x)
      (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) Q R x)
    rw [Set.disjoint_left]
    intro y hyP hyQ
    apply hPQ
    have hcellP := hyP.1
    have hcellQ := hyQ.1
    have hp := (mem_booleanCell_iff _ P _).mp hcellP
    have hq := (mem_booleanCell_iff _ Q _).mp hcellQ
    exact hp.symm.trans hq
  · intro P _
    exact measurableSet_booleanCellSlice _ _ _ _ _

def activeSliceLength {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R x : ℝ) : ℝ :=
  ∑ P ∈ activeBooleanPatterns E i, actualCellSliceLength a H P R x

def frozenActiveSliceLength {n : ℕ} (a : Real.Angle) (E : BooleanFunction n)
    (H : Fin n → PlanarHalfPlaneData) (i : Fin n) (R h x : ℝ) : ℝ := by
  classical
  exact ∑ P ∈ activeBooleanPatterns E i,
    if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0

lemma continuous_frozenActiveSliceLength {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h : ℝ) :
    Continuous (frozenActiveSliceLength a E H i R h) := by
  classical
  unfold frozenActiveSliceLength
  apply continuous_finsetSum
  intro P hP
  by_cases hp : parallelCellFeasible a H P h
  · simpa [hp] using continuous_cellSliceLength a H P R
  · simpa [hp] using (continuous_const : Continuous (fun _ : ℝ ↦ (0 : ℝ)))

lemma activeSliceLength_eq_frozen_of_stable {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h x : ℝ)
    (hstable : ∀ P : Fin n → Bool,
      parallelCellFeasible a H P x ↔ parallelCellFeasible a H P h) :
    activeSliceLength a E H i R x = frozenActiveSliceLength a E H i R h x := by
  classical
  unfold activeSliceLength frozenActiveSliceLength
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hp : parallelCellFeasible a H P h
  · have hpx := (hstable P).mpr hp
    simp [actualCellSliceLength, hp, hpx]
  · have hpx : ¬parallelCellFeasible a H P x := fun hx ↦ hp ((hstable P).mp hx)
    simp [actualCellSliceLength, hp, hpx]

lemma abs_frozenActiveSliceLength_sub_le {n : ℕ} (a : Real.Angle)
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData)
    (i : Fin n) (R h x z : ℝ) :
    |frozenActiveSliceLength a E H i R h x -
        frozenActiveSliceLength a E H i R h z| ≤
      ((activeBooleanPatterns E i).card : ℝ) * (2 * slopeBound a H) * |x - z| := by
  classical
  unfold frozenActiveSliceLength
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ P ∈ activeBooleanPatterns E i,
        ((if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0) -
          if parallelCellFeasible a H P h then cellSliceLength a H P R z else 0)| ≤
        ∑ P ∈ activeBooleanPatterns E i,
          |(if parallelCellFeasible a H P h then cellSliceLength a H P R x else 0) -
            if parallelCellFeasible a H P h then cellSliceLength a H P R z else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _P ∈ activeBooleanPatterns E i,
        (2 * slopeBound a H) * |x - z| := by
      apply Finset.sum_le_sum
      intro P hP
      by_cases hp : parallelCellFeasible a H P h
      · simpa [hp] using abs_cellSliceLength_sub_le a H P R x z
      · simp only [hp, ↓reduceIte, sub_self, abs_zero]
        exact mul_nonneg (mul_nonneg (by norm_num) (slopeBound_nonneg a H))
          (abs_nonneg _)
    _ = ((activeBooleanPatterns E i).card : ℝ) * (2 * slopeBound a H) *
        |x - z| := by
      simp
      ring

lemma volume_activeRegionSlice_toReal_eq_activeSliceLength {n : ℕ}
    (E : BooleanFunction n) (H : Fin n → PlanarHalfPlaneData) (i : Fin n)
    (M R x : ℝ) (hxM : x ≤ M)
    (hx : noParallelBoundaryAt (H i).angle (auxiliaryHalfPlaneFamily H i M) x) :
    (MeasureTheory.volume (activeRegionSlice (H i).angle E H i R x)).toReal =
      activeSliceLength (H i).angle E (auxiliaryHalfPlaneFamily H i M) i R x := by
  rw [measure_activeRegionSlice_eq_sum E H i M R x hxM]
  unfold activeSliceLength
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro P hP
    exact volume_booleanCellSlice_toReal_eq_actual _ _ _ _ _ hx
  · intro P hP
    apply ne_of_lt
    calc
      MeasureTheory.volume
          (booleanCellSlice (H i).angle (auxiliaryHalfPlaneFamily H i M) P R x) ≤
          MeasureTheory.volume (Set.Icc (-R) R) :=
        MeasureTheory.measure_mono Set.inter_subset_right
      _ = ENNReal.ofReal (R - -R) := Real.volume_Icc
      _ < ⊤ := ENNReal.ofReal_lt_top

end MovingSofa.Nef
