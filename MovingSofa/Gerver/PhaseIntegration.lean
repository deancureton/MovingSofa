import MovingSofa.Gerver.PhaseMeasures
import MovingSofa.Area.QVariation

/-!
# Integrating the variation of `𝒬` over the Gerver phases

The ten phase windows `gerverPhaseAngles j` partition the angular window `[0, π]` except for the
single angle `π/2`, and six of them cover the domain of the inner-corner measure except for two
angles.  Since the cap surface measure integrates a continuous integrand and the corner measure
has no atoms, `qVariationIntegral_eq_phaseSum` rewrites the four integrals of the variation
formula as the eight contributions of the source table (`gerverPhaseContribution`), grouped so
that `gerver_phaseMeasures` applies to each of them.

`gerverPhaseContribution_nonpos` then signs each contribution.  Six of the eight vanish or cancel
outright against the corner measure; on the two active right windows and the two active left
windows the phase identities turn the remaining cap measure into the tail measure, and the
resulting integrand is the difference between the competitor's support sum and the base support
sum, which is `≤ 1 - 1 = 0` by the cap-tail constraints.
-/

noncomputable section

open MeasureTheory

namespace MovingSofa

/-! ### The angular phase windows are measurable -/

/-- Each of the ten angular phase windows of Gerver's cap is a Borel set. -/
theorem measurableSet_gerverPhaseAngles (j : Fin 10) : MeasurableSet (gerverPhaseAngles j) := by
  have hmono := gerverStageTimes_strictMono
  have h01 := hmono (show (0 : Fin 6) < 1 by decide)
  have h12 := hmono (show (1 : Fin 6) < 2 by decide)
  have h23 := hmono (show (2 : Fin 6) < 3 by decide)
  have h34 := hmono (show (3 : Fin 6) < 4 by decide)
  have h45 := hmono (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hturn : Real.pi ≤ -1 + 2 * Real.pi := by linarith
  simp only [gerverPhaseAngles, gerverPhaseIntervals_explicit]
  fin_cases j <;>
    refine Real.Angle.measurableSet_image_of_subset_Ioc hturn
      (by first | exact measurableSet_Ico | exact measurableSet_Ioc) ?_ <;>
    exact fun x hx ↦ ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩

/-! ### The phase windows partition the upper half-circle -/

private theorem injOn_angleCoe_Icc_zero_pi :
    Set.InjOn (fun t : ℝ ↦ (t : Real.Angle)) (Set.Icc 0 Real.pi) := by
  have hsub : Set.Icc (0 : ℝ) Real.pi ⊆ Set.Ioc (-1 : ℝ) Real.pi :=
    fun x hx ↦ ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  exact (Real.Angle.injOn_coe_Ioc (by linarith [Real.pi_gt_three])).mono hsub

private theorem iUnion_gerverPhaseIntervals :
    (⋃ j, gerverPhaseIntervals j) =
      Set.Ico 0 (Real.pi / 2) ∪ Set.Ioc (Real.pi / 2) Real.pi := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  have h23 := horder (show (2 : Fin 6) < 3 by decide)
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  have h45 := horder (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  simp only [gerverPhaseIntervals_explicit]
  simp only [Set.iUnion_fin_add_one_eq_iUnion_succ, Function.comp_def,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Set.iUnion_of_empty, Set.union_empty]
  have hlo : (((Set.Ico 0 GerversSofa.φ ∪ Set.Ico GerversSofa.φ GerversSofa.θ) ∪
      Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ)) ∪
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ)) ∪
      Set.Ico (Real.pi / 2 - GerversSofa.φ) (Real.pi / 2) =
      Set.Ico 0 (Real.pi / 2) := by
    rw [Set.Ico_union_Ico_eq_Ico h01.le h12.le,
      Set.Ico_union_Ico_eq_Ico (by linarith) h23.le,
      Set.Ico_union_Ico_eq_Ico (by linarith) h34.le,
      Set.Ico_union_Ico_eq_Ico (by linarith) h45.le]
  have hhi : (((Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.φ) ∪
      Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ)) ∪
      Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ)) ∪
      Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ)) ∪
      Set.Ioc (Real.pi - GerversSofa.φ) Real.pi = Set.Ioc (Real.pi / 2) Real.pi := by
    rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  rw [← hlo, ← hhi]
  ac_rfl

private theorem pairwise_disjoint_gerverPhaseIntervals :
    Pairwise (fun i j ↦ Disjoint (gerverPhaseIntervals i) (gerverPhaseIntervals j)) := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  have h23 := horder (show (2 : Fin 6) < 3 by decide)
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  have h45 := horder (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12 h23 h34 h45
  intro i j hij
  apply Set.disjoint_left.mpr
  intro t hi hj
  rw [gerverPhaseIntervals_explicit] at hi hj
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals linarith [hi.1, hi.2, hj.1, hj.2]

private theorem gerverPhaseIntervals_subset_Icc (k : Fin 10) :
    gerverPhaseIntervals k ⊆ Set.Icc 0 Real.pi := by
  intro z hz
  have hz' := Set.mem_iUnion.mpr ⟨k, hz⟩
  rw [iUnion_gerverPhaseIntervals] at hz'
  rcases hz' with h | h
  · exact ⟨h.1, by linarith [h.2, Real.pi_pos]⟩
  · exact ⟨by linarith [h.1, Real.pi_pos], h.2⟩

private theorem iUnion_gerverPhaseAngles_union_top :
    (⋃ j, gerverPhaseAngles j) ∪ {((Real.pi / 2 : ℝ) : Real.Angle)} =
      (fun t : ℝ ↦ (t : Real.Angle)) '' Set.Icc 0 Real.pi := by
  have hreal : (⋃ j, gerverPhaseIntervals j) ∪ {Real.pi / 2} = Set.Icc 0 Real.pi := by
    rw [iUnion_gerverPhaseIntervals]
    ext t
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc, Set.mem_singleton_iff, Set.mem_Icc]
    constructor
    · rintro ((h | h) | rfl) <;> constructor <;> linarith [Real.pi_pos]
    · intro ht
      rcases lt_trichotomy t (Real.pi / 2) with h | h | h
      · exact Or.inl (Or.inl ⟨ht.1, h⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨h, ht.2⟩)
  rw [← hreal, Set.image_union, Set.image_iUnion]
  simp only [gerverPhaseAngles, Set.image_singleton]

private theorem pairwise_disjoint_gerverPhaseAngles :
    Pairwise (fun i j ↦ Disjoint (gerverPhaseAngles i) (gerverPhaseAngles j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro t ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have hxy := injOn_angleCoe_Icc_zero_pi (gerverPhaseIntervals_subset_Icc j hy)
    (gerverPhaseIntervals_subset_Icc i hx) heq
  subst y
  exact Set.disjoint_left.mp (pairwise_disjoint_gerverPhaseIntervals hij) hx hy

/-- The two active right-tail phases make up the angular window `[π/2 - θ, π/2)`. -/
theorem gerverPhaseAngles_three_union_four :
    gerverPhaseAngles 3 ∪ gerverPhaseAngles 4 =
      (fun t : ℝ ↦ (t : Real.Angle)) ''
        Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) := by
  have horder := gerverStageTimes_strictMono
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  have h45 := horder (show (4 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h34 h45
  simp only [gerverPhaseAngles, ← Set.image_union, gerverPhaseIntervals_explicit,
    Matrix.cons_val]
  rw [Set.Ico_union_Ico_eq_Ico h34.le h45.le]

/-- The two active left-tail phases make up the angular window `(π/2, π/2 + θ]`. -/
theorem gerverPhaseAngles_five_union_six :
    gerverPhaseAngles 5 ∪ gerverPhaseAngles 6 =
      (fun t : ℝ ↦ (t : Real.Angle)) ''
        Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) := by
  have horder := gerverStageTimes_strictMono
  have h01 := horder (show (0 : Fin 6) < 1 by decide)
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h01 h12
  simp only [gerverPhaseAngles, ← Set.image_union, gerverPhaseIntervals_explicit,
    Matrix.cons_val]
  rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]

/-! ### Splitting the four variation integrals over the phase windows -/

private theorem setIntegral_union_eq_left_of_measure_eq_zero (μ : Measure Real.Angle)
    (f : Real.Angle → ℝ) {S T : Set Real.Angle} (hT : μ T = 0) :
    (∫ t in S ∪ T, f t ∂μ) = ∫ t in S, f t ∂μ := by
  apply integral_union_eq_left_of_ae
  rw [Measure.restrict_eq_zero.mpr hT]
  simp

private theorem setIntegral_angleImage_Icc_eq_sum (μ : Measure Real.Angle)
    (f : Real.Angle → ℝ) (hf : Integrable f μ)
    (htop : f ((Real.pi / 2 : ℝ) : Real.Angle) = 0) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) '' Set.Icc 0 Real.pi, f t ∂μ) =
      ∑ j, ∫ t in gerverPhaseAngles j, f t ∂μ := by
  rw [← iUnion_gerverPhaseAngles_union_top,
    integral_union_eq_left_of_forall (measurableSet_singleton _) (by
      intro t ht
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact htop)]
  exact integral_iUnion_fintype measurableSet_gerverPhaseAngles
    pairwise_disjoint_gerverPhaseAngles fun _ ↦ hf.restrict

private theorem setIntegral_right_window_eq_add (μ : Measure Real.Angle) (f : Real.Angle → ℝ)
    (hf : Integrable f μ)
    (hinactive : μ ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ)) = 0) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2), f t ∂μ) =
      (∫ t in gerverPhaseAngles 3, f t ∂μ) + (∫ t in gerverPhaseAngles 4, f t ∂μ) := by
  have horder := gerverStageTimes_strictMono
  have h13 := horder (show (1 : Fin 6) < 3 by decide)
  have h35 := horder (show (3 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h13 h35
  have hreal : Set.Ioo paperGerverConstants.2.1 (Real.pi / 2) =
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2) ∪
        Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ) := by
    ext t
    change (_ < t ∧ t < _) ↔ (_ ≤ t ∧ t < _) ∨ (_ < t ∧ t < _)
    change (GerversSofa.φ < t ∧ t < Real.pi / 2) ↔ _
    constructor
    · intro ht
      by_cases h : Real.pi / 2 - GerversSofa.θ ≤ t
      · exact Or.inl ⟨h, ht.2⟩
      · exact Or.inr ⟨ht.1, lt_of_not_ge h⟩
    · rintro (h | h) <;> (try simp only [paperGerverConstants] at h) <;>
        constructor <;> linarith [h.1, h.2]
  rw [hreal, Set.image_union, ← gerverPhaseAngles_three_union_four,
    setIntegral_union_eq_left_of_measure_eq_zero μ f hinactive]
  exact setIntegral_union (pairwise_disjoint_gerverPhaseAngles (by decide : (3 : Fin 10) ≠ 4))
    (measurableSet_gerverPhaseAngles 4) hf.restrict hf.restrict

private theorem setIntegral_left_window_eq_add (μ : Measure Real.Angle) (f : Real.Angle → ℝ)
    (hf : Integrable f μ)
    (hinactive : μ ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2 + GerversSofa.θ)
        (Real.pi / 2 + paperGerverConstants.2.2)) = 0) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2), f t ∂μ) =
      (∫ t in gerverPhaseAngles 5, f t ∂μ) + (∫ t in gerverPhaseAngles 6, f t ∂μ) := by
  have horder := gerverStageTimes_strictMono
  have h02 := horder (show (0 : Fin 6) < 2 by decide)
  have h24 := horder (show (2 : Fin 6) < 4 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h02 h24
  have hreal : Set.Ioo (Real.pi / 2) (Real.pi / 2 + paperGerverConstants.2.2) =
      Set.Ioc (Real.pi / 2) (Real.pi / 2 + GerversSofa.θ) ∪
        Set.Ioo (Real.pi / 2 + GerversSofa.θ)
          (Real.pi / 2 + paperGerverConstants.2.2) := by
    ext t
    change (_ < t ∧ t < _) ↔ (_ < t ∧ t ≤ _) ∨ (_ < t ∧ t < _)
    change (Real.pi / 2 < t ∧ t < Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ)) ↔ _
    constructor
    · intro ht
      by_cases h : t ≤ Real.pi / 2 + GerversSofa.θ
      · exact Or.inl ⟨ht.1, h⟩
      · exact Or.inr ⟨lt_of_not_ge h, ht.2⟩
    · rintro (h | h) <;> (try simp only [paperGerverConstants] at h) <;>
        constructor <;> linarith [h.1, h.2]
  rw [hreal, Set.image_union, ← gerverPhaseAngles_five_union_six,
    setIntegral_union_eq_left_of_measure_eq_zero μ f hinactive]
  exact setIntegral_union (pairwise_disjoint_gerverPhaseAngles (by decide : (5 : Fin 10) ≠ 6))
    (measurableSet_gerverPhaseAngles 6) hf.restrict hf.restrict

/-- The six phases on which the inner-corner measure is active. -/
private def cornerPhaseIndex : Fin 6 → Fin 10 := ![1, 2, 3, 6, 7, 8]

private theorem iUnion_gerverPhaseIntervals_cornerPhaseIndex :
    (⋃ i, gerverPhaseIntervals (cornerPhaseIndex i)) =
      Set.Ico paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Ioc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2) := by
  have horder := gerverStageTimes_strictMono
  have h12 := horder (show (1 : Fin 6) < 2 by decide)
  have h23 := horder (show (2 : Fin 6) < 3 by decide)
  have h34 := horder (show (3 : Fin 6) < 4 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h12 h23 h34
  simp only [Set.iUnion_fin_add_one_eq_iUnion_succ, Function.comp_def,
    cornerPhaseIndex, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Set.iUnion_of_empty, Set.union_empty, gerverPhaseIntervals_explicit]
  simp only [Matrix.cons_val, paperGerverConstants]
  have hlo : (Set.Ico GerversSofa.φ GerversSofa.θ ∪
      Set.Ico GerversSofa.θ (Real.pi / 2 - GerversSofa.θ)) ∪
      Set.Ico (Real.pi / 2 - GerversSofa.θ) (Real.pi / 2 - GerversSofa.φ) =
      Set.Ico GerversSofa.φ (Real.pi / 2 - GerversSofa.φ) := by
    rw [Set.Ico_union_Ico_eq_Ico h12.le h23.le, Set.Ico_union_Ico_eq_Ico (by linarith) h34.le]
  have hhi : (Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi / 2 + GerversSofa.θ) ∪
      Set.Ioc (Real.pi / 2 + GerversSofa.θ) (Real.pi - GerversSofa.θ)) ∪
      Set.Ioc (Real.pi - GerversSofa.θ) (Real.pi - GerversSofa.φ) =
      Set.Ioc (Real.pi / 2 + GerversSofa.φ) (Real.pi - GerversSofa.φ) := by
    rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith),
      Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)]
  have hend : Real.pi / 2 + (Real.pi / 2 - GerversSofa.φ) = Real.pi - GerversSofa.φ := by ring
  rw [hend, ← hlo, ← hhi]
  ac_rfl

private theorem iUnion_gerverPhaseAngles_cornerPhaseIndex_union_ends :
    (⋃ i, gerverPhaseAngles (cornerPhaseIndex i)) ∪
      {((paperGerverConstants.2.2 : ℝ) : Real.Angle),
        ((Real.pi / 2 + paperGerverConstants.2.1 : ℝ) : Real.Angle)} =
      (fun t : ℝ ↦ (t : Real.Angle)) ''
        (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
          Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
            (Real.pi / 2 + paperGerverConstants.2.2)) := by
  have horder := gerverStageTimes_strictMono
  have h14 := horder (show (1 : Fin 6) < 4 by decide)
  change paperGerverConstants.2.1 < paperGerverConstants.2.2 at h14
  have hreal : (⋃ i, gerverPhaseIntervals (cornerPhaseIndex i)) ∪
      {paperGerverConstants.2.2, Real.pi / 2 + paperGerverConstants.2.1} =
      Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2) := by
    rw [iUnion_gerverPhaseIntervals_cornerPhaseIndex]
    ext t
    simp only [Set.mem_union, Set.mem_Ico, Set.mem_Ioc, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_Icc]
    constructor
    · rintro ((h | h) | (rfl | rfl))
      · exact Or.inl ⟨h.1, h.2.le⟩
      · exact Or.inr ⟨h.1.le, h.2⟩
      · exact Or.inl ⟨h14.le, le_rfl⟩
      · exact Or.inr ⟨le_rfl, by linarith⟩
    · rintro (h | h)
      · rcases lt_or_eq_of_le h.2 with hlt | heq
        · exact Or.inl (Or.inl ⟨h.1, hlt⟩)
        · exact Or.inr (Or.inl heq)
      · rcases lt_or_eq_of_le h.1 with hlt | heq
        · exact Or.inl (Or.inr ⟨hlt, h.2⟩)
        · exact Or.inr (Or.inr heq.symm)
  rw [← hreal, Set.image_union, Set.image_iUnion]
  simp only [gerverPhaseAngles, Set.image_pair]

private theorem setIntegral_corner_window_eq_sum (μ : Measure Real.Angle)
    [NullSingletonClass μ] (f : Real.Angle → ℝ) (hf : Integrable f μ) :
    (∫ t in (fun s : ℝ ↦ (s : Real.Angle)) ''
      (Set.Icc paperGerverConstants.2.1 paperGerverConstants.2.2 ∪
        Set.Icc (Real.pi / 2 + paperGerverConstants.2.1)
          (Real.pi / 2 + paperGerverConstants.2.2)), f t ∂μ) =
      ∑ i, ∫ t in gerverPhaseAngles (cornerPhaseIndex i), f t ∂μ := by
  rw [← iUnion_gerverPhaseAngles_cornerPhaseIndex_union_ends,
    setIntegral_union_eq_left_of_measure_eq_zero μ f
      (((Set.finite_singleton _).insert _).measure_zero μ)]
  have hinj : Function.Injective cornerPhaseIndex := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [cornerPhaseIndex]
  exact integral_iUnion_fintype (fun i ↦ measurableSet_gerverPhaseAngles (cornerPhaseIndex i))
    (fun i j hij ↦ pairwise_disjoint_gerverPhaseAngles fun h ↦ hij (hinj h)) fun _ ↦ hf.restrict

/-! ### The eight phase contributions of the variation integral -/

/-- The eight contributions of the source table of the variation of `𝒬`: on each group of phases,
the cap surface integral of the support difference, minus the active inner-corner integral, plus
the active tail integral of the tail support difference. -/
def gerverPhaseContribution (X Y : CapTailSpace) : Fin 8 → ℝ :=
  let f := fun t ↦ supportValue Y.cap.val.val t - supportValue X.cap.val.val t
  let g := fun t ↦ (oppositeSurfaceData Y.rightBody).2 t -
    (oppositeSurfaceData X.rightBody).2 t
  let h := fun t ↦ (oppositeSurfaceData Y.leftBody).2 t -
    (oppositeSurfaceData X.leftBody).2 t
  let a := fun S ↦ ∫ t in S, f t ∂surfaceAreaMeasure X.cap.val.val
  let c := fun S ↦ ∫ t in S, f t ∂capCornerAngleMeasure X.cap
  let b := fun S ↦ ∫ t in S, g t ∂(oppositeSurfaceData X.rightBody).1
  let d := fun S ↦ ∫ t in S, h t ∂(oppositeSurfaceData X.leftBody).1
  ![a (gerverPhaseAngles 0),
    a (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2) -
      c (gerverPhaseAngles 1 ∪ gerverPhaseAngles 2),
    a (gerverPhaseAngles 3) - c (gerverPhaseAngles 3) + b (gerverPhaseAngles 3),
    a (gerverPhaseAngles 4) + b (gerverPhaseAngles 4),
    a (gerverPhaseAngles 5) + d (gerverPhaseAngles 5),
    a (gerverPhaseAngles 6) - c (gerverPhaseAngles 6) + d (gerverPhaseAngles 6),
    a (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8) -
      c (gerverPhaseAngles 7 ∪ gerverPhaseAngles 8),
    a (gerverPhaseAngles 9)]

private theorem setIntegral_add_of_restrict_eq_add {S : Set Real.Angle}
    {μ ν κ : Measure Real.Angle} {f g : Real.Angle → ℝ}
    (h : μ.restrict S = (ν + κ).restrict S)
    (hfν : Integrable f ν) (hfκ : Integrable f κ) (hg : Integrable g ν) :
    (∫ t in S, f t ∂μ) - (∫ t in S, f t ∂κ) + (∫ t in S, g t ∂ν) =
      ∫ t in S, (f t + g t) ∂ν := by
  rw [h, Measure.restrict_add, integral_add_measure hfν.restrict hfκ.restrict,
    integral_add hfν.restrict hg.restrict]
  ring

private theorem setIntegral_add_of_restrict_eq {S : Set Real.Angle}
    {μ ν : Measure Real.Angle} {f g : Real.Angle → ℝ}
    (h : μ.restrict S = ν.restrict S)
    (hf : Integrable f ν) (hg : Integrable g ν) :
    (∫ t in S, f t ∂μ) + (∫ t in S, g t ∂ν) =
      ∫ t in S, (f t + g t) ∂ν := by
  rw [h, integral_add hf.restrict hg.restrict]

private theorem right_support_difference_nonpos (X Y : CapTailSpace) (t : ℝ)
    (ht : t ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2))
    (hX : supportValue X.cap.val.val (t : Real.Angle) +
      (oppositeSurfaceData X.rightBody).2 (t : Real.Angle) = 1) :
    (supportValue Y.cap.val.val (t : Real.Angle) -
      supportValue X.cap.val.val (t : Real.Angle)) +
      ((oppositeSurfaceData Y.rightBody).2 (t : Real.Angle) -
        (oppositeSurfaceData X.rightBody).2 (t : Real.Angle)) ≤ 0 := by
  have hY := Y.right_bound t ht
  simp only [oppositeSurfaceData] at hX ⊢
  simp only [Real.Angle.coe_add, add_comm (Real.pi : Real.Angle)] at hY
  linarith

private theorem left_support_difference_nonpos (X Y : CapTailSpace) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2)
    (hX : supportValue X.cap.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle) +
      (oppositeSurfaceData X.leftBody).2 ((Real.pi / 2 + t : ℝ) : Real.Angle) = 1) :
    (supportValue Y.cap.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle) -
      supportValue X.cap.val.val ((Real.pi / 2 + t : ℝ) : Real.Angle)) +
      ((oppositeSurfaceData Y.leftBody).2 ((Real.pi / 2 + t : ℝ) : Real.Angle) -
        (oppositeSurfaceData X.leftBody).2 ((Real.pi / 2 + t : ℝ) : Real.Angle)) ≤ 0 := by
  have hY := Y.left_bound t ht
  have heq : (((Real.pi / 2 + t : ℝ) : Real.Angle) + (Real.pi : Real.Angle)) =
      ((3 * Real.pi / 2 + t : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
    congr 1
    ring
  simp only [oppositeSurfaceData, heq] at hX ⊢
  linarith

private theorem exists_mem_right_tail_domain {t : Real.Angle}
    (ht : t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4) :
    ∃ s ∈ Set.Icc paperGerverConstants.2.1 (Real.pi / 2), (s : Real.Angle) = t := by
  have horder := gerverStageTimes_strictMono
  have h13 := horder (show (1 : Fin 6) < 3 by decide)
  have h35 := horder (show (3 : Fin 6) < 5 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h13 h35
  rw [gerverPhaseAngles_three_union_four] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨s, ⟨le_trans h13.le hs.1, hs.2.le⟩, rfl⟩

private theorem exists_mem_left_tail_domain {t : Real.Angle}
    (ht : t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6) :
    ∃ s ∈ Set.Icc (0 : ℝ) paperGerverConstants.2.2,
      ((Real.pi / 2 + s : ℝ) : Real.Angle) = t := by
  have horder := gerverStageTimes_strictMono
  have h02 := horder (show (0 : Fin 6) < 2 by decide)
  have h24 := horder (show (2 : Fin 6) < 4 by decide)
  simp only [gerverStageTimes, Matrix.cons_val] at h02 h24
  rw [gerverPhaseAngles_five_union_six] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  refine ⟨s - Real.pi / 2, ⟨by linarith [hs.1], ?_⟩, ?_⟩
  · show s - Real.pi / 2 ≤ Real.pi / 2 - GerversSofa.φ
    linarith [hs.2]
  · congr 1
    ring

/-- Each of the eight phase contributions is nonpositive: the phase measure identities cancel the
cap measure against the active corner and tail measures, and the cap-tail constraints sign the
remaining tail integrands. -/
theorem gerverPhaseContribution_nonpos (X Y : CapTailSpace)
    (hphase : GerverPhaseMeasureIdentities X.cap X.rightBody X.leftBody)
    (hbaseB : ∀ t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.rightBody).2 t = 1)
    (hbaseD : ∀ t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6,
      supportValue X.cap.val.val t + (oppositeSurfaceData X.leftBody).2 t = 1)
    (i : Fin 8) : gerverPhaseContribution X Y i ≤ 0 := by
  obtain ⟨h0, h12, h3, h4, h5, h6, h78, h9⟩ := hphase
  have hfB : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (oppositeSurfaceData X.rightBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hfD : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (oppositeSurfaceData X.leftBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hfC : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (capCornerAngleMeasure X.cap) :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hgB : Integrable (fun t ↦ (oppositeSurfaceData Y.rightBody).2 t -
      (oppositeSurfaceData X.rightBody).2 t) (oppositeSurfaceData X.rightBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  have hgD : Integrable (fun t ↦ (oppositeSurfaceData Y.leftBody).2 t -
      (oppositeSurfaceData X.leftBody).2 t) (oppositeSurfaceData X.leftBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  have hB : ∀ t ∈ gerverPhaseAngles 3 ∪ gerverPhaseAngles 4,
      (supportValue Y.cap.val.val t - supportValue X.cap.val.val t) +
        ((oppositeSurfaceData Y.rightBody).2 t -
          (oppositeSurfaceData X.rightBody).2 t) ≤ 0 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := exists_mem_right_tail_domain ht
    exact right_support_difference_nonpos X Y s hs (hbaseB _ ht)
  have hD : ∀ t ∈ gerverPhaseAngles 5 ∪ gerverPhaseAngles 6,
      (supportValue Y.cap.val.val t - supportValue X.cap.val.val t) +
        ((oppositeSurfaceData Y.leftBody).2 t -
          (oppositeSurfaceData X.leftBody).2 t) ≤ 0 := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := exists_mem_left_tail_domain ht
    exact left_support_difference_nonpos X Y s hs (hbaseD _ ht)
  fin_cases i
  · simp [gerverPhaseContribution, h0]
  · simp [gerverPhaseContribution, h12]
  · change (_ - _ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq_add h3 hfB hfC hgB]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 3) fun t ht ↦ hB t (Or.inl ht)
  · change (_ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq h4 hfB hgB]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 4) fun t ht ↦ hB t (Or.inr ht)
  · change (_ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq h5 hfD hgD]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 5) fun t ht ↦ hD t (Or.inl ht)
  · change (_ - _ + _) ≤ 0
    rw [setIntegral_add_of_restrict_eq_add h6 hfD hfC hgD]
    exact setIntegral_nonpos (measurableSet_gerverPhaseAngles 6) fun t ht ↦ hD t (Or.inr ht)
  · simp [gerverPhaseContribution, h78]
  · simp [gerverPhaseContribution, h9]

/-! ### The four variation integrals as the eight phase contributions -/

/-- The four integrals of the variation formula regroup into the eight contributions of the source
table, given that the two tails carry no surface measure between their active windows. -/
theorem qVariationIntegral_eq_phaseSum (X Y : CapTailSpace)
    (hinactiveB : (oppositeSurfaceData X.rightBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo paperGerverConstants.2.1 (Real.pi / 2 - GerversSofa.θ)) = 0)
    (hinactiveD : (oppositeSurfaceData X.leftBody).1 ((fun s : ℝ ↦ (s : Real.Angle)) ''
      Set.Ioo (Real.pi / 2 + GerversSofa.θ) (Real.pi / 2 + paperGerverConstants.2.2)) = 0) :
    qVariationIntegral X Y = ∑ i, gerverPhaseContribution X Y i := by
  have hfK : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (surfaceAreaMeasure X.cap.val.val) :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hfC : Integrable (fun t ↦ supportValue Y.cap.val.val t -
      supportValue X.cap.val.val t) (capCornerAngleMeasure X.cap) :=
    Real.Angle.integrable_of_continuous
      ((continuous_supportValue _).sub (continuous_supportValue _))
  have hgB : Integrable (fun t ↦ (oppositeSurfaceData Y.rightBody).2 t -
      (oppositeSurfaceData X.rightBody).2 t) (oppositeSurfaceData X.rightBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  have hgD : Integrable (fun t ↦ (oppositeSurfaceData Y.leftBody).2 t -
      (oppositeSurfaceData X.leftBody).2 t) (oppositeSurfaceData X.leftBody).1 :=
    Real.Angle.integrable_of_continuous
      ((continuous_oppositeSurfaceData_snd _).sub (continuous_oppositeSurfaceData_snd _))
  rw [qVariationIntegral,
    setIntegral_angleImage_Icc_eq_sum _ _ hfK (by
      rw [Y.cap.val.property.2.2.2.1, X.cap.val.property.2.2.2.1, sub_self]),
    setIntegral_corner_window_eq_sum _ _ hfC,
    setIntegral_right_window_eq_add _ _ hgB hinactiveB,
    setIntegral_left_window_eq_add _ _ hgD hinactiveD]
  have h12 := pairwise_disjoint_gerverPhaseAngles (by decide : (1 : Fin 10) ≠ 2)
  have h78 := pairwise_disjoint_gerverPhaseAngles (by decide : (7 : Fin 10) ≠ 8)
  have hK12 := setIntegral_union h12 (measurableSet_gerverPhaseAngles 2)
    hfK.restrict hfK.restrict
  have hC12 := setIntegral_union h12 (measurableSet_gerverPhaseAngles 2)
    hfC.restrict hfC.restrict
  have hK78 := setIntegral_union h78 (measurableSet_gerverPhaseAngles 8)
    hfK.restrict hfK.restrict
  have hC78 := setIntegral_union h78 (measurableSet_gerverPhaseAngles 8)
    hfC.restrict hfC.restrict
  simp only [gerverPhaseContribution, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, cornerPhaseIndex,
    hK12, hC12, hK78, hC78]
  ring!

end MovingSofa
