import MovingSofa.Polygon.DiscreteCapData

noncomputable section

open Set MeasureTheory

namespace MovingSofa

/-- Directions in the right-angle grid are positive integer multiples of its step size. -/
theorem mem_rightAngleSet_directions_iff (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    t ∈ (rightAngleSet n hn).directions ↔
      ∃ i : ℕ, i ∈ Finset.Ioo 0 n ∧ t = i * polygonStepSize n := by
  simp only [rightAngleSet, uniformAngleSet, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [polygonStepSize]
    ring
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, hi, ?_⟩
    simp only [polygonStepSize]
    ring

/-- No grid direction lies strictly between the predecessor of a grid point and the point. -/
theorem rightAngleSet_direction_le_pred_or_ge (n : ℕ) (hn : 2 ≤ n) {r t : ℝ}
    (hr : r ∈ (rightAngleSet n hn).directions)
    (ht : t ∈ (rightAngleSet n hn).directions) :
    r ≤ t - polygonStepSize n ∨ t ≤ r := by
  obtain ⟨j, hj, rfl⟩ := (mem_rightAngleSet_directions_iff n hn r).mp hr
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  have hnpos : (0 : ℝ) < n := by positivity
  have hδ : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  by_cases hji : j < i
  · left
    have hnat : j + 1 ≤ i := hji
    have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hnat
    nlinarith
  · right
    have hij : i ≤ j := Nat.le_of_not_gt hji
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hδ.le

/-- No grid direction lies strictly between a grid point and its successor. -/
theorem rightAngleSet_direction_le_or_succ_le (n : ℕ) (hn : 2 ≤ n) {r t : ℝ}
    (hr : r ∈ (rightAngleSet n hn).directions)
    (ht : t ∈ (rightAngleSet n hn).directions) :
    r ≤ t ∨ t + polygonStepSize n ≤ r := by
  obtain ⟨j, hj, rfl⟩ := (mem_rightAngleSet_directions_iff n hn r).mp hr
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  have hδ : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  by_cases hji : j ≤ i
  · left
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hji) hδ.le
  · right
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hji))
    nlinarith

/-- Every interior grid direction stays at least one step from both endpoints. -/
theorem rightAngleSet_direction_bounds (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    polygonStepSize n ≤ t ∧ t ≤ Real.pi / 2 - polygonStepSize n := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  have hnpos : (0 : ℝ) < n := by positivity
  have hδ : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi0
  have hin1 : (i : ℝ) + 1 ≤ n := by exact_mod_cast hin
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hi1 hδ.le
  · have hstep : (n : ℝ) * polygonStepSize n = Real.pi / 2 := by
      simp only [polygonStepSize]
      field_simp
    nlinarith

/-- The two lower normals of a right-angle polygon cap coincide at `3π/2`. -/
theorem rightAngle_polygon_normals_eq (n : ℕ) (hn : 2 ≤ n) :
    ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain (rightAngleSet n hn)) ∪
        capLowerNormals (rightAngleSet n hn).angle =
      (fun r : ℝ ↦ (r : Real.Angle)) ''
        (angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) := by
  ext a
  simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro (⟨r, hr, rfl⟩ | ha)
    · exact ⟨r, Or.inl hr, rfl⟩
    · simp only [capLowerNormals, rightAngleSet, uniformAngleSet,
        Set.mem_insert_iff] at ha
      rcases ha with ha | ha
      · subst a
        refine ⟨3 * Real.pi / 2, Or.inr rfl, ?_⟩
        congr 1
        ring
      · subst a
        exact ⟨3 * Real.pi / 2, Or.inr rfl, rfl⟩
  · rintro ⟨r, hr | rfl, rfl⟩
    · exact Or.inl ⟨r, hr, rfl⟩
    · right
      simp [capLowerNormals, rightAngleSet, uniformAngleSet]

/-- The predecessor of a right-angle grid direction is zero or again a grid direction. -/
theorem rightAngleSet_sub_step (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    t - polygonStepSize n = 0 ∨
      t - polygonStepSize n ∈ (rightAngleSet n hn).directions := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  by_cases hi1 : i = 1
  · left
    subst hi1
    push_cast
    ring
  · right
    refine (mem_rightAngleSet_directions_iff n hn _).mpr ⟨i - 1, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · rw [Nat.cast_sub (by omega)]
      push_cast
      ring

/-- The successor of a right-angle grid direction is the terminal angle or a grid direction. -/
theorem rightAngleSet_add_step (n : ℕ) (hn : 2 ≤ n) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    t + polygonStepSize n = Real.pi / 2 ∨
      t + polygonStepSize n ∈ (rightAngleSet n hn).directions := by
  obtain ⟨i, hi, rfl⟩ := (mem_rightAngleSet_directions_iff n hn t).mp ht
  obtain ⟨hi0, hin⟩ := Finset.mem_Ioo.mp hi
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  by_cases hi1 : i + 1 = n
  · left
    have : ((i : ℝ) + 1) = (n : ℝ) := by exact_mod_cast congrArg (fun m : ℕ ↦ (m : ℝ)) hi1
    simp only [polygonStepSize]
    field_simp
    linarith [this]
  · right
    refine (mem_rightAngleSet_directions_iff n hn _).mpr ⟨i + 1, Finset.mem_Ioo.mpr ⟨?_, ?_⟩, ?_⟩
    · omega
    · omega
    · push_cast
      ring

end MovingSofa
