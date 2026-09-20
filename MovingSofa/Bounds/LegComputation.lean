import MovingSofa.Cap.SupportIntersections
import MovingSofa.Geometry.HallwayRay
import MovingSofa.Polygon.RightAngleGrid
import MovingSofa.Cap.ContactIdentities
import MovingSofa.Cap.Tail.Canonical

noncomputable section

open Set MeasureTheory

namespace MovingSofa

private theorem rightAngle_allowedReal_gap_left (n : ℕ) (hn : 2 ≤ n) {t r : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions)
    (hr : r ∈ angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) :
    r ∈ Set.Icc (t - polygonStepSize n + Real.pi / 2 - Real.pi)
        (t - polygonStepSize n + Real.pi / 2) ∨
    r ∈ Set.Icc (t + Real.pi / 2) (t + Real.pi / 2 + Real.pi) := by
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  obtain ⟨hδt, htδ⟩ := rightAngleSet_direction_bounds n hn ht
  have htI := (rightAngleSet n hn).interior t ht
  change t ∈ Set.Ioo 0 (Real.pi / 2) at htI
  obtain ⟨ht0, htT⟩ := htI
  rcases hr with hr | rfl
  · change r ∈ ((rightAngleSet n hn).directions : Set ℝ) ∪
        ((fun q : ℝ ↦ q + Real.pi / 2) ''
          ((rightAngleSet n hn).directions : Set ℝ)) ∪
        {(rightAngleSet n hn).angle, Real.pi / 2} at hr
    rcases hr with (hr | ⟨q, hq, rfl⟩) | hr
    · have hrI := (rightAngleSet n hn).interior r hr
      change r ∈ Set.Ioo 0 (Real.pi / 2) at hrI
      obtain ⟨hr0, hrT⟩ := hrI
      left
      constructor <;> linarith [Real.pi_pos]
    · have hqI := (rightAngleSet n hn).interior q hq
      change q ∈ Set.Ioo 0 (Real.pi / 2) at hqI
      obtain ⟨hq0, hqT⟩ := hqI
      simp only
      rcases rightAngleSet_direction_le_pred_or_ge n hn hq ht with hqle | hqge
      · left
        constructor
        ·
          linarith [Real.pi_pos]
        · linarith
      · right
        constructor <;> linarith [Real.pi_pos]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> left
      all_goals
        change _ ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ _
        constructor <;> linarith [Real.pi_pos]
  · right
    constructor <;> linarith [Real.pi_pos]

private theorem rightAngle_allowedReal_gap_right (n : ℕ) (hn : 2 ≤ n) {t r : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions)
    (hr : r ∈ angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}) :
    r ∈ Set.Icc (t + Real.pi / 2 - Real.pi) (t + Real.pi / 2) ∨
      r ∈ Set.Icc (t + polygonStepSize n + Real.pi / 2)
        (t + polygonStepSize n + Real.pi / 2 + Real.pi) := by
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  obtain ⟨hδt, htδ⟩ := rightAngleSet_direction_bounds n hn ht
  have htI := (rightAngleSet n hn).interior t ht
  change t ∈ Set.Ioo 0 (Real.pi / 2) at htI
  obtain ⟨ht0, htT⟩ := htI
  rcases hr with hr | rfl
  · change r ∈ ((rightAngleSet n hn).directions : Set ℝ) ∪
        ((fun q : ℝ ↦ q + Real.pi / 2) ''
          ((rightAngleSet n hn).directions : Set ℝ)) ∪
        {(rightAngleSet n hn).angle, Real.pi / 2} at hr
    rcases hr with (hr | ⟨q, hq, rfl⟩) | hr
    · have hrI := (rightAngleSet n hn).interior r hr
      change r ∈ Set.Ioo 0 (Real.pi / 2) at hrI
      obtain ⟨hr0, hrT⟩ := hrI
      left
      constructor <;> linarith [Real.pi_pos]
    · have hqI := (rightAngleSet n hn).interior q hq
      change q ∈ Set.Ioo 0 (Real.pi / 2) at hqI
      obtain ⟨hq0, hqT⟩ := hqI
      simp only
      rcases rightAngleSet_direction_le_or_succ_le n hn hq ht with hqle | hqge
      · left
        constructor <;> linarith [Real.pi_pos]
      · right
        constructor <;> linarith [Real.pi_pos]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl <;> left
      all_goals
        change _ ≤ Real.pi / 2 ∧ Real.pi / 2 ≤ _
        constructor <;> linarith [Real.pi_pos]
  · right
    constructor <;> linarith [Real.pi_pos]

/-- The preceding shifted grid support is attained at the negative left-wall contact. -/
private theorem rightAngle_supportValue_prev_shift (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    supportValue K.val.val
        ((t - polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle) =
      inner ℝ (capVertices K.val t).2.2
        (normalVector ((t - polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle)) := by
  let a := t - polygonStepSize n + Real.pi / 2
  let b := t + Real.pi / 2
  let R := angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  have hδpi : polygonStepSize n < Real.pi := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hδT : polygonStepSize n < Real.pi / 2 := by
      simp only [polygonStepSize]
      apply (div_lt_iff₀ hnpos).2
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hrepr : HasHalfPlaneRepresentation K.val.val
      ((fun r : ℝ ↦ (r : Real.Angle)) '' R) := by
    rw [← rightAngle_polygon_normals_eq n hn]
    exact K.property
  have hp : supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) ∈ K.val.val := by
    apply hrepr.supportingIntersection_mem_of_gap K.val.val R
    · dsimp [a, b]
      linarith
    · dsimp [a, b]
      linarith
    · intro r hr
      simpa only [a, b] using rightAngle_allowedReal_gap_left n hn ht hr
  have heq := supportingIntersection_eq_edgeVertices_snd_of_mem K.val.val
    (a := a) (b := b) (by dsimp [a, b]; linarith)
    (by dsimp [a, b]; linarith) hp
  have hinter := supportingIntersection_inner_left K.val.val a b
  change inner ℝ (supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle))
      (normalVector (a : Real.Angle)) = supportValue K.val.val (a : Real.Angle) at hinter
  change supportValue K.val.val (a : Real.Angle) =
    inner ℝ (edgeVertices K.val.val (b : Real.Angle)).2 (normalVector (a : Real.Angle))
  rw [← heq, hinter]

/-- The next shifted support is attained at the positive contact, including the final grid point. -/
private theorem rightAngle_supportValue_next_shift (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    supportValue K.val.val
        ((t + polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle) =
      inner ℝ (capVertices K.val t).2.1
        (normalVector ((t + polygonStepSize n + Real.pi / 2 : ℝ) : Real.Angle)) := by
  let a := t + Real.pi / 2
  let b := t + polygonStepSize n + Real.pi / 2
  let R := angleDomain (rightAngleSet n hn) ∪ {3 * Real.pi / 2}
  have hδpos : 0 < polygonStepSize n := by simp [polygonStepSize]; positivity
  have hδpi : polygonStepSize n < Real.pi := by
    have hnpos : (0 : ℝ) < n := by positivity
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hδT : polygonStepSize n < Real.pi / 2 := by
      simp only [polygonStepSize]
      apply (div_lt_iff₀ hnpos).2
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  have hrepr : HasHalfPlaneRepresentation K.val.val
      ((fun r : ℝ ↦ (r : Real.Angle)) '' R) := by
    rw [← rightAngle_polygon_normals_eq n hn]
    exact K.property
  have hp : supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle) ∈ K.val.val := by
    apply hrepr.supportingIntersection_mem_of_gap K.val.val R
    · dsimp [a, b]
      linarith
    · dsimp [a, b]
      linarith
    · intro r hr
      simpa only [a, b] using rightAngle_allowedReal_gap_right n hn ht hr
  have heq := supportingIntersection_eq_edgeVertices_fst_of_mem K.val.val
    (a := a) (b := b) (by dsimp [a, b]; linarith)
    (by dsimp [a, b]; linarith) hp
  have hinter := supportingIntersection_inner_right K.val.val a b
    (show Real.sin (b - a) ≠ 0 by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [a, b] <;> linarith)
  change inner ℝ (supportingIntersection K.val.val (a : Real.Angle) (b : Real.Angle))
      (normalVector (b : Real.Angle)) = supportValue K.val.val (b : Real.Angle) at hinter
  change supportValue K.val.val (b : Real.Angle) =
    inner ℝ (edgeVertices K.val.val (a : Real.Angle)).1 (normalVector (b : Real.Angle))
  rw [← heq, hinter]

private theorem one_sub_cos_div_cos_eq_tan_mul_tan_half {δ : ℝ}
    (hδ0 : 0 < δ) (hδT : δ < Real.pi / 2) :
    (1 - Real.cos δ) / Real.cos δ = Real.tan δ * Real.tan (δ / 2) := by
  have hc : Real.cos δ ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hδT⟩)
  have hch : Real.cos (δ / 2) ≠ 0 := ne_of_gt
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩)
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hc, hch]
  have htwo : δ = 2 * (δ / 2) := by ring
  have hcos : Real.cos δ = 1 - 2 * Real.sin (δ / 2) ^ 2 :=
    (congrArg Real.cos htwo).trans (Real.cos_two_mul_eq_one_sub _)
  have hsin : Real.sin δ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) :=
    (congrArg Real.sin htwo).trans (Real.sin_two_mul _)
  rw [hcos, hsin]
  ring

private theorem polygonStepSize_mem_Ioo (n : ℕ) (hn : 2 ≤ n) :
    polygonStepSize n ∈ Set.Ioo 0 (Real.pi / 2) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · simp only [polygonStepSize]
    positivity
  · simp only [polygonStepSize]
    apply (div_lt_iff₀ hnpos).2
    nlinarith [Real.pi_pos]

private theorem rightAngle_bRay_prev_leg_length (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
          (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 ((tangentArmLengths K.val t).2.2 - 1 +
          Real.tan (polygonStepSize n / 2))) := by
  let δ := polygonStepSize n
  let x := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerCorner
  let y := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).outerCorner
  let c := (capVertices K.val t).2.2
  let g := (tangentArmLengths K.val t).2.2
  let u := t - δ + Real.pi / 2
  have hδI : δ ∈ Set.Ioo 0 (Real.pi / 2) := polygonStepSize_mem_Ioo n hn
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδI.1, Real.pi_pos], hδI.2⟩
  have htI : t ∈ Set.Icc 0 (Real.pi / 2) := by
    have hi := (rightAngleSet n hn).interior t ht
    change t ∈ Set.Ioo 0 (Real.pi / 2) at hi
    exact ⟨hi.1.le, hi.2.le⟩
  have hnormal : normalVector (u : Real.Angle) =
      Real.sin δ • normalVector (t : Real.Angle) +
        Real.cos δ • tangentVector (t : Real.Angle) := by
    have h := normalVector_add_real t (Real.pi / 2 - δ)
    rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
    have hu : u = t + (Real.pi / 2 - δ) := by dsimp [u]; ring
    rw [hu]
    exact h
  have htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    simpa using hcδ
  rw [show (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2 =
      normalHalfPlane (u : Real.Angle)
        (supportValue K.val.val (u : Real.Angle) - 1) true false by
    simp only [innerWallUpperHalfPlanes, u, δ]
    ]
  rw [hausdorffMeasure_bRay_inter_normalHalfPlane _ _ _ _ htrans]
  have hx : x = y - normalVector (t : Real.Angle) - tangentVector (t : Real.Angle) := by
    have hf := rotatingHallwayParts_formulas (K.val.val : Set Point) (t : Real.Angle)
    rw [show x = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).innerCorner by rfl, hf.2.1]
    rw [show y = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner by rfl, hf.2.2.1]
    module
  have hy : y = c + g • normalVector (t : Real.Angle) := by
    change (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner =
        (capVertices K.val t).2.2 +
          (tangentArmLengths K.val t).2.2 • normalVector (t : Real.Angle)
    exact (capTangentArm_identities K.val t htI).2.2.2
  have hsupport : supportValue K.val.val (u : Real.Angle) =
      inner ℝ c (normalVector (u : Real.Angle)) := by
    simpa only [u, δ, c] using rightAngle_supportValue_prev_shift n hn K ht
  have hd : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) = Real.cos δ := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    ring
  have hnum : inner ℝ x (normalVector (u : Real.Angle)) -
      (supportValue K.val.val (u : Real.Angle) - 1) =
      (g - 1) * Real.sin δ + 1 - Real.cos δ := by
    rw [hx, hy, hsupport, hnormal]
    simp only [inner_sub_left, inner_add_left,
      inner_add_right, inner_smul_right, inner_normalVector_self,
      inner_normalVector_tangentVector, real_inner_comm, inner_tangentVector_self]
    ring
  have hratio :
      (inner ℝ x (normalVector (u : Real.Angle)) -
          (supportValue K.val.val (u : Real.Angle) - 1)) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)) =
        Real.tan δ * (g - 1 + Real.tan (δ / 2)) := by
    rw [hnum, hd]
    calc
      ((g - 1) * Real.sin δ + 1 - Real.cos δ) / Real.cos δ =
          Real.tan δ * (g - 1) + (1 - Real.cos δ) / Real.cos δ := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcδ.ne']
            ring
      _ = Real.tan δ * (g - 1) + Real.tan δ * Real.tan (δ / 2) := by
        rw [one_sub_cos_div_cos_eq_tan_mul_tan_half hδI.1 hδI.2]
      _ = Real.tan δ * (g - 1 + Real.tan (δ / 2)) := by ring
  change ENNReal.ofReal (max 0 _) = ENNReal.ofReal (_ * max 0 _)
  rw [hratio]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.tan_pos_of_pos_of_lt_pi_div_two hδI.1 hδI.2).le,
    mul_zero]

private theorem rightAngle_bRay_next_leg_length (n : ℕ) (hn : 2 ≤ n)
    (K : PolygonCapSpace (rightAngleSet n hn)) {t : ℝ}
    (ht : t ∈ (rightAngleSet n hn).directions) :
    Measure.hausdorffMeasure 1
        ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
          (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 (1 - (tangentArmLengths K.val t).2.1 +
          Real.tan (polygonStepSize n / 2))) := by
  let δ := polygonStepSize n
  let x := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).innerCorner
  let y := (rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).outerCorner
  let c := (capVertices K.val t).2.1
  let g := (tangentArmLengths K.val t).2.1
  let u := t + δ + Real.pi / 2
  have hδI : δ ∈ Set.Ioo 0 (Real.pi / 2) := polygonStepSize_mem_Ioo n hn
  have hcδ : 0 < Real.cos δ := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hδI.1, Real.pi_pos], hδI.2⟩
  have htI : t ∈ Set.Icc 0 (Real.pi / 2) := by
    have hi := (rightAngleSet n hn).interior t ht
    change t ∈ Set.Ioo 0 (Real.pi / 2) at hi
    exact ⟨hi.1.le, hi.2.le⟩
  have hnormal : normalVector (u : Real.Angle) =
      (-Real.sin δ) • normalVector (t : Real.Angle) +
        Real.cos δ • tangentVector (t : Real.Angle) := by
    have h := normalVector_add_real t (Real.pi / 2 + δ)
    simp only [Real.cos_add, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, zero_mul, one_mul, zero_sub, add_zero] at h
    have hu : u = t + (Real.pi / 2 + δ) := by dsimp [u]; ring
    rw [hu]
    exact h
  have htrans : 0 < inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    simpa using hcδ
  rw [show (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2 =
      normalHalfPlane (u : Real.Angle)
        (supportValue K.val.val (u : Real.Angle) - 1) true false by
    simp only [innerWallUpperHalfPlanes, u, δ]
    ]
  rw [hausdorffMeasure_bRay_inter_normalHalfPlane _ _ _ _ htrans]
  have hx : x = y - normalVector (t : Real.Angle) - tangentVector (t : Real.Angle) := by
    have hf := rotatingHallwayParts_formulas (K.val.val : Set Point) (t : Real.Angle)
    rw [show x = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).innerCorner by rfl, hf.2.1]
    rw [show y = (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner by rfl, hf.2.2.1]
    module
  have hy : y = c + g • normalVector (t : Real.Angle) := by
    change (rotatingHallwayParts (K.val.val : Set Point)
      (t : Real.Angle)).outerCorner =
        (capVertices K.val t).2.1 +
          (tangentArmLengths K.val t).2.1 • normalVector (t : Real.Angle)
    exact (capTangentArm_identities K.val t htI).2.2.1
  have hsupport : supportValue K.val.val (u : Real.Angle) =
      inner ℝ c (normalVector (u : Real.Angle)) := by
    simpa only [u, δ, c] using rightAngle_supportValue_next_shift n hn K ht
  have hd : inner ℝ (tangentVector (t : Real.Angle))
      (normalVector (u : Real.Angle)) = Real.cos δ := by
    rw [hnormal, inner_add_right, inner_smul_right, inner_smul_right,
      real_inner_comm, inner_normalVector_tangentVector, inner_tangentVector_self]
    ring
  have hnum : inner ℝ x (normalVector (u : Real.Angle)) -
      (supportValue K.val.val (u : Real.Angle) - 1) =
      (1 - g) * Real.sin δ + 1 - Real.cos δ := by
    rw [hx, hy, hsupport, hnormal]
    simp only [inner_sub_left, inner_add_left, inner_add_right, inner_smul_right,
      inner_normalVector_self, inner_normalVector_tangentVector, real_inner_comm,
      inner_tangentVector_self]
    ring
  have hratio :
      (inner ℝ x (normalVector (u : Real.Angle)) -
          (supportValue K.val.val (u : Real.Angle) - 1)) /
          inner ℝ (tangentVector (t : Real.Angle)) (normalVector (u : Real.Angle)) =
        Real.tan δ * (1 - g + Real.tan (δ / 2)) := by
    rw [hnum, hd]
    calc
      ((1 - g) * Real.sin δ + 1 - Real.cos δ) / Real.cos δ =
          Real.tan δ * (1 - g) + (1 - Real.cos δ) / Real.cos δ := by
            rw [Real.tan_eq_sin_div_cos]
            field_simp [hcδ.ne']
            ring
      _ = Real.tan δ * (1 - g) + Real.tan δ * Real.tan (δ / 2) := by
        rw [one_sub_cos_div_cos_eq_tan_mul_tan_half hδI.1 hδI.2]
      _ = Real.tan δ * (1 - g + Real.tan (δ / 2)) := by ring
  change ENNReal.ofReal (max 0 _) = ENNReal.ofReal (_ * max 0 _)
  rw [hratio]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.tan_pos_of_pos_of_lt_pi_div_two hδI.1 hδI.2).le,
    mul_zero]

theorem maximumPolygonCap_leg_lengths (n : ℕ) (hn : 2 ≤ n) (hdyadic : ∃ k : ℕ, n = 2 ^ k)
    (K : PolygonCapSpace (rightAngleSet n hn))
    (hK : IsMaximumPolygonCap (rightAngleSet n hn) K)
    (t : ℝ) (ht : t ∈ (rightAngleSet n hn).directions) :
    MeasureTheory.Measure.hausdorffMeasure 1
      ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
        (innerWallUpperHalfPlanes K.val (t - polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 ((tangentArmLengths K.val t).2.2 - 1 +
          Real.tan (polygonStepSize n / 2))) ∧
    MeasureTheory.Measure.hausdorffMeasure 1
      ((rotatingHallwayParts (K.val.val : Set Point) (t : Real.Angle)).bRay ∩
        (innerWallUpperHalfPlanes K.val (t + polygonStepSize n)).2) =
      ENNReal.ofReal (Real.tan (polygonStepSize n) *
        max 0 (1 - (tangentArmLengths K.val t).2.1 +
          Real.tan (polygonStepSize n / 2))) := by
  exact ⟨rightAngle_bRay_prev_leg_length n hn K ht,
    rightAngle_bRay_next_leg_length n hn K ht⟩

/-- The face line of a convex body meets the two adjacent inner-wall half-planes in a set whose
length is at most `2 tan(δ/2)` less the face length. -/
theorem hausdorffMeasure_faceLine_inter_innerWalls_le (K : ConvexBody Point)
    (t δ : ℝ) (hδ0 : 0 < δ) (hδ : δ < Real.pi) :
    Measure.hausdorffMeasure 1
        ({p : Point | inner ℝ p (normalVector (t : Real.Angle)) =
            supportValue (K : Set Point) (t : Real.Angle) - 1} ∩
          (normalHalfPlane ((t - δ : ℝ) : Real.Angle)
              (supportValue (K : Set Point) ((t - δ : ℝ) : Real.Angle) - 1) true false ∩
            normalHalfPlane ((t + δ : ℝ) : Real.Angle)
              (supportValue (K : Set Point) ((t + δ : ℝ) : Real.Angle) - 1) true false)) ≤
      ENNReal.ofReal (max 0 (2 * Real.tan (δ / 2) -
        (surfaceAreaMeasure K {(t : Real.Angle)}).toReal)) := by
  have hpi := Real.pi_pos
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ0 hδ
  have hhalfcos : 0 < Real.cos (δ / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hhalfsin : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have htanhalf : (1 - Real.cos δ) / Real.sin δ = Real.tan (δ / 2) := by
    have h1 : Real.sin δ = 2 * Real.sin (δ / 2) * Real.cos (δ / 2) := by
      have h := Real.sin_two_mul (δ / 2)
      rwa [show 2 * (δ / 2) = δ by ring] at h
    have h2 : Real.cos δ = 2 * Real.cos (δ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (δ / 2)
      rwa [show 2 * (δ / 2) = δ by ring] at h
    rw [Real.tan_eq_sin_div_cos, h1, h2, div_eq_div_iff (by positivity) hhalfcos.ne']
    nlinarith [Real.sin_sq_add_cos_sq (δ / 2)]
  have hneg : t - (t + δ) = -δ := by ring
  have hpos : t - (t - δ) = δ := by ring
  have hAn : inner ℝ (edgeVertices K (t : Real.Angle)).1 (normalVector (t : Real.Angle)) =
      supportValue (K : Set Point) (t : Real.Angle) := (edgeVertices_fst_mem K _).2
  have hBn : inner ℝ (edgeVertices K (t : Real.Angle)).2 (normalVector (t : Real.Angle)) =
      supportValue (K : Set Point) (t : Real.Angle) := (edgeVertices_snd_mem K _).2
  have hApb := inner_le_supportValue K (edgeVertices_fst_mem K (t : Real.Angle)).1
    ((t + δ : ℝ) : Real.Angle)
  have hBmb := inner_le_supportValue K (edgeVertices_snd_mem K (t : Real.Angle)).1
    ((t - δ : ℝ) : Real.Angle)
  rw [inner_normalVector_eq_frame_rotate _ t (t + δ), hneg, Real.cos_neg, Real.sin_neg,
    hAn] at hApb
  rw [inner_normalVector_eq_frame_rotate _ t (t - δ), hpos, hBn] at hBmb
  have hAB := (surfaceAreaMeasure_atom_length K (t : Real.Angle)).2.2
  have hgap : inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) =
      inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
        (surfaceAreaMeasure K {(t : Real.Angle)}).toReal := by
    rw [hAB, inner_add_left, real_inner_smul_left, inner_tangentVector_self, mul_one]
  refine le_trans (hausdorffMeasure_le_of_frame_bounds (t := t)
    (e := supportValue (K : Set Point) (t : Real.Angle) - 1)
    (lo := inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
      Real.tan (δ / 2))
    (hi := inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
      Real.tan (δ / 2)) ?_) (le_of_eq ?_)
  · rintro p ⟨hline, hprev, hnext⟩
    have hpn : inner ℝ p (normalVector (t : Real.Angle)) =
        supportValue (K : Set Point) (t : Real.Angle) - 1 := hline
    change supportValue (K : Set Point) ((t - δ : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t - δ : ℝ) : Real.Angle)) at hprev
    change supportValue (K : Set Point) ((t + δ : ℝ) : Real.Angle) - 1 ≤
      inner ℝ p (normalVector ((t + δ : ℝ) : Real.Angle)) at hnext
    rw [inner_normalVector_eq_frame_rotate p t (t - δ), hpos, hpn] at hprev
    rw [inner_normalVector_eq_frame_rotate p t (t + δ), hneg, Real.cos_neg, Real.sin_neg,
      hpn] at hnext
    have hkeyU : (inner ℝ p (tangentVector (t : Real.Angle)) -
        inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle))) *
          Real.sin δ ≤ 1 - Real.cos δ := by nlinarith [hprev, hBmb]
    have hkeyL : (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
        inner ℝ p (tangentVector (t : Real.Angle))) * Real.sin δ ≤ 1 - Real.cos δ := by
      nlinarith [hnext, hApb]
    have hU := (le_div_iff₀ hsin).mpr hkeyU
    have hL := (le_div_iff₀ hsin).mpr hkeyL
    rw [htanhalf] at hU hL
    exact ⟨hpn, by linarith, by linarith⟩
  · have hlen : inner ℝ (edgeVertices K (t : Real.Angle)).2 (tangentVector (t : Real.Angle)) +
        Real.tan (δ / 2) -
        (inner ℝ (edgeVertices K (t : Real.Angle)).1 (tangentVector (t : Real.Angle)) -
          Real.tan (δ / 2)) =
        2 * Real.tan (δ / 2) - (surfaceAreaMeasure K {(t : Real.Angle)}).toReal := by
      rw [hgap]
      ring
    rw [hlen]

end MovingSofa
