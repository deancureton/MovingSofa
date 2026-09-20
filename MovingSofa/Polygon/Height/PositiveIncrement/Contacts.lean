import MovingSofa.Polygon.Height.RaisedSupport
import MovingSofa.Polygon.Height.Reconstruction
import MovingSofa.Polygon.PerturbationBounds
import MovingSofa.Cap.TopCorner
import MovingSofa.Cap.ContactIdentities
import MovingSofa.Cap.AngleDomain
import MovingSofa.Cap.FanProjection
import MovingSofa.Geometry.ParallelogramGap
import MovingSofa.Geometry.NormalLines
import MovingSofa.ForMathlib.Topology.Order.Compact

noncomputable section

namespace MovingSofa

private theorem polygonHeightValue_raisedPolygonSupport {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) (ε : ℝ) {s : ℝ}
    (hs : s ∈ angleDomain Θ) :
    polygonHeightValue (raisedPolygonSupport K t ε) s =
      supportValue K.val.val (s : Real.Angle) +
        if (⟨s, hs⟩ : angleDomain Θ) = t then ε else 0 := by
  simp [polygonHeightValue, raisedPolygonSupport, hs]

private theorem mem_polygonHeightCap_raised_of_mem_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) {p : Point}
    (hp : p ∈ (K.val.val : Set Point)) :
    p ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
  have hupper (s : ℝ) (hs : s ∈ angleDomain Θ) :
      inner ℝ p (normalVector (s : Real.Angle)) ≤
        polygonHeightValue (raisedPolygonSupport K t ε) s := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε hs]
    exact (inner_le_supportValue K.val.val hp _).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro s hs
    constructor
    · exact hupper s (Or.inr hs)
    · change polygonHeightValue (raisedPolygonSupport K t ε) s - 1 ≤
        inner ℝ p (normalVector (s : Real.Angle))
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr hs)]
      have hne : (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
        intro heq
        apply ht
        have hval : s = t.val := congrArg Subtype.val heq
        simpa [← hval] using hs
      rw [ite_eq_right hne]
      simp only [add_zero]
      rcases hs with rfl | rfl
      · have hlower := inner_le_supportValue K.val.val hp
          ((Θ.angle + Real.pi : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
        rw [K.val.property.2.2.1]
        linarith
      · have hlower := inner_le_supportValue K.val.val hp
          ((3 * Real.pi / 2 : ℝ) : Real.Angle)
        rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hlower
        rw [K.val.property.2.2.2.1]
        simpa [normalVector, frame, PiLp.inner_apply] using hlower
  · intro s hs
    exact hupper s (Or.inl hs)

private theorem raisedPolygonSupport_endpoint_contacts_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ) {ε : ℝ} (hε : 0 ≤ ε)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
        inner ℝ p (normalVector (s : Real.Angle)) =
          polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
    (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
      ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
        inner ℝ p (normalVector (s : Real.Angle)) =
          polygonHeightValue (raisedPolygonSupport K t ε) s - 1) := by
  have hne (s : ℝ) (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      (⟨s, Or.inr hs⟩ : angleDomain Θ) ≠ t := by
    intro heq
    apply ht
    have hval : s = t.val := congrArg Subtype.val heq
    simpa [← hval] using hs
  have hvalue (s : ℝ) (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
      polygonHeightValue (raisedPolygonSupport K t ε) s =
        supportValue K.val.val (s : Real.Angle) := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr hs), ite_eq_right (hne s hs),
      add_zero]
  constructor
  · intro s hs
    obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
      (s : Real.Angle)
    exact ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp,
      hpinner.trans (hvalue s hs).symm⟩
  · intro s hs
    rcases hs with rfl | rfl
    · obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
        ((Θ.angle + Real.pi : ℝ) : Real.Angle)
      refine ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp, ?_⟩
      rw [normalVector_add_pi, inner_neg_right,
        K.val.property.2.2.2.2.1] at hpinner
      rw [hvalue Θ.angle (by simp), K.val.property.2.2.1]
      linarith
    · obtain ⟨p, hp, hpinner⟩ := exists_mem_inner_eq_supportValue K.val.val
        ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      refine ⟨p, mem_polygonHeightCap_raised_of_mem_of_not_endpoint K t hε ht hp, ?_⟩
      rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hpinner
      rw [hvalue (Real.pi / 2) (by simp), K.val.property.2.2.2.1]
      simpa [normalVector, frame, PiLp.inner_apply] using hpinner

private theorem independentWallCap_self_sub_one_eq {Θ : AngleSet}
    (h : PolygonHeightSpace Θ) :
    independentWallCap h (fun t ↦ h t - 1) = polygonHeightCap h := by
  ext p
  simp only [independentWallCap, polygonHeightCap, polygonHeightParallelogram,
    Set.mem_inter_iff, Set.mem_iInter]
  apply and_congr
  · apply forall_congr'
    intro t
    apply forall_congr'
    intro ht
    have htD : t ∈ angleDomain Θ := Or.inr ht
    simp only [polygonHeightValue, dite_eq_left htD]
  · rfl

private theorem polygonHeightCap_raised_bounded {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| ≤ ε₀ →
      Bornology.IsBounded (polygonHeightCap (raisedPolygonSupport K t ε)) := by
  let h : PolygonHeightSpace Θ :=
    fun s ↦ supportValue K.val.val (s.val : Real.Angle)
  obtain ⟨R, ε₀, hR, hε₀, hbound⟩ := polygonPerturbation_uniform_bounds Θ h
  refine ⟨ε₀, hε₀, fun ε hε ↦ ?_⟩
  let hε' := raisedPolygonSupport K t ε
  let lower : PolygonHeightSpace Θ := fun s ↦ hε' s - 1
  have hu (s : angleDomain Θ) : |hε' s - h s| ≤ ε₀ := by
    change |(supportValue K.val.val (s.val : Real.Angle) + if s = t then ε else 0) -
      supportValue K.val.val (s.val : Real.Angle)| ≤ ε₀
    split_ifs
    · simpa using hε
    · simp [hε₀.le]
  have hl (s : angleDomain Θ) : |lower s - (h s - 1)| ≤ ε₀ := by
    simpa only [lower, sub_sub_sub_cancel_right] using hu s
  have hsub := (hbound hε' lower hu hl).1
  rw [independentWallCap_self_sub_one_eq] at hsub
  exact Metric.isBounded_closedBall.subset hsub

/-- A sufficiently small interior height increase yields a translated polygon cap. -/
theorem polygonCap_positive_height_increment_of_not_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∉ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  obtain ⟨ε₀, hε₀, hbounded⟩ := polygonHeightCap_raised_bounded K t
  refine ⟨ε₀, hε₀, fun ε hε hεlt ↦ ?_⟩
  have hcontacts := raisedPolygonSupport_endpoint_contacts_of_not_endpoint
    K t hε.le ht
  exact exists_polygonCapTranslate_eq_polygonHeightCap _
    (hbounded ε (abs_le.mpr ⟨by linarith, hεlt.le⟩)) hcontacts.1 hcontacts.2

private theorem midpoint_mem_strict_support_of_face {Θ : AngleSet}
    (K : PolygonCapSpace Θ) {a b : Point} {t c : ℝ} (ht : t ∈ angleDomain Θ)
    (ha : a ∈ (K.val.val : Set Point)) (hb : b ∈ (K.val.val : Set Point))
    (hat : inner ℝ a (normalVector (t : Real.Angle)) = c)
    (hbt : inner ℝ b (normalVector (t : Real.Angle)) = c)
    (hab : a ≠ b) :
    let m := (2 : ℝ)⁻¹ • (a + b)
    m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t : Real.Angle)) = c ∧
      ∀ s ∈ angleDomain Θ, s ≠ t →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  dsimp
  have hm : (2 : ℝ)⁻¹ • (a + b) ∈ (K.val.val : Set Point) := by
    rw [smul_add]
    exact K.val.val.convex ha hb (by norm_num) (by norm_num) (by norm_num)
  have hmt : inner ℝ ((2 : ℝ)⁻¹ • (a + b)) (normalVector (t : Real.Angle)) =
      c := by
    rw [inner_smul_left, inner_add_left]
    simp only [RCLike.conj_to_real, hat, hbt]
    ring
  refine ⟨hm, hmt, ?_⟩
  intro s hs hst
  have hle := inner_le_supportValue K.val.val hm (s : Real.Angle)
  apply lt_of_le_of_ne hle
  intro heq
  have hae := inner_le_supportValue K.val.val ha (s : Real.Angle)
  have hbe := inner_le_supportValue K.val.val hb (s : Real.Angle)
  have hmavg : inner ℝ ((2 : ℝ)⁻¹ • (a + b)) (normalVector (s : Real.Angle)) =
      (2 : ℝ)⁻¹ * (inner ℝ a (normalVector (s : Real.Angle)) +
        inner ℝ b (normalVector (s : Real.Angle))) := by
    rw [inner_smul_left, inner_add_left]
    simp only [RCLike.conj_to_real]
  have haeq : inner ℝ a (normalVector (s : Real.Angle)) =
      supportValue K.val.val (s : Real.Angle) := by
    rw [hmavg] at heq
    nlinarith
  have hbeq : inner ℝ b (normalVector (s : Real.Angle)) =
      supportValue K.val.val (s : Real.Angle) := by
    rw [hmavg] at heq
    nlinarith
  have hortht : inner ℝ (b - a) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hbt, hat, sub_self]
  have horths : inner ℝ (b - a) (normalVector (s : Real.Angle)) = 0 := by
    rw [inner_sub_left, hbeq, haeq, sub_self]
  exact hst (eq_of_inner_sub_normalVector_eq_zero_of_ne
    (angleDomain_subset_Ioo Θ hs) (angleDomain_subset_Ioo Θ ht) hab horths hortht)

private theorem exists_pos_uniform_strict_support_gap {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (m : Point) (t : angleDomain Θ)
    (hstrict : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      inner ℝ m (normalVector (s : Real.Angle)) <
        supportValue K.val.val (s : Real.Angle)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δ ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ m (normalVector (s : Real.Angle)) := by
  let gap : ℝ → ℝ := fun s ↦ if s = t.val then 1 else
    supportValue K.val.val (s : Real.Angle) - inner ℝ m (normalVector (s : Real.Angle))
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact (Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun s : ℝ ↦ s + Real.pi / 2))).union
        (Set.finite_singleton (Real.pi / 2) |>.insert Θ.angle)
  have hnonempty : (angleDomain Θ).Nonempty := ⟨Θ.angle, by simp [angleDomain]⟩
  obtain ⟨δ, hδ, hδle⟩ := hdomain.isCompact.exists_pos_forall_le hnonempty
    (hdomain.continuousOn gap) (fun s hs ↦ by
      dsimp only [gap]
      split_ifs with heq
      · positivity
      · linarith [hstrict s hs heq])
  refine ⟨δ, hδ, ?_⟩
  intro s hs hne
  simpa [gap, hne] using hδle s hs

private theorem cos_sub_nonneg_of_mem_endpoints {Θ : AngleSet} {s t : ℝ}
    (hs : s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (ht : t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) : 0 ≤ Real.cos (s - t) := by
  apply Real.cos_nonneg_of_mem_Icc
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  all_goals constructor <;> linarith [Θ.angle_pos, Θ.angle_le, Real.pi_pos]

private theorem add_smul_normal_mem_raisedPolygonSupport {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (htendpoint : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (m : Point) (hm : m ∈ (K.val.val : Set Point))
    (hmLower : supportValue K.val.val (t.val : Real.Angle) - 1 ≤
      inner ℝ m (normalVector (t.val : Real.Angle)))
    (hmUpper : inner ℝ m (normalVector (t.val : Real.Angle)) ≤
      supportValue K.val.val (t.val : Real.Angle))
    {δ ε : ℝ} (hδ : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δ ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ m (normalVector (s : Real.Angle)))
    (hε : 0 < ε) (hεδ : ε < δ) :
    m + ε • normalVector (t.val : Real.Angle) ∈
      polygonHeightCap (raisedPolygonSupport K t ε) := by
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inr hr
    have hval := polygonHeightValue_raisedPolygonSupport K t ε hrD
    constructor
    · change inner ℝ (m + ε • normalVector (t.val : Real.Angle))
          (normalVector (r : Real.Angle)) ≤
        polygonHeightValue (raisedPolygonSupport K t ε) r
      rw [hval, inner_add_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt, inner_normalVector_self]
        linarith
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub]
        have hcos := Real.cos_le_one (t.val - r)
        rw [inner_normalVector_normalVector]
        have hgap := hδ r hrD hrt
        nlinarith
    · change polygonHeightValue (raisedPolygonSupport K t ε) r - 1 ≤
        inner ℝ (m + ε • normalVector (t.val : Real.Angle))
          (normalVector (r : Real.Angle))
      rw [hval, inner_add_left, inner_smul_left]
      simp only [RCLike.conj_to_real]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt, inner_normalVector_self]
        nlinarith
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub, add_zero]
        have hbase : supportValue K.val.val (r : Real.Angle) - 1 ≤
            inner ℝ m (normalVector (r : Real.Angle)) := by
          rcases hr with rfl | rfl
          · have hl := inner_le_supportValue K.val.val hm
              ((Θ.angle + Real.pi : ℝ) : Real.Angle)
            rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hl
            rw [K.val.property.2.2.1]
            linarith
          · have hl := inner_le_supportValue K.val.val hm
              ((3 * Real.pi / 2 : ℝ) : Real.Angle)
            rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hl
            rw [K.val.property.2.2.2.1]
            simpa [normalVector, frame, PiLp.inner_apply] using hl
        have hcos := cos_sub_nonneg_of_mem_endpoints htendpoint hr
        rw [inner_normalVector_normalVector]
        exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hε.le hcos))
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inl hr
    have hval := polygonHeightValue_raisedPolygonSupport K t ε hrD
    change inner ℝ (m + ε • normalVector (t.val : Real.Angle))
        (normalVector (r : Real.Angle)) ≤
      polygonHeightValue (raisedPolygonSupport K t ε) r
    rw [hval, inner_add_left, inner_smul_left]
    simp only [RCLike.conj_to_real]
    by_cases hrt : r = t.val
    · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
      rw [ite_eq_left hsub, hrt, inner_normalVector_self]
      linarith
    · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
        intro heq
        exact hrt (congrArg Subtype.val heq)
      rw [ite_eq_right hsub]
      have hcos := Real.cos_le_one (t.val - r)
      rw [inner_normalVector_normalVector]
      have hgap := hδ r hrD hrt
      nlinarith

private theorem mem_raisedPolygonSupport_of_endpoint_of_le_inner {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) {p : Point}
    (hp : p ∈ (K.val.val : Set Point)) {ε : ℝ} (hε : 0 ≤ ε)
    (hinner : ε ≤ inner ℝ p (normalVector (t.val : Real.Angle))) :
    p ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
  unfold polygonHeightCap polygonHeightParallelogram
  simp only [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inr hr
    have hvalue := polygonHeightValue_raisedPolygonSupport K t ε hrD
    constructor
    · change inner ℝ p (normalVector (r : Real.Angle)) ≤
          polygonHeightValue (raisedPolygonSupport K t ε) r
      rw [hvalue]
      exact (inner_le_supportValue K.val.val hp _).trans
        (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · change polygonHeightValue (raisedPolygonSupport K t ε) r - 1 ≤
          inner ℝ p (normalVector (r : Real.Angle))
      rw [hvalue]
      by_cases hrt : r = t.val
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) = t := Subtype.ext hrt
        rw [ite_eq_left hsub, hrt]
        have hsupport : supportValue K.val.val (t.val : Real.Angle) = 1 := by
          rcases ht with ht | ht
          · simpa [ht] using K.val.property.2.2.1
          · have ht' : t.val = Real.pi / 2 := by simpa using ht
            simpa [ht'] using K.val.property.2.2.2.1
        rw [hsupport]
        simpa using hinner
      · have hsub : (⟨r, hrD⟩ : angleDomain Θ) ≠ t := by
          intro heq
          exact hrt (congrArg Subtype.val heq)
        rw [ite_eq_right hsub, add_zero]
        rcases hr with rfl | rfl
        · have hlower := inner_le_supportValue K.val.val hp
              ((Θ.angle + Real.pi : ℝ) : Real.Angle)
          rw [K.val.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
          rw [K.val.property.2.2.1]
          linarith
        · have hlower := inner_le_supportValue K.val.val hp
              ((3 * Real.pi / 2 : ℝ) : Real.Angle)
          rw [K.val.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hlower
          rw [K.val.property.2.2.2.1]
          simpa [normalVector, frame, PiLp.inner_apply] using hlower
  · intro r hr
    have hrD : r ∈ angleDomain Θ := Or.inl hr
    rw [polygonHeightValue_raisedPolygonSupport K t ε hrD]
    exact (inner_le_supportValue K.val.val hp _).trans
      (le_add_of_nonneg_right (by split_ifs <;> positivity))

private theorem moved_upper_lower_contacts {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (u l : Point) (hu : u ∈ (K.val.val : Set Point))
    (huval : inner ℝ u (normalVector (t.val : Real.Angle)) =
      supportValue K.val.val (t.val : Real.Angle))
    (hl : l ∈ (K.val.val : Set Point))
    (hlval : inner ℝ l (normalVector (t.val : Real.Angle)) =
      supportValue K.val.val (t.val : Real.Angle) - 1)
    {δu δl ε : ℝ}
    (hδu : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δu ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ u (normalVector (s : Real.Angle)))
    (hδl : ∀ s ∈ angleDomain Θ, s ≠ t.val →
      δl ≤ supportValue K.val.val (s : Real.Angle) -
        inner ℝ l (normalVector (s : Real.Angle)))
    (hε : 0 < ε) (hεu : ε < δu) (hεl : ε < δl) :
    (∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
      inner ℝ p (normalVector (t.val : Real.Angle)) =
        polygonHeightValue (raisedPolygonSupport K t ε) t.val) ∧
    (∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
      inner ℝ p (normalVector (t.val : Real.Angle)) =
        polygonHeightValue (raisedPolygonSupport K t ε) t.val - 1) := by
  have huLower : supportValue K.val.val (t.val : Real.Angle) - 1 ≤
      inner ℝ u (normalVector (t.val : Real.Angle)) := by linarith
  have hlUpper : inner ℝ l (normalVector (t.val : Real.Angle)) ≤
      supportValue K.val.val (t.val : Real.Angle) := by linarith
  have hu' := add_smul_normal_mem_raisedPolygonSupport K t ht u hu huLower huval.le
    hδu hε hεu
  have hl' := add_smul_normal_mem_raisedPolygonSupport K t ht l hl hlval.ge hlUpper
    hδl hε hεl
  have hvalue : polygonHeightValue (raisedPolygonSupport K t ε) t.val =
      supportValue K.val.val (t.val : Real.Angle) + ε := by
    rw [polygonHeightValue_raisedPolygonSupport K t ε t.property]
    simp
  constructor
  · refine ⟨u + ε • normalVector (t.val : Real.Angle), hu', ?_⟩
    rw [inner_add_left, inner_smul_left, huval, inner_normalVector_self, hvalue]
    simp
  · refine ⟨l + ε • normalVector (t.val : Real.Angle), hl', ?_⟩
    rw [inner_add_left, inner_smul_left, hlval, inner_normalVector_self, hvalue]
    simp
    ring

private theorem exists_upperFace_midpoint_strict {Θ : AngleSet} (K : PolygonCapSpace Θ)
    (t : angleDomain Θ)
    (ht : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  let a := (edgeVertices K.val.val (t.val : Real.Angle)).1
  let b := (edgeVertices K.val.val (t.val : Real.Angle)).2
  have haedge := edgeVertices_fst_mem K.val.val (t.val : Real.Angle)
  have hbedge := edgeVertices_snd_mem K.val.val (t.val : Real.Angle)
  have hab : a ≠ b := by
    have hdist : 0 < dist a b := by
      rw [(surfaceAreaMeasure_atom_length K.val.val (t.val : Real.Angle)).2.1] at ht
      exact ENNReal.ofReal_pos.mp ht
    exact dist_ne_zero.mp hdist.ne'
  let m := (2 : ℝ)⁻¹ • (a + b)
  have hm := midpoint_mem_strict_support_of_face K t.property
    haedge.1 hbedge.1 haedge.2 hbedge.2 hab
  exact ⟨m, hm⟩

private theorem stripParallelogram_top_inner_angle (Θ : AngleSet)
    (hΘ : Θ.angle < Real.pi / 2) :
    inner ℝ (stripParallelogram Θ.angle).2.2 (normalVector (Θ.angle : Real.Angle)) = 1 := by
  have hc : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  have hgap : Real.tan (Real.pi / 4 - Θ.angle / 2) =
      (Real.cos Θ.angle)⁻¹ - Real.tan Θ.angle := by
    simpa [show Real.pi / 4 - Θ.angle / 2 =
        (Real.pi / 2 - Θ.angle) / 2 by ring]
      using Real.tan_pi_div_two_sub_div_two Θ.angle ⟨Θ.angle_pos.le, hΘ⟩
  have htan := Real.tan_eq_sin_div_cos Θ.angle
  simp [stripParallelogram, normalVector, frame, PiLp.inner_apply, hgap, htan]
  field_simp [hc.ne']
  ring

private theorem stripParallelogram_top_sub_vertical_mem_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2) :
    (stripParallelogram Θ.angle).2.2 - tangentVector 0 ∈ (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  let a := o - tangentVector 0
  have ho := stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have haFan : a ∈ capFan Θ.angle := by
    constructor
    · change 0 ≤ inner ℝ a (normalVector (Θ.angle : Real.Angle))
      dsimp [a]
      have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
        stripParallelogram_top_inner_angle Θ hΘ
      rw [inner_sub_left, hoω]
      simp [tangentVector, normalVector, frame, PiLp.inner_apply]
      exact Real.sin_le_one Θ.angle
    · change 0 ≤ inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      simp [a, o, stripParallelogram, tangentVector, normalVector, frame,
        PiLp.inner_apply]
  apply K.val.mem_of_mem_capFan_of_le_supportValue haFan
  intro s hs
  have ho_le := inner_le_supportValue K.val.val ho (s : Real.Angle)
  have hale : inner ℝ a (normalVector (s : Real.Angle)) ≤
      inner ℝ o (normalVector (s : Real.Angle)) := by
    rw [show a = o - tangentVector 0 by rfl, inner_sub_left]
    apply sub_le_self
    have hsI : s ∈ Set.Icc 0 Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, hs.2.trans (Θ.angle_le.trans (by linarith [Real.pi_pos]))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans hs.1,
          hs.2.trans (by linarith [Θ.angle_le, Real.pi_pos])⟩
    simpa [tangentVector, normalVector, frame, PiLp.inner_apply] using
      Real.sin_nonneg_of_mem_Icc hsI
  exact hale.trans ho_le

private theorem stripParallelogram_top_sub_normal_mem_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2) :
    (stripParallelogram Θ.angle).2.2 - normalVector (Θ.angle : Real.Angle) ∈
      (K.val.val : Set Point) := by
  let o := (stripParallelogram Θ.angle).2.2
  let b := o - normalVector (Θ.angle : Real.Angle)
  have ho := stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have hbFan : b ∈ capFan Θ.angle := by
    constructor
    · change 0 ≤ inner ℝ b (normalVector (Θ.angle : Real.Angle))
      dsimp [b]
      have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
        stripParallelogram_top_inner_angle Θ hΘ
      rw [inner_sub_left, hoω, inner_normalVector_self, sub_self]
    · change 0 ≤ inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      dsimp [b]
      have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
        simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
      rw [inner_sub_left, hoT]
      simp [normalVector, frame, PiLp.inner_apply]
      exact Real.sin_le_one Θ.angle
  apply K.val.mem_of_mem_capFan_of_le_supportValue hbFan
  intro s hs
  have ho_le := inner_le_supportValue K.val.val ho (s : Real.Angle)
  have hble : inner ℝ b (normalVector (s : Real.Angle)) ≤
      inner ℝ o (normalVector (s : Real.Angle)) := by
    rw [show b = o - normalVector (Θ.angle : Real.Angle) by rfl, inner_sub_left]
    apply sub_le_self
    rw [inner_normalVector_normalVector]
    apply Real.cos_nonneg_of_mem_Icc
    rcases hs with hs | hs
    · constructor <;> linarith [hs.1, hs.2, Θ.angle_pos, Θ.angle_le, Real.pi_pos]
    · constructor <;> linarith [hs.1, hs.2, Θ.angle_pos, Θ.angle_le, Real.pi_pos]
  exact hble.trans ho_le

private theorem exists_lowerFace_midpoint_strict_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ)) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) - 1 ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  have hzero := zero_mem_cap_of_lt K.val hΘ
  rcases ht with ht | ht
  · have htval : t.val = Θ.angle := ht
    let b := (stripParallelogram Θ.angle).2.2 - normalVector (Θ.angle : Real.Angle)
    have hb := stripParallelogram_top_sub_normal_mem_of_angle_lt K hΘ
    have hbnormal : inner ℝ b (normalVector (Θ.angle : Real.Angle)) = 0 := by
      dsimp [b]
      rw [inner_sub_left, stripParallelogram_top_inner_angle Θ hΘ,
        inner_normalVector_self, sub_self]
    have hbne : (0 : Point) ≠ b := by
      intro heq
      have hgap := (parallelogram_gap Θ.angle ⟨Θ.angle_pos.le, hΘ⟩).2.1
      rw [← show b = (stripParallelogram Θ.angle).2.2 -
        normalVector (Θ.angle : Real.Angle) by rfl, ← heq] at hgap
      have hgappos : 0 < Real.tan ((Real.pi / 2 - Θ.angle) / 2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
          (by linarith [Θ.angle_pos, Real.pi_pos])
      have hcoord := congrArg (fun p : Point ↦ p 1) hgap
      have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
      simp [tangentVector, frame] at hcoord
      rcases hcoord with hgapzero | hcoszero
      · exact hgappos.ne' hgapzero
      · exact hcos.ne' hcoszero
    have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property hzero hb
      (by simp) (by simpa [htval, K.val.property.2.2.1] using hbnormal) hbne
    refine ⟨(2 : ℝ)⁻¹ • ((0 : Point) + b), hm.1, ?_, ?_⟩
    · rw [hm.2.1, htval, K.val.property.2.2.1]
      ring
    · simpa [htval] using hm.2.2
  · have htval : t.val = Real.pi / 2 := ht
    let a := (stripParallelogram Θ.angle).2.2 - tangentVector 0
    have ha := stripParallelogram_top_sub_vertical_mem_of_angle_lt K hΘ
    have hanormal : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
      simp [a, stripParallelogram, tangentVector, normalVector, frame, PiLp.inner_apply]
    have hane : (0 : Point) ≠ a := by
      intro heq
      have hgap := (parallelogram_gap Θ.angle ⟨Θ.angle_pos.le, hΘ⟩).1
      rw [← show a = (stripParallelogram Θ.angle).2.2 - tangentVector 0 by rfl,
        ← heq] at hgap
      have hgappos : 0 < Real.tan ((Real.pi / 2 - Θ.angle) / 2) :=
        Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith)
          (by linarith [Θ.angle_pos, Real.pi_pos])
      have hcoord := congrArg (fun p : Point ↦ p 0) hgap
      simp [normalVector, frame] at hcoord
      linarith
    have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property hzero ha
      (by simp) (by simpa [htval, K.val.property.2.2.2.1] using hanormal) hane
    refine ⟨(2 : ℝ)⁻¹ • ((0 : Point) + a), hm.1, ?_, ?_⟩
    · rw [hm.2.1, htval, K.val.property.2.2.2.1]
      ring
    · simpa [htval] using hm.2.2

private theorem sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2) {p : Point}
    (hp : p ∈ (K.val.val : Set Point))
    (hpT : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1) :
    p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (K.val.val : Set Point) := by
  apply K.val.mem_of_mem_capFan_of_le_supportValue
  · constructor
    · change 0 ≤ inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          (normalVector (Θ.angle : Real.Angle))
      rw [hΘ, inner_sub_left, hpT, inner_normalVector_self, sub_self]
    · change 0 ≤ inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
          (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      rw [inner_sub_left, hpT, inner_normalVector_self, sub_self]
  · intro s hs
    have hsI : s ∈ Set.Icc 0 Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, by rw [hΘ] at hs; linarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hs.1, Real.pi_pos], by rw [hΘ] at hs; linarith [hs.2]⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_mem_Icc hsI
    have hle : inner ℝ (p - normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
        (normalVector (s : Real.Angle)) ≤ inner ℝ p (normalVector (s : Real.Angle)) := by
      rw [inner_sub_left]
      apply sub_le_self
      rw [inner_normalVector_normalVector]
      simpa [Real.cos_pi_div_two_sub] using hsin
    exact hle.trans (inner_le_supportValue K.val.val hp (s : Real.Angle))

private theorem exists_lowerFace_midpoint_strict_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ m : Point,
      m ∈ (K.val.val : Set Point) ∧
      inner ℝ m (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) - 1 ∧
      ∀ s ∈ angleDomain Θ, s ≠ t.val →
        inner ℝ m (normalVector (s : Real.Angle)) <
          supportValue K.val.val (s : Real.Angle) := by
  have htval : t.val = Real.pi / 2 := by
    rcases ht with ht | ht
    · simpa [hΘ] using ht
    · exact ht
  let a := (edgeVertices K.val.val (t.val : Real.Angle)).1
  let b := (edgeVertices K.val.val (t.val : Real.Angle)).2
  let a' := a - normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  let b' := b - normalVector ((Real.pi / 2 : ℝ) : Real.Angle)
  have haedge := edgeVertices_fst_mem K.val.val (t.val : Real.Angle)
  have hbedge := edgeVertices_snd_mem K.val.val (t.val : Real.Angle)
  have hab : a ≠ b := by
    have hdist : 0 < dist a b := by
      rw [(surfaceAreaMeasure_atom_length K.val.val (t.val : Real.Angle)).2.1] at hmass
      exact ENNReal.ofReal_pos.mp hmass
    exact dist_ne_zero.mp hdist.ne'
  have haT : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    have haSupport : inner ℝ a (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) := haedge.2
    simpa [htval, K.val.property.2.2.2.1] using haSupport
  have hbT : inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    have hbSupport : inner ℝ b (normalVector (t.val : Real.Angle)) =
        supportValue K.val.val (t.val : Real.Angle) := hbedge.2
    simpa [htval, K.val.property.2.2.2.1] using hbSupport
  have ha' : a' ∈ (K.val.val : Set Point) :=
    sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq K hΘ haedge.1 haT
  have hb' : b' ∈ (K.val.val : Set Point) :=
    sub_normalVector_pi_div_two_mem_of_mem_of_angle_eq K hΘ hbedge.1 hbT
  have ha'normal : inner ℝ a' (normalVector (t.val : Real.Angle)) = 0 := by
    rw [htval]
    dsimp [a']
    rw [inner_sub_left, haT, inner_normalVector_self, sub_self]
  have hb'normal : inner ℝ b' (normalVector (t.val : Real.Angle)) = 0 := by
    rw [htval]
    dsimp [b']
    rw [inner_sub_left, hbT, inner_normalVector_self, sub_self]
  have hab' : a' ≠ b' := by
    intro heq
    apply hab
    dsimp [a', b'] at heq
    exact sub_left_injective heq
  have hm := midpoint_mem_strict_support_of_face (c := 0) K t.property ha' hb'
    ha'normal hb'normal hab'
  refine ⟨(2 : ℝ)⁻¹ • (a' + b'), hm.1, ?_, hm.2.2⟩
  rw [hm.2.1, htval, K.val.property.2.2.2.1]
  ring

private theorem raisedPolygonSupport_endpoint_contacts_of_angle_lt {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle < Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
  obtain ⟨u, hu, huval, hustrict⟩ := exists_upperFace_midpoint_strict K t hmass
  obtain ⟨l, hl, hlval, hlstrict⟩ :=
    exists_lowerFace_midpoint_strict_of_angle_lt K hΘ t ht
  obtain ⟨δu, hδupos, hδu⟩ := exists_pos_uniform_strict_support_gap K u t hustrict
  obtain ⟨δl, hδlpos, hδl⟩ := exists_pos_uniform_strict_support_gap K l t hlstrict
  let o := (stripParallelogram Θ.angle).2.2
  let a := o - tangentVector 0
  let b := o - normalVector (Θ.angle : Real.Angle)
  have ho : o ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_mem_of_angle_lt Θ hΘ K
  have ha : a ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_sub_vertical_mem_of_angle_lt K hΘ
  have hb : b ∈ (K.val.val : Set Point) :=
    stripParallelogram_top_sub_normal_mem_of_angle_lt K hΘ
  have hoω : inner ℝ o (normalVector (Θ.angle : Real.Angle)) = 1 :=
    stripParallelogram_top_inner_angle Θ hΘ
  have hoT : inner ℝ o (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 1 := by
    simp [o, stripParallelogram, normalVector, frame, PiLp.inner_apply]
  have haT : inner ℝ a (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    simp [a, o, stripParallelogram, tangentVector, normalVector, frame,
      PiLp.inner_apply]
  have hbω : inner ℝ b (normalVector (Θ.angle : Real.Angle)) = 0 := by
    dsimp [b]
    rw [inner_sub_left, hoω, inner_normalVector_self, sub_self]
  let gap := 1 - Real.sin Θ.angle
  have hcos : 0 < Real.cos Θ.angle := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Θ.angle_pos, Real.pi_pos], hΘ⟩
  have hgappos : 0 < gap := by
    have hcosSq : 0 < Real.cos Θ.angle ^ 2 := sq_pos_of_pos hcos
    have htrig := Real.sin_sq_add_cos_sq Θ.angle
    have hsinle := Real.sin_le_one Θ.angle
    dsimp [gap]
    nlinarith
  have haω : inner ℝ a (normalVector (Θ.angle : Real.Angle)) = gap := by
    dsimp [a, gap]
    rw [inner_sub_left, hoω]
    simp [tangentVector, normalVector, frame, PiLp.inner_apply]
  have hbT : inner ℝ b (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = gap := by
    dsimp [b, gap]
    rw [inner_sub_left, hoT]
    simp [normalVector, frame, PiLp.inner_apply]
  refine ⟨min δu (min δl (min 1 gap)), by positivity, ?_⟩
  intro ε hε hεlt
  have hεu : ε < δu := hεlt.trans_le (min_le_left _ _)
  have hεl : ε < δl := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεgap : ε < gap :=
    hεlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hmoved := moved_upper_lower_contacts K t ht u l hu huval hl hlval
    hδu hδl hε hεu hεl
  rcases ht with ht | ht
  · have htval : t.val = Θ.angle := ht
    have hoMem : o ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inl htval) ho hε.le
      rw [htval, hoω]
      exact hε1.le
    have haMem : a ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inl htval) ha hε.le
      rw [htval, haω]
      exact hεgap.le
    have hother : polygonHeightValue (raisedPolygonSupport K t ε) (Real.pi / 2) = 1 := by
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr (by simp))]
      have hne : (⟨Real.pi / 2, Or.inr (by simp)⟩ : angleDomain Θ) ≠ t := by
        intro heq
        have := congrArg Subtype.val heq
        linarith [hΘ]
      rw [ite_eq_right hne, add_zero, K.val.property.2.2.2.1]
    constructor
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        simpa [htval] using hmoved.1
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        exact ⟨o, hoMem, hoT.trans hother.symm⟩
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        simpa [htval] using hmoved.2
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        refine ⟨a, haMem, ?_⟩
        rw [haT, hother]
        ring
  · have htval : t.val = Real.pi / 2 := by simpa using ht
    have hoMem : o ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inr ht) ho hε.le
      rw [htval, hoT]
      exact hε1.le
    have hbMem : b ∈ polygonHeightCap (raisedPolygonSupport K t ε) := by
      apply mem_raisedPolygonSupport_of_endpoint_of_le_inner K t (Or.inr ht) hb hε.le
      rw [htval, hbT]
      exact hεgap.le
    have hother : polygonHeightValue (raisedPolygonSupport K t ε) Θ.angle = 1 := by
      rw [polygonHeightValue_raisedPolygonSupport K t ε (Or.inr (by simp))]
      have hne : (⟨Θ.angle, Or.inr (by simp)⟩ : angleDomain Θ) ≠ t := by
        intro heq
        have := congrArg Subtype.val heq
        linarith [hΘ]
      rw [ite_eq_right hne, add_zero, K.val.property.2.2.1]
    constructor
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        exact ⟨o, hoMem, hoω.trans hother.symm⟩
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        simpa [htval] using hmoved.1
    · intro s hs
      rcases hs with hs | hs
      · have hsval : s = Θ.angle := hs
        subst s
        refine ⟨b, hbMem, ?_⟩
        rw [hbω, hother]
        ring
      · have hsval : s = Real.pi / 2 := by simpa using hs
        subst s
        simpa [htval] using hmoved.2

private theorem raisedPolygonSupport_endpoint_contacts_of_angle_eq {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (hΘ : Θ.angle = Real.pi / 2)
    (t : angleDomain Θ) (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
  obtain ⟨u, hu, huval, hustrict⟩ := exists_upperFace_midpoint_strict K t hmass
  obtain ⟨l, hl, hlval, hlstrict⟩ :=
    exists_lowerFace_midpoint_strict_of_angle_eq K hΘ t ht hmass
  obtain ⟨δu, hδupos, hδu⟩ := exists_pos_uniform_strict_support_gap K u t hustrict
  obtain ⟨δl, hδlpos, hδl⟩ := exists_pos_uniform_strict_support_gap K l t hlstrict
  have htval : t.val = Real.pi / 2 := by
    rcases ht with ht | ht
    · simpa [hΘ] using ht
    · simpa using ht
  refine ⟨min δu δl, by positivity, ?_⟩
  intro ε hε hεlt
  have hmoved := moved_upper_lower_contacts K t ht u l hu huval hl hlval
    hδu hδl hε (hεlt.trans_le (min_le_left _ _))
      (hεlt.trans_le (min_le_right _ _))
  constructor
  · intro s hs
    have hsval : s = Real.pi / 2 := by
      rcases hs with hs | hs
      · simpa [hΘ] using hs
      · simpa using hs
    subst s
    simpa [htval] using hmoved.1
  · intro s hs
    have hsval : s = Real.pi / 2 := by
      rcases hs with hs | hs
      · simpa [hΘ] using hs
      · simpa using hs
    subst s
    simpa [htval] using hmoved.2

/-- A sufficiently small endpoint height increase preserves both unit widths. -/
theorem polygonCap_positive_height_increment_of_endpoint {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : angleDomain Θ)
    (ht : t.val ∈ ({Θ.angle, Real.pi / 2} : Set ℝ))
    (hmass : 0 < surfaceAreaMeasure K.val.val {(t.val : Real.Angle)}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ K' : PolygonCapTranslateSpace Θ,
        K'.val = polygonHeightCap (raisedPolygonSupport K t ε) := by
  obtain ⟨εb, hεb, hbounded⟩ := polygonHeightCap_raised_bounded K t
  obtain ⟨εc, hεc, hcontacts⟩ : ∃ εc : ℝ, 0 < εc ∧ ∀ ε : ℝ, 0 < ε → ε < εc →
      ((∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s) ∧
      (∀ s ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        ∃ p ∈ polygonHeightCap (raisedPolygonSupport K t ε),
          inner ℝ p (normalVector (s : Real.Angle)) =
            polygonHeightValue (raisedPolygonSupport K t ε) s - 1)) := by
    rcases lt_or_eq_of_le Θ.angle_le with hΘ | hΘ
    · exact raisedPolygonSupport_endpoint_contacts_of_angle_lt K hΘ t ht hmass
    · exact raisedPolygonSupport_endpoint_contacts_of_angle_eq K hΘ t ht hmass
  refine ⟨min εb εc, by positivity, ?_⟩
  intro ε hε hεlt
  have hb : ε < εb := hεlt.trans_le (min_le_left _ _)
  have hc : ε < εc := hεlt.trans_le (min_le_right _ _)
  have hcontact := hcontacts ε hε hc
  exact exists_polygonCapTranslate_eq_polygonHeightCap _
    (hbounded ε (abs_le.mpr ⟨by linarith, hb.le⟩)) hcontact.1 hcontact.2

end MovingSofa
