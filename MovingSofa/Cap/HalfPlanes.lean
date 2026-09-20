import MovingSofa.Geometry.Contacts
import MovingSofa.Geometry.Parallelogram
import MovingSofa.Cap.Basic
import MovingSofa.ForMathlib.Convex.Support
import MovingSofa.ForMathlib.Convex.Translation

noncomputable section

namespace MovingSofa

/-- A finite set of allowed normals gives a finite supporting-half-plane representation. -/
theorem HasHalfPlaneRepresentation.finite_constraints
    {K : ConvexBody Point} {N : Set Real.Angle} (hN : N.Finite)
    (hK : HasHalfPlaneRepresentation K N) :
    ∃ constraints : Set (Real.Angle × ℝ), constraints.Finite ∧
      (∀ c ∈ constraints, c.1 ∈ N) ∧
      (K : Set Point) = ⋂ c ∈ constraints, normalHalfPlane c.1 c.2 false false := by
  obtain ⟨C, hC, hKC⟩ := hK
  refine ⟨(fun t ↦ (t, supportValue K t)) '' N, hN.image _, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact ht
  · ext x
    simp only [Set.mem_iInter]
    constructor
    · intro hx c hc
      obtain ⟨t, ht, rfl⟩ := hc
      change inner ℝ x (normalVector t) ≤ supportValue K t
      exact le_csSup ((K.isCompact.image
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove)
        ⟨x, hx, rfl⟩
    · intro hx
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have hxs := hx (c.1, supportValue K c.1) ⟨c.1, hC c hc, rfl⟩
      change inner ℝ x (normalVector c.1) ≤ supportValue K c.1 at hxs
      change inner ℝ x (normalVector c.1) ≤ c.2
      apply hxs.trans
      apply csSup_le (K.nonempty.image _)
      rintro z ⟨p, hp, rfl⟩
      rw [hKC] at hp
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hp c) hc

/-- Translation preserves a half-plane representation's allowed normals. -/
theorem HasHalfPlaneRepresentation.translate {K : ConvexBody Point}
    {N : Set Real.Angle} (hK : HasHalfPlaneRepresentation K N) (v : Point) :
    HasHalfPlaneRepresentation (ConvexBody.translate K v) N := by
  obtain ⟨C, hC, hKC⟩ := hK
  refine ⟨(fun c ↦ (c.1, c.2 + inner ℝ v (normalVector c.1))) '' C, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hC c hc
  · ext x
    simp only [ConvexBody.translate, Set.mem_image, Set.mem_iInter]
    constructor
    · rintro ⟨y, hy, rfl⟩ c ⟨d, hd, rfl⟩
      change inner ℝ (y + v) (normalVector d.1) ≤
        d.2 + inner ℝ v (normalVector d.1)
      rw [inner_add_left]
      have hmem := Set.mem_iInter.mp (Set.mem_iInter.mp (hKC ▸ hy) d) hd
      change inner ℝ y (normalVector d.1) ≤ d.2 at hmem
      simpa [add_comm] using add_le_add_right hmem (inner ℝ v (normalVector d.1))
    · intro hx
      refine ⟨x - v, ?_, by simp⟩
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have h := hx (c.1, c.2 + inner ℝ v (normalVector c.1)) ⟨c, hc, rfl⟩
      change inner ℝ x (normalVector c.1) ≤
        c.2 + inner ℝ v (normalVector c.1) at h
      change inner ℝ (x - v) (normalVector c.1) ≤ c.2
      rw [inner_sub_left]
      linarith

/-- A normalized cap is contained in its lower fan. -/
theorem CapSpace.subset_capFan {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) ⊆ capFan ω := by
  intro p hp
  constructor
  · change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle))
    have h := inner_le_supportValue K.val hp ((ω + Real.pi : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at h
    linarith
  · change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    have h := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
        ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
      congr 1
      ring
    rw [K.property.2.2.2.2.2.1, ← hang] at h
    rw [normalVector_add_pi, inner_neg_right] at h
    linarith

/-- Fan membership and strict upper support inequalities imply cap membership. -/
theorem CapSpace.mem_of_mem_capFan_of_lt_supportValue {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hp : p ∈ capFan ω)
    (hupper : ∀ t ∈ Set.Icc 0 (ω + Real.pi / 2),
      inner ℝ p (normalVector (t : Real.Angle)) < supportValue K.val (t : Real.Angle)) :
    p ∈ (K.val : Set Point) := by
  obtain ⟨C, hCN, hKC⟩ := K.property.2.2.2.2.2.2
  rw [hKC]
  simp only [Set.mem_iInter]
  intro c hc
  have hsupport : supportValue K.val c.1 ≤ c.2 := by
    apply supportValue_le_of_subset_normalHalfPlane
    intro q hq
    rw [hKC] at hq
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hq c) hc
  rcases hCN c hc with hcupper | hclower
  · obtain ⟨t, ht, heq⟩ := hcupper
    rw [← heq] at hsupport ⊢
    have htI : t ∈ Set.Icc 0 (ω + Real.pi / 2) := by
      rcases ht with ht | ht
      · exact ⟨ht.1, ht.2.trans (le_add_of_nonneg_right (by positivity))⟩
      · exact ⟨(by positivity : 0 ≤ Real.pi / 2).trans ht.1, ht.2⟩
    change inner ℝ p (normalVector (t : Real.Angle)) ≤ c.2
    exact (hupper t htI).le.trans hsupport
  · rcases hclower with hclower | hclower
    · rw [hclower] at hsupport ⊢
      change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤ c.2
      rw [normalVector_add_pi, inner_neg_right]
      have hpω := hp.1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      rw [K.property.2.2.2.2.1] at hsupport
      linarith [hsupport]
    · rw [hclower] at hsupport ⊢
      have hang : (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) =
          ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
        congr 1
        ring
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ c.2
      rw [← hang, normalVector_add_pi, inner_neg_right]
      have hpT := hp.2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
      rw [K.property.2.2.2.2.2.1] at hsupport
      linarith [hsupport]

/-- A normalized cap lies in the intersection of its two unit strips. -/
theorem CapSpace.subset_stripParallelogram {ω : ℝ} (K : CapSpace ω) :
    (K.val : Set Point) ⊆ (stripParallelogram ω).1 := by
  intro p hp
  have hlower := inner_le_supportValue K.val hp ((ω + Real.pi : ℝ) : Real.Angle)
  have hbottom := inner_le_supportValue K.val hp ((3 * Real.pi / 2 : ℝ) : Real.Angle)
  rw [K.property.2.2.2.2.1, normalVector_add_pi, inner_neg_right] at hlower
  rw [K.property.2.2.2.2.2.1, inner_normalVector_three_pi_div_two] at hbottom
  have hupper := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
  have hright := inner_le_supportValue K.val hp (ω : Real.Angle)
  rw [K.property.2.2.2.1] at hupper
  rw [K.property.2.2.1] at hright
  rw [mem_stripParallelogram_iff]
  have hlo : 0 ≤ p 1 := by linarith
  have hhi : p 1 ≤ 1 := by
    simpa [normalVector, frame, PiLp.inner_apply] using hupper
  exact ⟨⟨hlo, hhi⟩, by linarith, hright⟩


/-- A half-plane representation can be tightened at every allowed normal. -/
theorem HasHalfPlaneRepresentation.eq_iInter_supportValue {K : ConvexBody Point}
    {N : Set Real.Angle} (hK : HasHalfPlaneRepresentation K N) :
    (K : Set Point) = ⋂ t ∈ N, normalHalfPlane t (supportValue K t) false false := by
  obtain ⟨C, hCN, hKC⟩ := hK
  ext p
  simp only [Set.mem_iInter]
  constructor
  · intro hp t _
    exact inner_le_supportValue K hp t
  · intro hp
    rw [hKC]
    simp only [Set.mem_iInter]
    intro c hc
    have ht := hp c.1 (hCN c hc)
    change inner ℝ p (normalVector c.1) ≤ c.2
    apply ht.trans
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    rw [hKC] at hq
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hq c) hc


/-- A fan point satisfying all upper supporting inequalities belongs to the cap. -/
theorem CapSpace.mem_of_mem_capFan_of_le_supportValue {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hp : p ∈ capFan ω)
    (hupper : ∀ t ∈ capUpperAngles ω,
      inner ℝ p (normalVector (t : Real.Angle)) ≤ supportValue K.val (t : Real.Angle)) :
    p ∈ (K.val : Set Point) := by
  rw [K.property.2.2.2.2.2.2.eq_iInter_supportValue]
  simp only [Set.mem_iInter]
  intro a ha
  rcases ha with ⟨t, ht, rfl⟩ | ha
  · exact hupper t ht
  rcases ha with rfl | rfl
  · change inner ℝ p (normalVector ((ω + Real.pi : ℝ) : Real.Angle)) ≤
      supportValue K.val ((ω + Real.pi : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.1]
    rw [normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hp.1
  · have hang : ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
        (((Real.pi / 2 + Real.pi : ℝ) : Real.Angle)) := by
      congr 1
      ring
    change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
      supportValue K.val ((3 * Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.2.2.1]
    rw [hang, normalVector_add_pi, inner_neg_right]
    exact neg_nonpos.mpr hp.2

/-- Upper support bounds supplied by the two unit-height constraints of a cap. -/
theorem CapSpace.supportValue_upper_bounds {ω t : ℝ} (K : CapSpace ω)
    (ht : t ∈ Set.Ioo 0 ω) :
    supportValue K.val (t : Real.Angle) ≤
        Real.cos t * supportValue K.val (0 : Real.Angle) + Real.sin t ∧
      supportValue K.val ((t + Real.pi / 2 : ℝ) : Real.Angle) ≤
        Real.sin (ω - t) + Real.cos (ω - t) *
          supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
  have hcost : 0 ≤ Real.cos t := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2.trans_le K.property.2.1⟩).le
  have hsint : 0 ≤ Real.sin t := (Real.sin_pos_of_pos_of_lt_pi ht.1
    (by linarith [ht.2, K.property.2.1, Real.pi_pos])).le
  have hcosδ : 0 ≤ Real.cos (ω - t) := (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [sub_pos.mpr ht.2, Real.pi_pos],
      by linarith [ht.1, K.property.2.1]⟩).le
  have hsinδ : 0 ≤ Real.sin (ω - t) := (Real.sin_pos_of_pos_of_lt_pi
    (sub_pos.mpr ht.2) (by linarith [ht.1, K.property.2.1, Real.pi_pos])).le
  constructor
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hx := inner_le_supportValue K.val hp (0 : Real.Angle)
    have hy := inner_le_supportValue K.val hp ((Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.2.1] at hy
    simp [normalVector, frame, PiLp.inner_apply] at hx hy ⊢
    nlinarith
  · apply csSup_le (K.val.nonempty.image _)
    rintro _ ⟨p, hp, rfl⟩
    have hu := inner_le_supportValue K.val hp (ω : Real.Angle)
    have hv := inner_le_supportValue K.val hp
      ((ω + Real.pi / 2 : ℝ) : Real.Angle)
    rw [K.property.2.2.1] at hu
    have hvec : normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        Real.sin (ω - t) • normalVector (ω : Real.Angle) +
          Real.cos (ω - t) • tangentVector (ω : Real.Angle) := by
      have h := normalVector_add_real ω (Real.pi / 2 - (ω - t))
      rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub] at h
      simpa only [show ω + (Real.pi / 2 - (ω - t)) = t + Real.pi / 2 by ring] using h
    change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
    rw [hvec, inner_add_right, inner_smul_right, inner_smul_right]
    have hv' : inner ℝ p (tangentVector (ω : Real.Angle)) ≤
        supportValue K.val ((ω + Real.pi / 2 : ℝ) : Real.Angle) := by
      simpa [normalVector, tangentVector, frame, Real.Angle.cos_add_pi_div_two,
        Real.Angle.sin_add_pi_div_two] using hv
    nlinarith

/-- Every point of a cap lies above the horizontal base line. -/
theorem CapSpace.inner_normalVector_pi_div_two_nonneg {ω : ℝ} (K : CapSpace ω) {q : Point}
    (hq : q ∈ (K.1 : Set Point)) :
    0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) := (K.subset_capFan hq).2

/-- Lowering a point of a right-angle cap onto the base line keeps it inside the cap: every
upper normal of such a cap has nonnegative vertical component, so no upper constraint is
tightened, and the two base constraints of the fan coincide here and hold with equality. -/
theorem CapSpace.base_projection_mem (K : CapSpace (Real.pi / 2)) {q : Point}
    (hq : q ∈ (K.val : Set Point)) :
    q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (K.val : Set Point) := by
  have hq1 : 0 ≤ q 1 := by
    simpa only [inner_normalVector_pi_div_two] using K.inner_normalVector_pi_div_two_nonneg hq
  have hinner (s : ℝ) : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector (s : Real.Angle)) =
      inner ℝ q (normalVector (s : Real.Angle)) - q 1 * Real.sin s := by
    rw [inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector,
      Real.cos_pi_div_two_sub]
  have hbase : inner ℝ (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) = 0 := by
    rw [hinner, inner_normalVector_pi_div_two, Real.sin_pi_div_two, mul_one, sub_self]
  refine K.mem_of_mem_capFan_of_le_supportValue ⟨?_, ?_⟩ ?_
  · change 0 ≤ inner ℝ _ (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    rw [hbase]
  · change 0 ≤ inner ℝ _ (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
    rw [hbase]
  · intro s hs
    have hs' : 0 ≤ s ∧ s ≤ Real.pi := by
      rcases hs with hs | hs
      · exact ⟨hs.1, by linarith [hs.2, Real.pi_pos]⟩
      · exact ⟨by linarith [hs.1, Real.pi_pos], by linarith [hs.2]⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs'.1 hs'.2
    rw [hinner]
    linarith [mul_nonneg hq1 hsin, inner_le_supportValue K.val hq (s : Real.Angle)]

/-- The top supporting line of a right-angle cap is the horizontal line of height one, so every
point attaining the support value at the vertical normal has height one. -/
theorem CapSpace.apply_one_eq_one (K : CapSpace (Real.pi / 2)) {p : Point}
    (hp : inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) =
      supportValue (K.val : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle)) : p 1 = 1 := by
  rwa [inner_normalVector_pi_div_two, K.property.2.2.2.1] at hp

/-- A singleton extreme face of a right-angle cap at a horizontal normal lies on the base line.
Lowering its unique point onto the base line keeps it in the cap, and a horizontal normal does not
see that vertical displacement, so the lowered point lies in the same face; the face being a
singleton, the displacement vanishes. -/
theorem CapSpace.edgeVertices_fst_apply_one_eq_zero (K : CapSpace (Real.pi / 2)) {s : ℝ}
    (hs : Real.sin s = 0)
    (hface : (edgeVertices K.val (s : Real.Angle)).1 = (edgeVertices K.val (s : Real.Angle)).2) :
    (edgeVertices K.val (s : Real.Angle)).1 1 = 0 := by
  have hmem := edgeVertices_fst_mem K.val (s : Real.Angle)
  have hkey : inner ℝ ((edgeVertices K.val (s : Real.Angle)).1 -
      (edgeVertices K.val (s : Real.Angle)).1 1 •
        normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) (normalVector (s : Real.Angle)) =
      supportValue (K.val : Set Point) (s : Real.Angle) := by
    rw [inner_sub_left, real_inner_smul_left, inner_normalVector_normalVector,
      Real.cos_pi_div_two_sub, hs, mul_zero, sub_zero]
    exact hmem.2
  have hlow : (edgeVertices K.val (s : Real.Angle)).1 -
      (edgeVertices K.val (s : Real.Angle)).1 1 •
        normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈
      exposedEdge K.val (s : Real.Angle) := ⟨K.base_projection_mem hmem.1, hkey⟩
  rw [exposedEdge_eq_segment_edgeVertices, ← hface, segment_same, Set.mem_singleton_iff,
    sub_eq_self] at hlow
  have h := congrArg (fun p : Point ↦ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)))
    hlow
  rwa [real_inner_smul_left, inner_normalVector_self, mul_one, inner_zero_left] at h

/-- A convex body with vanishing base support value that is stable under vertical projection to
the base line is cut out by upper half-planes together with the base half-plane. -/
theorem hasHalfPlaneRepresentation_of_base_projection (M : ConvexBody Point)
    (hbase : supportValue M ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0)
    (hproj : ∀ q ∈ (M : Set Point),
      q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈ (M : Set Point)) :
    HasHalfPlaneRepresentation M
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
        capLowerNormals (Real.pi / 2)) := by
  -- At a right angle the allowed upper normals are exactly the angles of `[0, π]`.
  have hangle : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
      ((s : ℝ) : Real.Angle) ∈
        (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
          capLowerNormals (Real.pi / 2)) := by
    intro s hs
    refine Or.inl ⟨s, ?_, rfl⟩
    rcases le_or_gt s (Real.pi / 2) with h | h
    · exact Or.inl ⟨hs.1, h⟩
    · exact Or.inr ⟨h.le, by linarith [hs.2]⟩
  -- The vertical projection keeps the horizontal coordinate and kills the vertical one.
  have hflat : ∀ q : Point,
      (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 0 = q 0 ∧
        (q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) 1 = 0 := by
    intro q
    constructor <;> simp [normalVector, frame]
  -- The two attained horizontal extrema, lowered onto the base line.
  obtain ⟨qR, hqR, hqRval⟩ := exists_mem_inner_eq_supportValue M ((0 : ℝ) : Real.Angle)
  obtain ⟨qL, hqL, hqLval⟩ := exists_mem_inner_eq_supportValue M ((Real.pi : ℝ) : Real.Angle)
  rw [inner_normalVector_zero] at hqRval
  rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi] at hqLval
  refine ⟨(fun a : Real.Angle ↦ (a, supportValue M a)) ''
    ((((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
      capLowerNormals (Real.pi / 2))), ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ha
  · ext p
    simp only [Set.mem_iInter]
    refine ⟨fun hp c hc ↦ ?_, fun hp ↦ ?_⟩
    · obtain ⟨a, -, rfl⟩ := hc
      exact inner_le_supportValue M hp a
    · have hpupper : ∀ s ∈ Set.Icc (0 : ℝ) Real.pi,
          inner ℝ p (normalVector ((s : ℝ) : Real.Angle)) ≤
            supportValue M ((s : ℝ) : Real.Angle) :=
        fun s hs ↦ hp _ ⟨_, hangle s hs, rfl⟩
      have hpbase := hp _ ⟨((3 * Real.pi / 2 : ℝ) : Real.Angle),
        Or.inr (Set.mem_insert_iff.2 (Or.inr rfl)), rfl⟩
      change inner ℝ p (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤
        supportValue M ((3 * Real.pi / 2 : ℝ) : Real.Angle) at hpbase
      rw [inner_normalVector_three_pi_div_two, hbase] at hpbase
      have hp1 : 0 ≤ p 1 := by linarith
      have hpR : p 0 ≤ qR 0 := by
        have h := hpupper 0 ⟨le_rfl, Real.pi_pos.le⟩
        rw [inner_normalVector_zero, ← hqRval] at h
        exact h
      have hpL : qL 0 ≤ p 0 := by
        have h := hpupper Real.pi ⟨Real.pi_pos.le, le_rfl⟩
        rw [inner_normalVector_real, Real.cos_pi, Real.sin_pi, ← hqLval] at h
        linarith
      rw [M.eq_iInter_halfSpaces]
      simp only [Set.mem_iInter]
      intro u hu
      obtain ⟨θ, rfl⟩ := exists_angle_normalVector_eq hu
      show inner ℝ p (normalVector θ) ≤ supportValue M θ
      rw [← Real.Angle.coe_toReal θ]
      set s : ℝ := θ.toReal
      rcases le_or_gt 0 s with hs0 | hs0
      · exact hpupper s ⟨hs0, Real.Angle.toReal_le_pi θ⟩
      · have hsin : Real.sin s < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hs0 (Real.Angle.neg_pi_lt_toReal θ)
        rw [inner_normalVector_real]
        rcases le_or_gt 0 (Real.cos s) with hc | hc
        · have h := inner_le_supportValue M (hproj qR hqR) ((s : ℝ) : Real.Angle)
          rw [inner_normalVector_real, (hflat qR).1, (hflat qR).2] at h
          nlinarith [mul_le_mul_of_nonneg_right hpR hc,
            mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le]
        · have h := inner_le_supportValue M (hproj qL hqL) ((s : ℝ) : Real.Angle)
          rw [inner_normalVector_real, (hflat qL).1, (hflat qL).2] at h
          nlinarith [mul_le_mul_of_nonpos_right hpL hc.le,
            mul_nonpos_of_nonneg_of_nonpos hp1 hsin.le]

end MovingSofa
