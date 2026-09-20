import MovingSofa.Geometry.Support

noncomputable section

namespace MovingSofa

/-- The exposed edge at a normal direction, including singleton edges. -/
def exposedEdge (K : ConvexBody Point) (t : Real.Angle) : Set Point :=
  (K : Set Point) ∩ (supportingLineHalfPlane K t).1

/-- The positive and negative tangent endpoints of an exposed edge. -/
def edgeVertices (K : ConvexBody Point) (t : Real.Angle) : Point × Point :=
  let heights := (fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t
  (supportValue K t • normalVector t + sSup heights • tangentVector t,
    supportValue K t • normalVector t + sInf heights • tangentVector t)

/-- The intersection point of two supporting lines at nonparallel normal directions. -/
def supportingIntersection (K : ConvexBody Point) (a b : Real.Angle) : Point :=
  supportValue K a • normalVector a +
    ((supportValue K b - supportValue K a * (b - a).cos) / (b - a).sin) • tangentVector a

theorem exposedEdge_nonempty (K : ConvexBody Point) (t : Real.Angle) :
    (exposedEdge K t).Nonempty := by
  obtain ⟨x, hx, hxmax, _⟩ := K.isCompact.exists_sSup_image_eq_and_ge
    (f := fun x : Point ↦ inner ℝ x (normalVector t)) K.nonempty
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  refine ⟨x, hx, ?_⟩
  simpa [supportingLineHalfPlane, normalLine, supportValue] using hxmax.symm

theorem convex_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    Convex ℝ (exposedEdge K t) := by
  apply K.convex.inter
  intro x hx y hy a b ha hb hab
  change inner ℝ x (normalVector t) = supportValue K t at hx
  change inner ℝ y (normalVector t) = supportValue K t at hy
  change inner ℝ (a • x + b • y) (normalVector t) = supportValue K t
  rw [inner_add_left, inner_smul_left, inner_smul_left, hx, hy]
  simp only [RCLike.conj_to_real]
  rw [← add_mul, hab, one_mul]

theorem isConnected_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsConnected (exposedEdge K t) :=
  (convex_exposedEdge K t).isConnected (exposedEdge_nonempty K t)

theorem supportingIntersection_inner_left (K : ConvexBody Point) (s t : ℝ) :
    inner ℝ (supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (normalVector (s : Real.Angle)) = supportValue K (s : Real.Angle) := by
  have htn : inner ℝ (tangentVector (s : Real.Angle)) (normalVector (s : Real.Angle)) = 0 := by
    rw [real_inner_comm, inner_normalVector_tangentVector]
  simp only [supportingIntersection, inner_add_left, real_inner_smul_left,
    inner_normalVector_self, htn, mul_one, mul_zero, add_zero]

theorem supportingIntersection_inner_right (K : ConvexBody Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    inner ℝ (supportingIntersection K (s : Real.Angle) (t : Real.Angle))
      (normalVector (t : Real.Angle)) = supportValue K (t : Real.Angle) := by
  have hn : normalVector (t : Real.Angle) =
      Real.cos (t - s) • normalVector (s : Real.Angle) +
      Real.sin (t - s) • tangentVector (s : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real s (t - s)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right,
    supportingIntersection_inner_left]
  simp only [supportingIntersection, inner_add_left, real_inner_smul_left,
    inner_normalVector_tangentVector, inner_tangentVector_self, mul_zero, mul_one, zero_add,
    ← Real.Angle.coe_sub, Real.Angle.cos_coe, Real.Angle.sin_coe]
  field_simp
  ring

theorem supportingIntersection_comm (K : ConvexBody Point) (s t : ℝ)
    (h : Real.sin (t - s) ≠ 0) :
    supportingIntersection K (s : Real.Angle) (t : Real.Angle) =
      supportingIntersection K (t : Real.Angle) (s : Real.Angle) := by
  have h' : Real.sin (s - t) ≠ 0 := by
    rw [show s - t = -(t - s) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr h
  let p := supportingIntersection K (t : Real.Angle) (s : Real.Angle)
  have hp := supportingIntersection_inner_right K t s h'
  have hq := supportingIntersection_inner_left K t s
  change inner ℝ p (normalVector (s : Real.Angle)) = _ at hp
  change inner ℝ p (normalVector (t : Real.Angle)) = _ at hq
  have hn : normalVector (t : Real.Angle) =
      Real.cos (t - s) • normalVector (s : Real.Angle) +
      Real.sin (t - s) • tangentVector (s : Real.Angle) := by
    simpa only [add_sub_cancel] using normalVector_add_real s (t - s)
  rw [hn, inner_add_right, inner_smul_right, inner_smul_right, hp] at hq
  have ht : inner ℝ p (tangentVector (s : Real.Angle)) =
      (supportValue K (t : Real.Angle) - supportValue K (s : Real.Angle) *
        Real.cos (t - s)) / Real.sin (t - s) := by
    apply (eq_div_iff h).mpr
    linarith
  have heq := inner_normalVector_smul_add_inner_tangentVector_smul p (s : Real.Angle)
  rw [hp, ht] at heq
  simpa only [p, supportingIntersection, ← Real.Angle.coe_sub, Real.Angle.cos_coe,
    Real.Angle.sin_coe] using heq

/-- Every exposed edge of a compact convex body is compact. -/
theorem isCompact_exposedEdge (K : ConvexBody Point) (t : Real.Angle) :
    IsCompact (exposedEdge K t) :=
  K.isCompact.inter_right (isClosed_eq
    (continuous_id.inner continuous_const) continuous_const)

/-- The positive tangent endpoint belongs to its exposed edge. -/
theorem edgeVertices_fst_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).1 ∈ exposedEdge K t := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_exposedEdge K t).exists_sSup_image_eq
    (exposedEdge_nonempty K t)
    (f := fun p : Point ↦ inner ℝ p (tangentVector t))
    (continuous_id.inner continuous_const).continuousOn
  have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
  have heq : (edgeVertices K t).1 = p := by
    change supportValue K t • normalVector t +
      sSup ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) • tangentVector t = p
    rw [hmax, ← hpnormal]
    exact inner_normalVector_smul_add_inner_tangentVector_smul p t
  exact heq ▸ hp

/-- The negative tangent endpoint belongs to its exposed edge. -/
theorem edgeVertices_snd_mem (K : ConvexBody Point) (t : Real.Angle) :
    (edgeVertices K t).2 ∈ exposedEdge K t := by
  obtain ⟨p, hp, hmin⟩ := (isCompact_exposedEdge K t).exists_sInf_image_eq
    (exposedEdge_nonempty K t)
    (f := fun p : Point ↦ inner ℝ p (tangentVector t))
    (continuous_id.inner continuous_const).continuousOn
  have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
  have heq : (edgeVertices K t).2 = p := by
    change supportValue K t • normalVector t +
      sInf ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) • tangentVector t = p
    rw [hmin, ← hpnormal]
    exact inner_normalVector_smul_add_inner_tangentVector_smul p t
  exact heq ▸ hp

/-- A singleton exposed face is both of its tangent endpoints. -/
theorem edgeVertices_eq_of_exposedEdge_singleton {K : ConvexBody Point} {t : Real.Angle}
    {p : Point} (h : exposedEdge K t = {p}) : edgeVertices K t = (p, p) := by
  have h1 := edgeVertices_fst_mem K t
  have h2 := edgeVertices_snd_mem K t
  rw [h, Set.mem_singleton_iff] at h1 h2
  exact Prod.ext h1 h2

/-- The positive face vertex attains the largest tangent coordinate. -/
theorem inner_edgeVertices_fst_tangent (K : ConvexBody Point) (t : Real.Angle) :
    inner ℝ (edgeVertices K t).1 (tangentVector t) =
      sSup ((fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp only [edgeVertices, inner_add_left, real_inner_smul_left,
      inner_normalVector_tangentVector, inner_tangentVector_self]
    ring

/-- The negative face vertex attains the smallest tangent coordinate. -/
theorem inner_edgeVertices_snd_tangent (K : ConvexBody Point) (t : Real.Angle) :
    inner ℝ (edgeVertices K t).2 (tangentVector t) =
      sInf ((fun p ↦ inner ℝ p (tangentVector t)) '' exposedEdge K t) := by
  induction t using Real.Angle.induction_on with
  | _ t =>
    simp only [edgeVertices, inner_add_left, real_inner_smul_left,
      inner_normalVector_tangentVector, inner_tangentVector_self]
    ring

private theorem exposedEdge_subset_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t ⊆ segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  intro p hp
  let lo := (edgeVertices K t).2
  let hi := (edgeVertices K t).1
  let z := inner ℝ p (tangentVector t)
  let zlo := inner ℝ lo (tangentVector t)
  let zhi := inner ℝ hi (tangentVector t)
  have hbddBelow : BddBelow ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) :=
    (isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const) |>.bddBelow
  have hbddAbove : BddAbove ((fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t) :=
    (isCompact_exposedEdge K t).image
      (continuous_id.inner continuous_const) |>.bddAbove
  have hzmem : z ∈ (fun q ↦ inner ℝ q (tangentVector t)) '' exposedEdge K t :=
    ⟨p, hp, rfl⟩
  have hzlo : zlo ≤ z := by
    dsimp only [zlo, z, lo]
    rw [inner_edgeVertices_snd_tangent]
    exact csInf_le hbddBelow hzmem
  have hzhi : z ≤ zhi := by
    dsimp only [zhi, z, hi]
    rw [inner_edgeVertices_fst_tangent]
    exact le_csSup hbddAbove hzmem
  by_cases hzh : zlo = zhi
  · have hz : z = zlo := le_antisymm (hzhi.trans_eq hzh.symm) hzlo
    have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
    have hlonormal : inner ℝ lo (normalVector t) = supportValue K t :=
      (edgeVertices_snd_mem K t).2
    have hpl : p = lo := by
      rw [← inner_normalVector_smul_add_inner_tangentVector_smul p t,
        ← inner_normalVector_smul_add_inner_tangentVector_smul lo t,
        hpnormal, hlonormal]
      change inner ℝ p (tangentVector t) = inner ℝ lo (tangentVector t) at hz
      rw [hz]
    simpa only [lo, hi, hpl] using left_mem_segment ℝ lo hi
  · have hlt : zlo < zhi := lt_of_le_of_ne (hzlo.trans hzhi) hzh
    let u := (z - zlo) / (zhi - zlo)
    have hu : u ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hzlo) (sub_nonneg.mpr hlt.le)
      · rw [div_le_one (sub_pos.mpr hlt)]
        linarith
    rw [segment_eq_image]
    refine ⟨u, hu, ?_⟩
    change (1 - u) • lo + u • hi = p
    have hpnormal : inner ℝ p (normalVector t) = supportValue K t := hp.2
    have hlonormal : inner ℝ lo (normalVector t) = supportValue K t :=
      (edgeVertices_snd_mem K t).2
    have hhinormal : inner ℝ hi (normalVector t) = supportValue K t :=
      (edgeVertices_fst_mem K t).2
    have hnormal : inner ℝ ((1 - u) • lo + u • hi) (normalVector t) =
        inner ℝ p (normalVector t) := by
      simp only [inner_add_left, real_inner_smul_left, hlonormal, hhinormal, hpnormal]
      ring
    have htangent : inner ℝ ((1 - u) • lo + u • hi) (tangentVector t) =
        inner ℝ p (tangentVector t) := by
      simp only [inner_add_left, real_inner_smul_left]
      change (1 - u) * zlo + u * zhi = z
      dsimp [u]
      field_simp [sub_ne_zero.mpr (ne_of_gt hlt)]
      ring
    rw [← inner_normalVector_smul_add_inner_tangentVector_smul
      ((1 - u) • lo + u • hi) t,
      ← inner_normalVector_smul_add_inner_tangentVector_smul p t,
      hnormal, htangent]

/-- An exposed face is the segment joining its two tangent-extreme vertices. -/
theorem exposedEdge_eq_segment_edgeVertices (K : ConvexBody Point)
    (t : Real.Angle) :
    exposedEdge K t = segment ℝ (edgeVertices K t).2 (edgeVertices K t).1 := by
  apply Set.Subset.antisymm (exposedEdge_subset_segment_edgeVertices K t)
  exact (convex_exposedEdge K t).segment_subset
    (edgeVertices_snd_mem K t) (edgeVertices_fst_mem K t)

/-- An exposed face determines the support value and both of its endpoint vertices. -/
theorem edgeVertices_eq_of_exposedEdge_eq (K L : ConvexBody Point) (u : Real.Angle)
    (h : exposedEdge K u = exposedEdge L u) : edgeVertices K u = edgeVertices L u := by
  obtain ⟨p, hp⟩ := exposedEdge_nonempty K u
  have hpL : p ∈ exposedEdge L u := h ▸ hp
  have hK : inner ℝ p (normalVector u) = supportValue K u := hp.2
  have hL : inner ℝ p (normalVector u) = supportValue L u := hpL.2
  simp only [edgeVertices, hK.symm.trans hL, h]


/-- A support-line intersection in the body is the negative endpoint at the later normal. -/
theorem supportingIntersection_eq_edgeVertices_snd_of_mem (K : ConvexBody Point) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hp : supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) =
      (edgeVertices K (b : Real.Angle)).2 := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let e := (edgeVertices K (b : Real.Angle)).2
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hsina : Real.sin (a - b) < 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_neg_of_pos hsin
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hpedge : p ∈ exposedEdge K (b : Real.Angle) := ⟨hp, hpb⟩
  have heedge := edgeVertices_snd_mem K (b : Real.Angle)
  have hen : inner ℝ e (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) := heedge.2
  have hpt : inner ℝ p (tangentVector (b : Real.Angle)) =
      inner ℝ e (tangentVector (b : Real.Angle)) := by
    rw [inner_edgeVertices_snd_tangent]
    apply le_antisymm
    · apply le_csInf ((exposedEdge_nonempty K _).image _)
      rintro _ ⟨q, hq, rfl⟩
      have hqa := inner_le_supportValue K hq.1 (a : Real.Angle)
      have hna : normalVector (a : Real.Angle) =
          Real.cos (a - b) • normalVector (b : Real.Angle) +
            Real.sin (a - b) • tangentVector (b : Real.Angle) := by
        simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
      rw [← hpa, hna] at hqa
      simp only [inner_add_right, inner_smul_right] at hqa
      rw [hpb, hq.2] at hqa
      nlinarith
    · exact csInf_le ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddBelow ⟨p, hpedge, rfl⟩
  change p = e
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (b : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul e (b : Real.Angle), hpb, hen,
    hpt]

/-- A support-line intersection in the body is the positive endpoint at the earlier normal. -/
theorem supportingIntersection_eq_edgeVertices_fst_of_mem (K : ConvexBody Point) {a b : ℝ}
    (hab : 0 < b - a) (hpi : b - a < Real.pi)
    (hp : supportingIntersection K (a : Real.Angle) (b : Real.Angle) ∈ K) :
    supportingIntersection K (a : Real.Angle) (b : Real.Angle) =
      (edgeVertices K (a : Real.Angle)).1 := by
  let p := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let e := (edgeVertices K (a : Real.Angle)).1
  have hsin : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi hab hpi
  have hpa : inner ℝ p (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := supportingIntersection_inner_left K a b
  have hpb : inner ℝ p (normalVector (b : Real.Angle)) =
      supportValue K (b : Real.Angle) :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hpedge : p ∈ exposedEdge K (a : Real.Angle) := ⟨hp, hpa⟩
  have heedge := edgeVertices_fst_mem K (a : Real.Angle)
  have hen : inner ℝ e (normalVector (a : Real.Angle)) =
      supportValue K (a : Real.Angle) := heedge.2
  have hpt : inner ℝ p (tangentVector (a : Real.Angle)) =
      inner ℝ e (tangentVector (a : Real.Angle)) := by
    rw [inner_edgeVertices_fst_tangent]
    apply le_antisymm
    · exact le_csSup ((isCompact_exposedEdge K _).image
        (continuous_id.inner continuous_const)).bddAbove ⟨p, hpedge, rfl⟩
    · apply csSup_le ((exposedEdge_nonempty K _).image _)
      rintro _ ⟨q, hq, rfl⟩
      have hqb := inner_le_supportValue K hq.1 (b : Real.Angle)
      have hnb : normalVector (b : Real.Angle) =
          Real.cos (b - a) • normalVector (a : Real.Angle) +
            Real.sin (b - a) • tangentVector (a : Real.Angle) := by
        simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
      rw [← hpb, hnb] at hqb
      simp only [inner_add_right, inner_smul_right] at hqb
      rw [hpa, hq.2] at hqb
      nlinarith
  change p = e
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul p (a : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul e (a : Real.Angle), hpa, hen,
    hpt]


/-- The first endpoint reaches the adjacent supporting-line intersection along a positive
tangent ray. -/
theorem supportingIntersection_eq_fst_add_pos_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ d : ℝ, 0 < d ∧ supportingIntersection K a b =
      (edgeVertices K (a : Real.Angle)).1 + d • tangentVector (a : Real.Angle) := by
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let P := (edgeVertices K (a : Real.Angle)).1
  let d := inner ℝ (O - P) (tangentVector (a : Real.Angle))
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hOn : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
    supportingIntersection_inner_left K a b
  have hPn : inner ℝ P (normalVector (a : Real.Angle)) = supportValue K a :=
    (edgeVertices_fst_mem K (a : Real.Angle)).2
  have hnormal : inner ℝ (O - P) (normalVector (a : Real.Angle)) = 0 := by
    rw [inner_sub_left, hOn, hPn, sub_self]
  have hdir : O = P + d • tangentVector (a : Real.Angle) := by
    rw [show O = P + (O - P) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
      (O - P) (a : Real.Angle), hnormal, zero_smul, zero_add]
  have hdnonneg : 0 ≤ d := by
    have hOb : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
      supportingIntersection_inner_right K a b hsin.ne'
    have hPb := inner_le_supportValue K (edgeVertices_fst_mem K (a : Real.Angle)).1
      (b : Real.Angle)
    change inner ℝ P (normalVector (b : Real.Angle)) ≤ supportValue K b at hPb
    have hnb : normalVector (b : Real.Angle) =
        Real.cos (b - a) • normalVector (a : Real.Angle) +
          Real.sin (b - a) • tangentVector (a : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real a (b - a)
    rw [← hOb, hdir, hnb, inner_add_left, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_smul_left, hPn] at hPb
    have htn : inner ℝ (tangentVector (a : Real.Angle))
        (normalVector (a : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    simp only [inner_add_right, inner_smul_right, htn,
      inner_tangentVector_self, mul_zero, mul_one, zero_add] at hPb
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    have hOP : O = P := by simpa [hd] using hdir
    have hOmem : O ∈ K := hOP ▸ (edgeVertices_fst_mem K _).1
    have hOQ := supportingIntersection_eq_edgeVertices_snd_of_mem K
      (sub_pos.mpr hab) (by linarith) hOmem
    exact hne (hOP.symm.trans hOQ)
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdir⟩

/-- The second endpoint reaches the adjacent supporting-line intersection against a positive
tangent ray. -/
theorem supportingIntersection_eq_snd_sub_pos_tangent
    (K : ConvexBody Point) {a b : ℝ} (hab : a < b) (hba : b < a + Real.pi)
    (hne : (edgeVertices K (a : Real.Angle)).1 ≠
      (edgeVertices K (b : Real.Angle)).2) :
    ∃ d : ℝ, 0 < d ∧ supportingIntersection K a b =
      (edgeVertices K (b : Real.Angle)).2 - d • tangentVector (b : Real.Angle) := by
  let O := supportingIntersection K (a : Real.Angle) (b : Real.Angle)
  let Q := (edgeVertices K (b : Real.Angle)).2
  let d := inner ℝ (Q - O) (tangentVector (b : Real.Angle))
  have hsin : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hab) (by linarith)
  have hOn : inner ℝ O (normalVector (b : Real.Angle)) = supportValue K b :=
    supportingIntersection_inner_right K a b hsin.ne'
  have hQn : inner ℝ Q (normalVector (b : Real.Angle)) = supportValue K b :=
    (edgeVertices_snd_mem K (b : Real.Angle)).2
  have hnormal : inner ℝ (Q - O) (normalVector (b : Real.Angle)) = 0 := by
    rw [inner_sub_left, hQn, hOn, sub_self]
  have hdir : O = Q - d • tangentVector (b : Real.Angle) := by
    rw [show O = Q - (Q - O) by abel, ← inner_normalVector_smul_add_inner_tangentVector_smul
      (Q - O) (b : Real.Angle), hnormal, zero_smul, zero_add]
  have hdnonneg : 0 ≤ d := by
    have hOa : inner ℝ O (normalVector (a : Real.Angle)) = supportValue K a :=
      supportingIntersection_inner_left K a b
    have hQa := inner_le_supportValue K (edgeVertices_snd_mem K (b : Real.Angle)).1
      (a : Real.Angle)
    change inner ℝ Q (normalVector (a : Real.Angle)) ≤ supportValue K a at hQa
    have hna : normalVector (a : Real.Angle) =
        Real.cos (a - b) • normalVector (b : Real.Angle) +
          Real.sin (a - b) • tangentVector (b : Real.Angle) := by
      simpa only [add_sub_cancel] using normalVector_add_real b (a - b)
    rw [← hOa, hdir, hna, inner_sub_left, inner_add_right, inner_smul_right,
      inner_smul_right, real_inner_smul_left, hQn] at hQa
    have htn : inner ℝ (tangentVector (b : Real.Angle))
        (normalVector (b : Real.Angle)) = 0 := by
      rw [real_inner_comm, inner_normalVector_tangentVector]
    simp only [inner_add_right, inner_smul_right, htn,
      inner_tangentVector_self, mul_zero, mul_one, zero_add] at hQa
    have hsneg : Real.sin (a - b) < 0 := by
      rw [show a - b = -(b - a) by ring, Real.sin_neg]
      exact neg_neg_of_pos hsin
    nlinarith
  have hdne : d ≠ 0 := by
    intro hd
    have hOQ : O = Q := by simpa [hd] using hdir
    have hOmem : O ∈ K := hOQ ▸ (edgeVertices_snd_mem K _).1
    have hOP := supportingIntersection_eq_edgeVertices_fst_of_mem K
      (sub_pos.mpr hab) (by linarith) hOmem
    exact hne (hOP.symm.trans hOQ)
  exact ⟨d, lt_of_le_of_ne hdnonneg (Ne.symm hdne), hdir⟩

/-! ### Faces at a reversed normal direction -/

/-- A body bounded below in a normal direction, with the bound attained, has the opposite
support value in the reversed direction. -/
theorem supportValue_add_pi_eq_neg_of_forall_le {L : ConvexBody Point} {c t : ℝ} {p : Point}
    (hle : ∀ q ∈ (L : Set Point), c ≤ inner ℝ q (normalVector (t : Real.Angle)))
    (hp : p ∈ (L : Set Point)) (hpc : inner ℝ p (normalVector (t : Real.Angle)) = c) :
    supportValue L ((t + Real.pi : ℝ) : Real.Angle) = -c :=
  le_antisymm (supportValue_le_of_cut L.nonempty rfl hle)
    (le_supportValue_of_cut L.isCompact rfl hp hpc)

/-- The face at a reversed normal direction consists of the points attaining the attained
lower bound. -/
theorem exposedEdge_add_pi_eq_of_forall_le {L : ConvexBody Point} {c t : ℝ} {p : Point}
    (hle : ∀ q ∈ (L : Set Point), c ≤ inner ℝ q (normalVector (t : Real.Angle)))
    (hp : p ∈ (L : Set Point)) (hpc : inner ℝ p (normalVector (t : Real.Angle)) = c) :
    exposedEdge L ((t + Real.pi : ℝ) : Real.Angle) =
      {q | q ∈ (L : Set Point) ∧ inner ℝ q (normalVector (t : Real.Angle)) = c} := by
  have hsup := supportValue_add_pi_eq_neg_of_forall_le hle hp hpc
  ext q
  constructor
  · intro hq
    have h2 : inner ℝ q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) =
      supportValue L ((t + Real.pi : ℝ) : Real.Angle) := hq.2
    rw [normalVector_add_pi, inner_neg_right, hsup] at h2
    exact ⟨hq.1, by linarith only [h2]⟩
  · rintro ⟨hqL, hqc⟩
    refine ⟨hqL, ?_⟩
    show inner ℝ q (normalVector ((t + Real.pi : ℝ) : Real.Angle)) = _
    rw [normalVector_add_pi, inner_neg_right, hsup, hqc]

/-! ### Faces between two supporting normals with a common contact point -/

/-- A point on two transverse supporting lines is their intersection. -/
theorem eq_supportingIntersection_of_mem_exposedEdge {L : ConvexBody Point} {a b : ℝ}
    {p : Point} (hsin : Real.sin (a - b) ≠ 0) (hpa : p ∈ exposedEdge L (a : Real.Angle))
    (hpb : p ∈ exposedEdge L (b : Real.Angle)) :
    p = supportingIntersection L (a : Real.Angle) (b : Real.Angle) := by
  have hsin' : Real.sin (b - a) ≠ 0 := by
    rw [show b - a = -(a - b) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsin
  refine eq_of_inner_normalVector_eq hsin ?_ ?_
  · rw [supportingIntersection_inner_left]
    exact hpa.2
  · rw [supportingIntersection_inner_right L a b hsin']
    exact hpb.2

/-- Between two supporting normals less than a straight angle apart with a common contact
point, every intervening face is that point. -/
theorem exposedEdge_eq_singleton_of_mem_exposedEdge_of_mem_Ioo {L : ConvexBody Point}
    {a b s : ℝ} {p : Point} (hba : b < a + Real.pi) (hs : s ∈ Set.Ioo a b)
    (hpa : p ∈ exposedEdge L (a : Real.Angle)) (hpb : p ∈ exposedEdge L (b : Real.Angle)) :
    exposedEdge L (s : Real.Angle) = {p} := by
  have hab : a < b := hs.1.trans hs.2
  have hsba : 0 < Real.sin (b - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hab]) (by linarith only [hba])
  have hsbs : 0 < Real.sin (b - s) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hs.2]) (by linarith only [hba, hs.1])
  have hssa : 0 < Real.sin (s - a) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith only [hs.1]) (by linarith only [hba, hs.2])
  -- the positive combination of the two endpoint normals
  have hcomb : ∀ q : Point, Real.sin (b - s) * inner ℝ q (normalVector (a : Real.Angle)) +
      Real.sin (s - a) * inner ℝ q (normalVector (b : Real.Angle)) =
      Real.sin (b - a) * inner ℝ q (normalVector (s : Real.Angle)) := by
    intro q
    rw [inner_normalVector_real, inner_normalVector_real, inner_normalVector_real,
      Real.sin_sub, Real.sin_sub, Real.sin_sub]
    ring
  have hqa : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (a : Real.Angle)) ≤
      inner ℝ p (normalVector (a : Real.Angle)) := by
    intro q hq
    rw [hpa.2]
    exact inner_le_supportValue L hq _
  have hqb : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (b : Real.Angle)) ≤
      inner ℝ p (normalVector (b : Real.Angle)) := by
    intro q hq
    rw [hpb.2]
    exact inner_le_supportValue L hq _
  have hps : ∀ q ∈ (L : Set Point), inner ℝ q (normalVector (s : Real.Angle)) ≤
      inner ℝ p (normalVector (s : Real.Angle)) := by
    intro q hq
    have h1 := mul_le_mul_of_nonneg_left (hqa q hq) hsbs.le
    have h2 := mul_le_mul_of_nonneg_left (hqb q hq) hssa.le
    have h := add_le_add h1 h2
    rw [hcomb q, hcomb p] at h
    exact le_of_mul_le_mul_left (by linarith only [h]) hsba
  have hpsval : inner ℝ p (normalVector (s : Real.Angle)) = supportValue L (s : Real.Angle) :=
    le_antisymm (inner_le_supportValue L hpa.1 _) (csSup_le (L.nonempty.image _)
      (by rintro _ ⟨q, hq, rfl⟩; exact hps q hq))
  ext q
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hq ↦ ?_, fun hq ↦ hq ▸ ⟨hpa.1, hpsval⟩⟩
  have hqs : inner ℝ q (normalVector (s : Real.Angle)) =
      inner ℝ p (normalVector (s : Real.Angle)) := by rw [hq.2, hpsval]
  have hsum : Real.sin (b - s) *
        (inner ℝ p (normalVector (a : Real.Angle)) - inner ℝ q (normalVector (a : Real.Angle))) +
      Real.sin (s - a) *
        (inner ℝ p (normalVector (b : Real.Angle)) - inner ℝ q (normalVector (b : Real.Angle)))
      = 0 := by
    have h1 := hcomb p
    have h2 := hcomb q
    rw [hqs] at h2
    linear_combination h1 - h2
  have hza : inner ℝ q (normalVector (a : Real.Angle)) =
      inner ℝ p (normalVector (a : Real.Angle)) := by
    nlinarith only [hsum, hsbs, hssa, hqa q hq.1, hqb q hq.1]
  have hzb : inner ℝ q (normalVector (b : Real.Angle)) =
      inner ℝ p (normalVector (b : Real.Angle)) := by
    nlinarith only [hsum, hsbs, hssa, hqa q hq.1, hqb q hq.1]
  have hsinab : Real.sin (a - b) ≠ 0 := by
    rw [show a - b = -(b - a) by ring, Real.sin_neg]
    exact neg_ne_zero.mpr hsba.ne'
  exact eq_of_inner_normalVector_eq hsinab hza hzb

end MovingSofa
