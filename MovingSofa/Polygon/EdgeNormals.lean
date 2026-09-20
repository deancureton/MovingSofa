import MovingSofa.Analysis.SurfaceMeasure.Polygon
import MovingSofa.Polygon.Balancing.Coefficients

/-!
# Edge normals and contact vertices of a finite half-plane intersection

A convex body presented as a finite intersection of closed half-planes has only finitely many
possible contact points and only finitely many possible proper edge normals. This file records
both facts in the form used by the discrete estimates on polygon caps:

* `exists_active_constraint_of_mem_notMem_interior`: a boundary point activates a constraint;
* `exists_active_constraint_of_forall_notMem_add_smul`: a direction that immediately leaves the
  body activates a constraint increasing along it;
* `properEdgeNormal_eq_constraint_or_add_pi`: a nondegenerate exposed edge has a constraint
  normal, up to half a turn;
* `properEdgeNormal_eq_constraint`: the same, without the antipodal alternative;
* `PolygonCapSpace.properEdgeNormal_mem_allowed_or_antipodal` and
  `PolygonCapSpace.properEdgeNormal_mem_allowed`: the polygon-cap versions;
* `finiteConstraintVertices`: the finite set of transversal constraint-line intersections, which
  contains every singleton exposed edge;
* `PolygonCapSpace.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero`: the surface measure of a
  polygon cap is carried by its proper edge normals.
-/

noncomputable section

namespace MovingSofa

/-- A point of a finite half-plane intersection off its interior lies on an active constraint. -/
theorem exists_active_constraint_of_mem_notMem_interior
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (S : Set Point)
    (hS : S = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {x : Point} (hxS : x ∈ S) (hxint : x ∉ interior S) :
    ∃ c ∈ C, inner ℝ x (normalVector c.1) = c.2 := by
  by_contra h
  push Not at h
  apply hxint
  rw [hS, hC.interior_biInter]
  simp only [Set.mem_iInter]
  intro c hc
  have hxc : inner ℝ x (normalVector c.1) < c.2 := by
    rw [hS] at hxS
    have hle := Set.mem_iInter.mp (Set.mem_iInter.mp hxS c) hc
    change inner ℝ x (normalVector c.1) ≤ c.2 at hle
    exact lt_of_le_of_ne hle (h c hc)
  have hUopen : IsOpen {p : Point | inner ℝ p (normalVector c.1) < c.2} :=
    isOpen_lt (by fun_prop) continuous_const
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hUopen.mem_nhds hxc)
  intro p hp
  change inner ℝ p (normalVector c.1) < c.2 at hp
  change inner ℝ p (normalVector c.1) ≤ c.2
  exact hp.le

/-- A nondegenerate exposed edge has the normal angle of one of the constraints, up to half a
turn. -/
theorem properEdgeNormal_eq_constraint_or_add_pi
    (K : ConvexBody Point) (C : Set (Real.Angle × ℝ)) (hC : C.Finite)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    (t : Real.Angle) (ht : (edgeVertices K t).1 ≠ (edgeVertices K t).2) :
    ∃ c ∈ C, t = c.1 ∨ t = c.1 + (Real.pi : Real.Angle) := by
  set p := (edgeVertices K t).1 with hpdef
  set q := (edgeVertices K t).2 with hqdef
  have hp : p ∈ exposedEdge K t := edgeVertices_fst_mem K t
  have hq : q ∈ exposedEdge K t := edgeVertices_snd_mem K t
  have hxedge : midpoint ℝ p q ∈ exposedEdge K t :=
    (convex_exposedEdge K t).segment_subset hp hq (midpoint_mem_segment p q)
  have hxfront : midpoint ℝ p q ∈ frontier (K : Set Point) := by
    rw [← frontier_inter_supportingLine_eq_exposedEdge K t] at hxedge
    exact hxedge.1
  obtain ⟨c, hcC, hcx⟩ := exists_active_constraint_of_mem_notMem_interior
    C hC (K : Set Point) hK hxedge.1 hxfront.2
  refine ⟨c, hcC, ?_⟩
  have hpc : inner ℝ p (normalVector c.1) ≤ c.2 := by
    have hpK : p ∈ (K : Set Point) := hp.1
    rw [hK] at hpK
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hpK c) hcC
  have hqc : inner ℝ q (normalVector c.1) ≤ c.2 := by
    have hqK : q ∈ (K : Set Point) := hq.1
    rw [hK] at hqK
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hqK c) hcC
  rw [midpoint_eq_smul_add, inner_smul_left, inner_add_left] at hcx
  norm_num at hcx
  have hpcEq : inner ℝ p (normalVector c.1) = c.2 := by linarith
  have hqcEq : inner ℝ q (normalVector c.1) = c.2 := by linarith
  have hvt : inner ℝ (p - q) (normalVector t) = 0 := by
    rw [inner_sub_left, hp.2, hq.2, sub_self]
  have hvc : inner ℝ (p - q) (normalVector c.1) = 0 := by
    rw [inner_sub_left, hpcEq, hqcEq, sub_self]
  exact normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr ht) hvt hvc

/-- If a direction immediately leaves a finite intersection of closed half-planes at a point of
it, some constraint is active there and increases along that direction. -/
theorem exists_active_constraint_of_forall_notMem_add_smul
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (S : Set Point)
    (hS : S = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {x w : Point} (hxS : x ∈ S) (hw : ∀ r : ℝ, 0 < r → x + r • w ∉ S) :
    ∃ c ∈ C, inner ℝ x (normalVector c.1) = c.2 ∧ 0 < inner ℝ w (normalVector c.1) := by
  by_contra hcon
  push Not at hcon
  have hmem : ∀ c ∈ C, inner ℝ x (normalVector c.1) ≤ c.2 := by
    intro c hc
    rw [hS] at hxS
    have hle := Set.mem_iInter.mp (Set.mem_iInter.mp hxS c) hc
    change inner ℝ x (normalVector c.1) ≤ c.2 at hle
    exact hle
  have hall : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ c ∈ C,
      inner ℝ (x + r • w) (normalVector c.1) ≤ c.2 := by
    refine hC.eventually_all.mpr ?_
    intro c hc
    by_cases hact : inner ℝ x (normalVector c.1) = c.2
    · have hwc : inner ℝ w (normalVector c.1) ≤ 0 := hcon c hc hact
      filter_upwards [self_mem_nhdsWithin] with r hr
      rw [inner_add_left, real_inner_smul_left, hact]
      have hrw : r * inner ℝ w (normalVector c.1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hr) hwc
      linarith
    · have hlt : inner ℝ x (normalVector c.1) < c.2 := lt_of_le_of_ne (hmem c hc) hact
      have hcont : Continuous fun r : ℝ ↦ inner ℝ (x + r • w) (normalVector c.1) := by
        fun_prop
      have h0 : inner ℝ (x + (0 : ℝ) • w) (normalVector c.1) < c.2 := by simpa using hlt
      have hev := (hcont.tendsto 0).eventually (gt_mem_nhds h0)
      exact (hev.filter_mono nhdsWithin_le_nhds).mono fun r hr ↦ hr.le
  obtain ⟨r, hrall, hrpos⟩ := (hall.and self_mem_nhdsWithin).exists
  refine hw r hrpos ?_
  rw [hS]
  refine Set.mem_iInter.2 fun c ↦ Set.mem_iInter.2 fun hc ↦ ?_
  change inner ℝ (x + r • w) (normalVector c.1) ≤ c.2
  exact hrall c hc

/-- The normal of a nondegenerate exposed edge of a finite intersection of closed half-planes is
itself a constraint normal. -/
theorem properEdgeNormal_eq_constraint (K : ConvexBody Point)
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    (t : Real.Angle) (ht : (edgeVertices K t).1 ≠ (edgeVertices K t).2) :
    ∃ c ∈ C, t = c.1 := by
  set p := (edgeVertices K t).1 with hpdef
  set q := (edgeVertices K t).2 with hqdef
  have hp : p ∈ exposedEdge K t := edgeVertices_fst_mem K t
  have hq : q ∈ exposedEdge K t := edgeVertices_snd_mem K t
  have hx : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q ∈ exposedEdge K t :=
    (convex_exposedEdge K t) hp hq (by norm_num) (by norm_num) (by norm_num)
  have hout : ∀ r : ℝ, 0 < r →
      (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q + r • normalVector t ∉ (K : Set Point) := by
    intro r hr hmemK
    have hle := inner_le_supportValue K hmemK t
    rw [inner_add_left, real_inner_smul_left, inner_normalVector_self_angle, mul_one,
      hx.2] at hle
    linarith
  obtain ⟨c, hcC, hact, hpos⟩ :=
    exists_active_constraint_of_forall_notMem_add_smul C hC _ hK hx.1 hout
  have hpc : inner ℝ p (normalVector c.1) ≤ c.2 := by
    have hpK : p ∈ (K : Set Point) := hp.1
    rw [hK] at hpK
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hpK c) hcC
    change inner ℝ p (normalVector c.1) ≤ c.2 at h
    exact h
  have hqc : inner ℝ q (normalVector c.1) ≤ c.2 := by
    have hqK : q ∈ (K : Set Point) := hq.1
    rw [hK] at hqK
    have h := Set.mem_iInter.mp (Set.mem_iInter.mp hqK c) hcC
    change inner ℝ q (normalVector c.1) ≤ c.2 at h
    exact h
  have hmid : inner ℝ ((1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q) (normalVector c.1) =
      (inner ℝ p (normalVector c.1) + inner ℝ q (normalVector c.1)) / 2 := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  rw [hmid] at hact
  have hpceq : inner ℝ p (normalVector c.1) = c.2 := by linarith
  have hqceq : inner ℝ q (normalVector c.1) = c.2 := by linarith
  have hvt : inner ℝ (p - q) (normalVector t) = 0 := by
    rw [inner_sub_left, hp.2, hq.2, sub_self]
  have hvc : inner ℝ (p - q) (normalVector c.1) = 0 := by
    rw [inner_sub_left, hpceq, hqceq, sub_self]
  rcases normalVector_eq_or_eq_add_pi_of_orthogonal (sub_ne_zero.mpr ht) hvt hvc with h | h
  · exact ⟨c, hcC, h⟩
  · exfalso
    rw [h, normalVector_add_pi_angle, inner_neg_left, inner_normalVector_self_angle] at hpos
    linarith

/-- The allowed normal set of a polygon cap is finite. -/
theorem finite_polygonCapNormals (Θ : AngleSet) :
    (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
      capLowerNormals Θ.angle).Finite := by
  have hdomain : (angleDomain Θ).Finite := by
    unfold angleDomain
    exact ((Θ.directions.finite_toSet.union
      (Θ.directions.finite_toSet.image (fun t ↦ t + Real.pi / 2))).union
        ((Set.finite_singleton (Real.pi / 2)).insert Θ.angle))
  exact (hdomain.image _).union ((Set.finite_singleton _).insert _)

/-- Every nondegenerate exposed edge of a polygon cap has an allowed or antipodal normal. -/
theorem PolygonCapSpace.properEdgeNormal_mem_allowed_or_antipodal
    {Θ : AngleSet} (K : PolygonCapSpace Θ) (t : Real.Angle)
    (ht : (edgeVertices K.val.val t).1 ≠ (edgeVertices K.val.val t).2) :
    t ∈ ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
        capLowerNormals Θ.angle ∪
      ((fun u : Real.Angle ↦ u + (Real.pi : Real.Angle)) ''
        (((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪
          capLowerNormals Θ.angle)) := by
  obtain ⟨C, hC, hCN, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  obtain ⟨c, hcC, htc | htc⟩ :=
    properEdgeNormal_eq_constraint_or_add_pi K.val.val C hC hKC t ht
  · exact Or.inl (htc ▸ hCN c hcC)
  · exact Or.inr ⟨c.1, hCN c hcC, htc.symm⟩

/-- Every proper edge normal of a polygon cap is an allowed normal. -/
theorem PolygonCapSpace.properEdgeNormal_mem_allowed {Θ : AngleSet}
    (K : PolygonCapSpace Θ) (t : Real.Angle)
    (ht : (edgeVertices K.val.val t).1 ≠ (edgeVertices K.val.val t).2) :
    t ∈ ((fun r : ℝ ↦ (r : Real.Angle)) '' angleDomain Θ) ∪ capLowerNormals Θ.angle := by
  obtain ⟨C, hC, hCN, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  obtain ⟨c, hcC, htc⟩ := properEdgeNormal_eq_constraint K.val.val C hC hKC t ht
  exact htc ▸ hCN c hcC

/-- The finitely many transversal intersection points of a finite constraint family. -/
def finiteConstraintVertices (C : Set (Real.Angle × ℝ)) : Set Point := by
  classical
  exact ⋃ c ∈ C, ⋃ d ∈ C,
    if c.1 = d.1 ∨ c.1 = d.1 + (Real.pi : Real.Angle) then ∅
    else normalLine c.1 c.2 ∩ normalLine d.1 d.2

/-- A finite constraint family has finitely many transversal intersection points. -/
theorem finite_finiteConstraintVertices (C : Set (Real.Angle × ℝ))
    (hC : C.Finite) : (finiteConstraintVertices C).Finite := by
  classical
  unfold finiteConstraintVertices
  refine hC.biUnion fun c _ ↦ hC.biUnion fun d _ ↦ ?_
  split_ifs with hparallel
  · exact Set.finite_empty
  · apply Set.Subsingleton.finite
    intro p hp q hq
    simp only [Set.mem_inter_iff, normalLine, Set.mem_ofPred_eq] at hp hq
    by_contra hpq
    have hcorth : inner ℝ (p - q) (normalVector c.1) = 0 := by
      rw [inner_sub_left, hp.1, hq.1, sub_self]
    have hdorth : inner ℝ (p - q) (normalVector d.1) = 0 := by
      rw [inner_sub_left, hp.2, hq.2, sub_self]
    exact hparallel (normalVector_eq_or_eq_add_pi_of_orthogonal
      (sub_ne_zero.mpr hpq) hcorth hdorth)

/-- A singleton exposed edge of a finite half-plane intersection is a constraint vertex. -/
theorem singleton_exposedEdge_mem_finiteConstraintVertices
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (K : ConvexBody Point)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false)
    {t : Real.Angle} {p : Point} (hp : exposedEdge K t = {p}) :
    p ∈ finiteConstraintVertices C := by
  classical
  have hpedge : p ∈ exposedEdge K t := by rw [hp]; exact Set.mem_singleton p
  have hpfront : p ∈ frontier (K : Set Point) := by
    rw [← frontier_inter_supportingLine_eq_exposedEdge K t] at hpedge
    exact hpedge.1
  obtain ⟨c, hc, hpc⟩ := exists_active_constraint_of_mem_notMem_interior
    C hC (K : Set Point) hK hpedge.1 hpfront.2
  by_contra hnot
  have hparallel (d : Real.Angle × ℝ) (hd : d ∈ C)
      (hpd : inner ℝ p (normalVector d.1) = d.2) :
      c.1 = d.1 ∨ c.1 = d.1 + (Real.pi : Real.Angle) := by
    by_contra hnon
    apply hnot
    unfold finiteConstraintVertices
    exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, Set.mem_iUnion.2 ⟨d,
      Set.mem_iUnion.2 ⟨hd, by simp only [hnon, ↓reduceIte]; exact ⟨hpc, hpd⟩⟩⟩⟩⟩
  have horth : inner ℝ (tangentVector c.1) (normalVector c.1) = 0 := by
    induction c.1 using Real.Angle.induction_on with
    | _ r => rw [real_inner_comm, inner_normalVector_tangentVector]
  have hvne : tangentVector c.1 ≠ 0 := by
    have hvself : inner ℝ (tangentVector c.1) (tangentVector c.1) = 1 := by
      induction c.1 using Real.Angle.induction_on with
      | _ r => exact inner_tangentVector_self r
    intro hv
    simp [hv] at hvself
  have hevent : ∀ᶠ r : ℝ in nhds 0, p + r • tangentVector c.1 ∈ (K : Set Point) := by
    have hall : ∀ᶠ r : ℝ in nhds 0, ∀ d ∈ C,
        inner ℝ (p + r • tangentVector c.1) (normalVector d.1) ≤ d.2 := by
      apply hC.eventually_all.mpr
      intro d hd
      by_cases hpd : inner ℝ p (normalVector d.1) = d.2
      · have hvd : inner ℝ (tangentVector c.1) (normalVector d.1) = 0 := by
          rcases hparallel d hd hpd with heq | heq
          · rwa [← heq]
          · have hnn : normalVector d.1 = -normalVector c.1 := by
              rw [heq, normalVector_add_pi_angle, neg_neg]
            rw [hnn, inner_neg_right, horth, neg_zero]
        exact Filter.Eventually.of_forall fun r ↦ by
          rw [inner_add_left, real_inner_smul_left, hvd, mul_zero, add_zero, hpd]
      · have hple : inner ℝ p (normalVector d.1) ≤ d.2 := by
          have hm := hpedge.1
          rw [hK] at hm
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hm d) hd
        have hlt : inner ℝ p (normalVector d.1) < d.2 := lt_of_le_of_ne hple hpd
        have hcont : Continuous
            (fun r : ℝ ↦ inner ℝ (p + r • tangentVector c.1) (normalVector d.1)) := by
          fun_prop
        have hzero : inner ℝ (p + (0 : ℝ) • tangentVector c.1) (normalVector d.1) < d.2 := by
          simpa using hlt
        filter_upwards [(hcont.tendsto 0).eventually (gt_mem_nhds hzero)] with r hr
        exact hr.le
    filter_upwards [hall] with r hr
    rw [hK]
    exact Set.mem_iInter.2 fun d ↦ Set.mem_iInter.2 fun hd ↦ hr d hd
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hevent
  have hplus : p + (ε / 2) • tangentVector c.1 ∈ (K : Set Point) := hball (by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hminus : p + (-(ε / 2)) • tangentVector c.1 ∈ (K : Set Point) := hball (by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_neg]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith)
  have hplusle := inner_le_supportValue K hplus t
  have hminusle := inner_le_supportValue K hminus t
  rw [inner_add_left, real_inner_smul_left, hpedge.2] at hplusle hminusle
  have hvt : inner ℝ (tangentVector c.1) (normalVector t) = 0 := by nlinarith
  have hplusface : p + (ε / 2) • tangentVector c.1 ∈ exposedEdge K t := by
    refine ⟨hplus, ?_⟩
    change inner ℝ (p + (ε / 2) • tangentVector c.1) (normalVector t) = supportValue K t
    rw [inner_add_left, real_inner_smul_left, hvt, mul_zero, add_zero, hpedge.2]
  rw [hp, Set.mem_singleton_iff] at hplusface
  have hzero : (ε / 2) • tangentVector c.1 = 0 :=
    add_left_cancel (show p + (ε / 2) • tangentVector c.1 = p + 0 by simpa using hplusface)
  exact hvne ((smul_eq_zero.mp hzero).resolve_left (ne_of_gt (by positivity)))

/-- The transversal constraint vertices form a one-dimensional null set. -/
theorem finiteConstraintVertices_measure_zero (C : Set (Real.Angle × ℝ))
    (hC : C.Finite) :
    MeasureTheory.Measure.hausdorffMeasure 1 (finiteConstraintVertices C) = 0 := by
  let _ := MeasureTheory.Measure.nullSingletonClass_hausdorff Point (by norm_num : (0 : ℝ) < 1)
  exact (finite_finiteConstraintVertices C hC).measure_zero _

/-- Surface measure of a finite intersection of closed half-planes is carried by its proper
edge normals. -/
theorem surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_constraints
    (C : Set (Real.Angle × ℝ)) (hC : C.Finite) (K : ConvexBody Point)
    (hK : (K : Set Point) = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false) :
    surfaceAreaMeasure K {t | (edgeVertices K t).1 = (edgeVertices K t).2} = 0 := by
  have hN : {t | (edgeVertices K t).1 ≠ (edgeVertices K t).2}.Finite := by
    apply (hC.image Prod.fst).subset
    intro t ht
    obtain ⟨c, hc, heq⟩ := properEdgeNormal_eq_constraint K C hC hK t ht
    exact ⟨c, hc, heq.symm⟩
  apply surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_carrier
    K hN (finiteConstraintVertices C) (finiteConstraintVertices_measure_zero C hC)
  intro p hp
  obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
  have hsingle : exposedEdge K t = {(edgeVertices K t).1} := by
    rw [exposedEdge_eq_segment_edgeVertices, ht, segment_same]
  have hpeq : p = (edgeVertices K t).1 := by simpa [hsingle] using hp
  exact hpeq ▸ singleton_exposedEdge_mem_finiteConstraintVertices C hC K hK hsingle

/-- Surface measure of a polygon cap is carried by its proper edge normals. -/
theorem PolygonCapSpace.surfaceAreaMeasure_compl_properEdgeNormals_eq_zero
    {Θ : AngleSet} (K : PolygonCapSpace Θ) :
    surfaceAreaMeasure K.val.val
      {t | (edgeVertices K.val.val t).1 = (edgeVertices K.val.val t).2} = 0 := by
  obtain ⟨C, hC, _, hKC⟩ := K.property.finite_constraints (finite_polygonCapNormals Θ)
  exact surfaceAreaMeasure_compl_properEdgeNormals_eq_zero_of_finite_constraints
    C hC K.val.val hKC

end MovingSofa
