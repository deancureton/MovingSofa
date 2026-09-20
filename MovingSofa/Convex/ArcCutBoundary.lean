import MovingSofa.Analysis.SurfaceMeasure.ExposedFrontier
import MovingSofa.Convex.CurveCut
import MovingSofa.Analysis.SurfaceMeasure.SegmentFaces
import MovingSofa.ForMathlib.Convex.Body.Segment
import MovingSofa.Geometry.RadialBoundary
import MovingSofa.Curve.Jordan.Subarc
import TauCeti.Topology.JordanCurve.Path

noncomputable section

namespace MovingSofa

open Set

private theorem normalVector_injective_cut : Function.Injective normalVector := by
  intro a b hab
  induction a using Real.Angle.induction_on with
  | _ a =>
    induction b using Real.Angle.induction_on with
    | _ b =>
      apply Real.Angle.cos_sin_inj
      · exact congrFun (congrArg WithLp.ofLp hab) 0
      · exact congrFun (congrArg WithLp.ofLp hab) 1

-- Duplicate of the current private UpperGraph helper; promote with the separation helper.
private theorem exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut
    (K : ConvexBody Point) (hK : (interior (K : Set Point)).Nonempty)
    {p v : Point} (hv : v ≠ 0) {a b : Real.Angle}
    (ha : IsExteriorNormal K p a) (hb : IsExteriorNormal K p b)
    (hva : inner ℝ v (normalVector a) = 0)
    (hvb : inner ℝ v (normalVector b) = 0) : a = b := by
  let orientation : Orientation ℝ Point (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases EuclideanGeometry.eq_or_eq_neg_of_unit_orthogonal orientation hv
      (norm_normalVector a) (norm_normalVector b) hva hvb with hab | hab
  · exact normalVector_injective_cut hab
  · exfalso
    obtain ⟨z, hz⟩ := hK
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    let q := z + (ε / 2) • normalVector a
    have hq : q ∈ K := interior_subset (hball (by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [show q - z = (ε / 2) • normalVector a by simp [q], norm_smul,
        norm_normalVector, Real.norm_eq_abs, abs_of_pos (div_pos hε (by norm_num))]
      norm_num
      linarith))
    have haz := ha z (interior_subset hz)
    have hbz := hb z (interior_subset hz)
    have hba : normalVector b = -normalVector a := by rw [hab]; simp
    rw [hba, inner_neg_right] at hbz
    have heq : inner ℝ (z - p) (normalVector a) = 0 := by linarith
    have haq := ha q hq
    have hqp : q - p = (z - p) + (ε / 2) • normalVector a := by
      dsimp only [q]
      module
    rw [hqp, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
      norm_normalVector a, heq, zero_add] at haq
    have : ε / 2 ≤ 0 := by simpa using haq
    linarith

private theorem isExteriorNormal_of_mem_exposedEdge
    (K : ConvexBody Point) {p : Point} {a : Real.Angle}
    (hp : p ∈ exposedEdge K a) : IsExteriorNormal K p a := by
  intro q hq
  have hqle := inner_le_supportValue K hq a
  have hpEq := hp.2
  change inner ℝ p (normalVector a) = supportValue K a at hpEq
  rw [inner_sub_left, hpEq]
  linarith

/-- The frontier of a cut body is the retained convex boundary arc together with its chord. -/
theorem frontier_eq_convexBoundaryArc_union_segment_of_cut
    (K K' : ConvexBody Point) (a b t : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    frontier (K' : Set Point) = convexBoundaryArc K a b ∪ segment ℝ P Q := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨u, hxu⟩ := exists_mem_exposedEdge_of_mem_frontier K' hInt hx
    let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
    let s := AddCircle.equivIoc (2 * Real.pi) (t - Real.pi) u
    have hs : (s : ℝ) ∈ Set.Ioc (t - Real.pi) (t + Real.pi) := by
      have := s.property
      convert this using 1
      ring_nf
    have hsu : (((s : ℝ) : Real.Angle)) = u := AddCircle.coe_equivIoc
    have hxs : x ∈ exposedEdge K' (s : ℝ) := by simpa [hsu] using hxu
    rcases le_or_gt (s : ℝ) a with hsa | has
    · left
      left
      left
      have hface := hleft (s : ℝ) ⟨hs.1, hsa⟩
      rw [hface] at hxs
      simpa [hP] using hxs
    · rcases lt_or_ge (s : ℝ) b with hsb | hbs
      · left
        left
        right
        refine Set.mem_iUnion_of_mem (s : ℝ) ?_
        refine Set.mem_iUnion_of_mem ⟨has, hsb⟩ ?_
        · rw [← hmiddle (s : ℝ) ⟨has, hsb⟩]
          exact hxs
      · rcases lt_or_eq_of_le hs.2 with hst | hst
        · left
          right
          have hface := hright (s : ℝ) ⟨hbs, hst⟩
          rw [hface] at hxs
          simpa [hQ] using hxs
        · right
          rw [hst] at hxs
          change x ∈ exposedEdge K'
            ((t : Real.Angle) + (Real.pi : Real.Angle)) at hxs
          rw [hterminal] at hxs
          simpa [segment_symm] using hxs
  · rintro x (hx | hx)
    · rcases hx with hx | hx
      · rcases hx with hx | hx
        · have hPa : P ∈ exposedEdge K' (a : ℝ) := by
            rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
            simp
          have hxP : x = P := by simpa [hP] using hx
          rw [hxP]
          exact exposedEdge_subset_frontier K'
            (a : Real.Angle) hPa
        · rcases Set.mem_iUnion.mp hx with ⟨s, hx⟩
          rcases Set.mem_iUnion.mp hx with ⟨hs, hx⟩
          rw [← hmiddle s hs] at hx
          exact exposedEdge_subset_frontier K' (s : Real.Angle) hx
      · have hQb : Q ∈ exposedEdge K' (b : ℝ) := by
          rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
          simp
        have hxQ : x = Q := by simpa [hQ] using hx
        rw [hxQ]
        exact exposedEdge_subset_frontier K'
          (b : Real.Angle) hQb
    · rw [segment_symm, ← hterminal] at hx
      exact exposedEdge_subset_frontier K'
        ((t + Real.pi : ℝ) : Real.Angle) hx

/-- A retained convex boundary arc meets its cutting chord only at the endpoints. -/
theorem convexBoundaryArc_inter_segment_eq_endpoints_of_cut
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    convexBoundaryArc K a b ∩ segment ℝ P Q = {P, Q} := by
  have hPa : P ∈ exposedEdge K' (a : ℝ) := by
    rw [hleft a ⟨by linarith [Real.pi_pos], le_rfl⟩]
    simp
  have hQb : Q ∈ exposedEdge K' (b : ℝ) := by
    rw [hright b ⟨le_rfl, by linarith [Real.pi_pos]⟩]
    simp
  have hPterm : P ∈ exposedEdge K' (t + Real.pi) := by
    rw [hterminal]
    exact right_mem_segment ℝ Q P
  have hQterm : Q ∈ exposedEdge K' (t + Real.pi) := by
    rw [hterminal]
    exact left_mem_segment ℝ Q P
  apply Set.Subset.antisymm
  · rintro x ⟨hxarc, hxseg⟩
    rcases hxarc with hxarc | hxQ
    · rcases hxarc with hxP | hxmid
      · left
        simpa [hP] using hxP
      · rcases Set.mem_iUnion.mp hxmid with ⟨s, hxmid⟩
        rcases Set.mem_iUnion.mp hxmid with ⟨hs, hxsK⟩
        have hxs : x ∈ exposedEdge K' (s : ℝ) := by
          rw [hmiddle s hs]
          exact hxsK
        rw [segment_eq_image] at hxseg
        obtain ⟨r, hr, hxr⟩ := hxseg
        by_cases hr0 : r = 0
        · left
          subst r
          simpa using hxr.symm
        by_cases hr1 : r = 1
        · right
          subst r
          simpa using hxr.symm
        have hrpos : 0 < r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
        have hrlt : r < 1 := lt_of_le_of_ne hr.2 hr1
        have hPK : P ∈ K' := hPa.1
        have hQK : Q ∈ K' := hQb.1
        have hPLe := inner_le_supportValue K' hPK (s : Real.Angle)
        have hQLe := inner_le_supportValue K' hQK (s : Real.Angle)
        have hxEq := hxs.2
        change inner ℝ x (normalVector (s : Real.Angle)) =
          supportValue K' (s : Real.Angle) at hxEq
        rw [← hxr, inner_add_left, inner_smul_left, inner_smul_left] at hxEq
        simp only [map_sub, map_one, RCLike.conj_to_real] at hxEq
        have hPEq : inner ℝ P (normalVector (s : Real.Angle)) =
            supportValue K' (s : Real.Angle) := by
          nlinarith
        have hQEq : inner ℝ Q (normalVector (s : Real.Angle)) =
            supportValue K' (s : Real.Angle) := by
          nlinarith
        have hPs : P ∈ exposedEdge K' (s : ℝ) := ⟨hPK, hPEq⟩
        have hQs : Q ∈ exposedEdge K' (s : ℝ) := ⟨hQK, hQEq⟩
        have hos : inner ℝ (Q - P) (normalVector (s : Real.Angle)) = 0 := by
          rw [inner_sub_left, hPEq, hQEq]
          ring
        have hot : inner ℝ (Q - P) (normalVector (t + Real.pi : Real.Angle)) = 0 := by
          change inner ℝ (Q - P)
            (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = 0
          rw [normalVector_add_pi, inner_neg_right, inner_sub_left, hPt, hQt]
          ring
        have hQP : Q - P ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
        have hang : (s : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) :=
          exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut K' hInt hQP
            (isExteriorNormal_of_mem_exposedEdge K' hPs)
            (isExteriorNormal_of_mem_exposedEdge K' hPterm) hos hot
        have hnv := congrArg normalVector hang
        have hcos : Real.cos (s - (t + Real.pi)) = 1 := by
          rw [← inner_normalVector_normalVector s (t + Real.pi), hnv,
            inner_normalVector_self]
        have htupper : t < a + Real.pi := lt_trans htb hba
        have hlower : -(2 * Real.pi) < s - (t + Real.pi) := by
          nlinarith [hs.1, htupper]
        have hupper : s - (t + Real.pi) < 2 * Real.pi := by
          nlinarith [hs.2, hat, Real.pi_pos]
        have := (Real.cos_eq_one_iff_of_lt_of_lt hlower hupper).mp hcos
        have hbtpi : b < t + Real.pi := by nlinarith [hba, hat]
        linarith [hs.2, hbtpi]
    · right
      simpa [hQ] using hxQ
  · intro x hx
    rcases hx with hx | hx
    · subst x
      constructor
      · left
        left
        simp [hP]
      · exact left_mem_segment ℝ P Q
    · subst x
      constructor
      · right
        simp [hQ]
      · exact right_mem_segment ℝ P Q

/-- A convex body admits a counterclockwise BV frontier parametrization based off a fixed face. -/
theorem exists_closedBVJordan_frontier_base_not_mem_chord
    (K : ConvexBody Point) (t : ℝ) (P Q : Point)
    (hInt : (interior (K : Set Point)).Nonempty)
    (hterminal : exposedEdge K (t + Real.pi) = segment ℝ Q P) :
    ∃ (a b : ℝ) (x : ContinuousBVPaths a b),
      ∃ hab : a < b, IsOrientedJordanParametrization hab.le (frontier (K : Set Point))
        true x.val ∧ x.val ⟨a, le_rfl, hab.le⟩ ∉ segment ℝ P Q := by
  obtain ⟨R, hRt⟩ := exposedEdge_nonempty K (t : Real.Angle)
  have hRnot : R ∉ segment ℝ P Q := by
    intro hRseg
    have hRopp : R ∈ exposedEdge K (t + Real.pi) := by
      rw [hterminal]
      simpa [segment_symm] using hRseg
    have hv : tangentVector (t : Real.Angle) ≠ 0 := by
      intro hzero
      have := inner_tangentVector_self t
      rw [hzero, inner_zero_left] at this
      norm_num at this
    have hot : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t : Real.Angle)) = 0 := by
      rw [real_inner_comm]
      exact inner_normalVector_tangentVector t
    have hopp : inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (t + Real.pi : Real.Angle)) = 0 := by
      change inner ℝ (tangentVector (t : Real.Angle))
        (normalVector (((t + Real.pi : ℝ) : Real.Angle))) = 0
      rw [normalVector_add_pi, inner_neg_right, hot, neg_zero]
    have hang : (t : Real.Angle) = ((t + Real.pi : ℝ) : Real.Angle) :=
      exteriorNormal_eq_of_orthogonal_of_interior_nonempty_cut K hInt hv
        (isExteriorNormal_of_mem_exposedEdge K hRt)
        (isExteriorNormal_of_mem_exposedEdge K hRopp) hot hopp
    have hnv := congrArg normalVector hang
    change normalVector (t : Real.Angle) =
      normalVector (((t + Real.pi : ℝ) : Real.Angle)) at hnv
    rw [normalVector_add_pi] at hnv
    have hz : normalVector (t : Real.Angle) = 0 := by
      ext i
      have hi := congrFun (congrArg WithLp.ofLp hnv) i
      simp only [PiLp.neg_apply] at hi
      have : (normalVector (t : Real.Angle)) i = 0 := by linarith
      exact this
    have := norm_normalVector (t : Real.Angle)
    rw [hz, norm_zero] at this
    norm_num at this
  obtain ⟨o, ho⟩ := hInt
  obtain ⟨ρ, e, C, γ, hradial, he, hLip, hγ, hγJordan, hinterior⟩ :=
    convexBody_radial_boundary K o ho
  have hRrange : R ∈ Set.range γ.val := by
    rw [hγJordan.2.2.2.1]
    exact exposedEdge_subset_frontier K (t : Real.Angle) hRt
  obtain ⟨s, hstop, hsR⟩ := exists_param_lt_top_of_mem_range (by positivity) γ.val
    hγJordan.2.2.2.2.1 hRrange
  by_cases hs0 : (s : ℝ) = 0
  · refine ⟨0, 2 * Real.pi, γ, mul_pos (by norm_num) Real.pi_pos, hγJordan, ?_⟩
    have hs : s = ⟨0, le_rfl, (mul_pos (by norm_num) Real.pi_pos).le⟩ :=
      Subtype.ext hs0
    rw [← hsR, hs] at hRnot
    exact hRnot
  · have hspos : 0 < (s : ℝ) := lt_of_le_of_ne s.property.1 (Ne.symm hs0)
    obtain ⟨r, hrJordan, hr⟩ :=
      exists_oriented_cyclic_rotation_eq_concat (by positivity) γ hγJordan s hspos hstop
    refine ⟨0, 2, r, by norm_num, hrJordan, ?_⟩
    simpa [hr, Function.concatUnitIntervals, hsR] using hRnot

end MovingSofa

noncomputable section

namespace MovingSofa

/-- The nonterminal boundary of a convex cut body realizes the corresponding convex boundary arc. -/
theorem exists_rectifiableOrientedArc_convexBoundaryArc_of_cut
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hterminal : exposedEdge K' (t + Real.pi) = segment ℝ Q P)
    (hInt : (interior (K' : Set Point)).Nonempty) :
    ∃ A : RectifiableOrientedArc,
      A.val.carrier = convexBoundaryArc K a b ∧
        A.val.startPoint = P ∧ A.val.endPoint = Q := by
  have hfrontier := frontier_eq_convexBoundaryArc_union_segment_of_cut
    K K' a b t P Q hat htb hba hP hQ hleft hmiddle hright hterminal hInt
  have hinter := convexBoundaryArc_inter_segment_eq_endpoints_of_cut
    K K' a b t c P Q hat htb hba hPQ hPt hQt hP hQ hleft hmiddle hright
      hterminal hInt
  obtain ⟨α, β, x, hαβ, hx, hbase⟩ :=
    exists_closedBVJordan_frontier_base_not_mem_chord K' t P Q hInt hterminal
  exact exists_rectifiableOrientedArc_of_closedJordan_cut hαβ hx P Q hPQ hbase
    hfrontier hinter

private theorem isExposed_exposedEdge_jordan (K : ConvexBody Point) (t : Real.Angle) :
    IsExposed ℝ (K : Set Point) (exposedEdge K t) := by
  intro _
  refine ⟨innerSL ℝ (normalVector t), ?_⟩
  ext p
  simp only [Set.mem_ofPred_eq, innerSL_apply_apply, real_inner_comm]
  constructor
  · intro hp
    refine ⟨hp.1, fun q hq ↦ ?_⟩
    rw [hp.2]
    exact inner_le_supportValue K hq t
  · rintro ⟨hp, hmax⟩
    refine ⟨hp, le_antisymm (inner_le_supportValue K hp t) ?_⟩
    apply csSup_le (K.nonempty.image _)
    rintro _ ⟨q, hq, rfl⟩
    exact hmax q hq

/-- A singleton exposed face of a segment is one of its endpoints. -/
theorem endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    (K : ConvexBody Point) (x y P : Point) (s : Real.Angle)
    (hK : (K : Set Point) = segment ℝ x y)
    (hface : exposedEdge K s = {P}) : x = P ∨ y = P := by
  have hPextreme : P ∈ Set.extremePoints ℝ (K : Set Point) := by
    have hexposed : IsExposed ℝ (K : Set Point) {P} := by
      rw [← hface]
      exact isExposed_exposedEdge_jordan K s
    exact hexposed.isExtreme.mem_extremePoints
  rw [mem_extremePoints_iff_forall_segment] at hPextreme
  have hxK : x ∈ (K : Set Point) := by rw [hK]; exact left_mem_segment ℝ x y
  have hyK : y ∈ (K : Set Point) := by rw [hK]; exact right_mem_segment ℝ x y
  have hPseg : P ∈ segment ℝ x y := by rw [← hK]; exact hPextreme.1
  exact hPextreme.2 x hxK y hyK hPseg

/-- A cut body with empty interior has its selected boundary arc equal to the endpoint segment. -/
theorem convexBoundaryArc_eq_segment_of_cut_interior_empty
    (K K' : ConvexBody Point) (a b t c : ℝ) (P Q : Point)
    (hat : a < t) (htb : t < b) (hba : b < a + Real.pi)
    (hPQ : P ≠ Q)
    (hPt : inner ℝ P (normalVector (t : Real.Angle)) = c)
    (hQt : inner ℝ Q (normalVector (t : Real.Angle)) = c)
    (hP : P = (edgeVertices K (a : Real.Angle)).1)
    (hQ : Q = (edgeVertices K (b : Real.Angle)).2)
    (hleft : ∀ s ∈ Set.Ioc (t - Real.pi) a, exposedEdge K' s = {P})
    (hmiddle : ∀ s ∈ Set.Ioo a b, exposedEdge K' s = exposedEdge K s)
    (hright : ∀ s ∈ Set.Ico b (t + Real.pi), exposedEdge K' s = {Q})
    (hInt : interior (K' : Set Point) = ∅) :
    convexBoundaryArc K a b = segment ℝ P Q := by
  have hPmem : P ∈ (K' : Set Point) := by
    have ha : a ∈ Set.Ioc (t - Real.pi) a := ⟨by linarith, le_rfl⟩
    have : P ∈ exposedEdge K' (a : Real.Angle) := by rw [hleft a ha]; simp
    exact this.1
  have hQmem : Q ∈ (K' : Set Point) := by
    have hb : b ∈ Set.Ico b (t + Real.pi) := ⟨le_rfl, by linarith⟩
    have : Q ∈ exposedEdge K' (b : Real.Angle) := by rw [hright b hb]; simp
    exact this.1
  have hnsub : ¬(K' : Set Point).Subsingleton := by
    intro hs
    exact hPQ (hs hPmem hQmem)
  obtain ⟨x, y, hxy, hK'⟩ := K'.exists_eq_segment_of_interior_empty hnsub hInt
  have hxP : x = P ∨ y = P := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y P (a : Real.Angle) hK' (hleft a ⟨by linarith, le_rfl⟩)
  have hxQ : x = Q ∨ y = Q := endpoint_of_exposedEdge_eq_singleton_of_eq_segment
    K' x y Q (b : Real.Angle) hK' (hright b ⟨le_rfl, by linarith⟩)
  have hK'PQ : (K' : Set Point) = segment ℝ P Q := by
    rcases hxP with rfl | rfl <;> rcases hxQ with hxQ | hxQ
    · exact (hPQ hxQ).elim
    · simpa [hxQ] using hK'
    · simpa [hxQ, segment_symm ℝ] using hK'
    · exact (hPQ hxQ).elim
  have horth : inner ℝ (Q - P) (normalVector (t : Real.Angle)) = 0 := by
    rw [inner_sub_left, hQt, hPt, sub_self]
  let d : Point × Point × Real.Angle := (P, Q, (t : Real.Angle))
  have hd : IsSegmentPresentation K' d := ⟨hPQ, hK'PQ, horth⟩
  have hface : exposedEdge K (t : Real.Angle) = (K' : Set Point) := by
    rw [← hmiddle t ⟨hat, htb⟩]
    exact exposedEdge_eq_segment_of_orthogonal K' d hd (t : Real.Angle) horth
  apply Set.Subset.antisymm
  · rw [convexBoundaryArc]
    refine Set.union_subset (Set.union_subset (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hP]
      exact left_mem_segment ℝ _ _) ?_) (by
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      rw [hQ]
      exact right_mem_segment ℝ _ _)
    refine Set.iUnion₂_subset fun s hs z hz ↦ ?_
    rw [← hK'PQ]
    have hz' : z ∈ exposedEdge K' (s : Real.Angle) := by
      rw [hmiddle s hs]
      exact hz
    exact hz'.1
  · intro z hz
    have hzK' : z ∈ (K' : Set Point) := by rw [hK'PQ]; exact hz
    have hzface : z ∈ exposedEdge K (t : Real.Angle) := by rw [hface]; exact hzK'
    rw [convexBoundaryArc]
    apply Set.mem_union_left
    apply Set.mem_union_right
    apply Set.mem_iUnion.mpr
    refine ⟨t, Set.mem_iUnion.mpr ⟨⟨hat, htb⟩, hzface⟩⟩


end MovingSofa
