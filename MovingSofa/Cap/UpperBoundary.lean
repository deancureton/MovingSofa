import MovingSofa.Cap.HalfPlanes
import MovingSofa.ForMathlib.Topology.Order.Compact
import MovingSofa.Cap.Contacts
import MovingSofa.Motion.Basic
import MovingSofa.Convex.Limits
import Mathlib.Topology.Connected.Clopen

noncomputable section

namespace MovingSofa

def capUpperBoundary {ω : ℝ} (K : CapSpace ω) : Set Point :=
  ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2), exposedEdge K.val (t : Real.Angle)

theorem capUpperBoundary_connected {ω : ℝ} (K : CapSpace ω) :
    IsConnected (capUpperBoundary K) := by
  let I : Set ℝ := Set.Icc 0 (ω + Real.pi / 2)
  let G : Set (I × Point) :=
    {q | q.2 ∈ exposedEdge K.val ((q.1 : ℝ) : Real.Angle)}
  have hω : 0 ≤ ω + Real.pi / 2 := by
    have := K.property.1
    positivity
  have hI : IsConnected I := isConnected_Icc hω
  let _ : ConnectedSpace I := Subtype.connectedSpace hI
  have hnormal : Continuous (fun q : I × Point ↦
      normalVector (((q.1 : I) : ℝ) : Real.Angle)) :=
    continuous_normalVector_real.comp (continuous_subtype_val.comp continuous_fst)
  have hsupport : Continuous (fun q : I × Point ↦
      supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)) :=
    (continuous_supportValue_real K.val).comp (continuous_subtype_val.comp continuous_fst)
  have heq : IsClosed {q : I × Point |
      inner ℝ q.2 (normalVector (((q.1 : I) : ℝ) : Real.Angle)) =
        supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)} :=
    isClosed_eq (continuous_snd.inner hnormal) hsupport
  have hG : IsCompact G := by
    rw [show G = Set.univ ×ˢ (K.val : Set Point) ∩
        {q : I × Point | inner ℝ q.2 (normalVector (((q.1 : I) : ℝ) : Real.Angle)) =
          supportValue K.val (((q.1 : I) : ℝ) : Real.Angle)} by
      ext q
      simp only [G, exposedEdge, supportingLineHalfPlane, normalLine, Set.mem_ofPred_eq,
        Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, true_and]]
    exact (isCompact_univ.prod K.val.isCompact).inter_right heq
  let _ : CompactSpace G := isCompact_iff_compactSpace.mp hG
  let π : G → I := fun q ↦ q.1.1
  have hπcont : Continuous π := continuous_fst.comp continuous_subtype_val
  have hπsurj : Function.Surjective π := by
    intro t
    obtain ⟨x, hx⟩ := exposedEdge_nonempty K.val ((t : ℝ) : Real.Angle)
    exact ⟨⟨(t, x), hx⟩, rfl⟩
  have hπquot : Topology.IsQuotientMap π :=
    Topology.IsQuotientMap.of_surjective_continuous hπsurj hπcont
  have hfiber (t : I) : IsConnected (π ⁻¹' {t}) := by
    let E := exposedEdge K.val ((t : ℝ) : Real.Angle)
    let e : E → G := fun x ↦ ⟨(t, x), x.property⟩
    have hecont : Continuous e := by
      apply Continuous.subtype_mk
      exact continuous_const.prodMk continuous_subtype_val
    have himage : e '' Set.univ = π ⁻¹' {t} := by
      ext q
      constructor
      · rintro ⟨x, -, rfl⟩
        simp [π, e]
      · intro hq
        have hqt : q.1.1 = t := by simpa [π] using hq
        have hqx : q.1.2 ∈ exposedEdge K.val ((t : ℝ) : Real.Angle) := by
          have hqG := q.property
          change q.1.2 ∈ exposedEdge K.val (((q.1.1 : I) : ℝ) : Real.Angle) at hqG
          simpa [hqt] using hqG
        let x : E := ⟨q.1.2, hqx⟩
        refine ⟨x, Set.mem_univ x, ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · exact hqt.symm
        · rfl
    rw [← himage]
    let _ : ConnectedSpace E :=
      Subtype.connectedSpace (isConnected_exposedEdge K.val ((t : ℝ) : Real.Angle))
    exact isConnected_univ.image e hecont.continuousOn
  have hGconn : IsConnected (Set.univ : Set G) := by
    exact hπquot.isCoinducing.isConnected_preimage_of_isClosed hfiber isClosed_univ
      isConnected_univ
  have himage : (fun q : G ↦ q.1.2) '' Set.univ = capUpperBoundary K := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, capUpperBoundary, Set.mem_iUnion]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1.1, q.1.1.property, q.property⟩
    · rintro ⟨t, ht, hx⟩
      exact ⟨⟨(⟨t, ht⟩, x), hx⟩, rfl⟩
  rw [← himage]
  exact hGconn.image _ (continuous_snd.comp continuous_subtype_val).continuousOn

private theorem CapSpace.mem_interior_of_mem_not_upperBoundary {ω : ℝ}
    (K : CapSpace ω) {p : Point} (hpK : p ∈ (K.val : Set Point))
    (hpδ : p ∉ ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2),
      exposedEdge K.val (t : Real.Angle)) :
    (⟨p, K.subset_capFan hpK⟩ : capFan ω) ∈
      interior {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
  let I := Set.Icc 0 (ω + Real.pi / 2)
  let gap : ℝ → ℝ := fun t ↦
    supportValue K.val (t : Real.Angle) - inner ℝ p (normalVector (t : Real.Angle))
  have hgap_cont : Continuous gap := (continuous_supportValue_real K.val).sub
    (continuous_const.inner continuous_normalVector_real)
  have hgap_pos : ∀ t ∈ I, 0 < gap t := by
    intro t ht
    have hle := inner_le_supportValue K.val hpK (t : Real.Angle)
    have hne : inner ℝ p (normalVector (t : Real.Angle)) ≠
        supportValue K.val (t : Real.Angle) := by
      intro heq
      apply hpδ
      exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨ht,
        ⟨hpK, by simpa [supportingLineHalfPlane, normalLine]⟩⟩⟩
    dsimp [gap]
    exact sub_pos.mpr (lt_of_le_of_ne hle hne)
  have hIne : I.Nonempty := ⟨0, by
    change 0 ∈ Set.Icc 0 (ω + Real.pi / 2)
    exact ⟨le_rfl, by linarith [K.property.1, Real.pi_pos]⟩⟩
  have hIcompact : IsCompact I := by
    dsimp [I]
    exact isCompact_Icc
  obtain ⟨m, hm, hmle⟩ := IsCompact.exists_pos_forall_le hIcompact hIne
    hgap_cont.continuousOn hgap_pos
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (Metric.ball_mem_nhds _ (half_pos hm)) ?_
  intro q hq
  change (q : Point) ∈ (K.val : Set Point)
  apply K.mem_of_mem_capFan_of_lt_supportValue q.property
  intro t ht
  have hdist : ‖(q : Point) - p‖ < m / 2 := by
    change dist (q : Point) p < m / 2 at hq
    simpa [dist_eq_norm] using hq
  have hnorm := norm_normalVector_real t
  have hinner : inner ℝ ((q : Point) - p) (normalVector (t : Real.Angle)) < m / 2 := by
    calc
      inner ℝ ((q : Point) - p) (normalVector (t : Real.Angle))
          ≤ ‖(q : Point) - p‖ * ‖normalVector (t : Real.Angle)‖ := real_inner_le_norm _ _
      _ < m / 2 := by simpa [hnorm] using hdist
  have := hmle t ht
  dsimp [gap] at this
  rw [inner_sub_left] at hinner
  linarith

private theorem CapSpace.mem_frontier_of_mem_upperBoundary {ω : ℝ}
    (K : CapSpace ω) {p : Point}
    (hp : p ∈ ⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2), exposedEdge K.val (t : Real.Angle)) :
    ∃ z : capFan ω, (z : Point) = p ∧
      z ∈ frontier {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := by
  obtain ⟨t, hp⟩ := Set.mem_iUnion.mp hp
  obtain ⟨htI, hpedge⟩ := Set.mem_iUnion.mp hp
  let z : capFan ω := ⟨p, K.subset_capFan hpedge.1⟩
  have hzK : z ∈ {q : capFan ω | (q : Point) ∈ (K.val : Set Point)} := hpedge.1
  refine ⟨z, rfl, (mem_frontier_iff_notMem_interior hzK).2 ?_⟩
  intro hzint
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hzint
  let e := ε / 2
  have he : 0 < e := half_pos hε
  let q : Point := p + e • normalVector (t : Real.Angle)
  have hsin : 0 ≤ Real.sin t := Real.sin_nonneg_of_nonneg_of_le_pi htI.1
    (htI.2.trans (by linarith [K.property.2.1, Real.pi_pos]))
  have hcos : 0 ≤ Real.cos (t - ω) := Real.cos_nonneg_of_mem_Icc ⟨by
    linarith [htI.1, K.property.2.1, Real.pi_pos], by linarith [htI.2]⟩
  have hqfan : q ∈ capFan ω := by
    constructor
    · change 0 ≤ inner ℝ q (normalVector (ω : Real.Angle))
      dsimp [q]
      rw [inner_add_left, inner_smul_left, inner_normalVector_normalVector]
      have hpω := (K.subset_capFan hpedge.1).1
      change 0 ≤ inner ℝ p (normalVector (ω : Real.Angle)) at hpω
      simp at *
      nlinarith
    · change 0 ≤ inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle))
      dsimp [q]
      rw [inner_add_left, inner_smul_left, inner_normalVector_normalVector]
      have hpT := (K.subset_capFan hpedge.1).2
      change 0 ≤ inner ℝ p (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) at hpT
      rw [Real.cos_sub]
      simp
      nlinarith
  have hqball : (⟨q, hqfan⟩ : capFan ω) ∈ Metric.ball z ε := by
    change dist q p < ε
    simp only [q, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_normalVector_real,
      mul_one]
    rw [Real.norm_eq_abs, abs_of_pos he]
    dsimp [e]
    linarith
  have hqK := interior_subset (hball hqball)
  change q ∈ (K.val : Set Point) at hqK
  have hqle := inner_le_supportValue K.val hqK (t : Real.Angle)
  have hpedge_eq := hpedge.2
  change inner ℝ p (normalVector (t : Real.Angle)) = supportValue K.val (t : Real.Angle)
    at hpedge_eq
  dsimp [q] at hqle
  rw [inner_add_left, inner_smul_left, inner_normalVector_self, hpedge_eq] at hqle
  simp at hqle
  nlinarith

theorem capUpperBoundary_relativeBoundary {ω : ℝ} (K : CapSpace ω) :
    capUpperBoundary K =
      Subtype.val '' frontier {p : capFan ω | (p : Point) ∈ (K.val : Set Point)} := by
  ext p
  constructor
  · intro hp
    obtain ⟨z, rfl, hz⟩ := K.mem_frontier_of_mem_upperBoundary hp
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hzfront, rfl⟩
    let S : Set (capFan ω) := {p | (p : Point) ∈ (K.val : Set Point)}
    have hSclosed : IsClosed S := K.val.isClosed.preimage continuous_subtype_val
    have hzS : z ∈ S := by
      apply hSclosed.closure_subset
      exact frontier_subset_closure hzfront
    by_contra hzupper
    have hzint := K.mem_interior_of_mem_not_upperBoundary hzS hzupper
    exact ((mem_frontier_iff_notMem_interior hzS).1 hzfront) hzint

end MovingSofa
