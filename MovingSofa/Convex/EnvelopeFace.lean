import MovingSofa.Convex.CombinationProperties
import MovingSofa.ForMathlib.Analysis.Calculus.LocalExtr.OneSided

noncomputable section

namespace MovingSofa

/-!
# Faces of a body cut out by a differentiable family of half-planes

Let `L` be a convex body lying in every half-plane `{q | m s ≤ ⟪q, u_s⟫}` of a family indexed
by a real angle parameter `s`, and let `p ∈ L` attain the bound at `s = t`.  If `m` is
differentiable at `t` with `m' t = ⟪p, v_t⟫` — that is, if `p` is the first-order contact point
of the family — then the reversed face of `L` at `t + π` is pinned down by the sign of the
one-sided derivatives of `s ↦ ⟪z, u_s⟫ - m s` at `t`:
`exposedEdge_add_pi_eq_singleton_of_mem_Ioo` at an interior parameter gives the singleton
`{p}`, while `edgeVertices_add_pi_fst_eq_of_lt` and `edgeVertices_add_pi_snd_eq_of_lt` identify
`p` with one endpoint vertex of the face at the two boundary parameters.
-/

/-- The tangent coordinate of a point whose normal coordinate dominates a differentiable family
to the left of the touching parameter is at most that of the contact point. -/
theorem inner_tangentVector_le_of_forall_le_Ioo {m : ℝ → ℝ} {p z : Point} {a t : ℝ}
    (hat : a < t) (hle : ∀ s ∈ Set.Ioo a t, m s ≤ inner ℝ z (normalVector (s : Real.Angle)))
    (hzm : inner ℝ z (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    inner ℝ z (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) := by
  have hmin : IsLocalMinOn (fun s : ℝ ↦ inner ℝ z (normalVector (s : Real.Angle)) - m s)
      (Set.Iic t) t := by
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hat), self_mem_nhdsWithin] with s hs hst
    rcases (Set.mem_Iic.1 hst).lt_or_eq with h | rfl
    · simpa only [hzm, sub_self] using sub_nonneg.2 (hle s ⟨hs, h⟩)
    · exact le_rfl
  have hF := (hasDerivAt_inner_normalVector z t).sub hd
  linarith only [hmin.hasDerivWithinAt_Iic_nonpos hF.hasDerivWithinAt]

/-- The tangent coordinate of a point whose normal coordinate dominates a differentiable family
to the right of the touching parameter is at least that of the contact point. -/
theorem le_inner_tangentVector_of_forall_le_Ioo {m : ℝ → ℝ} {p z : Point} {t b : ℝ}
    (htb : t < b) (hle : ∀ s ∈ Set.Ioo t b, m s ≤ inner ℝ z (normalVector (s : Real.Angle)))
    (hzm : inner ℝ z (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ z (tangentVector (t : Real.Angle)) := by
  have hmin : IsLocalMinOn (fun s : ℝ ↦ inner ℝ z (normalVector (s : Real.Angle)) - m s)
      (Set.Ici t) t := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htb), self_mem_nhdsWithin] with s hs hst
    rcases (Set.mem_Ici.1 hst).lt_or_eq with h | rfl
    · simpa only [hzm, sub_self] using sub_nonneg.2 (hle s ⟨h, hs⟩)
    · exact le_rfl
  have hF := (hasDerivAt_inner_normalVector z t).sub hd
  linarith only [hmin.hasDerivWithinAt_Ici_nonneg hF.hasDerivWithinAt]

/-- At an interior touching parameter of a differentiable family of supporting half-planes the
reversed face is the singleton contact point. -/
theorem exposedEdge_add_pi_eq_singleton_of_mem_Ioo {L : ConvexBody Point} {m : ℝ → ℝ}
    {p : Point} {a b t : ℝ} (ht : t ∈ Set.Ioo a b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (t : Real.Angle)) = m t)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (t : Real.Angle))) t) :
    exposedEdge L ((t + Real.pi : ℝ) : Real.Angle) = {p} := by
  have hlet : ∀ q ∈ (L : Set Point), m t ≤ inner ℝ q (normalVector (t : Real.Angle)) :=
    fun q hq ↦ hle q hq t ht
  rw [exposedEdge_add_pi_eq_of_forall_le hlet hp hpm]
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  refine ⟨fun hq ↦ ?_, fun hq ↦ ⟨hq ▸ hp, hq ▸ hpm⟩⟩
  have h1 : inner ℝ q (tangentVector (t : Real.Angle)) ≤
      inner ℝ p (tangentVector (t : Real.Angle)) :=
    inner_tangentVector_le_of_forall_le_Ioo ht.1
      (fun s hs ↦ hle q hq.1 s ⟨hs.1, hs.2.trans ht.2⟩) hq.2 hd
  have h2 : inner ℝ p (tangentVector (t : Real.Angle)) ≤
      inner ℝ q (tangentVector (t : Real.Angle)) :=
    le_inner_tangentVector_of_forall_le_Ioo ht.2
      (fun s hs ↦ hle q hq.1 s ⟨ht.1.trans hs.1, hs.2⟩) hq.2 hd
  rw [← inner_normalVector_smul_add_inner_tangentVector_smul q (t : Real.Angle),
    ← inner_normalVector_smul_add_inner_tangentVector_smul p (t : Real.Angle),
    hq.2, hpm, le_antisymm h1 h2]

/-- At the left endpoint parameter of a differentiable family of supporting half-planes the
contact point is the positive vertex of the reversed face. -/
theorem edgeVertices_add_pi_fst_eq_of_lt {L : ConvexBody Point} {m : ℝ → ℝ} {p : Point}
    {a b : ℝ} (hab : a < b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hlea : ∀ q ∈ (L : Set Point), m a ≤ inner ℝ q (normalVector (a : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (a : Real.Angle)) = m a)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (a : Real.Angle))) a) :
    (edgeVertices L ((a + Real.pi : ℝ) : Real.Angle)).1 = p := by
  have hface := exposedEdge_add_pi_eq_of_forall_le hlea hp hpm
  refine edgeVertices_fst_eq_of_tangent_isGreatest L _ (hface ▸ ⟨hp, hpm⟩) ?_
  intro q hq
  rw [hface] at hq
  have h1 : inner ℝ p (tangentVector (a : Real.Angle)) ≤
      inner ℝ q (tangentVector (a : Real.Angle)) :=
    le_inner_tangentVector_of_forall_le_Ioo hab (fun s hs ↦ hle q hq.1 s hs) hq.2 hd
  rw [tangentVector_add_pi, inner_neg_right, inner_neg_right]
  linarith only [h1]

/-- At the right endpoint parameter of a differentiable family of supporting half-planes the
contact point is the negative vertex of the reversed face. -/
theorem edgeVertices_add_pi_snd_eq_of_lt {L : ConvexBody Point} {m : ℝ → ℝ} {p : Point}
    {a b : ℝ} (hab : a < b)
    (hle : ∀ q ∈ (L : Set Point), ∀ s ∈ Set.Ioo a b,
      m s ≤ inner ℝ q (normalVector (s : Real.Angle)))
    (hleb : ∀ q ∈ (L : Set Point), m b ≤ inner ℝ q (normalVector (b : Real.Angle)))
    (hp : p ∈ (L : Set Point))
    (hpm : inner ℝ p (normalVector (b : Real.Angle)) = m b)
    (hd : HasDerivAt m (inner ℝ p (tangentVector (b : Real.Angle))) b) :
    (edgeVertices L ((b + Real.pi : ℝ) : Real.Angle)).2 = p := by
  have hface := exposedEdge_add_pi_eq_of_forall_le hleb hp hpm
  refine edgeVertices_snd_eq_of_tangent_isLeast L _ (hface ▸ ⟨hp, hpm⟩) ?_
  intro q hq
  rw [hface] at hq
  have h1 : inner ℝ q (tangentVector (b : Real.Angle)) ≤
      inner ℝ p (tangentVector (b : Real.Angle)) :=
    inner_tangentVector_le_of_forall_le_Ioo hab (fun s hs ↦ hle q hq.1 s hs) hq.2 hd
  rw [tangentVector_add_pi, inner_neg_right, inner_neg_right]
  linarith only [h1]

end MovingSofa
