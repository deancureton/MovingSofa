import MovingSofa.Geometry.QuadrantBounds
import MovingSofa.Polygon.Height.Space

noncomputable section

namespace MovingSofa

def independentWallCap {Θ : AngleSet} (upper lower : PolygonHeightSpace Θ) : Set Point :=
  (⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false ∩
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) ∩
  ⋂ t ∈ (Θ.directions : Set ℝ) ∪ ((fun t : ℝ ↦ t + Real.pi / 2) '' Θ.directions),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue upper t) false false

def independentWallNiche {Θ : AngleSet} (lower : PolygonHeightSpace Θ) : Set Point :=
  (⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) ∩
  ⋃ t ∈ Θ.directions,
    normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) false true ∩
    normalHalfPlane ((t + Real.pi / 2 : ℝ) : Real.Angle)
      (polygonHeightValue lower (t + Real.pi / 2)) false true

theorem polygonPerturbation_uniform_bounds (Θ : AngleSet)
    (h : PolygonHeightSpace Θ) :
    ∃ R ε₀ : ℝ, 0 < R ∧ 0 < ε₀ ∧
      ∀ upper lower : PolygonHeightSpace Θ,
        (∀ t, |upper t - h t| ≤ ε₀) →
        (∀ t, |lower t - (h t - 1)| ≤ ε₀) →
        independentWallCap upper lower ⊆ Metric.closedBall 0 R ∧
        independentWallNiche lower ⊆ Metric.closedBall 0 R := by
  let a := polygonHeightValue h (Real.pi / 2) - 2
  let Q (t : ℝ) : Set Point := {p | a ≤ p 1 ∧
    inner ℝ p (normalVector (t : Real.Angle)) < polygonHeightValue h t + 2 ∧
    inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) <
      polygonHeightValue h (t + Real.pi / 2) + 2}
  have hQ : Bornology.IsBounded (⋃ t ∈ Θ.directions, Q t) := by
    apply (Bornology.isBounded_biUnion_finset Θ.directions).2
    intro t ht
    exact isBounded_setOf_le_snd_and_inner_lt _ _ _ t
      ⟨(Θ.interior t ht).1, (Θ.interior t ht).2.trans_le Θ.angle_le⟩
  obtain ⟨R, hR, hbound⟩ := hQ.exists_pos_norm_le
  refine ⟨R, 1, hR, zero_lt_one, ?_⟩
  intro upper lower hu hl
  have huv (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue upper t ≤ polygonHeightValue h t + 1 := by
    have hh := (abs_le.mp (hu ⟨t, ht⟩)).2
    simp only [polygonHeightValue, dite_eq_left ht]
    linarith
  have hlv (t : ℝ) (ht : t ∈ angleDomain Θ) :
      polygonHeightValue h t - 2 ≤ polygonHeightValue lower t ∧
      polygonHeightValue lower t ≤ polygonHeightValue h t := by
    have hh := abs_le.mp (hl ⟨t, ht⟩)
    simp only [polygonHeightValue, dite_eq_left ht]
    constructor <;> linarith [hh.1, hh.2]
  have hy {p : Point}
      (hp : p ∈ ⋂ t ∈ ({Θ.angle, Real.pi / 2} : Set ℝ),
        normalHalfPlane (t : Real.Angle) (polygonHeightValue lower t) true false) :
      a ≤ p 1 := by
    have hp' := Set.mem_iInter₂.mp hp (Real.pi / 2) (by simp)
    have hb := (hlv (Real.pi / 2) (Or.inr (by simp))).1
    have hp'' : polygonHeightValue lower (Real.pi / 2) ≤ p 1 := by
      simpa [normalHalfPlane, normalVector, frame, PiLp.inner_apply] using hp'
    exact hb.trans hp''
  have hball {p : Point} (hp : p ∈ ⋃ t ∈ Θ.directions, Q t) :
      p ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound p hp
  constructor
  · intro p hp
    apply hball
    obtain ⟨t, ht⟩ := Θ.nonempty
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, ?_, ?_, ?_⟩
    · apply hy
      exact Set.mem_iInter₂.mpr fun s hs ↦ (Set.mem_iInter₂.mp hp.1 s hs).2
    · have hb := Set.mem_iInter₂.mp hp.2 t (Or.inl ht)
      change inner ℝ p (normalVector (t : Real.Angle)) ≤ polygonHeightValue upper t at hb
      have hu' := huv t (Or.inl (Or.inl ht))
      linarith
    · have hb := Set.mem_iInter₂.mp hp.2 (t + Real.pi / 2) (Or.inr ⟨t, ht, rfl⟩)
      change inner ℝ p (normalVector ((t + Real.pi / 2 : ℝ) : Real.Angle)) ≤
        polygonHeightValue upper (t + Real.pi / 2) at hb
      have hu' := huv (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))
      linarith
  · rintro p ⟨hpF, hpN⟩
    apply hball
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hpN
    apply Set.mem_iUnion₂.mpr
    refine ⟨t, ht, hy hpF, ?_, ?_⟩
    · have hb := (hlv t (Or.inl (Or.inl ht))).2
      have hp₁ : inner ℝ p (normalVector (t : Real.Angle)) <
          polygonHeightValue lower t := hp.1
      exact hp₁.trans_le (by linarith)
    · have hb := (hlv (t + Real.pi / 2) (Or.inl (Or.inr ⟨t, ht, rfl⟩))).2
      exact hp.2.trans_le (by linarith)

end MovingSofa
