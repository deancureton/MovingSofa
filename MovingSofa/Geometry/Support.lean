import MovingSofa.Geometry.Frame

noncomputable section

namespace MovingSofa

/-- A compact convex body attains its support value in every normal direction. -/
theorem exists_mem_inner_eq_supportValue (K : ConvexBody Point) (t : Real.Angle) :
    ∃ p ∈ (K : Set Point), inner ℝ p (normalVector t) = supportValue K t := by
  obtain ⟨p, hp, hmax, _⟩ := K.isCompact.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector t)) K.nonempty
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  exact ⟨p, hp, by simpa only [supportValue] using hmax.symm⟩


/-- Translating a nonempty compact set adds the normal component to its support value. -/
theorem supportValue_image_add_of_isCompact {s : Set Point}
    (hs : IsCompact s) (hne : s.Nonempty) (v : Point) (t : Real.Angle) :
    supportValue ((fun p ↦ p + v) '' s) t =
      supportValue s t + inner ℝ v (normalVector t) := by
  obtain ⟨x, hx, hmax, hbound⟩ := hs.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector t)) hne
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨x + v, ⟨x, hx, rfl⟩, ?_⟩
    simpa only [inner_add_left, supportValue] using congrArg
      (fun r ↦ r + inner ℝ v (normalVector t)) hmax.symm
  · rintro z ⟨y, ⟨p, hp, rfl⟩, rfl⟩
    simp only [inner_add_left]
    simpa only [supportValue, hmax] using
      add_le_add (hbound p hp) (le_refl (inner ℝ v (normalVector t)))

/-- Translating a compact convex body adds the normal component of the translation to support. -/
theorem supportValue_image_add (K : ConvexBody Point) (v : Point) (t : Real.Angle) :
    supportValue ((fun p ↦ p + v) '' (K : Set Point)) t =
      supportValue K t + inner ℝ v (normalVector t) :=
  supportValue_image_add_of_isCompact K.isCompact K.nonempty v t

/-- Every point of a compact set lies below its support value. -/
theorem inner_le_supportValue_of_isCompact {s : Set Point}
    (hs : IsCompact s) {p : Point} (hp : p ∈ s) (a : Real.Angle) :
    inner ℝ p (normalVector a) ≤ supportValue s a := by
  apply le_csSup (hs.image
    (continuous_inner.comp (continuous_id.prodMk continuous_const))).bddAbove
  exact ⟨p, hp, rfl⟩

/-- A point of a convex body lies below each supporting line. -/
theorem inner_le_supportValue (K : ConvexBody Point) {p : Point}
    (hp : p ∈ K) (t : Real.Angle) : inner ℝ p (normalVector t) ≤ supportValue K t :=
  inner_le_supportValue_of_isCompact K.isCompact hp t

/-- Containment in a closed normal half-plane bounds the support value. -/
theorem supportValue_le_of_subset_normalHalfPlane (K : ConvexBody Point)
    (t : Real.Angle) (c : ℝ)
    (hK : (K : Set Point) ⊆ normalHalfPlane t c false false) :
    supportValue K t ≤ c := by
  apply csSup_le (K.nonempty.image _)
  rintro _ ⟨p, hp, rfl⟩
  exact hK hp

/-- Enlarging a nonempty set without increasing its directional upper bound preserves support. -/
theorem supportValue_eq_of_subset_of_inner_le {s u : Set Point}
    (hs : s.Nonempty) (hsu : s ⊆ u) (a : Real.Angle)
    (hu : ∀ p ∈ u, inner ℝ p (normalVector a) ≤ supportValue s a) :
    supportValue u a = supportValue s a := by
  have hbounded : BddAbove ((fun p ↦ inner ℝ p (normalVector a)) '' u) :=
    ⟨supportValue s a, by rintro _ ⟨p, hp, rfl⟩; exact hu p hp⟩
  apply le_antisymm
  · exact csSup_le ((hs.mono hsu).image _) (by rintro _ ⟨p, hp, rfl⟩; exact hu p hp)
  · exact csSup_le_csSup hbounded (hs.image _) (Set.image_mono hsu)

/-- A convex set meets every intermediate level of a linear functional. -/
theorem exists_mem_inner_eq_of_convex {s : Set Point} (hconv : Convex ℝ s)
    {A C : Point} (hA : A ∈ s) (hC : C ∈ s) {u : Point} {c : ℝ}
    (hCle : inner ℝ C u ≤ c) (hAge : c ≤ inner ℝ A u) :
    ∃ q ∈ s, inner ℝ q u = c := by
  rcases eq_or_lt_of_le (hCle.trans hAge) with heq | hlt
  · exact ⟨C, hC, le_antisymm hCle (heq ▸ hAge)⟩
  · set d : ℝ := inner ℝ A u - inner ℝ C u with hd
    have hdpos : 0 < d := by simp only [hd]; linarith
    set lam : ℝ := (c - inner ℝ C u) / d with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hdpos.le
    have hlam1 : lam ≤ 1 := by
      rw [hlam, div_le_one hdpos]
      simp only [hd]; linarith
    refine ⟨lam • A + (1 - lam) • C, hconv hA hC hlam0 (by linarith) (by ring), ?_⟩
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hlam]
    field_simp
    simp only [hd]
    ring

/-- Support bound in the direction opposite to a cut line lying below the set. -/
theorem supportValue_le_of_cut {s : Set Point} (hne : s.Nonempty) {a b c : ℝ}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle))
    (hs : ∀ p ∈ s, c ≤ inner ℝ p (normalVector (a : Real.Angle))) :
    supportValue s ((b : ℝ) : Real.Angle) ≤ -c := by
  rw [hab]
  refine csSup_le (hne.image _) ?_
  rintro _ ⟨p, hp, rfl⟩
  dsimp only
  rw [normalVector_add_pi, inner_neg_right]
  linarith only [hs p hp]

/-- A contact point on a cut line attains the opposite support value. -/
theorem le_supportValue_of_cut {s : Set Point} (hcomp : IsCompact s) {a b c : ℝ} {p : Point}
    (hab : ((b : ℝ) : Real.Angle) = ((a + Real.pi : ℝ) : Real.Angle)) (hp : p ∈ s)
    (hpc : inner ℝ p (normalVector (a : Real.Angle)) = c) :
    -c ≤ supportValue s ((b : ℝ) : Real.Angle) := by
  rw [hab]
  have h := inner_le_supportValue_of_isCompact hcomp hp ((a + Real.pi : ℝ) : Real.Angle)
  rw [normalVector_add_pi, inner_neg_right, hpc] at h
  linarith only [h]
end MovingSofa
