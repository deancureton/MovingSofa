import MovingSofa.Analysis.BoundedVariation

noncomputable section

namespace MovingSofa

structure RectifiablePathData where
  a : ℝ
  b : ℝ
  ordered : a ≤ b
  path : ContinuousBVPaths a b

def IsPathConcatenation (Γ : RectifiablePathData) {n : ℕ}
    (pieces : Fin n → RectifiablePathData) : Prop :=
  0 < n ∧ ∃ cuts : Fin (n + 1) → Set.Icc Γ.a Γ.b,
    Monotone cuts ∧ (cuts 0 : ℝ) = Γ.a ∧ (cuts (Fin.last n) : ℝ) = Γ.b ∧
    ∀ i : Fin n,
      ∃ (φ : Set.Icc (0 : ℝ) 1 →
          Set.Icc (cuts i.castSucc : ℝ) (cuts i.succ : ℝ))
        (ψ : Set.Icc (0 : ℝ) 1 → Set.Icc (pieces i).a (pieces i).b),
        Continuous φ ∧ Monotone φ ∧ Function.Surjective φ ∧
        Continuous ψ ∧ Monotone ψ ∧ Function.Surjective ψ ∧
        ∀ s, Γ.path.val ⟨(φ s : ℝ),
          le_trans (cuts i.castSucc).property.1 (φ s).property.1,
          le_trans (φ s).property.2 (cuts i.succ).property.2⟩ = (pieces i).path.val (ψ s)

/-- A concatenated path stays inside the union of the ranges of its pieces. -/
theorem IsPathConcatenation.range_subset_iUnion {Γ : RectifiablePathData} {n : ℕ}
    {pieces : Fin n → RectifiablePathData} (h : IsPathConcatenation Γ pieces) :
    Set.range Γ.path.val ⊆ ⋃ i, Set.range (pieces i).path.val := by
  classical
  obtain ⟨hn, cuts, hmono, hfirst, hlast, hconc⟩ := h
  rintro _ ⟨t, rfl⟩
  obtain ⟨i, hi₁, hi₂⟩ : ∃ i : Fin n,
      (cuts i.castSucc : ℝ) ≤ (t : ℝ) ∧ (t : ℝ) ≤ (cuts i.succ : ℝ) := by
    set T := Finset.univ.filter fun i : Fin (n + 1) ↦ (t : ℝ) ≤ (cuts i : ℝ) with hT
    have hmemT : ∀ i, i ∈ T ↔ (t : ℝ) ≤ (cuts i : ℝ) := fun i ↦ by simp [hT]
    have hTne : T.Nonempty :=
      ⟨Fin.last n, (hmemT _).mpr (by rw [hlast]; exact t.property.2)⟩
    have hmin : (t : ℝ) ≤ (cuts (T.min' hTne) : ℝ) := (hmemT _).mp (T.min'_mem hTne)
    rcases Fin.eq_zero_or_eq_succ (T.min' hTne) with hzero | ⟨j, hj⟩
    · refine ⟨⟨0, hn⟩, ?_, ?_⟩
      · rw [show ((⟨0, hn⟩ : Fin n).castSucc) = 0 from rfl, hfirst]
        exact t.property.1
      · exact (hzero ▸ hmin).trans
          (Subtype.coe_le_coe.mpr (hmono (Fin.zero_le ((⟨0, hn⟩ : Fin n).succ))))
    · refine ⟨j, ?_, by rw [← hj]; exact hmin⟩
      by_contra hlt
      have hle := T.min'_le _ ((hmemT j.castSucc).mpr (not_le.mp hlt).le)
      rw [hj] at hle
      exact absurd (lt_of_lt_of_le (Fin.castSucc_lt_succ (i := j)) hle) (lt_irrefl _)
  obtain ⟨φ, ψ, -, -, hφs, -, -, -, heq⟩ := hconc i
  obtain ⟨s, hs⟩ := hφs ⟨(t : ℝ), hi₁, hi₂⟩
  have hval : ((φ s : ℝ)) = (t : ℝ) := congrArg Subtype.val hs
  refine Set.mem_iUnion.mpr ⟨i, ψ s, ?_⟩
  rw [← heq s]
  exact congrArg _ (Subtype.ext hval)

end MovingSofa
