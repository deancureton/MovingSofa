import MovingSofa.Cap.Balanced

noncomputable section

namespace MovingSofa

def rightAngleSet (n : ℕ) (hn : 2 ≤ n) : AngleSet :=
  uniformAngleSet (Real.pi / 2) (by positivity) le_rfl n hn

def polygonStepSize (n : ℕ) : ℝ := (Real.pi / 2) / n

def IsMaximumPolygonCapSteps (n : ℕ) (K : RightAngleCapSpace) : Prop :=
  ∃ hn : 2 ≤ n, (∃ k : ℕ, n = 2 ^ k) ∧
    ∃ P : PolygonCapSpace (rightAngleSet n hn),
      P.val = K ∧ IsMaximumPolygonCap (rightAngleSet n hn) P

def magicFunctions : (NNReal → ℝ) × (NNReal → ℝ) :=
  (fun x ↦ max |(x : ℝ) - 1| ((|(x : ℝ) - 1| + 1) / 2),
   fun x ↦ (x : ℝ) - max |(x : ℝ) - 1| ((|(x : ℝ) - 1| + 1) / 2))

/-- The magic function `m₀` is nondecreasing: it is `3 * x / 2 - 1` on `[0, 1]`, `x / 2` on
`[1, 2]`, and constant equal to `1` afterwards. -/
theorem magicFunctions_snd_monotone : Monotone magicFunctions.2 := by
  intro a b hab
  have hab' : (a : ℝ) ≤ (b : ℝ) := hab
  simp only [magicFunctions, max_def]
  rcases abs_cases ((a : ℝ) - 1) with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;>
    rcases abs_cases ((b : ℝ) - 1) with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;>
      rw [ha1, hb1] <;> split_ifs <;> linarith

end MovingSofa
