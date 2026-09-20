import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice

/-!
# Basic planar geometry for the moving-sofa problem

This file fixes the exact hallway convention used by the manuscript.
The inner quadrant is open, so contact with an inner wall is allowed.
-/

namespace GerverSofa

abbrev Point := ℝ × ℝ

/-- Horizontal unit-width arm `(-∞,1] × [0,1]`. -/
def horizontalArm : Set Point :=
  {p | p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1}

/-- Vertical unit-width arm `[0,1] × (-∞,1]`. -/
def verticalArm : Set Point :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- Closed outer quarter-plane `(-∞,1]²`. -/
def outerQuarter : Set Point :=
  {p | p.1 ≤ 1 ∧ p.2 ≤ 1}

/-- Open inner quarter-plane `(-∞,0)²`. -/
def innerQuarter : Set Point :=
  {p | p.1 < 0 ∧ p.2 < 0}

/-- The standard unit right-angled hallway. -/
def hallway : Set Point := horizontalArm ∪ verticalArm

/-- Quarter-plane presentation of the standard hallway. -/
theorem hallway_eq_outer_diff_inner :
    hallway = outerQuarter \ innerQuarter := by
  ext p
  constructor
  · intro hp
    rcases hp with hp | hp
    · exact ⟨⟨hp.1, hp.2.2⟩, fun hn => (not_lt_of_ge hp.2.1) hn.2⟩
    · exact ⟨⟨hp.2.1, hp.2.2⟩, fun hn => (not_lt_of_ge hp.1) hn.1⟩
  · rintro ⟨hout, hnotin⟩
    by_cases hx : 0 ≤ p.1
    · exact Or.inr ⟨hx, hout.1, hout.2⟩
    · have hxneg : p.1 < 0 := lt_of_not_ge hx
      have hy : 0 ≤ p.2 := by
        by_contra hy0
        exact hnotin ⟨hxneg, lt_of_not_ge hy0⟩
      exact Or.inl ⟨hout.1, hy, hout.2⟩

@[simp] theorem mem_horizontalArm (p : Point) :
    p ∈ horizontalArm ↔ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := Iff.rfl

@[simp] theorem mem_verticalArm (p : Point) :
    p ∈ verticalArm ↔ 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ p.2 ≤ 1 := Iff.rfl

@[simp] theorem mem_outerQuarter (p : Point) :
    p ∈ outerQuarter ↔ p.1 ≤ 1 ∧ p.2 ≤ 1 := Iff.rfl

@[simp] theorem mem_innerQuarter (p : Point) :
    p ∈ innerQuarter ↔ p.1 < 0 ∧ p.2 < 0 := Iff.rfl

end GerverSofa
