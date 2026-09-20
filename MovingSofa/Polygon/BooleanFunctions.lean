import Mathlib.Data.Fin.Basic

namespace MovingSofa

abbrev BooleanFunction (n : ℕ) := (Fin n → Bool) → Bool

def IsMonotoneBooleanFunction {n : ℕ} (E : BooleanFunction n) : Prop :=
  ∀ P Q, (∀ i, P i = true → Q i = true) → E P = true → E Q = true

inductive PositiveBooleanFormula (n : ℕ) where
  | variable (i : Fin n)
  | conjunction (left right : PositiveBooleanFormula n)
  | disjunction (left right : PositiveBooleanFormula n)

def PositiveBooleanFormula.eval {n : ℕ} : PositiveBooleanFormula n → BooleanFunction n
  | .variable i => fun P ↦ P i
  | .conjunction left right => fun P ↦ left.eval P && right.eval P
  | .disjunction left right => fun P ↦ left.eval P || right.eval P

theorem positiveBooleanFormula_monotone {n : ℕ} (E : PositiveBooleanFormula n) :
    IsMonotoneBooleanFunction E.eval := by
  induction E <;>
    simp_all [IsMonotoneBooleanFunction, PositiveBooleanFormula.eval,
      Bool.and_eq_true, Bool.or_eq_true] <;>
    aesop

end MovingSofa
