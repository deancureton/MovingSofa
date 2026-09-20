import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Specification boundary for interval/Krawczyk certification

The records below make the logical target explicit.  A completed numerical
formalisation must construct these records from exact interval operations,
Taylor bounds for `sin`/`cos`, a certified interval Jacobian and the general
Krawczyk theorem.  No global axiom is introduced here.
-/

namespace GerverSofa

/-- A unique solution of a predicate inside an explicit set. -/
structure CertifiedUniqueSolution {α : Type*} (P : α → Prop) (X : Set α) where
  solution : α
  solution_mem : solution ∈ X
  satisfies : P solution
  unique : ∀ y, y ∈ X → P y → y = solution

abbrev Vec (n : Nat) := Fin n → ℝ

/-- A unique zero of a vector-valued function in a set. -/
def CertifiedUniqueZero {n : Nat} (F : Vec n → Vec n) (X : Set (Vec n)) :=
  CertifiedUniqueSolution (fun x => F x = 0) X

end GerverSofa
