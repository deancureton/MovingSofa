import GerverSofa.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Orientation-preserving rigid motions of the plane

An element is represented by `(c,s,tₓ,tᵧ)` with `c²+s²=1`.  Its linear
part is the rotation matrix `[[c,-s],[s,c]]`, hence every value is an element
of `SE(2)` and not an arbitrary affine equivalence.
-/

namespace GerverSofa

structure SE2 where
  c : ℝ
  s : ℝ
  tx : ℝ
  ty : ℝ
  unit : c * c + s * s = 1

namespace SE2

/-- Action of an orientation-preserving rigid motion on the plane. -/
def act (g : SE2) (p : Point) : Point :=
  (g.c * p.1 - g.s * p.2 + g.tx,
   g.s * p.1 + g.c * p.2 + g.ty)

/-- Identity element. -/
def one : SE2 where
  c := 1
  s := 0
  tx := 0
  ty := 0
  unit := by norm_num

/-- Inverse orientation-preserving rigid motion. -/
def inv (g : SE2) : SE2 where
  c := g.c
  s := -g.s
  tx := -(g.c * g.tx + g.s * g.ty)
  ty := g.s * g.tx - g.c * g.ty
  unit := by nlinarith [g.unit]

@[simp] theorem one_act (p : Point) : one.act p = p := by
  rcases p with ⟨x, y⟩
  simp [one, act]

@[simp] theorem inv_act_act (g : SE2) (p : Point) :
    g.inv.act (g.act p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · dsimp [act, inv]
    linear_combination x * g.unit
  · dsimp [act, inv]
    linear_combination y * g.unit

@[simp] theorem act_inv_act (g : SE2) (p : Point) :
    g.act (g.inv.act p) = p := by
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · dsimp [act, inv]
    linear_combination (x - g.tx) * g.unit
  · dsimp [act, inv]
    linear_combination (y - g.ty) * g.unit

/-- Componentwise continuity is the topology-free representation of a path
in `SE(2)` used by the formal moving-sofa definition. -/
def ContinuousPath (g : ℝ → SE2) : Prop :=
  Continuous (fun t => (g t).c) ∧
  Continuous (fun t => (g t).s) ∧
  Continuous (fun t => (g t).tx) ∧
  Continuous (fun t => (g t).ty)

/-- Inversion preserves continuous `SE(2)` paths. -/
theorem continuousPath_inv {g : ℝ → SE2} (hg : ContinuousPath g) :
    ContinuousPath (fun t => (g t).inv) := by
  rcases hg with ⟨hc, hs, htx, hty⟩
  refine ⟨hc, hs.neg, ?_, ?_⟩
  · exact ((hc.mul htx).add (hs.mul hty)).neg
  · exact (hs.mul htx).sub (hc.mul hty)

end SE2
end GerverSofa
