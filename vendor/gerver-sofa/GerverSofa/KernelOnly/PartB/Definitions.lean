import GerverSofa.KernelOnly.PartB.Arithmetic
import GerverSofa.Geometry
import GerverSofa.KernelOnly.ConcreteUniqueZeros

/-!
# Part B semantic definitions

The numerical layer from Part A is frozen.  This file names the certified
parameter vector and the two real support functions whose continuum lower
bounds are established by the exact cell certificate.
-/

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

/-- The unique direct-system parameter vector certified in Part A. -/
def params : Romik.Params :=
  Romik.coordEquiv.symm PartALeanCert.fullRoot

/-- The physical parameter interval. -/
def physicalInterval : Set ℝ := Set.Icc (0 : ℝ) (Real.pi / 2)

/-- The two global support functions used in the manuscript's grid lemma. -/
def Gu (s t : ℝ) : ℝ :=
  1 + dot (Romik.path params s - Romik.path params t) (u s)

def Gv (s t : ℝ) : ℝ :=
  1 + dot (Romik.path params s - Romik.path params t) (v s)

/-- The real version of the exact rational target. -/
def target : ℝ := (targetQ : ℝ)

/-- Physical mesh node `iπ/128`. -/
def nodeTime (i : Nat) : ℝ := (nodeCoeff i : ℝ) * Real.pi

/-- Physical closed cell. -/
def cellSet (i : Cell) : Set ℝ :=
  Set.Icc (nodeTime i.1) (nodeTime (i.1 + 1))

/-- Semantic containment in a planar interval box. -/
def PointContains (z : RatInterval × RatInterval) (p : Point) : Prop :=
  RatInterval.Contains z.1 p.1 ∧ RatInterval.Contains z.2 p.2

end PartB
end GerverSofa
