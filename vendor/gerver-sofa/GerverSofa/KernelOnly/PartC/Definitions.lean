import GerverSofa.KernelOnly.EndpointSymmetry
import GerverSofa.KernelOnly.Identification
import GerverSofa.KernelOnly.PartB.Continuum

/-!
# Part C concrete objects

This file fixes the exact objects used throughout Part C.  The numerical root,
regularity and global two-variable support margins are inherited from the
closed Parts A and B.  No alternative parameter vector or geometric set is
introduced here.
-/

noncomputable section

namespace GerverSofa
namespace PartC

/-- The certified twenty-two dimensional Gerver parameter vector. -/
abbrev params : Romik.Params := PartB.params

/-- Physical terminal angle. -/
def T : ℝ := Real.pi / 2

/-- Reflected switching angles. -/
def eta : ℝ := T - params.theta
def tau : ℝ := T - params.phi

/-- The concrete cap, fixed sofa, reconstructed Romik set and frame. -/
abbrev K : Set Point := Romik.K0 params
abbrev G : Set Point := Romik.sofa params
abbrev Sx : Set Point := Romik.reconstructedSet params
abbrev frame : ℝ → SE2 := Romik.frame params

/-- Endpoint support point used for the direct nonemptiness proof. -/
def anchor : Point := (1, 0)

/-- Piecewise body-frame derivative coefficients.  This definition is local to
Part C so that the geometric layer does not import the later Part D article
claims. -/
def alphaBetaAt (t : ℝ) : Point :=
  if t ≤ params.phi then Romik.alphaBeta1 params t
  else if t ≤ params.theta then Romik.alphaBeta2 params t
  else if t ≤ eta then Romik.alphaBeta3 params t
  else if t ≤ tau then Romik.alphaBeta4 params t
  else Romik.alphaBeta5 params t

def alpha (t : ℝ) : ℝ := (alphaBetaAt t).1
def beta (t : ℝ) : ℝ := (alphaBetaAt t).2

/-- The four standard contact curves. -/
def A (t : ℝ) : Point :=
  let x := Romik.path params t
  let a := alpha t
  (x.1 + a * (v t).1 + (u t).1,
   x.2 + a * (v t).2 + (u t).2)

def B (t : ℝ) : Point :=
  let x := Romik.path params t
  let a := alpha t
  (x.1 + a * (v t).1,
   x.2 + a * (v t).2)

def C (t : ℝ) : Point :=
  let x := Romik.path params t
  let b := beta t
  (x.1 - b * (u t).1 + (v t).1,
   x.2 - b * (u t).2 + (v t).2)

def D (t : ℝ) : Point :=
  let x := Romik.path params t
  let b := beta t
  (x.1 - b * (u t).1,
   x.2 - b * (u t).2)

/-- Image of a parametrized curve over a time set. -/
def curveImage (f : ℝ → Point) (I : Set ℝ) : Set Point := f '' I

/-- A closed line segment, written without depending on a specialized convex
geometry API. -/
def lineSegment (a b : Point) : Set Point :=
  {q | ∃ r ∈ Set.Icc (0 : ℝ) 1,
    q = ((1 - r) * a.1 + r * b.1,
         (1 - r) * a.2 + r * b.2)}

/-- Set-valued form of the niche boundary described in the manuscript. -/
def claimedNicheBoundary : Set Point :=
  lineSegment (D 0) (B T) ∪
  curveImage B (Set.Icc eta T) ∪
  curveImage (Romik.path params) (Set.Icc params.phi tau) ∪
  curveImage D (Set.Icc 0 params.theta)

end PartC
end GerverSofa
