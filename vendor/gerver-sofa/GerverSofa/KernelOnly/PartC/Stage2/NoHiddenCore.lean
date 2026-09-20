import GerverSofa.KernelOnly.PartC.Stage2.MeshFacts

/-!
# Exact cell reduction of the two no-hidden-crossing inequalities

Off-diagonal mesh cells are reduced to executable upper bounds for the already
sound Part B intervals `Gu` and `Gv`.  The only analytic remainder after all
128 row certificates pass is the ordered triangle inside each single mesh
cell, named `SameCellU` and `SameCellV` below.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage2

/-- Manuscript `U(r,t)` in the orientation used by `NoHiddenCrossingU`. -/
def UValue (r t : ℝ) : ℝ :=
  dot (Romik.path params r - Romik.path params t) (u t)

/-- Reflected manuscript `V(t,r)`. -/
def VValue (t r : ℝ) : ℝ :=
  dot (Romik.path params r - Romik.path params t) (v t)

end Stage2
end PartC
end GerverSofa
