import GerverSofa.KernelOnly.PartB.CellSemanticsCore

/-! Semantic enclosure for analytic path phase 5. -/

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece5_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 5 i) (Romik.path5 params t) := by
  let ti := cellTimeInterval i
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hone := point_contains 1
  have hhalf := point_contains (1 / 2)
  have hz1 := RatInterval.contains_sub
    (RatInterval.contains_add (RatInterval.contains_mul e1_contains hc)
      (RatInterval.contains_mul e2_contains hs)) hhalf
  have hz2 := RatInterval.contains_sub
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg e2_contains) hc)
      (RatInterval.contains_mul e1_contains hs)) hone
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path5, Romik.rot, Romik.addK, ExactReplay.oneI] using
      RatInterval.contains_add hr1 k51_contains
  · simpa [cellPieceInterval, ti, Romik.path5, Romik.rot, Romik.addK, ExactReplay.oneI] using
      RatInterval.contains_add hr2 k52_contains

end PartB
end GerverSofa
