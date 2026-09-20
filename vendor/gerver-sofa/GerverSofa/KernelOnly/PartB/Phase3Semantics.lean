import GerverSofa.KernelOnly.PartB.CellSemanticsCore

/-! Semantic enclosure for analytic path phase 3. -/

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece3_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 3 i) (Romik.path3 params t) := by
  let ti := cellTimeInterval i
  have htI : Contains ti t := cellTimeInterval_contains htCell
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hz1 := RatInterval.contains_sub c1_contains htI
  have hz2 := RatInterval.contains_add c2_contains htI
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path3, Romik.rot, Romik.addK] using
      RatInterval.contains_add hr1 k31_contains
  · simpa [cellPieceInterval, ti, Romik.path3, Romik.rot, Romik.addK] using
      RatInterval.contains_add hr2 k32_contains

end PartB
end GerverSofa
