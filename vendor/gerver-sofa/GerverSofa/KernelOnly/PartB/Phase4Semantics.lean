import GerverSofa.KernelOnly.PartB.CellSemanticsCore

/-! Semantic enclosure for analytic path phase 4. -/

noncomputable section

namespace GerverSofa
namespace PartB

open RatInterval

theorem cellPiece4_contains {i : Cell} {t : ℝ}
    (htCell : t ∈ cellSet i) (htPhys : t ∈ physicalInterval) :
    PointContains (cellPieceInterval 4 i) (Romik.path4 params t) := by
  let ti := cellTimeInterval i
  have htI : Contains ti t := cellTimeInterval_contains htCell
  have htr := trig_contains htCell htPhys
  have hc := htr.1
  have hs := htr.2
  have hone := point_contains 1
  have hhalf := point_contains (1 / 2)
  have hquarter := point_contains (1 / 4)
  have htt := RatInterval.contains_mul htI htI
  have hz1 := RatInterval.contains_sub
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg hhalf) htI)
      d1_contains) hone
  have hz2 := RatInterval.contains_add
    (RatInterval.contains_add
      (RatInterval.contains_mul (RatInterval.contains_neg hquarter) htt)
      (RatInterval.contains_mul d1_contains htI)) d2_contains
  have hr1 := RatInterval.contains_sub
    (RatInterval.contains_mul hc hz1) (RatInterval.contains_mul hs hz2)
  have hr2 := RatInterval.contains_add
    (RatInterval.contains_mul hs hz1) (RatInterval.contains_mul hc hz2)
  constructor
  · simpa [cellPieceInterval, ti, Romik.path4, Romik.rot, Romik.addK,
      ExactReplay.oneI, mul_assoc] using RatInterval.contains_add hr1 k41_contains
  · simpa [cellPieceInterval, ti, Romik.path4, Romik.rot, Romik.addK,
      ExactReplay.oneI, mul_assoc] using RatInterval.contains_add hr2 k42_contains

end PartB
end GerverSofa
