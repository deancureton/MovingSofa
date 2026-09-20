import GerverSofa.KernelOnly.PartB.Arithmetic

/-!
Independent exact product-cell lower bounds for row 44.
Build all 64 row modules sequentially before the final Part B assembly.
-/

namespace GerverSofa.PartB

set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
theorem cell_row_44 :
    ∀ j : Cell,
      targetQ < (guCellInterval (44 : Cell) j).lo ∧
      targetQ < (gvCellInterval (44 : Cell) j).lo := by
  decide +kernel

end GerverSofa.PartB
