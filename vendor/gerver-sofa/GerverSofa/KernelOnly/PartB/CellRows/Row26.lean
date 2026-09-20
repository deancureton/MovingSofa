import GerverSofa.KernelOnly.PartB.Arithmetic

/-!
Independent exact product-cell lower bounds for row 26.
Build all 64 row modules sequentially before the final Part B assembly.
-/

namespace GerverSofa.PartB

set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
theorem cell_row_26 :
    ∀ j : Cell,
      targetQ < (guCellInterval (26 : Cell) j).lo ∧
      targetQ < (gvCellInterval (26 : Cell) j).lo := by
  decide +kernel

end GerverSofa.PartB
