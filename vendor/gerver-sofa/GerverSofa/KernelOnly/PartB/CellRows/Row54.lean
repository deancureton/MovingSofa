import GerverSofa.KernelOnly.PartB.Arithmetic

/-!
Independent exact product-cell lower bounds for row 54.
Build all 64 row modules sequentially before the final Part B assembly.
-/

namespace GerverSofa.PartB

set_option maxRecDepth 200000 in
set_option maxHeartbeats 50000000 in
theorem cell_row_54 :
    ∀ j : Cell,
      targetQ < (guCellInterval (54 : Cell) j).lo ∧
      targetQ < (gvCellInterval (54 : Cell) j).lo := by
  decide +kernel

end GerverSofa.PartB
