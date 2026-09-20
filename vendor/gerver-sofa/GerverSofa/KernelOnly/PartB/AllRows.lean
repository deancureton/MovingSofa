import GerverSofa.KernelOnly.PartB.CellRows.Row00
import GerverSofa.KernelOnly.PartB.CellRows.Row01
import GerverSofa.KernelOnly.PartB.CellRows.Row02
import GerverSofa.KernelOnly.PartB.CellRows.Row03
import GerverSofa.KernelOnly.PartB.CellRows.Row04
import GerverSofa.KernelOnly.PartB.CellRows.Row05
import GerverSofa.KernelOnly.PartB.CellRows.Row06
import GerverSofa.KernelOnly.PartB.CellRows.Row07
import GerverSofa.KernelOnly.PartB.CellRows.Row08
import GerverSofa.KernelOnly.PartB.CellRows.Row09
import GerverSofa.KernelOnly.PartB.CellRows.Row10
import GerverSofa.KernelOnly.PartB.CellRows.Row11
import GerverSofa.KernelOnly.PartB.CellRows.Row12
import GerverSofa.KernelOnly.PartB.CellRows.Row13
import GerverSofa.KernelOnly.PartB.CellRows.Row14
import GerverSofa.KernelOnly.PartB.CellRows.Row15
import GerverSofa.KernelOnly.PartB.CellRows.Row16
import GerverSofa.KernelOnly.PartB.CellRows.Row17
import GerverSofa.KernelOnly.PartB.CellRows.Row18
import GerverSofa.KernelOnly.PartB.CellRows.Row19
import GerverSofa.KernelOnly.PartB.CellRows.Row20
import GerverSofa.KernelOnly.PartB.CellRows.Row21
import GerverSofa.KernelOnly.PartB.CellRows.Row22
import GerverSofa.KernelOnly.PartB.CellRows.Row23
import GerverSofa.KernelOnly.PartB.CellRows.Row24
import GerverSofa.KernelOnly.PartB.CellRows.Row25
import GerverSofa.KernelOnly.PartB.CellRows.Row26
import GerverSofa.KernelOnly.PartB.CellRows.Row27
import GerverSofa.KernelOnly.PartB.CellRows.Row28
import GerverSofa.KernelOnly.PartB.CellRows.Row29
import GerverSofa.KernelOnly.PartB.CellRows.Row30
import GerverSofa.KernelOnly.PartB.CellRows.Row31
import GerverSofa.KernelOnly.PartB.CellRows.Row32
import GerverSofa.KernelOnly.PartB.CellRows.Row33
import GerverSofa.KernelOnly.PartB.CellRows.Row34
import GerverSofa.KernelOnly.PartB.CellRows.Row35
import GerverSofa.KernelOnly.PartB.CellRows.Row36
import GerverSofa.KernelOnly.PartB.CellRows.Row37
import GerverSofa.KernelOnly.PartB.CellRows.Row38
import GerverSofa.KernelOnly.PartB.CellRows.Row39
import GerverSofa.KernelOnly.PartB.CellRows.Row40
import GerverSofa.KernelOnly.PartB.CellRows.Row41
import GerverSofa.KernelOnly.PartB.CellRows.Row42
import GerverSofa.KernelOnly.PartB.CellRows.Row43
import GerverSofa.KernelOnly.PartB.CellRows.Row44
import GerverSofa.KernelOnly.PartB.CellRows.Row45
import GerverSofa.KernelOnly.PartB.CellRows.Row46
import GerverSofa.KernelOnly.PartB.CellRows.Row47
import GerverSofa.KernelOnly.PartB.CellRows.Row48
import GerverSofa.KernelOnly.PartB.CellRows.Row49
import GerverSofa.KernelOnly.PartB.CellRows.Row50
import GerverSofa.KernelOnly.PartB.CellRows.Row51
import GerverSofa.KernelOnly.PartB.CellRows.Row52
import GerverSofa.KernelOnly.PartB.CellRows.Row53
import GerverSofa.KernelOnly.PartB.CellRows.Row54
import GerverSofa.KernelOnly.PartB.CellRows.Row55
import GerverSofa.KernelOnly.PartB.CellRows.Row56
import GerverSofa.KernelOnly.PartB.CellRows.Row57
import GerverSofa.KernelOnly.PartB.CellRows.Row58
import GerverSofa.KernelOnly.PartB.CellRows.Row59
import GerverSofa.KernelOnly.PartB.CellRows.Row60
import GerverSofa.KernelOnly.PartB.CellRows.Row61
import GerverSofa.KernelOnly.PartB.CellRows.Row62
import GerverSofa.KernelOnly.PartB.CellRows.Row63
import Mathlib.Tactic.FinCases

/-! Assembly of the 64 independently kernel-checked product-cell rows. -/

namespace GerverSofa.PartB

theorem all_cell_lower (i j : Cell) :
    targetQ < (guCellInterval i j).lo ∧
    targetQ < (gvCellInterval i j).lo := by
  fin_cases i
  · exact cell_row_00 j
  · exact cell_row_01 j
  · exact cell_row_02 j
  · exact cell_row_03 j
  · exact cell_row_04 j
  · exact cell_row_05 j
  · exact cell_row_06 j
  · exact cell_row_07 j
  · exact cell_row_08 j
  · exact cell_row_09 j
  · exact cell_row_10 j
  · exact cell_row_11 j
  · exact cell_row_12 j
  · exact cell_row_13 j
  · exact cell_row_14 j
  · exact cell_row_15 j
  · exact cell_row_16 j
  · exact cell_row_17 j
  · exact cell_row_18 j
  · exact cell_row_19 j
  · exact cell_row_20 j
  · exact cell_row_21 j
  · exact cell_row_22 j
  · exact cell_row_23 j
  · exact cell_row_24 j
  · exact cell_row_25 j
  · exact cell_row_26 j
  · exact cell_row_27 j
  · exact cell_row_28 j
  · exact cell_row_29 j
  · exact cell_row_30 j
  · exact cell_row_31 j
  · exact cell_row_32 j
  · exact cell_row_33 j
  · exact cell_row_34 j
  · exact cell_row_35 j
  · exact cell_row_36 j
  · exact cell_row_37 j
  · exact cell_row_38 j
  · exact cell_row_39 j
  · exact cell_row_40 j
  · exact cell_row_41 j
  · exact cell_row_42 j
  · exact cell_row_43 j
  · exact cell_row_44 j
  · exact cell_row_45 j
  · exact cell_row_46 j
  · exact cell_row_47 j
  · exact cell_row_48 j
  · exact cell_row_49 j
  · exact cell_row_50 j
  · exact cell_row_51 j
  · exact cell_row_52 j
  · exact cell_row_53 j
  · exact cell_row_54 j
  · exact cell_row_55 j
  · exact cell_row_56 j
  · exact cell_row_57 j
  · exact cell_row_58 j
  · exact cell_row_59 j
  · exact cell_row_60 j
  · exact cell_row_61 j
  · exact cell_row_62 j
  · exact cell_row_63 j

end GerverSofa.PartB
