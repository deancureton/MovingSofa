import GerverSofa.KernelOnly.PartB.CellSemantics
import Mathlib.Data.Nat.Find

/-!
# Coverage by the 64 exact mesh cells
-/

noncomputable section

namespace GerverSofa
namespace PartB

/-- Every physical angle belongs to one of the 64 closed cells between the
65 nodes `iπ/128`. -/
theorem exists_cell_cover {t : ℝ} (ht : t ∈ physicalInterval) :
    ∃ i : Cell, t ∈ cellSet i := by
  let P : Nat → Prop := fun n => t ≤ nodeTime (n + 1)
  have hnode64 : nodeTime 64 = Real.pi / 2 := by
    norm_num [nodeTime, nodeCoeff] <;> ring
  have h63 : P 63 := by
    change t ≤ nodeTime 64
    simpa [hnode64] using ht.2
  have hex : ∃ n : Nat, P n := ⟨63, h63⟩
  let n : Nat := Nat.find hex
  have hn63 : n ≤ 63 := Nat.find_min' hex h63
  have hn64 : n < 64 := by omega
  refine ⟨⟨n, hn64⟩, ?_⟩
  constructor
  · by_cases hn0 : n = 0
    · have hnode0 : nodeTime n = 0 := by
        rw [hn0]
        norm_num [nodeTime, nodeCoeff]
      simpa [cellSet, hnode0] using ht.1
    · have hpred : n - 1 < n := Nat.sub_one_lt hn0
      have hnot : ¬ P (n - 1) := Nat.find_min hex hpred
      have hlt : nodeTime ((n - 1) + 1) < t := lt_of_not_ge hnot
      have hsucc : (n - 1) + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn0)
      simpa [cellSet, hsucc] using hlt.le
  · exact Nat.find_spec hex

end PartB
end GerverSofa
