import GerverSofa.KernelOnly.PartB.AllRows
import GerverSofa.KernelOnly.PartB.CellCover

/-!
# Exact continuum support margins

The 64×64 cell certificate is now transported to every pair of physical
angles.  This is the semantic conclusion needed from Part B.
-/

noncomputable section

namespace GerverSofa
namespace PartB

/-- First global support inequality on the complete square. -/
theorem Gu_gt_target :
    ∀ s ∈ physicalInterval, ∀ t ∈ physicalInterval, target < Gu s t := by
  intro s hs t ht
  rcases exists_cell_cover hs with ⟨i, hsi⟩
  rcases exists_cell_cover ht with ⟨j, htj⟩
  have hsem := guCell_contains hsi htj hs ht
  have hrat := (all_cell_lower i j).1
  have hcast : (targetQ : ℝ) < ((guCellInterval i j).lo : ℝ) := by
    exact_mod_cast hrat
  simpa [target] using lt_of_lt_of_le hcast hsem.1

/-- Second global support inequality on the complete square. -/
theorem Gv_gt_target :
    ∀ s ∈ physicalInterval, ∀ t ∈ physicalInterval, target < Gv s t := by
  intro s hs t ht
  rcases exists_cell_cover hs with ⟨i, hsi⟩
  rcases exists_cell_cover ht with ⟨j, htj⟩
  have hsem := gvCell_contains hsi htj hs ht
  have hrat := (all_cell_lower i j).2
  have hcast : (targetQ : ℝ) < ((gvCellInterval i j).lo : ℝ) := by
    exact_mod_cast hrat
  simpa [target] using lt_of_lt_of_le hcast hsem.1

/-- Manuscript form of the two `0.171` inequalities. -/
theorem global_half_plane_margins :
    (∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (171 : ℝ) / 1000 < Gu s t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      ∀ t ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
        (171 : ℝ) / 1000 < Gv s t) := by
  constructor
  · simpa [physicalInterval, target, targetQ] using Gu_gt_target
  · simpa [physicalInterval, target, targetQ] using Gv_gt_target

end PartB
end GerverSofa
