import GerverSofa.KernelOnly.PartE.E24AlignedLogic

/-!
# E24KC2 proof helpers

The discovery phase is intentionally outside the trusted chain.  It only chooses
where to stop splitting and which terminal reason to claim.

Every claimed leaf is then checked by the Lean kernel:
* physically irrelevant leaf -> `physicallyIrrelevant cell = true`;
* local leaf -> `cellInsideLocal cell = true`;
* interval-rejected leaf -> `cell.rejected = true`;
* unresolved frontier -> the old adaptive checker, but with remaining depth <= 9.

These lemmas lift a primitive terminal fact to an `adaptiveCoverCheck` fact at
arbitrary remaining depth without asking the kernel to explore the subtree.
-/

noncomputable section

namespace GerverSofa
namespace PartE

theorem adaptiveCoverCheck_true_of_physicallyIrrelevant
    (depth : Nat) (cell : AngleCell)
    (h : physicallyIrrelevant cell = true) :
    adaptiveCoverCheck depth cell = true := by
  cases depth <;> simp [adaptiveCoverCheck, h]

theorem adaptiveCoverCheck_true_of_rejected
    (depth : Nat) (cell : AngleCell)
    (h : cell.rejected = true) :
    adaptiveCoverCheck depth cell = true := by
  by_cases hirr : physicallyIrrelevant cell = true
  · cases depth <;> simp [adaptiveCoverCheck, hirr]
  · by_cases hlocal : cellInsideLocal cell = true
    · cases depth <;> simp [adaptiveCoverCheck, hirr, hlocal]
    · cases depth <;> simp [adaptiveCoverCheck, hirr, hlocal, h]

end PartE
end GerverSofa
