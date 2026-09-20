import GerverSofa.KernelOnly.PartE.E24AlignedLogic

/-! E24 kernel child certificate: PhiBelow/LH, remaining depth 13. -/

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24PhiBelowKernelLH :
    adaptiveCoverCheck 13 (childLH e24PhiBelowRoot) = true := by
  decide +kernel

end PartE
end GerverSofa
