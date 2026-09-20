import GerverSofa.KernelOnly.PartE.E24AlignedLogic

/-! E24 kernel child certificate: PhiBelow/LL, remaining depth 13. -/

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24PhiBelowKernelLL :
    adaptiveCoverCheck 13 (childLL e24PhiBelowRoot) = true := by
  decide +kernel

end PartE
end GerverSofa
