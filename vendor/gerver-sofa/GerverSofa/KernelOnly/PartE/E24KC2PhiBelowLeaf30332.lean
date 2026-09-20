import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30332 remaining=9 kind=F reason=ADAPTIVE. -/

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf30332 :
    adaptiveCoverCheck 9 (childHL (childHH (childHH (childLL (childHH e24PhiBelowRoot))))) = true := by
  decide +kernel

end PartE
end GerverSofa
