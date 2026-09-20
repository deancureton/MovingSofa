import GerverSofa.KernelOnly.PartE.E24KC2ProofHelpers

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31020 remaining=9 kind=T reason=R. -/

noncomputable section

namespace GerverSofa
namespace PartE

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000000 in
theorem e24KC2PhiBelowLeaf31020 :
    adaptiveCoverCheck 9 (childLL (childHL (childLL (childLH (childHH e24PhiBelowRoot))))) = true := by
  have h : ((childLL (childHL (childLL (childLH (childHH e24PhiBelowRoot)))))).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL (childHL (childLL (childLH (childHH e24PhiBelowRoot))))) h

end PartE
end GerverSofa
