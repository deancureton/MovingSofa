import GerverSofa.KernelOnly.PartC.Stage3.SupportDirect

/-!
# Part C direct final assembly

This module bypasses the earlier conditional calculus/branch certificate layers.
The two outer-support fields are now concrete theorems.  What remains here is
exactly the six substantive topology/no-hidden facts; no additional certificate
wrapper is introduced.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage3

/-- Direct global geometry from the concrete support proof and the six exact
remaining topology/no-hidden statements. -/
def globalGeometryDirect
    (hU : NoHiddenCrossingU)
    (hV : NoHiddenCrossingV)
    (hboundary : frontier (Romik.niche params) = claimedNicheBoundary)
    (hniche : IsConnected (Romik.niche params))
    (hanchor : anchor ∈ G)
    (hG : IsConnected G) : GlobalGeometryCertificate :=
  { supportA := supportA_direct
    supportC := supportC_direct
    nicheTopology :=
      { noHiddenU := hU
        noHiddenV := hV
        boundary_eq := hboundary
        niche_connected := hniche }
    topology :=
      { anchor_mem := hanchor
        connected := hG } }

end Stage3
end PartC
end GerverSofa
