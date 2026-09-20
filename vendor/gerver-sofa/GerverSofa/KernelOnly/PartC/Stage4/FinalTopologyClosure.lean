import GerverSofa.KernelOnly.PartC.Stage4.SofaTopologyDirect

/-!
# Part C final unconditional closure

This is the only terminal assembly for Part C.  It contains no payload and no
new certificate interface.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

/-- Concrete global geometry certificate. -/
def globalGeometryCertificate : GlobalGeometryCertificate :=
  Stage3.globalGeometryDirect
    noHiddenU_direct noHiddenV_direct
    niche_frontier_direct niche_connected_direct
    anchor_mem_direct G_connected_direct

end Stage4
end PartC
end GerverSofa
