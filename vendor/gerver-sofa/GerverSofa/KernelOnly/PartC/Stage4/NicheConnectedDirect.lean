import GerverSofa.KernelOnly.PartC.Stage4.NicheFrontierTopology

/-!
# Part C Stage 4: connectedness of the literal niche

The independent vertical-fill module proves connectedness of the certified
three-piece region.  Once the boundary layer identifies that region with the
literal niche, connectedness is immediate.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set

/-- Concrete connectedness of the literal niche. -/
theorem niche_connected_direct : IsConnected (Romik.niche params) := by
  rw [niche_eq_certifiedNicheRegion]
  exact certifiedNicheRegion_connected

end Stage4
end PartC
end GerverSofa
