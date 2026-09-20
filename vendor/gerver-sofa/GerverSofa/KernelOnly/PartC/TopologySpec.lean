import GerverSofa.KernelOnly.PartC.BaseGeometry

/-!
# Exact topology target for the concrete Gerver set

This file states, but does not postulate, the two genuinely remaining
set-theoretic obligations.  A later concrete proof must construct a value of
`TopologyCertificate`; until then Part C cannot close.
-/

noncomputable section

namespace GerverSofa
namespace PartC

/-- Direct topology certificate with the manuscript's explicit endpoint
support witness, rather than an anonymous existential. -/
structure TopologyCertificate : Prop where
  anchor_mem : anchor ∈ G
  connected : IsConnected G

namespace TopologyCertificate

 theorem nonempty (cert : TopologyCertificate) : G.Nonempty :=
  ⟨anchor, cert.anchor_mem⟩

end TopologyCertificate
end PartC
end GerverSofa
