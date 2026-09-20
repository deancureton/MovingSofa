import GerverSofa.KernelOnly.PartC.TopologySpec

/-!
# Global support and niche-topology certificate interfaces

The statements here encode the exact Part C geometry that is not allowed to be
hidden inside an arbitrary `connected` field: contact support, the two
no-hidden-crossing inequalities, and the claimed boundary of the niche.
-/

noncomputable section

namespace GerverSofa
namespace PartC

/-- First no-hidden-crossing inequality from the manuscript. -/
def NoHiddenCrossingU : Prop :=
  ∀ r ∈ Set.Icc params.phi T,
    ∀ t ∈ Set.Icc r T,
      0 ≤ dot (Romik.path params r - Romik.path params t) (u t)

/-- Reflected no-hidden-crossing inequality. -/
def NoHiddenCrossingV : Prop :=
  ∀ t ∈ Set.Icc 0 tau,
    ∀ r ∈ Set.Icc t tau,
      0 ≤ dot (Romik.path params r - Romik.path params t) (v t)

/-- Proof-carrying niche topology.  The boundary equality is set-valued; the
orientation and eighteen-piece count belong to the later Part D boundary
certificate. -/
structure NicheTopologyCertificate : Prop where
  noHiddenU : NoHiddenCrossingU
  noHiddenV : NoHiddenCrossingV
  boundary_eq : frontier (Romik.niche params) = claimedNicheBoundary
  niche_connected : IsConnected (Romik.niche params)

/-- Complete genuinely new geometry required in Part C. -/
structure GlobalGeometryCertificate : Prop where
  supportA : ∀ t ∈ Set.Icc (0 : ℝ) T, A t ∈ K
  supportC : ∀ t ∈ Set.Icc (0 : ℝ) T, C t ∈ K
  nicheTopology : NicheTopologyCertificate
  topology : TopologyCertificate

namespace GlobalGeometryCertificate

 theorem nonempty (cert : GlobalGeometryCertificate) : G.Nonempty :=
  cert.topology.nonempty

 theorem connected (cert : GlobalGeometryCertificate) : IsConnected G :=
  cert.topology.connected

end GlobalGeometryCertificate
end PartC
end GerverSofa
