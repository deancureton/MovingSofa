import GerverSofa.ExactReplay

/-!
# Named consequences of the frozen kernel-only certificate

These handles intentionally reason about the proof-carrying rational data, not
about re-running the expensive Krawczyk/grid search inside kernel reduction.
The latter remains available under `ExactReplay.executable*` for independent
diagnostic comparison.
-/

namespace GerverSofa.CertificateManifest

set_option maxRecDepth 100000 in
theorem machin_inside_declared :
    RatInterval.strictInsideB machinPi declaredPi = true := by
  simpa [piCheck] using piCheck_eq_true

end GerverSofa.CertificateManifest
