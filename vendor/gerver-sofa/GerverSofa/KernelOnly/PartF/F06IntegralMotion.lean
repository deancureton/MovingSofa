import GerverSofa.KernelOnly.PartF.F06ParameterIdentification
import GerverSofa.KernelOnly.PartF.F04IntegralRepresentation

/-!
# F06: unconditional motion bridge for the literal integral construction

This is the translate-then-rotate body model defined in Part F, with the
canonical Euclidean orientation. It does not silently replace the current
upstream rotateTranslate definition discussed in issue #5270.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace GerverSofa.PartF.Integrals

open Phases Coordinates

theorem certified_dictionary_eq_params : dictionary certified = PartC.params :=
  Parameters.dictionary_eq_full_certified

theorem certified_integral_rotation_to_full (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    rotation t (toPlane (path certified t)) = toPlane (Romik.path PartC.params t) := by
  rw [certified_integral_rotation t ht, certified_dictionary_eq_params]

theorem integral_sofa_eq_certified :
    bodySofa (fun t => toPlane (path certified t))
        Model.horizontalHallway Model.verticalHallway Model.hallway =
      EuclideanMotion.sofa :=
  integral_sofa_eq_certified_of_dictionary certified_dictionary_eq_params

end GerverSofa.PartF.Integrals
