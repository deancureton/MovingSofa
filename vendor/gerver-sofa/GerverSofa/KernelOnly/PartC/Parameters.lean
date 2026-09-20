import GerverSofa.KernelOnly.PartC.Definitions

/-!
# Frozen parameter and endpoint consequences for Part C
-/

noncomputable section

namespace GerverSofa
namespace PartC

 theorem params_mem : params ∈ Romik.box := PartB.params_mem

 theorem params_equations : Romik.Equations params := PartB.params_equations

 theorem switchOrder : Romik.SwitchOrder params := PartB.params_switchOrder

 theorem pathContinuous : Continuous (Romik.path params) := PartB.continuous_path

 theorem frameContinuous : SE2.ContinuousPath frame := PartB.continuous_frame

 theorem pathZero : Romik.path params 0 = (0, 0) := PartB.path_zero

 theorem pathEndYZero : (Romik.path params T).2 = 0 := by
  simpa [T] using
    (Romik.path_end_y_zero_of_mem_box_and_equations params_mem params_equations)

 theorem phi_bounds :
    ((1958868239504182093160893749 : ℝ) /
      50000000000000000000000000000) ≤ params.phi ∧
    params.phi ≤
      ((78354729580167283726435751 : ℝ) /
        2000000000000000000000000000) :=
  PartB.phi_bounds

 theorem theta_bounds :
    ((34065075469136244723692787727 : ℝ) /
      50000000000000000000000000000) ≤ params.theta ∧
    params.theta ≤
      ((34065075469136244723692787983 : ℝ) /
        50000000000000000000000000000) :=
  PartB.theta_bounds

end PartC
end GerverSofa
