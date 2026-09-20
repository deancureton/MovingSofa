import GerverSofa.KernelOnly.PartB.Definitions

/-!
# Part B parameter, matching and regularity certificate

Every theorem in this file is a direct consequence of the concrete Part A
unique zero.  No numerical computation is repeated.
-/

noncomputable section

namespace GerverSofa
namespace PartB

/-- The certified parameter vector lies in the direct Romik box. -/
theorem params_mem : params ∈ Romik.box := by
  simpa [params, Romik.vectorBox] using PartALeanCert.fullRoot_mem

/-- The certified parameter vector satisfies all 22 direct equations. -/
theorem params_equations : Romik.Equations params := by
  simpa [params, Romik.Equations, Romik.vectorSystem] using
    PartALeanCert.fullRoot_zero

/-- The four physical switches are correctly ordered. -/
theorem params_switchOrder : Romik.SwitchOrder params :=
  Romik.switchOrder_of_mem_box params_mem

/-- Positional matching at `φ`. -/
theorem match12 : Romik.path1 params params.phi = Romik.path2 params params.phi :=
  Romik.match_path12_of_equations params_equations

/-- Positional matching at `θ`. -/
theorem match23 : Romik.path2 params params.theta = Romik.path3 params params.theta :=
  Romik.match_path23_of_equations params_equations

/-- Positional matching at `π/2-θ`. -/
theorem match34 :
    Romik.path3 params (Real.pi / 2 - params.theta) =
      Romik.path4 params (Real.pi / 2 - params.theta) :=
  Romik.match_path34_of_equations params_equations

/-- Positional matching at `π/2-φ`. -/
theorem match45 :
    Romik.path4 params (Real.pi / 2 - params.phi) =
      Romik.path5 params (Real.pi / 2 - params.phi) :=
  Romik.match_path45_of_equations params_equations


/-- Global continuity of the literal five-phase path. -/
theorem continuous_path : Continuous (Romik.path params) :=
  Romik.continuous_path_of_mem_box_and_equations params_mem params_equations

/-- Global continuity of the associated rigid frame. -/
theorem continuous_frame : SE2.ContinuousPath (Romik.frame params) :=
  Romik.continuousPath_frame_of_path params continuous_path

/-- Exact initial normalization. -/
theorem path_zero : Romik.path params 0 = (0, 0) :=
  Romik.path_zero_of_mem_box_and_equations params_mem params_equations

/-- Clean exact bounds for the two independent switching angles. -/
theorem phi_bounds :
    ((1958868239504182093160893749 : ℝ) /
      50000000000000000000000000000) ≤ params.phi ∧
    params.phi ≤
      ((78354729580167283726435751 : ℝ) /
        2000000000000000000000000000) := by
  have hp := params_mem
  dsimp [params, Romik.vectorBox, Romik.box, qR] at hp ⊢
  aesop

theorem theta_bounds :
    ((34065075469136244723692787727 : ℝ) /
      50000000000000000000000000000) ≤ params.theta ∧
    params.theta ≤
      ((34065075469136244723692787983 : ℝ) /
        50000000000000000000000000000) := by
  have hp := params_mem
  dsimp [params, Romik.vectorBox, Romik.box, qR] at hp ⊢
  aesop

end PartB
end GerverSofa
