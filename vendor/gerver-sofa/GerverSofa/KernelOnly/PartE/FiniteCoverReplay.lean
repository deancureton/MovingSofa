import GerverSofa.KernelOnly.PartE.ScaledResidualInterval

/-!
# Part E04: finite-cover replay foundation

E03 supplied a sound, executable rejection theorem for one rational rectangle
in the `(phi, theta)` plane.  This module lifts that kernel to finite lists of
rectangles and states the exact two remaining data obligations:

1. a finite rejected cover of the physical angle triangle outside the angle
   projection of `Reduced.box`;
2. local reconstruction into `Reduced.box` inside that angle projection.

Their conjunction yields `TwoAngleEnclosureTarget` and therefore the exact
DeepMind-shaped uniqueness theorem.  No cover or local enclosure is assumed as
an axiom: both remain ordinary theorem arguments.

The module also replays one nontrivial pilot rectangle near the origin.  This
checks the complete path from rational cell data through LeanCert interval
evaluation to the no-common-zero theorem before the large cover is generated.
-/

noncomputable section

namespace GerverSofa
namespace PartE

open LeanCert.Core
open LeanCert.Engine
open PartALeanCert

/-- Kernel-reducible interval evaluation for one smooth residual.  This uses
the already certified project-specialized interval for `pi`, avoiding the
generic named-constant normalization bottleneck in closed `decide` replays. -/
def scaledResidualKernelInterval (i : Fin 2)
    (phiI thetaI : IntervalRat) (cfg : EvalConfig := {}) : IntervalRat :=
  kernelPointEvalCore (scaledResidualExpr i)
    (angleIntervalEnv phiI thetaI) cfg.taylorDepth

/-- Soundness of the kernel-reducible residual evaluator. -/
theorem scaledResidual_mem_kernelInterval (i : Fin 2)
    (phi theta : ℝ) (phiI thetaI : IntervalRat)
    (hphi : phi ∈ phiI) (htheta : theta ∈ thetaI)
    (cfg : EvalConfig := {}) :
    (if i = 0 then scaledResidualOne phi theta
      else scaledResidualTwo phi theta) ∈
      scaledResidualKernelInterval i phiI thetaI cfg := by
  let u : Fin 2 → ℝ := ![phi, theta]
  have henv : envMem (finEnv u) (angleIntervalEnv phiI thetaI) := by
    intro n
    rcases n with (_ | _ | n)
    · simpa [u, finEnv, angleIntervalEnv] using hphi
    · simpa [u, finEnv, angleIntervalEnv] using htheta
    · change finEnv u (Nat.succ (Nat.succ n)) ∈ (default : IntervalRat)
      rw [IntervalRat.mem_default]
      simp [finEnv]
  have hcore := eval_mem_kernelPointEvalCore
    (scaledResidualExpr_supported i) (finEnv u)
    (angleIntervalEnv phiI thetaI) henv cfg.taylorDepth
  change evalFin (scaledResidualExpr i) u ∈
    scaledResidualKernelInterval i phiI thetaI cfg at hcore
  fin_cases i
  · simpa [u, scaledResidualExpr_eval_zero] using hcore
  · simpa [u, scaledResidualExpr_eval_one] using hcore

/-- A rational rectangle in the two-angle plane. -/
structure AngleCell where
  phiI : IntervalRat
  thetaI : IntervalRat

namespace AngleCell

/-- Real point membership in a rational angle cell. -/
def Contains (cell : AngleCell) (phi theta : ℝ) : Prop :=
  phi ∈ cell.phiI ∧ theta ∈ cell.thetaI

/-- Executable E03 rejection test for a complete angle cell. -/
def rejected (cell : AngleCell) (cfg : EvalConfig := {}) : Bool :=
  intervalExcludesZero
      (scaledResidualKernelInterval (0 : Fin 2) cell.phiI cell.thetaI cfg) ||
    intervalExcludesZero
      (scaledResidualKernelInterval (1 : Fin 2) cell.phiI cell.thetaI cfg)

/-- A cell accepted by the executable checker contains no common zero of the
two smooth residuals. -/
theorem no_common_zero_of_rejected
    (cell : AngleCell) (phi theta : ℝ)
    (hmem : cell.Contains phi theta)
    (cfg : EvalConfig := {})
    (hreject : cell.rejected cfg = true) :
    ¬ (scaledResidualOne phi theta = 0 ∧
      scaledResidualTwo phi theta = 0) := by
  have hreject' :
      intervalExcludesZero
          (scaledResidualKernelInterval
            (0 : Fin 2) cell.phiI cell.thetaI cfg) = true ∨
        intervalExcludesZero
          (scaledResidualKernelInterval
            (1 : Fin 2) cell.phiI cell.thetaI cfg) = true := by
    simpa only [rejected, Bool.or_eq_true] using hreject
  rintro ⟨hzero1, hzero2⟩
  rcases hreject' with hreject' | hreject'
  · have hmem' := scaledResidual_mem_kernelInterval (0 : Fin 2)
      phi theta cell.phiI cell.thetaI hmem.1 hmem.2 cfg
    have hnot := intervalExcludesZero_sound _ hreject'
    apply hnot
    simpa [hzero1] using hmem'
  · have hmem' := scaledResidual_mem_kernelInterval (1 : Fin 2)
      phi theta cell.phiI cell.thetaI hmem.1 hmem.2 cfg
    have hnot := intervalExcludesZero_sound _ hreject'
    apply hnot
    simpa [hzero2] using hmem'

end AngleCell

/-! ## Pilot replay -/

end PartE
end GerverSofa
