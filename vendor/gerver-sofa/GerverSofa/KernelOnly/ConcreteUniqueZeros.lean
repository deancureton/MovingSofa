import GerverSofa.KernelOnly.LeanCertGerverNumerics

noncomputable section

namespace GerverSofa

open LeanCert.Engine

namespace PartALeanCert

def reducedRootU : Fin 4 → ℝ := Classical.choose reduced_unique_scaled
def fullRootU : Fin 22 → ℝ := Classical.choose full_unique_scaled

theorem reducedRootU_spec :
    FinBoxMem reducedRootU (unitBox (n := 4)) ∧
      SystemZero reducedExpr reducedRootU :=
  (Classical.choose_spec reduced_unique_scaled).1

theorem fullRootU_spec :
    FinBoxMem fullRootU (unitBox (n := 22)) ∧
      SystemZero fullExpr fullRootU :=
  (Classical.choose_spec full_unique_scaled).1

def reducedRoot : Vec 4 := reducedAffine reducedRootU
def fullRoot : Vec 22 := fullAffine fullRootU

theorem reducedRoot_mem : reducedRoot ∈ Reduced.vectorBox :=
  reducedAffine_mem reducedRootU_spec.1

theorem fullRoot_mem : fullRoot ∈ Romik.vectorBox :=
  fullAffine_mem fullRootU_spec.1

theorem reducedRoot_zero : Reduced.vectorSystem reducedRoot = 0 := by
  have hz : systemEval reducedExpr reducedRootU = 0 := by
    funext i
    exact reducedRootU_spec.2 i
  rw [reduced_systemEval_eq] at hz
  exact hz

theorem fullRoot_zero : Romik.vectorSystem fullRoot = 0 := by
  have hz : systemEval fullExpr fullRootU = 0 := by
    funext i
    exact fullRootU_spec.2 i
  rw [full_systemEval_eq] at hz
  exact hz

/-- Concrete reduced 4D unique zero — no assumptions. -/
def reducedCertifiedUniqueZero :
    CertifiedUniqueZero Reduced.vectorSystem Reduced.vectorBox where
  solution := reducedRoot
  solution_mem := reducedRoot_mem
  satisfies := reducedRoot_zero
  unique := by
    intro y hy hzero
    let uy := reducedNormalize y
    have huy : FinBoxMem uy (unitBox (n := 4)) := reducedNormalize_mem hy
    have hsys : SystemZero reducedExpr uy := by
      intro i
      change systemEval reducedExpr uy i = 0
      calc
        systemEval reducedExpr uy i =
            Reduced.vectorSystem (reducedAffine uy) i :=
          congrFun (reduced_systemEval_eq uy) i
        _ = Reduced.vectorSystem y i := by
          rw [show reducedAffine uy = y by
            simpa [uy] using reducedAffine_normalize y]
        _ = 0 := congrFun hzero i
    have huEq : uy = reducedRootU := by
      exact reduced_unique_scaled.unique ⟨huy, hsys⟩ reducedRootU_spec
    calc
      y = reducedAffine uy := by symm; exact reducedAffine_normalize y
      _ = reducedAffine reducedRootU := by rw [huEq]
      _ = reducedRoot := rfl

/-- Existing manuscript-level unique-solution interfaces are now discharged
by concrete numerical certificates rather than assumptions. -/
def reducedCertifiedUniqueSolution :
    CertifiedUniqueSolution Reduced.Equations Reduced.box :=
  Reduced.uniqueSolutionOfVector reducedCertifiedUniqueZero

end PartALeanCert

end GerverSofa
