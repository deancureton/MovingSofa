import GerverSofa.KernelOnly.LeanCertGerverExpr

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-- LeanCert's named π has exactly Mathlib's real value. -/
@[simp] theorem mathConst_pi_toReal :
    MathConst.pi.toReal = Real.pi := rfl

/-! Reduced semantic correspondence. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reducedExpr_eval_0 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (0 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (0 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (0 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, eneg, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]
  <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reducedExpr_eval_1 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (1 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (1 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (1 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, eneg, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]
  <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reducedExpr_eval_2 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (2 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (2 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (2 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, eneg, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]
  <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
theorem reducedExpr_eval_3 (u : Fin 4 → ℝ) :
    evalFin (reducedExpr (3 : Fin 4)) u =
      Reduced.vectorSystem (reducedAffine u) (3 : Fin 4) := by
  have hm := congrFun (Reduced.vectorSystem_eq_models (reducedAffine u)) (3 : Fin 4)
  rw [hm]
  simp [reducedExpr, reducedExprList, reducedAffine, affineFromBox,
    scaledVar, boxMid, boxRad, eadd, eneg, esub, emul, escale, esin, ecos,
    ec, ev, epi, evalFin, finEnv, Reduced.models, ScalarModel.var,
    ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
    ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos]
  <;> ring

theorem reduced_systemEval_eq (u : Fin 4 → ℝ) :
    systemEval reducedExpr u = Reduced.vectorSystem (reducedAffine u) := by
  funext i
  fin_cases i
  · exact reducedExpr_eval_0 u
  · exact reducedExpr_eval_1 u
  · exact reducedExpr_eval_2 u
  · exact reducedExpr_eval_3 u

/-! Full 22D semantic correspondence through the already proved public
`fullDualOutput_model_eq`.  This avoids unfolding the private pathPrime helper. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_0 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (0 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (0 : Fin 22) := by
  calc
    evalFin (fullExpr (0 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 0 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (0 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (0 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_1 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (1 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (1 : Fin 22) := by
  calc
    evalFin (fullExpr (1 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 1 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (1 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (1 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_2 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (2 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (2 : Fin 22) := by
  calc
    evalFin (fullExpr (2 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 2 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (2 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (2 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_3 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (3 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (3 : Fin 22) := by
  calc
    evalFin (fullExpr (3 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 3 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (3 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (3 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_4 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (4 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (4 : Fin 22) := by
  calc
    evalFin (fullExpr (4 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 4 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (4 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (4 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_5 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (5 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (5 : Fin 22) := by
  calc
    evalFin (fullExpr (5 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 5 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (5 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (5 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_6 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (6 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (6 : Fin 22) := by
  calc
    evalFin (fullExpr (6 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 6 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (6 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (6 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_7 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (7 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (7 : Fin 22) := by
  calc
    evalFin (fullExpr (7 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 7 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (7 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (7 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_8 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (8 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (8 : Fin 22) := by
  calc
    evalFin (fullExpr (8 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 8 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (8 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (8 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_9 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (9 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (9 : Fin 22) := by
  calc
    evalFin (fullExpr (9 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 9 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (9 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (9 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_10 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (10 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (10 : Fin 22) := by
  calc
    evalFin (fullExpr (10 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 10 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (10 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (10 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_11 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (11 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (11 : Fin 22) := by
  calc
    evalFin (fullExpr (11 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 11 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (11 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (11 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_12 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (12 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (12 : Fin 22) := by
  calc
    evalFin (fullExpr (12 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 12 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (12 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (12 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_13 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (13 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (13 : Fin 22) := by
  calc
    evalFin (fullExpr (13 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 13 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (13 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (13 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_14 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (14 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (14 : Fin 22) := by
  calc
    evalFin (fullExpr (14 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 14 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (14 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (14 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_15 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (15 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (15 : Fin 22) := by
  calc
    evalFin (fullExpr (15 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 15 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (15 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (15 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_16 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (16 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (16 : Fin 22) := by
  calc
    evalFin (fullExpr (16 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 16 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (16 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (16 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_17 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (17 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (17 : Fin 22) := by
  calc
    evalFin (fullExpr (17 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 17 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (17 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (17 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_18 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (18 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (18 : Fin 22) := by
  calc
    evalFin (fullExpr (18 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 18 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (18 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (18 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_19 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (19 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (19 : Fin 22) := by
  calc
    evalFin (fullExpr (19 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 19 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (19 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (19 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_20 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (20 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (20 : Fin 22) := by
  calc
    evalFin (fullExpr (20 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 20 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (20 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (20 : Fin 22)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1800000 in
theorem fullExpr_eval_21 (u : Fin 22 → ℝ) :
    evalFin (fullExpr (21 : Fin 22)) u =
      Romik.vectorSystem (fullAffine u) (21 : Fin 22) := by
  calc
    evalFin (fullExpr (21 : Fin 22)) u =
        ((Romik.fullDualOutput.getD 21 (Romik.SoundDual.pointConst 0)).model.value
          (fullAffine u)) := by
      simp [fullExpr, fullExprList, fv, phiE, thetaE, etaE, tauE,
        rotE, pathPieceE, alphaBetaE, pathPrimeE,
        fullAffine, affineFromBox, scaledVar, boxMid, boxRad,
        eadd, eneg, esub, emul, escale, esin, ecos, ec, ev, epi,
        evalFin, finEnv,
        Romik.fullDualOutput, Romik.fullVars, Romik.inputDual, Romik.piDual,
        Romik.phiDual, Romik.thetaDual, Romik.etaDual, Romik.tauDual,
        Romik.rotDual, Romik.pathPieceDual, Romik.alphaBetaDual,
        Romik.pathPrimeDual]
      <;> ring
    _ = Romik.vectorSystem (fullAffine u) (21 : Fin 22) := by
      exact congrFun (Romik.fullDualOutput_model_eq (fullAffine u)) (21 : Fin 22)

theorem full_systemEval_eq (u : Fin 22 → ℝ) :
    systemEval fullExpr u = Romik.vectorSystem (fullAffine u) := by
  funext i
  fin_cases i
  · exact fullExpr_eval_0 u
  · exact fullExpr_eval_1 u
  · exact fullExpr_eval_2 u
  · exact fullExpr_eval_3 u
  · exact fullExpr_eval_4 u
  · exact fullExpr_eval_5 u
  · exact fullExpr_eval_6 u
  · exact fullExpr_eval_7 u
  · exact fullExpr_eval_8 u
  · exact fullExpr_eval_9 u
  · exact fullExpr_eval_10 u
  · exact fullExpr_eval_11 u
  · exact fullExpr_eval_12 u
  · exact fullExpr_eval_13 u
  · exact fullExpr_eval_14 u
  · exact fullExpr_eval_15 u
  · exact fullExpr_eval_16 u
  · exact fullExpr_eval_17 u
  · exact fullExpr_eval_18 u
  · exact fullExpr_eval_19 u
  · exact fullExpr_eval_20 u
  · exact fullExpr_eval_21 u

/-! ## Box transport -/

theorem reduced_box_strict :
    ∀ i : Fin 4,
      (ExactReplay.getI ExactReplay.reducedInputBox i.1).lo <
      (ExactReplay.getI ExactReplay.reducedInputBox i.1).hi := by
  intro i
  fin_cases i <;>
    norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4,
      CertificateManifest.q, ExactReplay.getI]

theorem full_box_strict :
    ∀ i : Fin 22,
      (ExactReplay.getI ExactReplay.fullInputBox i.1).lo <
      (ExactReplay.getI ExactReplay.fullInputBox i.1).hi := by
  intro i
  fin_cases i <;>
    norm_num [ExactReplay.fullInputBox, CertificateManifest.z22,
      CertificateManifest.q, ExactReplay.getI]

theorem affine_mem_interval
    (z : RatInterval) (hz : z.lo < z.hi) (u : ℝ)
    (hu : (-1 : ℝ) ≤ u ∧ u ≤ 1) :
    RatInterval.Contains z
      ((((z.lo + z.hi) / 2 : ℚ) : ℝ) +
       ((((z.hi - z.lo) / 2 : ℚ) : ℝ) * u)) := by
  have hzR : (z.lo : ℝ) < (z.hi : ℝ) := by
    exact_mod_cast hz
  have hrad : 0 ≤ ((z.hi : ℝ) - (z.lo : ℝ)) / 2 := by
    linarith
  constructor
  · push_cast
    calc
      (z.lo : ℝ) =
          ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * (-1) := by ring
      _ ≤ ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * u := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hu.1 hrad)
          (((z.lo : ℝ) + (z.hi : ℝ)) / 2)
  · push_cast
    calc
      ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * u
          ≤ ((z.lo : ℝ) + (z.hi : ℝ)) / 2 +
            (((z.hi : ℝ) - (z.lo : ℝ)) / 2) * 1 := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hu.2 hrad)
          (((z.lo : ℝ) + (z.hi : ℝ)) / 2)
      _ = (z.hi : ℝ) := by ring

theorem normalize_mem_unit
    (z : RatInterval) (hz : z.lo < z.hi) (x : ℝ)
    (hx : RatInterval.Contains z x) :
    ((x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
      ((((z.hi - z.lo) / 2 : ℚ) : ℝ))) ∈
      (unitBox (n := 1) (0 : Fin 1)) := by
  have hrQ : (0 : ℚ) < (z.hi - z.lo) / 2 := by
    linarith
  have hr : (0 : ℝ) < ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) := by
    exact_mod_cast hrQ
  have hbounds :
      (-1 : ℝ) ≤
          (x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
            ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) ∧
        (x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
            ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) ≤ 1 := by
    constructor
    · rw [le_div_iff₀ hr]
      push_cast
      have hxlo := hx.1
      linarith
    · rw [div_le_iff₀ hr]
      push_cast
      have hxhi := hx.2
      linarith
  simpa [unitBox, IntervalRat.mem_def] using hbounds

theorem affine_normalize_coord
    (z : RatInterval) (hz : z.lo < z.hi) (x : ℝ) :
    ((((z.lo + z.hi) / 2 : ℚ) : ℝ) +
      ((((z.hi - z.lo) / 2 : ℚ) : ℝ) *
        ((x - ((((z.lo + z.hi) / 2 : ℚ) : ℝ))) /
          ((((z.hi - z.lo) / 2 : ℚ) : ℝ))))) = x := by
  have hrQ : ((z.hi - z.lo) / 2 : ℚ) ≠ 0 := by
    have : (0 : ℚ) < (z.hi - z.lo) / 2 := by linarith
    exact ne_of_gt this
  have hr : ((((z.hi - z.lo) / 2 : ℚ) : ℝ)) ≠ 0 := by
    exact_mod_cast hrQ
  field_simp
  ring

theorem reducedAffine_mem {u : Fin 4 → ℝ}
    (hu : FinBoxMem u (unitBox (n := 4))) :
    reducedAffine u ∈ Reduced.vectorBox := by
  apply (Reduced.inputBox_exact _).2
  refine ⟨by norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4], ?_⟩
  intro i
  simpa [reducedAffine, affineFromBox, boxMid, boxRad,
    ExactReplay.getI, ExactReplay.zeroI, RatInterval.point] using
    affine_mem_interval
      (ExactReplay.getI ExactReplay.reducedInputBox i.1)
      (reduced_box_strict i) (u i) (by
        simpa [unitBox, IntervalRat.mem_def] using hu i)

theorem fullAffine_mem {u : Fin 22 → ℝ}
    (hu : FinBoxMem u (unitBox (n := 22))) :
    fullAffine u ∈ Romik.vectorBox := by
  apply (Romik.inputBox_exact _).2
  refine ⟨by norm_num [ExactReplay.fullInputBox, CertificateManifest.z22], ?_⟩
  intro i
  simpa [fullAffine, affineFromBox, boxMid, boxRad,
    ExactReplay.getI, ExactReplay.zeroI, RatInterval.point] using
    affine_mem_interval
      (ExactReplay.getI ExactReplay.fullInputBox i.1)
      (full_box_strict i) (u i) (by
        simpa [unitBox, IntervalRat.mem_def] using hu i)

theorem reducedNormalize_mem {x : Fin 4 → ℝ}
    (hx : x ∈ Reduced.vectorBox) :
    FinBoxMem (reducedNormalize x) (unitBox (n := 4)) := by
  have henc := (Reduced.inputBox_exact x).1 hx
  intro i
  have hi := henc.2 i
  have h := normalize_mem_unit
    (ExactReplay.getI ExactReplay.reducedInputBox i.1)
    (reduced_box_strict i) (x i) hi
  simpa [reducedNormalize, normalizeToBox, boxMid, boxRad, unitBox,
    IntervalRat.mem_def] using h

theorem reducedAffine_normalize (x : Fin 4 → ℝ) :
    reducedAffine (reducedNormalize x) = x := by
  funext i
  simpa [reducedAffine, reducedNormalize, affineFromBox, normalizeToBox,
    boxMid, boxRad] using
      affine_normalize_coord
        (ExactReplay.getI ExactReplay.reducedInputBox i.1)
        (reduced_box_strict i) (x i)

end PartALeanCert
end GerverSofa
