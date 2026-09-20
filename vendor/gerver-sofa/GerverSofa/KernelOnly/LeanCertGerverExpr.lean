import GerverSofa.KernelOnly.LeanCertGerverData
import GerverSofa.KernelOnly.LeanCertNamedConstAD

/-!
# LeanCert expression models for the normalized Gerver systems

These expressions use LeanCert's differentiable AD fragment plus exact
named mathematical constants.  `LeanCertNamedConstAD` supplies the one
missing soundness case for `namedConst` (derivative zero).
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

abbrev E := Expr

def ec (r : ℚ) : E := .const r
def ev (i : Nat) : E := .var i
def eadd (a b : E) : E := .add a b
def eneg (a : E) : E := .neg a
def esub (a b : E) : E := .add a (.neg b)
def emul (a b : E) : E := .mul a b
def escale (r : ℚ) (a : E) : E := .mul (.const r) a
def esin (a : E) : E := .sin a
def ecos (a : E) : E := .cos a
def epi : E := .namedConst .pi

def scaledVar (box : List RatInterval) (i : Nat) : E :=
  eadd (ec (boxMid box i)) (emul (ec (boxRad box i)) (ev i))

/-! ## Reduced 4D -/

def reducedExprList : List E :=
  let a := scaledVar ExactReplay.reducedInputBox 0
  let b := scaledVar ExactReplay.reducedInputBox 1
  let phi := scaledVar ExactReplay.reducedInputBox 2
  let theta := scaledVar ExactReplay.reducedInputBox 3
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let cp := ecos phi
  let sp := esin phi
  let ct := ecos theta
  let st := esin theta
  let delta := esub theta phi
  -- Keep the mathematical value exactly; AST need not match the old D object.
  let f1 :=
    eadd
      (esub
        (eadd
          (esub (emul a (esub ct cp)) (emul (escale 2 b) sp))
          (emul (esub delta one) ct))
        st)
      (eadd cp sp)
  let f2 :=
    eadd
      (esub
        (eadd
          (eadd
            (esub (emul a (eadd (escale 3 st) sp))
              (emul (escale 2 b) cp))
            (emul (escale 3 (esub delta one)) st))
          (escale 3 ct))
        sp)
      cp
  let f3 :=
    esub
      (eadd
        (esub (esub (emul a cp) sp) half)
        (emul half cp))
      (emul b sp)
  let f4 :=
    eadd
      (eadd
        (esub
          (esub
            (esub
              (esub (eadd a (escale (1 / 2) epi)) phi)
              theta)
            b)
          (ec 0))
        (emul (emul half delta) (eadd one a)))
      (emul (emul quarter delta) delta)
  List.cons f1 (List.cons f2 (List.cons f3 (List.cons f4 List.nil)))

def reducedExpr (i : Fin 4) : E :=
  reducedExprList.getD i.1 (ec 0)

/-! ## Direct 22D -/

def fv (i : Nat) : E := scaledVar ExactReplay.fullInputBox i

def phiE : E := fv 20
def thetaE : E := fv 21
def etaE : E := esub (escale (1 / 2) epi) thetaE
def tauE : E := esub (escale (1 / 2) epi) phiE

def rotE (t z1 z2 : E) : E × E :=
  let ct := ecos t
  let st := esin t
  (esub (emul ct z1) (emul st z2),
   eadd (emul st z1) (emul ct z2))

def pathPieceE (j : Nat) (t : E) : E × E :=
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let ct := ecos t
  let st := esin t
  let data : E × E × E × E :=
    if j = 1 then
      (esub (eadd (emul (fv 10) ct) (emul (fv 11) st)) one,
       esub (eadd (emul (eneg (fv 11)) ct) (emul (fv 10) st)) half,
       fv 0, fv 1)
    else if j = 2 then
      (eadd (eadd (emul (emul (eneg quarter) t) t) (emul (fv 12) t)) (fv 13),
       esub (esub (emul half t) (fv 12)) one,
       fv 2, fv 3)
    else if j = 3 then
      (esub (fv 14) t, eadd (fv 15) t, fv 4, fv 5)
    else if j = 4 then
      (esub (eadd (emul (eneg half) t) (fv 16)) one,
       eadd (eadd (emul (emul (eneg quarter) t) t) (emul (fv 16) t)) (fv 17),
       fv 6, fv 7)
    else
      (esub (eadd (emul (fv 18) ct) (emul (fv 19) st)) half,
       esub (eadd (emul (eneg (fv 19)) ct) (emul (fv 18) st)) one,
       fv 8, fv 9)
  let rr := rotE t data.1 data.2.1
  (eadd rr.1 data.2.2.1, eadd rr.2 data.2.2.2)

def alphaBetaE (j : Nat) (t : E) : E × E :=
  let one := ec 1
  let half := ec (1 / 2)
  let quarter := ec (1 / 4)
  let ct := ecos t
  let st := esin t
  if j = 1 then
    (eadd (eadd (emul (escale (-2) (fv 10)) st)
                 (emul (escale 2 (fv 11)) ct)) half,
     esub (eadd (emul (escale 2 (fv 10)) ct)
                 (emul (escale 2 (fv 11)) st)) one)
  else if j = 2 then
    (esub (eadd one (escale 2 (fv 12))) t,
     eadd (eadd (eadd (emul (emul (eneg quarter) t) t)
                       (emul (fv 12) t)) (fv 13)) half)
  else if j = 3 then
    (esub (esub (eneg one) (fv 15)) t,
     esub (eadd one (fv 14)) t)
  else if j = 4 then
    (esub (esub (esub (emul (emul quarter t) t)
                       (emul (fv 16) t)) (fv 17)) half,
     esub (esub (escale 2 (fv 16)) one) t)
  else
    (eadd (esub one (emul (escale 2 (fv 18)) st))
          (emul (escale 2 (fv 19)) ct),
     esub (eadd (emul (escale 2 (fv 18)) ct)
                 (emul (escale 2 (fv 19)) st)) half)

def pathPrimeE (j : Nat) (t : E) : E × E :=
  let ab := alphaBetaE j t
  rotE t ab.1 ab.2

def fullExprList : List E :=
  let halfPi := escale (1 / 2) epi
  let quarterPi := escale (1 / 4) epi
  let one := ec 1
  let quarter := ec (1 / 4)
  let first : List E := [
    esub (fv 18) (fv 10),
    eadd (fv 19) (fv 11),
    esub (eadd (fv 16) (fv 12)) quarterPi,
    esub (esub (fv 17) (fv 13))
      (emul quarterPi (esub (escale 2 (fv 12)) quarterPi)),
    eadd (esub (fv 15) (fv 14)) halfPi,
    eadd (esub (fv 0) one) (fv 10),
    esub (fv 1) quarter,
    eadd (fv 11) quarter
  ]
  let pairs : List ((E × E) × (E × E)) := [
    (pathPieceE 1 phiE, pathPieceE 2 phiE),
    (pathPrimeE 1 phiE, pathPrimeE 2 phiE),
    (pathPieceE 2 thetaE, pathPieceE 3 thetaE),
    (pathPrimeE 2 thetaE, pathPrimeE 3 thetaE),
    (pathPieceE 3 etaE, pathPieceE 4 etaE),
    (pathPieceE 4 tauE, pathPieceE 5 tauE)
  ]
  let matchEqs : List E := pairs.flatMap (fun lr =>
    List.cons (esub lr.1.1 lr.2.1)
      (List.cons (esub lr.1.2 lr.2.2) List.nil))
  let lhs := pathPieceE 1 phiE
  let xe := pathPieceE 3 etaE
  let ae := (alphaBetaE 3 etaE).1
  let be :=
    (esub xe.1 (emul ae (esin etaE)),
     eadd xe.2 (emul ae (ecos etaE)))
  first ++ matchEqs ++
    List.cons (esub lhs.1 be.1) (List.cons (esub lhs.2 be.2) List.nil)

def fullExpr (i : Fin 22) : E :=
  fullExprList.getD i.1 (ec 0)

/-- Purely syntactic support checks for the Gerver expression fragment. -/
theorem reducedExpr_supported :
    ∀ i : Fin 4, ADConstSupported (reducedExpr i) := by
  intro i
  apply checkADConstSupported_correct
  fin_cases i <;> decide

theorem fullExpr_supported :
    ∀ i : Fin 22, ADConstSupported (fullExpr i) := by
  intro i
  apply checkADConstSupported_correct
  fin_cases i <;> decide

end PartALeanCert
end GerverSofa
