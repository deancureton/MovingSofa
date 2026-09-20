import GerverSofa.KernelOnly.ADCoreSoundness

/-!
# Concrete interval-AD soundness for the reduced 4D system

This module instantiates the constructor-level AD theorem with equations
(F1)--(F4), proves that the frozen rational list is exactly the manuscript box,
and identifies the four smooth scalar models with `Reduced.vectorSystem`.
-/

noncomputable section

namespace GerverSofa

open RatInterval

namespace Reduced

/-- The four frozen rational intervals are exactly the named reduced box. -/
theorem inputBox_exact (x : Vec 4) :
    x ∈ vectorBox ↔ EnclosesVec ExactReplay.reducedInputBox x := by
  constructor
  · intro hx
    change coordEquiv.symm x ∈ box at hx
    dsimp [box, qR, coordEquiv] at hx
    refine ⟨?_, ?_⟩
    · norm_num [ExactReplay.reducedInputBox, CertificateManifest.x4]
    · intro i
      fin_cases i <;>
        simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
          CertificateManifest.q, ExactReplay.getI, RatInterval.Contains] <;>
        aesop
  · rintro ⟨hlen, hx⟩
    change coordEquiv.symm x ∈ box
    dsimp [box, qR, coordEquiv]
    have h0 := hx (0 : Fin 4)
    have h1 := hx (1 : Fin 4)
    have h2 := hx (2 : Fin 4)
    have h3 := hx (3 : Fin 4)
    simp [ExactReplay.reducedInputBox, CertificateManifest.x4,
      CertificateManifest.q, RatInterval.Contains] at h0 h1 h2 h3
    aesop

/-- Scalar models matching the four reduced equations. -/
def models : Fin 4 → ScalarModel 4 :=
  let a := ScalarModel.var 4 (0 : Fin 4)
  let b := ScalarModel.var 4 (1 : Fin 4)
  let phi := ScalarModel.var 4 (2 : Fin 4)
  let theta := ScalarModel.var 4 (3 : Fin 4)
  let one := ScalarModel.const 4 1
  let half := ScalarModel.const 4 (1 / 2 : ℝ)
  let quarter := ScalarModel.const 4 (1 / 4 : ℝ)
  let piM := ScalarModel.const 4 Real.pi
  let cp := ScalarModel.cos phi
  let sp := ScalarModel.sin phi
  let ct := ScalarModel.cos theta
  let st := ScalarModel.sin theta
  let delta := theta - phi
  let f1 := a * (ct - cp) - (2 : ℚ) * b * sp + (delta - one) * ct - st + cp + sp
  let f2 := a * ((3 : ℚ) * st + sp) - (2 : ℚ) * b * cp
    + (3 : ℚ) * (delta - one) * st + (3 : ℚ) * ct - sp + cp
  let f3 := a * cp - sp - half + half * cp - b * sp
  let f4 := a + (1 / 2 : ℚ) * piM - phi - theta - b
    + half * delta * (one + a) + quarter * delta * delta
  ![f1, f2, f3, f4]

/-- The model values are definitionally the manuscript reduced system after
coordinate conversion. -/
theorem vectorSystem_eq_models (x : Vec 4) :
    vectorSystem x = fun i => (models i).value x := by
  funext i
  fin_cases i <;>
    simp [vectorSystem, coordEquiv, system, models, ScalarModel.var,
      ScalarModel.const, ScalarModel.add, ScalarModel.neg, ScalarModel.sub,
      ScalarModel.mul, ScalarModel.scale, ScalarModel.sin, ScalarModel.cos] <;>
    ring

end Reduced

end GerverSofa
