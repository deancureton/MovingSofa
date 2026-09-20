import GerverSofa.KrawczykSpec
import GerverSofa.Boxes

/-!
# Coordinate equivalences for the certified systems

The executable interval layer works with `Fin n → ℝ`, while the manuscript
layer uses named parameter records.  These equivalences are the explicit,
kernel-checked bridge between the two representations.
-/

noncomputable section

namespace GerverSofa

namespace Reduced

/-- Named reduced parameters as a four-vector in manuscript order. -/
def coordEquiv : Params ≃ Vec 4 where
  toFun p := ![p.a, p.b, p.phi, p.theta]
  invFun x :=
    { a := x 0
      b := x 1
      phi := x 2
      theta := x 3 }
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Reduced system expressed in finite-vector coordinates. -/
def vectorSystem (x : Vec 4) : Vec 4 :=
  system (coordEquiv.symm x)

/-- The reduced parameter box expressed in finite-vector coordinates. -/
def vectorBox : Set (Vec 4) :=
  {x | coordEquiv.symm x ∈ box}

@[simp] theorem mem_vectorBox_iff (x : Vec 4) :
    x ∈ vectorBox ↔ coordEquiv.symm x ∈ box := Iff.rfl

/-- Transport a finite-vector uniqueness certificate back to named reduced
parameters. -/
def uniqueSolutionOfVector
    (c : CertifiedUniqueZero vectorSystem vectorBox) :
    CertifiedUniqueSolution Equations box where
  solution := coordEquiv.symm c.solution
  solution_mem := by
    simpa [vectorBox] using c.solution_mem
  satisfies := by
    simpa [Equations, vectorSystem] using c.satisfies
  unique y hy hEq := by
    have hyVec : coordEquiv y ∈ vectorBox := by
      simpa [vectorBox] using hy
    have hzero : vectorSystem (coordEquiv y) = 0 := by
      simpa [Equations, vectorSystem] using hEq
    have h := c.unique (coordEquiv y) hyVec hzero
    apply coordEquiv.injective
    simpa using h

end Reduced

namespace Romik

/-- Named Romik parameters as a 22-vector in verifier order. -/
def coordEquiv : Params ≃ Vec 22 where
  toFun p := ![
    p.k11, p.k12, p.k21, p.k22, p.k31, p.k32, p.k41, p.k42, p.k51, p.k52,
    p.a1, p.a2, p.b1, p.b2, p.c1, p.c2, p.d1, p.d2, p.e1, p.e2,
    p.phi, p.theta
  ]
  invFun x :=
    { k11 := x 0
      k12 := x 1
      k21 := x 2
      k22 := x 3
      k31 := x 4
      k32 := x 5
      k41 := x 6
      k42 := x 7
      k51 := x 8
      k52 := x 9
      a1 := x 10
      a2 := x 11
      b1 := x 12
      b2 := x 13
      c1 := x 14
      c2 := x 15
      d1 := x 16
      d2 := x 17
      e1 := x 18
      e2 := x 19
      phi := x 20
      theta := x 21 }
  left_inv p := by
    cases p
    rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl

/-- Direct Romik system expressed in finite-vector coordinates. -/
def vectorSystem (x : Vec 22) : Vec 22 :=
  system (coordEquiv.symm x)

/-- The direct Romik box expressed in finite-vector coordinates. -/
def vectorBox : Set (Vec 22) :=
  {x | coordEquiv.symm x ∈ box}

@[simp] theorem mem_vectorBox_iff (x : Vec 22) :
    x ∈ vectorBox ↔ coordEquiv.symm x ∈ box := Iff.rfl

/-- Transport a finite-vector uniqueness certificate back to named Romik
parameters. -/
def uniqueSolutionOfVector
    (c : CertifiedUniqueZero vectorSystem vectorBox) :
    CertifiedUniqueSolution Equations box where
  solution := coordEquiv.symm c.solution
  solution_mem := by
    simpa [vectorBox] using c.solution_mem
  satisfies := by
    simpa [Equations, vectorSystem] using c.satisfies
  unique y hy hEq := by
    have hyVec : coordEquiv y ∈ vectorBox := by
      simpa [vectorBox] using hy
    have hzero : vectorSystem (coordEquiv y) = 0 := by
      simpa [Equations, vectorSystem] using hEq
    have h := c.unique (coordEquiv y) hyVec hzero
    apply coordEquiv.injective
    simpa using h

end Romik

end GerverSofa
