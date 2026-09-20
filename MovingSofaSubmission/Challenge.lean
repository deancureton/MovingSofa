/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# The moving sofa problem: statements to be proved

The definitions and both theorem statements are copied from
`FormalConjectures/Wikipedia/MovingSofa.lean` in google-deepmind/formal-conjectures at commit
`ddfbaf90f4482030d88aae5233fe933874296a23`. The plane notation and instances are inlined so that
only Mathlib is imported, the topology instance on `E(2)` is given a name, and docstrings are
added to the definitions that had none. The statement that Gerver's sofa is the unique
maximizer, which is open, is not included.

`MovingSofaSubmission.Solution` proves all three theorems: `ABφθSpec.existsUnique`, that Gerver's
four constants exist and are unique; `isMovingSofa_gerversSofa`, that Gerver's sofa can be moved
around the corner; and `sofaConstant_eq_volume_gerversSofa`, that the largest area of a moving
sofa is the area of Gerver's sofa.

## References

* [Ge92] J. L. Gerver, *On moving a sofa around a corner*, Geometriae Dedicata 42 (1992).
* [Ro18] D. Romik, *Differential equations and exact solutions in the moving sofa problem*,
  Experimental Mathematics 27 (2018).
* J. Baek, *Optimality of Gerver's sofa*, arXiv:2411.19826.
-/

noncomputable section

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

open scoped EuclideanGeometry

/-- The plane `ℝ²` with the orientation of its standard basis, so that rotations are
counterclockwise. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Module.Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- The plane `ℝ²` has dimension two. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

namespace MovingSofa

open Topology
open scoped Real unitInterval EuclideanGeometry

/-- The **horizontal side** of the hallway is $(-\infty, 1] \times [0, 1]$. -/
def horizontalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1)}

/-- The **vertical side** of the hallway is $[0, 1] \times (-\infty, 1]$. -/
def verticalHallway : Set ℝ² := {!₂[x, y] | (x) (y) (_ : 0 ≤ x ∧ x ≤ 1 ∧ y ≤ 1)}

/-- The **hallway** is the union of its horizontal and vertical sides. -/
def hallway : Set ℝ² := horizontalHallway ∪ verticalHallway

scoped notation "E(2)" => ℝ² ≃ᵃⁱ[ℝ] ℝ²

/-- The topology on the isometry group `E(2)`, induced from the continuous affine maps of the
plane. -/
instance rigidMotionTopology : TopologicalSpace E(2) :=
  .induced (·.toAffineIsometry.toContinuousAffineMap) inferInstance

/--
A connected closed set $s$ is a **moving sofa** according to a rigid motion $m:I\to\mathrm{SE}(2)$,
if the sofa is initially in the horizontal side of the hallway and ends up in the vertical side.
Here, since $\mathrm{SE}(2)$ is not in Mathlib yet, we use $\mathrm{E}(2)$ and rely on continuity
and $m(0) = \mathrm{id}$ to ensure $m$ is in $\mathrm{SE}(2)$.
-/
structure IsMovingSofa (s : Set ℝ²) (m : I → E(2)) : Prop where
  isConnected : IsConnected s
  isClosed : IsClosed s
  continuous : Continuous m
  zero : m 0 = .refl ℝ ℝ²
  initial : s ⊆ horizontalHallway
  subset_hallway : ∀ t, m t '' s ⊆ hallway
  final : m 1 '' s ⊆ verticalHallway

/--
The rigid motion that translates by $p$ and then rotates counterclockwise by $\alpha$.
Note that [Ge92] used this definition while [Ro18] used rotation first and then translation.
-/
def rotateTranslate (α : Real.Angle) (p : ℝ²) : E(2) :=
  (AffineIsometryEquiv.vaddConst ℝ p).trans
    (EuclideanGeometry.o.rotation α).toAffineIsometryEquiv

/--
The sofa according to a rotation path $p : [0, \pi/2] \to \mathbb{R}^2$ as in [Ge92] is the
intersection over $\alpha \in [0, \pi/2]$ of hallways each translated by $p(\alpha)$ and then
rotated by $\alpha$, with the special cases that the hallway at $0$ is the horizontal side
and the hallway at $\pi/2$ is the vertical side.
-/
def sofaOfRotateTranslatePath (p : ℝ → ℝ²) : Set ℝ² :=
  rotateTranslate 0 (p 0) '' horizontalHallway ∩
  rotateTranslate ↑(π / 2) (p (π / 2)) '' verticalHallway ∩
  ⋂ α ∈ Set.Icc 0 (π / 2), rotateTranslate α (p α) '' hallway

namespace GerversSofa

/-
Gerver's constants defining the sofa.

This section follows Theorem 2 of Gerver's paper [Ge92].
-/

/--
Eq. 1-4 of [Ro18], which specifies the constants $A$, $B$, $\varphi$, and $\theta$ of [Ge92].
-/
def ABφθSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ π / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + π / 2 - φ - θ) - (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

/-- There exist unique constants $A$, $B$, $\varphi$, and $\theta$ satisfying the spec. -/
theorem ABφθSpec.existsUnique : ∃! ABφθ : ℝ × ℝ × ℝ × ℝ,
    ABφθSpec ABφθ.1 ABφθ.2.1 ABφθ.2.2.1 ABφθ.2.2.2 :=
  sorry

/-- Gerver's constant $A$: the first component of the unique solution of `ABφθSpec`. -/
def A : ℝ := ABφθSpec.existsUnique.choose.1
/-- Gerver's constant $B$: the second component of the unique solution of `ABφθSpec`. -/
def B : ℝ := ABφθSpec.existsUnique.choose.2.1
/-- Gerver's angle $\varphi$: the third component of the unique solution of `ABφθSpec`. -/
def φ : ℝ := ABφθSpec.existsUnique.choose.2.2.1
/-- Gerver's angle $\theta$: the fourth component of the unique solution of `ABφθSpec`. -/
def θ : ℝ := ABφθSpec.existsUnique.choose.2.2.2

/-- The piecewise function $r$ of [Ro18], Theorem 2, with break points $\varphi$, $\theta$,
$\pi/2 - \theta$ and $\pi/2 - \varphi$. The functions `x` and `y` are integrals of it. -/
def r (α : ℝ) : ℝ :=
  if α ≤ φ then
    1 / 2
  else if α ≤ θ then
    (1 + A + α - φ) / 2
  else if α ≤ π / 2 - θ then
    A + α - φ
  else if α ≤ π / 2 - φ then
    B - (π / 2 - α - φ) * (1 + A) / 2 - (π / 2 - α - φ) ^ 2 / 4
  else
    0

/-- $y(\alpha) = \int_\alpha^{\pi/2 - \varphi} r(t) \sin t \, dt$, as in [Ro18], Theorem 2. -/
def y (α : ℝ) : ℝ :=
  ∫ t in α..π / 2 - φ, r t * t.sin

/-- $x(\alpha) = 1 - \int_\alpha^{\pi/2 - \varphi} r(t) \cos t \, dt$, as in [Ro18], Theorem 2. -/
def x (α : ℝ) : ℝ :=
  1 - ∫ t in α..π / 2 - φ, r t * t.cos

/-- The rotation path of Gerver's sofa: `p α` is the translation applied to the hallway before it
is rotated by the angle $\alpha \in [0, \pi/2]$, in the convention of `rotateTranslate`. -/
def p (α : ℝ) : ℝ² :=
  !₂[if α ≤ φ
      then α.cos - 1
      else x (π / 2 - α) * α.cos + y (π / 2 - α) * α.sin - 1,
    if α ≤ π / 2 - φ
      then y α * α.cos - (4 * x 0 - 2 - x α) * α.sin - 1
      else -(4 * x 0 - 3) * α.sin - 1]

end GerversSofa

/-- Gerver's sofa is the sofa according to the rotation path `GerversSofa.p`. -/
def gerversSofa : Set ℝ² :=
  sofaOfRotateTranslatePath GerversSofa.p

/-- Gerver's concrete sofa admits a valid hallway motion. -/
theorem isMovingSofa_gerversSofa : ∃ m, IsMovingSofa gerversSofa m := by
  sorry

open MeasureTheory
open scoped ENNReal

/-- The **sofa constant** is the maximal area of a moving sofa. -/
def sofaConstant : ℝ≥0∞ := ⨆ (s : Set ℝ²) (_ : ∃ m, IsMovingSofa s m), volume s

/-- Gerver's sofa attains the sofa constant (Baek, arXiv:2411.19826). -/
theorem sofaConstant_eq_volume_gerversSofa : sofaConstant = volume gerversSofa := by
  sorry

end MovingSofa
