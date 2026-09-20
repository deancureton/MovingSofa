/-
MIT License

Copyright (c) 2026 Dawid Trela

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

import MovingSofa.Canonical.Definitions
import GerverSofa.KernelOnly.PartF.F06IntegralMotion

/-!
# Gerver's definitions in GerverSofaLean agree with the ones used here

Adapted from `F07UpstreamAdapter` in GerverSofaLean v1.1.0 (MIT). GerverSofaLean states its results
for its own copy of the moving sofa definitions. This file identifies that copy with the
definitions of `MovingSofa.Canonical.Definitions`.
-/

noncomputable section
open scoped unitInterval

namespace GerverSofa.PartF.ProjectAdapter

open Coordinates

theorem horizontalHallway_eq_model :
    MovingSofa.horizontalHallway = Model.horizontalHallway := by
  ext q
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hq
    exact ⟨q 0, q 1, hq, plane_ext rfl rfl⟩

theorem verticalHallway_eq_model :
    MovingSofa.verticalHallway = Model.verticalHallway := by
  ext q
  constructor
  · rintro ⟨x, y, hxy, rfl⟩
    exact hxy
  · intro hq
    exact ⟨q 0, q 1, hq, plane_ext rfl rfl⟩

theorem hallway_eq_model : MovingSofa.hallway = Model.hallway := by
  unfold MovingSofa.hallway Model.hallway
  rw [horizontalHallway_eq_model, verticalHallway_eq_model]

theorem isMovingSofa_iff_model (s : Set Plane) (m : I → Rigid) :
    MovingSofa.IsMovingSofa s m ↔ Model.IsMovingSofa s m := by
  constructor
  · intro h
    refine ⟨h.isConnected, h.isClosed, h.continuous, h.zero, ?_, ?_, ?_⟩
    · simpa only [horizontalHallway_eq_model] using h.initial
    · intro t
      simpa only [hallway_eq_model] using h.subset_hallway t
    · simpa only [verticalHallway_eq_model] using h.final
  · intro h
    refine ⟨h.isConnected, h.isClosed, h.continuous, h.zero, ?_, ?_, ?_⟩
    · simpa only [horizontalHallway_eq_model] using h.initial
    · intro t
      simpa only [hallway_eq_model] using h.subset_hallway t
    · simpa only [verticalHallway_eq_model] using h.final

theorem sofaOfRotateTranslatePath_eq_bodySofa (p : ℝ → Plane) :
    MovingSofa.sofaOfRotateTranslatePath p =
      bodySofa p Model.horizontalHallway Model.verticalHallway Model.hallway := by
  unfold MovingSofa.sofaOfRotateTranslatePath bodySofa angleIntersection
  rw [horizontalHallway_eq_model, verticalHallway_eq_model, hallway_eq_model]
  rfl

def selected : Reduced.Params :=
  PartE.tupleEquiv MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose

theorem selected_eq_certified : selected = Integrals.certified := by
  have h : MovingSofa.GerversSofa.ABφθSpec.existsUnique.choose = Parameters.certified :=
    Parameters.choice_independent MovingSofa.GerversSofa.ABφθSpec.existsUnique
  exact (congrArg PartE.tupleEquiv h).trans (PartE.tupleEquiv.apply_symm_apply _)

theorem p_eq_selected (t : ℝ) :
    MovingSofa.GerversSofa.p t = toPlane (Integrals.path selected t) := rfl

theorem p_eq_certified : MovingSofa.GerversSofa.p =
    fun t => toPlane (Integrals.path Integrals.certified t) := by
  funext t
  rw [p_eq_selected, selected_eq_certified]

theorem integral_rotation_to_full (t : ℝ) (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    rotation t (MovingSofa.GerversSofa.p t) = toPlane (Romik.path PartC.params t) := by
  rw [p_eq_certified]
  exact Integrals.certified_integral_rotation_to_full t ht

theorem gerversSofa_eq_certified : MovingSofa.gerversSofa = EuclideanMotion.sofa := by
  unfold MovingSofa.gerversSofa
  rw [sofaOfRotateTranslatePath_eq_bodySofa, p_eq_certified]
  exact Integrals.integral_sofa_eq_certified

end GerverSofa.PartF.ProjectAdapter
