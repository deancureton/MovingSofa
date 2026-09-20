import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Haar-null lines and inner-product level sets

Lines and hyperplanes of a finite-dimensional real normed space carry no additive Haar mass.
This file records the two convenient forms used when a planar region is exhausted by triangles
up to the rays through finitely many vertices.
-/

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A line through the origin is a proper subspace once the ambient dimension exceeds one. -/
theorem Submodule.span_singleton_ne_top (h : 1 < Module.finrank ℝ E) (v : E) :
    (ℝ ∙ v) ≠ ⊤ := by
  rcases eq_or_ne v 0 with rfl | hv
  · have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (M := E) (by omega)
    rw [Submodule.span_zero_singleton]
    exact bot_ne_top
  · intro htop
    have hfin : Module.finrank ℝ E = 1 := (finrank_eq_one_iff_of_nonzero v hv).2 htop
    omega

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Any line in a space of dimension at least two is null for an additive Haar measure. -/
theorem MeasureTheory.Measure.addHaar_vadd_span_singleton (μ : Measure E)
    [μ.IsAddHaarMeasure] (h : 1 < Module.finrank ℝ E) (o v : E) :
    μ (o +ᵥ (ℝ ∙ v : Set E)) = 0 := by
  rw [measure_vadd]
  exact μ.addHaar_submodule _ (Submodule.span_singleton_ne_top h v)

/-- A countable union of lines through a common point is null. -/
theorem MeasureTheory.Measure.addHaar_iUnion_vadd_span_singleton {ι : Type*} [Countable ι]
    (μ : Measure E) [μ.IsAddHaarMeasure] (h : 1 < Module.finrank ℝ E) (o : E) (v : ι → E) :
    μ (⋃ i, o +ᵥ (ℝ ∙ v i : Set E)) = 0 :=
  measure_iUnion_null fun i ↦ μ.addHaar_vadd_span_singleton h o (v i)

/-- A level set of a nonzero inner-product functional is null for an additive Haar measure. -/
theorem MeasureTheory.Measure.addHaar_setOf_real_inner_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {u : F} (hu : u ≠ 0) (c : ℝ) :
    μ {p : F | inner ℝ p u = c} = 0 := by
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by positivity
  set f : F →ᵃ[ℝ] ℝ := (innerSL ℝ u).toLinearMap.toAffineMap with hf
  set A := (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)).comap f with hA
  have hAset : (A : Set F) = {p : F | inner ℝ p u = c} := by
    ext p
    simp [hA, hf, AffineSubspace.mem_mk', real_inner_comm, sub_eq_zero]
  rw [← hAset]
  refine μ.addHaar_affineSubspace _ fun htop ↦ ?_
  have hp : ((c + ‖u‖ ^ 2) / ‖u‖ ^ 2) • u ∈ A := by rw [htop]; trivial
  rw [← SetLike.mem_coe, hAset, Set.mem_ofPred_eq] at hp
  have : inner ℝ (((c + ‖u‖ ^ 2) / ‖u‖ ^ 2) • u) u = c + ‖u‖ ^ 2 := by
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  rw [this] at hp
  linarith

