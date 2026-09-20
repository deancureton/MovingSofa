import GerverSofa.KernelOnly.PartE.E24KC6KernelFinalClosure

/-!
# F01: parameter selection is independent of the existence proof

This module reuses the frozen E24KC6 theorem. It does not repeat numerical
exclusion. The literal upstream order of conjunctions is checked against
the existing specification, and its selected tuple is identified with the
certified reduced solution. No identification with the full 22D tuple is
claimed by this module.
-/

noncomputable section

namespace GerverSofa.PartF.Parameters

def upstreamSpec (A B φ θ : ℝ) : Prop :=
  0 ≤ φ ∧ φ ≤ θ ∧ θ ≤ Real.pi / 4 ∧ 0 ≤ A ∧ 0 ≤ B ∧
  A * (θ.cos - φ.cos) - 2 * B * φ.sin
    + (θ - φ - 1) * θ.cos - θ.sin + φ.cos + φ.sin = 0 ∧
  A * (3 * θ.sin + φ.sin) - 2 * B * φ.cos
    + 3 * (θ - φ - 1) * θ.sin + 3 * θ.cos - φ.sin + φ.cos = 0 ∧
  A * φ.cos - (φ.sin + 1 / 2 - φ.cos / 2 + B * φ.sin) = 0 ∧
  (A + Real.pi / 2 - φ - θ) -
    (B - (θ - φ) * (1 + A) / 2 - (θ - φ)^2 / 4) = 0

theorem upstreamSpec_iff (A B φ θ : ℝ) :
    upstreamSpec A B φ θ ↔ PartE.DeepMindABPhiThetaSpec A B φ θ := by
  unfold upstreamSpec PartE.DeepMindABPhiThetaSpec PartE.PhysicalDomain
    PartE.reducedParams PartE.DeepMindEquations
  dsimp only
  tauto

def TupleSpec (q : ℝ × ℝ × ℝ × ℝ) : Prop :=
  upstreamSpec q.1 q.2.1 q.2.2.1 q.2.2.2

theorem existsUnique : ∃! q, TupleSpec q := by
  simpa only [TupleSpec, upstreamSpec_iff] using PartE.deepMindABPhiTheta_existsUnique

def certified : ℝ × ℝ × ℝ × ℝ :=
  PartE.tupleEquiv.symm PartALeanCert.reducedCertifiedUniqueSolution.solution

theorem certified_spec : TupleSpec certified := by
  apply (upstreamSpec_iff _ _ _ _).2
  exact PartE.deepMindSpec_of_mem_reducedBox_and_equations
    PartALeanCert.reducedCertifiedUniqueSolution.solution_mem
    PartALeanCert.reducedCertifiedUniqueSolution.satisfies

theorem any_solution_eq_certified (q : ℝ × ℝ × ℝ × ℝ) (hq : TupleSpec q) :
    q = certified := existsUnique.unique hq certified_spec

/-- This applies to any eventual upstream proof of the *same* specification. -/
theorem choice_independent (h : ∃! q, TupleSpec q) : h.choose = certified :=
  any_solution_eq_certified h.choose h.choose_spec.1

end GerverSofa.PartF.Parameters
