import GerverSofa.KernelOnly.ConcreteUniqueZeros
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Part E01: bridge to DeepMind's Gerver-constant specification

This module mirrors the four equations and the physical domain used by
`GerversSofa.ABφθSpec` in `google-deepmind/formal-conjectures`.  It proves that
the four displayed equations are exactly the already certified reduced Gerver
system, proves that the certified rational box lies in the physical domain,
and reduces the tuple-shaped global uniqueness statement to one explicit
global enclosure target.

The enclosure target is a proposition passed as an ordinary theorem argument.
E01 does not claim that the global exclusion step has already been proved.
-/

noncomputable section

namespace GerverSofa
namespace PartE

/-- Reduced parameters assembled in the order `(A, B, phi, theta)`. -/
def reducedParams (A B phi theta : ℝ) : Reduced.Params :=
  { a := A, b := B, phi := phi, theta := theta }

/-- The physical domain appearing in DeepMind's `ABφθSpec`. -/
def PhysicalDomain (p : Reduced.Params) : Prop :=
  0 ≤ p.phi ∧ p.phi ≤ p.theta ∧ p.theta ≤ Real.pi / 4 ∧
    0 ≤ p.a ∧ 0 ≤ p.b

/-- The four displayed equations in DeepMind's `ABφθSpec`. -/
def DeepMindEquations (A B phi theta : ℝ) : Prop :=
  A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
      + (theta - phi - 1) * Real.cos theta - Real.sin theta
      + Real.cos phi + Real.sin phi = 0 ∧
  A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
      + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
      - Real.sin phi + Real.cos phi = 0 ∧
  A * Real.cos phi
      - (Real.sin phi + 1 / 2 - Real.cos phi / 2 + B * Real.sin phi) = 0 ∧
  (A + Real.pi / 2 - phi - theta)
      - (B - (theta - phi) * (1 + A) / 2 - (theta - phi) ^ 2 / 4) = 0

/-- A local mirror of DeepMind's complete four-constant specification. -/
def DeepMindABPhiThetaSpec (A B phi theta : ℝ) : Prop :=
  PhysicalDomain (reducedParams A B phi theta) ∧
    DeepMindEquations A B phi theta

/-- Explicit equivalence between DeepMind's four equations and the certified
reduced Gerver system. -/
theorem deepMindEquations_iff_reducedEquations (A B phi theta : ℝ) :
    DeepMindEquations A B phi theta ↔
      Reduced.Equations (reducedParams A B phi theta) := by
  constructor
  · rintro ⟨h0, h1, h2, h3⟩
    change Reduced.system (reducedParams A B phi theta) = 0
    funext i
    fin_cases i
    · change
        A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
            + (theta - phi - 1) * Real.cos theta - Real.sin theta
            + Real.cos phi + Real.sin phi = 0
      exact h0
    · change
        A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
            + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
            - Real.sin phi + Real.cos phi = 0
      exact h1
    · change
        A * Real.cos phi - Real.sin phi - 1 / 2
            + 1 / 2 * Real.cos phi - B * Real.sin phi = 0
      ring_nf at h2 ⊢
      exact h2
    · change
        A + Real.pi / 2 - phi - theta - B
            + 1 / 2 * (theta - phi) * (1 + A)
            + 1 / 4 * (theta - phi) * (theta - phi) = 0
      ring_nf at h3 ⊢
      exact h3
  · intro h
    change Reduced.system (reducedParams A B phi theta) = 0 at h
    have h0 := congrFun h (0 : Fin 4)
    have h1 := congrFun h (1 : Fin 4)
    have h2 := congrFun h (2 : Fin 4)
    have h3 := congrFun h (3 : Fin 4)
    change
      A * (Real.cos theta - Real.cos phi) - 2 * B * Real.sin phi
          + (theta - phi - 1) * Real.cos theta - Real.sin theta
          + Real.cos phi + Real.sin phi = 0 at h0
    change
      A * (3 * Real.sin theta + Real.sin phi) - 2 * B * Real.cos phi
          + 3 * (theta - phi - 1) * Real.sin theta + 3 * Real.cos theta
          - Real.sin phi + Real.cos phi = 0 at h1
    change
      A * Real.cos phi - Real.sin phi - 1 / 2
          + 1 / 2 * Real.cos phi - B * Real.sin phi = 0 at h2
    change
      A + Real.pi / 2 - phi - theta - B
          + 1 / 2 * (theta - phi) * (1 + A)
          + 1 / 4 * (theta - phi) * (theta - phi) = 0 at h3
    refine ⟨h0, h1, ?_, ?_⟩
    · ring_nf at h2 ⊢
      exact h2
    · ring_nf at h3 ⊢
      exact h3

/-- Every point of the certified reduced box satisfies DeepMind's broad
physical-domain inequalities. -/
theorem physicalDomain_of_mem_reducedBox {p : Reduced.Params}
    (hp : p ∈ Reduced.box) : PhysicalDomain p := by
  dsimp [Reduced.box, qR] at hp
  rcases hp with
    ⟨haLo, _haHi, hbLo, _hbHi, hphiLo, hphiHi, hthetaLo, hthetaHi⟩
  have hphiNonneg : 0 ≤ p.phi := by
    have hconst :
        (0 : ℝ) ≤ (122429264969 : ℝ) / 3125000000000 := by
      norm_num
    exact hconst.trans hphiLo
  have hphiTheta : p.phi ≤ p.theta := by
    have hgap :
        (3917736479009 : ℝ) / 100000000000000 ≤
          (2129067216821 : ℝ) / 3125000000000 := by
      norm_num
    exact hphiHi.trans (hgap.trans hthetaLo)
  have hthetaPi : p.theta ≤ Real.pi / 4 := by
    have hrat :
        (68130150938273 : ℝ) / 100000000000000 < (3 : ℝ) / 4 := by
      norm_num
    have hthree : (3 : ℝ) / 4 < Real.pi / 4 := by
      nlinarith [Real.pi_gt_three]
    exact hthetaHi.trans (le_of_lt (hrat.trans hthree))
  have haNonneg : 0 ≤ p.a := by
    have hconst :
        (0 : ℝ) ≤ (1888531216873 : ℝ) / 20000000000000 := by
      norm_num
    exact hconst.trans haLo
  have hbNonneg : 0 ≤ p.b := by
    have hconst :
        (0 : ℝ) ≤ (69960186366677 : ℝ) / 50000000000000 := by
      norm_num
    exact hconst.trans hbLo
  exact ⟨hphiNonneg, hphiTheta, hthetaPi, haNonneg, hbNonneg⟩

/-- The mirrored DeepMind specification is precisely physical-domain
membership plus the already named reduced equations. -/
theorem deepMindSpec_iff_physicalDomain_and_reducedEquations
    (A B phi theta : ℝ) :
    DeepMindABPhiThetaSpec A B phi theta ↔
      PhysicalDomain (reducedParams A B phi theta) ∧
        Reduced.Equations (reducedParams A B phi theta) := by
  unfold DeepMindABPhiThetaSpec
  rw [deepMindEquations_iff_reducedEquations]

/-- A certified-box solution of the reduced system is automatically a
solution of the mirrored DeepMind specification. -/
theorem deepMindSpec_of_mem_reducedBox_and_equations {p : Reduced.Params}
    (hp : p ∈ Reduced.box) (heq : Reduced.Equations p) :
    DeepMindABPhiThetaSpec p.a p.b p.phi p.theta := by
  apply
    (deepMindSpec_iff_physicalDomain_and_reducedEquations
      p.a p.b p.phi p.theta).2
  simpa [reducedParams] using
    And.intro (physicalDomain_of_mem_reducedBox hp) heq

/-- The sole new mathematical target left after E01: every physical solution
of the reduced equations lies in the already certified rational box. -/
def GlobalEnclosureTarget : Prop :=
  ∀ p : Reduced.Params,
    PhysicalDomain p → Reduced.Equations p → p ∈ Reduced.box

/-- Coordinate equivalence between DeepMind's nested tuple and the named
reduced-parameter record. -/
def tupleEquiv : (ℝ × ℝ × ℝ × ℝ) ≃ Reduced.Params where
  toFun x := reducedParams x.1 x.2.1 x.2.2.1 x.2.2.2
  invFun p := (p.a, p.b, p.phi, p.theta)
  left_inv x := by
    rcases x with ⟨A, B, phi, theta⟩
    rfl
  right_inv p := by
    cases p
    rfl

/-- Once the explicit global enclosure theorem is supplied, the existing
kernel-checked local certificate yields the exact tuple-shaped uniqueness
statement required by DeepMind. -/
theorem deepMindABPhiTheta_existsUnique_of_globalEnclosure
    (hglobal : GlobalEnclosureTarget) :
    ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ,
      DeepMindABPhiThetaSpec
        ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 := by
  let cert := PartALeanCert.reducedCertifiedUniqueSolution
  refine ⟨tupleEquiv.symm cert.solution, ?_, ?_⟩
  · change
      DeepMindABPhiThetaSpec
        cert.solution.a cert.solution.b cert.solution.phi cert.solution.theta
    exact
      deepMindSpec_of_mem_reducedBox_and_equations
        cert.solution_mem cert.satisfies
  · intro y hy
    apply tupleEquiv.injective
    rw [tupleEquiv.apply_symm_apply]
    apply cert.unique (tupleEquiv y)
    · apply hglobal (tupleEquiv y)
      · exact
          ((deepMindSpec_iff_physicalDomain_and_reducedEquations
            y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy).1
      · exact
          ((deepMindSpec_iff_physicalDomain_and_reducedEquations
            y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy).2
    · exact
        ((deepMindSpec_iff_physicalDomain_and_reducedEquations
          y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy).2

end PartE
end GerverSofa
