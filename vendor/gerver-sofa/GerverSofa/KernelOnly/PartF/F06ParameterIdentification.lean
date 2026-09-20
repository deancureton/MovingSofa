import GerverSofa.KernelOnly.PartF.F06FullReconstruction
import GerverSofa.KernelOnly.PartF.F01ParameterChoice
import GerverSofa.KernelOnly.PartB.Parameters

/-!
# F06: identify the two independently certified parameter choices

The 22D box supplies only coarse physical inequalities for its reverse
parameters. Global 4D uniqueness from Part E then identifies the reduced root.
The full algebraic reconstruction closes the 22D identity without a new
Krawczyk run or a forward enclosure into the narrow full box.
-/

noncomputable section
set_option maxHeartbeats 2000000

namespace GerverSofa.PartF.Parameters

open Phases

theorem undictionary_physical_of_mem_full_box {p : Romik.Params}
    (hp : p ∈ Romik.box) : PartE.PhysicalDomain (undictionary p) := by
  dsimp [Romik.box, qR] at hp
  rcases hp with ⟨_, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hb1lo, hb1hi, hb2lo, _, _, _, _, _,
    _, _, _, _, _, _, _, _,
    hphilo, hphihi, hthetalo, hthetahi⟩
  norm_num at hb1lo hb1hi hb2lo hphilo hphihi hthetalo hthetahi
  have hphi0 : 0 ≤ p.phi := by linarith only [hphilo]
  have hphi1 : p.phi ≤ 1 / 20 := by linarith only [hphihi]
  have htheta0 : (3 / 5 : ℝ) ≤ p.theta := by linarith only [hthetalo]
  have htheta1 : p.theta ≤ 7 / 10 := by linarith only [hthetahi]
  change 0 ≤ p.phi ∧ p.phi ≤ p.theta ∧ p.theta ≤ Real.pi / 4 ∧
    0 ≤ p.phi - 1 - 2 * p.b1 ∧
    0 ≤ p.b2 + 1 / 2 - (1 + (p.phi - 1 - 2 * p.b1)) * p.phi / 2 + p.phi ^ 2 / 4
  refine ⟨hphi0, ?_, ?_, ?_, ?_⟩
  · linarith only [hphi1, htheta0]
  · nlinarith only [htheta1, Real.pi_gt_three]
  · linarith only [hphi0, hb1hi]
  · have hprod : 0 ≤ (p.b1 + 3 / 5) * p.phi :=
      mul_nonneg (by linarith only [hb1lo]) hphi0
    have hsq : 0 ≤ p.phi * (1 / 20 - p.phi) :=
      mul_nonneg hphi0 (by linarith only [hphi1])
    nlinarith only [hb2lo, hprod, hsq, hphi0, hphi1]

theorem undictionary_eq_reduced_certified {p : Romik.Params}
    (hp : p ∈ Romik.box) (heq : Romik.Equations p) :
    undictionary p = PartALeanCert.reducedCertifiedUniqueSolution.solution := by
  let d := undictionary p
  have hdom : PartE.PhysicalDomain d := undictionary_physical_of_mem_full_box hp
  have he : Reduced.Equations d := undictionary_equations heq
  have hspec : PartE.DeepMindABPhiThetaSpec d.a d.b d.phi d.theta :=
    (PartE.deepMindSpec_iff_physicalDomain_and_reducedEquations _ _ _ _).2 ⟨hdom, he⟩
  let q : ℝ × ℝ × ℝ × ℝ := (d.a, d.b, d.phi, d.theta)
  have hq : TupleSpec q := (upstreamSpec_iff _ _ _ _).2 hspec
  have htuple := any_solution_eq_certified q hq
  have hparams := congrArg PartE.tupleEquiv htuple
  rw [certified, PartE.tupleEquiv.apply_symm_apply] at hparams
  exact hparams

theorem dictionary_eq_full_certified :
    dictionary PartALeanCert.reducedCertifiedUniqueSolution.solution = PartB.params := by
  have hu := undictionary_eq_reduced_certified PartB.params_mem PartB.params_equations
  calc
    dictionary PartALeanCert.reducedCertifiedUniqueSolution.solution =
        dictionary (undictionary PartB.params) := congrArg dictionary hu.symm
    _ = PartB.params := dictionary_undictionary_of_equations PartB.params_equations

end GerverSofa.PartF.Parameters
