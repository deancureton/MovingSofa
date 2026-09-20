import GerverSofa.KernelOnly.PartC.Stage4.NoHiddenReflectionFacts

/-!
# Part C Stage 4: direct no-hidden-crossing closure

The first inequality follows from concavity and the two endpoint values.  The
second is its exact phase-derived horizontal reflection.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

/-- Concrete first no-hidden-crossing theorem. -/
theorem noHiddenU_direct : NoHiddenCrossingU := by
  intro r hr t ht
  change 0 ≤ Stage2.UValue r t
  have htPhys : t ∈ Icc params.phi T :=
    ⟨le_trans hr.1 ht.1, ht.2⟩
  have hconc := U_concave_on t htPhys
  have hphi := U_phi_nonneg htPhys
  have htt : Stage2.UValue t t = 0 := by
    simp [Stage2.UValue, dot]
  by_cases hrt : r = t
  · subst r
    exact le_of_eq htt.symm
  · have hrtlt : r < t := lt_of_le_of_ne ht.1 hrt
    have hphit : params.phi < t := lt_of_le_of_lt hr.1 hrtlt
    let a : ℝ := (t-r) / (t-params.phi)
    let b : ℝ := (r-params.phi) / (t-params.phi)
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hphit.le)
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (sub_nonneg.mpr hr.1) (sub_nonneg.mpr hphit.le)
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (ne_of_gt hphit)]
      ring
    have hrcomb : a • params.phi + b • t = r := by
      dsimp [a, b]
      field_simp [sub_ne_zero.mpr (ne_of_gt hphit)]
      ring
    have hJ := hconc.2
      (show params.phi ∈ Icc params.phi t from ⟨le_rfl, hphit.le⟩)
      (show t ∈ Icc params.phi t from ⟨hphit.le, le_rfl⟩)
      ha hb hab
    rw [hrcomb] at hJ
    change a • Stage2.UValue params.phi t + b • Stage2.UValue t t ≤
      Stage2.UValue r t at hJ
    rw [htt] at hJ
    simp only [smul_eq_mul, mul_zero, add_zero] at hJ
    nlinarith

/-- Concrete reflected no-hidden-crossing theorem. -/
theorem noHiddenV_direct : NoHiddenCrossingV := by
  intro t ht r hr
  change 0 ≤ Stage2.VValue t r
  have htT : t ∈ Icc (0 : ℝ) T :=
    ⟨ht.1, le_trans ht.2 Stage2.tau_le_T⟩
  have hrT : r ∈ Icc (0 : ℝ) T :=
    ⟨le_trans ht.1 hr.1, le_trans hr.2 Stage2.tau_le_T⟩
  have hleft : T-r ∈ Icc params.phi T := by
    constructor
    · dsimp [tau] at hr
      linarith [hr.2]
    · linarith [hrT.1]
  have hright : T-t ∈ Icc (T-r) T := by
    constructor
    · linarith [hr.1]
    · linarith [ht.1]
  have hU := noHiddenU_direct (T-r) hleft (T-t) hright
  change 0 ≤ Stage2.UValue (T-r) (T-t) at hU
  rw [← VValue_eq_reflected_UValue htT hrT] at hU
  exact hU

end Stage4
end PartC
end GerverSofa
