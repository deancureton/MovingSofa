import Mathlib.Topology.Algebra.Ring.Real

import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Function

/-- Concatenate two functions on `[0, 1]` on the interval `[0, 2]`. -/
noncomputable def concatUnitIntervals {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E)
    (t : Set.Icc (0 : ℝ) 2) : E :=
  if (t : ℝ) ≤ 1 then x (Set.projIcc 0 1 (by norm_num) t)
  else y (Set.projIcc 0 1 (by norm_num) ((t : ℝ) - 1))

/-- Concatenation is continuous when the endpoint values agree. -/
theorem continuous_concatUnitIntervals {E : Type*} [TopologicalSpace E]
    {x y : Set.Icc (0 : ℝ) 1 → E} (hx : Continuous x) (hy : Continuous y)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    Continuous (concatUnitIntervals x y) := by
  unfold concatUnitIntervals
  apply continuous_if_le continuous_subtype_val continuous_const
  · simpa only [Function.comp_def] using
      (hx.comp (continuous_projIcc.comp continuous_subtype_val)).continuousOn
  · simpa only [Function.comp_def, Pi.sub_apply] using
      (hy.comp
        (continuous_projIcc.comp (continuous_subtype_val.sub continuous_const))).continuousOn
  intro t ht
  simpa [ht] using hjoin

@[simp] theorem concatUnitIntervals_zero {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨0, by norm_num⟩ = x ⟨0, by norm_num⟩ := by
  simp [concatUnitIntervals]

@[simp] theorem concatUnitIntervals_one {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨1, by norm_num⟩ = x ⟨1, by norm_num⟩ := by
  simp [concatUnitIntervals]

@[simp] theorem concatUnitIntervals_two {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E) :
    concatUnitIntervals x y ⟨2, by norm_num⟩ = y ⟨1, by norm_num⟩ := by
  norm_num [concatUnitIntervals]

/-- Joined paths have precisely the union of the two original ranges. -/
theorem range_concatUnitIntervals {E : Type*} (x y : Set.Icc (0 : ℝ) 1 → E)
    (hjoin : x ⟨1, by norm_num⟩ = y ⟨0, by norm_num⟩) :
    Set.range (concatUnitIntervals x y) = Set.range x ∪ Set.range y := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    unfold concatUnitIntervals
    split_ifs
    · exact Or.inl (Set.mem_range_self _)
    · exact Or.inr (Set.mem_range_self _)
  · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
    · refine ⟨⟨t, t.property.1, t.property.2.trans (by norm_num)⟩, ?_⟩
      simp [concatUnitIntervals, t.property.2, Set.projIcc_of_mem (by norm_num) t.property]
    · by_cases ht : (t : ℝ) = 0
      · refine ⟨⟨1, by norm_num⟩, ?_⟩
        rw [concatUnitIntervals_one, hjoin]
        congr 1
        exact Subtype.ext ht.symm
      · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
        refine ⟨⟨(t : ℝ) + 1, by constructor <;> linarith [t.property.1, t.property.2]⟩, ?_⟩
        have hnot : ¬(t : ℝ) + 1 ≤ 1 := by linarith
        simp [concatUnitIntervals, hnot, Set.projIcc_of_mem (by norm_num) t.property]

/-- A strict cyclic cut preserves injectivity away from the final endpoint. -/
theorem injOn_concatUnitIntervals_comp_of_cyclic_endpoints
    {E : Type*} {a b : ℝ} (hab : a ≤ b) {x : Set.Icc a b → E}
    (hinj : Set.InjOn x {t | (t : ℝ) < b})
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b)
    (φ ψ : Set.Icc (0 : ℝ) 1 → Set.Icc a b)
    (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hφ₀ : φ ⟨0, by norm_num⟩ = s)
    (hψ₀ : ψ ⟨0, by norm_num⟩ = ⟨a, le_rfl, hab⟩)
    (hψ₁ : ψ ⟨1, by norm_num⟩ = s) :
    Set.InjOn (concatUnitIntervals (x ∘ φ) (x ∘ ψ)) {t | (t : ℝ) < 2} := by
  have hab' : a < b := has.trans hsb
  have hinj' : Set.InjOn x {t | a < (t : ℝ)} := by
    intro p hp q hq hpq
    by_cases hpb : (p : ℝ) < b
    · by_cases hqb : (q : ℝ) < b
      · exact hinj hpb hqb hpq
      · have hqeq : q = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
          apply Subtype.ext
          exact le_antisymm q.property.2 (le_of_not_gt hqb)
        have hpa : p = (⟨a, le_rfl, hab⟩ : Set.Icc a b) := by
          apply hinj hpb hab'
          rw [hqeq] at hpq
          exact hpq.trans hclosed.symm
        exact False.elim ((ne_of_gt hp) (congrArg Subtype.val hpa))
    · have hpeq : p = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
        apply Subtype.ext
        exact le_antisymm p.property.2 (le_of_not_gt hpb)
      by_cases hqb : (q : ℝ) < b
      · have hqa : q = (⟨a, le_rfl, hab⟩ : Set.Icc a b) := by
          apply hinj hqb hab'
          rw [hpeq] at hpq
          exact hpq.symm.trans hclosed.symm
        exact False.elim ((ne_of_gt hq) (congrArg Subtype.val hqa))
      · have hqeq : q = (⟨b, hab, le_rfl⟩ : Set.Icc a b) := by
          apply Subtype.ext
          exact le_antisymm q.property.2 (le_of_not_gt hqb)
        exact hpeq.trans hqeq.symm
  intro u hu v hv huv
  have hu0 : 0 ≤ (u : ℝ) := u.property.1
  have hv0 : 0 ≤ (v : ℝ) := v.property.1
  have hu2 : (u : ℝ) < 2 := hu
  have hv2 : (v : ℝ) < 2 := hv
  by_cases hu1 : (u : ℝ) ≤ 1
  · let pu : Set.Icc (0 : ℝ) 1 := ⟨u, hu0, hu1⟩
    have hueval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) u = x (φ pu) := by
      simp [concatUnitIntervals, hu1, pu,
        Set.projIcc_of_mem (by norm_num) ⟨hu0, hu1⟩]
    have hφu : (s : ℝ) ≤ φ pu := by
      rw [← hφ₀]
      exact hφ.monotone pu.property.1
    by_cases hv1 : (v : ℝ) ≤ 1
    · let pv : Set.Icc (0 : ℝ) 1 := ⟨v, hv0, hv1⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (φ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) ⟨hv0, hv1⟩]
      have hφv : (s : ℝ) ≤ φ pv := by
        rw [← hφ₀]
        exact hφ.monotone pv.property.1
      have hp : φ pu = φ pv := hinj' (has.trans_le hφu) (has.trans_le hφv)
        (hueval ▸ huv ▸ hveval)
      apply Subtype.ext
      simpa [pu, pv] using congrArg Subtype.val (hφ.injective hp)
    · have hv1' : 1 < (v : ℝ) := lt_of_not_ge hv1
      have hvp : 0 ≤ (v : ℝ) - 1 ∧ (v : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
      let pv : Set.Icc (0 : ℝ) 1 := ⟨(v : ℝ) - 1, hvp⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (ψ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) hvp]
      have hψvpos : a < (ψ pv : ℝ) := by
        have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pv by
          change 0 < (v : ℝ) - 1
          linarith)
        rw [hψ₀] at h
        exact h
      have hp : φ pu = ψ pv := hinj' (has.trans_le hφu) hψvpos
        (hueval ▸ huv ▸ hveval)
      have hψvlt : (ψ pv : ℝ) < s := by
        have h := hψ (show pv < (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) by
          change (v : ℝ) - 1 < 1
          linarith)
        rw [hψ₁] at h
        exact h
      exact False.elim ((not_le_of_gt hψvlt) (hp ▸ hφu))
  · have hu1' : 1 < (u : ℝ) := lt_of_not_ge hu1
    have hup : 0 ≤ (u : ℝ) - 1 ∧ (u : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
    let pu : Set.Icc (0 : ℝ) 1 := ⟨(u : ℝ) - 1, hup⟩
    have hueval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) u = x (ψ pu) := by
      simp [concatUnitIntervals, hu1, pu,
        Set.projIcc_of_mem (by norm_num) hup]
    have hψupos : a < (ψ pu : ℝ) := by
      have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pu by
        change 0 < (u : ℝ) - 1
        linarith)
      rw [hψ₀] at h
      exact h
    by_cases hv1 : (v : ℝ) ≤ 1
    · let pv : Set.Icc (0 : ℝ) 1 := ⟨v, hv0, hv1⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (φ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) ⟨hv0, hv1⟩]
      have hφv : (s : ℝ) ≤ φ pv := by
        rw [← hφ₀]
        exact hφ.monotone pv.property.1
      have hp : ψ pu = φ pv := hinj' hψupos (has.trans_le hφv)
        (hueval ▸ huv ▸ hveval)
      have hψult : (ψ pu : ℝ) < s := by
        have h := hψ (show pu < (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) by
          change (u : ℝ) - 1 < 1
          linarith)
        rw [hψ₁] at h
        exact h
      exact False.elim ((not_le_of_gt hψult) (hp ▸ hφv))
    · have hvp : 0 ≤ (v : ℝ) - 1 ∧ (v : ℝ) - 1 ≤ 1 := ⟨by linarith, by linarith⟩
      let pv : Set.Icc (0 : ℝ) 1 := ⟨(v : ℝ) - 1, hvp⟩
      have hveval : concatUnitIntervals (x ∘ φ) (x ∘ ψ) v = x (ψ pv) := by
        simp [concatUnitIntervals, hv1, pv,
          Set.projIcc_of_mem (by norm_num) hvp]
      have hψvpos : a < (ψ pv : ℝ) := by
        have h := hψ (show (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) < pv by
          change 0 < (v : ℝ) - 1
          linarith)
        rw [hψ₀] at h
        exact h
      have hp : ψ pu = ψ pv := hinj' hψupos hψvpos (hueval ▸ huv ▸ hveval)
      have hp' := congrArg Subtype.val (hψ.injective hp)
      apply Subtype.ext
      simp [pu, pv] at hp'
      linarith

end Function
