import MovingSofa.Curve.CyclicRotation
import MovingSofa.Curve.Jordan.WindingConcatenation

noncomputable section
namespace MovingSofa

private theorem strictMono_convexComb {a b : ℝ} (l u : Set.Icc a b) (hlu : l < u) :
    StrictMono (Set.Icc.convexComb l u) := by
  intro s t hst
  have hlu' : (l : ℝ) < u := hlu
  have hst' : (s : ℝ) < t := hst
  change (1 - (s : ℝ)) * l + (s : ℝ) * u <
    (1 - (t : ℝ)) * l + (t : ℝ) * u
  nlinarith [mul_pos (sub_pos.mpr hst') (sub_pos.mpr hlu')]

/-- Moving an oriented Jordan path's start to an interior parameter preserves area and
orientation. -/
theorem exists_oriented_cyclic_rotation {a b : ℝ} (hab : a ≤ b)
    {Γ : Set Point} {ccw : Bool} (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ ccw x.val)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b) :
    ∃ r : ContinuousBVPaths 0 2,
      IsOrientedJordanParametrization (by norm_num) Γ ccw r.val ∧
      r.val ⟨0, by norm_num⟩ = x.val s ∧
      curveAreaFunctional r = curveAreaFunctional x := by
  have hclosed := hx.2.2.2.2.1
  obtain ⟨r, hr, _, harea⟩ := exists_cyclic_rotation_eq_concat hab x s hclosed.symm
  refine ⟨r, ?_, ?_, harea⟩
  · refine ⟨by norm_num, hx.2.1, r.property.1, ?_, ?_, ?_, ?_⟩
    · rw [hr, range_cyclic_concat hab x.val s hclosed]
      exact hx.2.2.2.1
    · rw [hr]
      simp
    · rw [hr]
      exact Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab
        hx.2.2.2.2.2.1 hclosed s has hsb
        (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
        (strictMono_convexComb _ _ hsb) (strictMono_convexComb _ _ has)
        (by simp) (by simp) (by simp)
    · intro p hp
      have hxw := hx.2.2.2.2.2.2 p hp
      have hn : curveWinding hab x.val p ≠ 0 := by
        rw [hxw]
        cases ccw <;> norm_num
      obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hn
      rw [hr, curveWinding_concat_of_cyclic_endpoints hab hθ hclosed s
        (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
        (Set.Icc.continuous_convexComb _ _) (Set.Icc.continuous_convexComb _ _)
        (by simp) (by simp) (by simp) (by simp)]
      exact hxw
  · rw [hr]
    simp

/-- A cyclic rotation together with its literal tail-then-head formula. -/
theorem exists_oriented_cyclic_rotation_eq_concat {a b : ℝ} (hab : a ≤ b)
    {Γ : Set Point} {ccw : Bool} (x : ContinuousBVPaths a b)
    (hx : IsOrientedJordanParametrization hab Γ ccw x.val)
    (s : Set.Icc a b) (has : a < s) (hsb : (s : ℝ) < b) :
    ∃ r : ContinuousBVPaths 0 2,
      IsOrientedJordanParametrization (by norm_num) Γ ccw r.val ∧
      r.val = Function.concatUnitIntervals
        (x.val ∘ Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
        (x.val ∘ Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s) := by
  have hclosed := hx.2.2.2.2.1
  obtain ⟨r, hr, _⟩ :=
    exists_cyclic_rotation_path hab x s hclosed.symm
  refine ⟨r, ?_, hr⟩
  refine ⟨by norm_num, hx.2.1, r.property.1, ?_, ?_, ?_, ?_⟩
  · rw [hr, range_cyclic_concat hab x.val s hclosed]
    exact hx.2.2.2.1
  · rw [hr]
    simp
  · rw [hr]
    exact Function.injOn_concatUnitIntervals_comp_of_cyclic_endpoints hab
      hx.2.2.2.2.2.1 hclosed s has hsb
      (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
      (strictMono_convexComb _ _ hsb)
      (strictMono_convexComb _ _ has)
      (by simp) (by simp) (by simp)
  · intro p hp
    have hxw := hx.2.2.2.2.2.2 p hp
    have hn : curveWinding hab x.val p ≠ 0 := by
      rw [hxw]
      cases ccw <;> norm_num
    obtain ⟨θ, hθ⟩ := exists_curveAngleLift_of_curveWinding_ne_zero hab hn
    rw [hr, curveWinding_concat_of_cyclic_endpoints hab hθ hclosed s
      (Set.Icc.convexComb s ⟨b, hab, le_rfl⟩)
      (Set.Icc.convexComb ⟨a, le_rfl, hab⟩ s)
      (Set.Icc.continuous_convexComb _ _) (Set.Icc.continuous_convexComb _ _)
      (by simp) (by simp) (by simp) (by simp)]
    exact hxw

end MovingSofa
