import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Algebra.Ring.Real

noncomputable section
namespace OrderIso

/-- Extend an order isomorphism of open real intervals by matching the endpoints. -/
def extendIoo {a b c d : ℝ} (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) (x : Set.Icc a b) : Set.Icc c d :=
  if hxa : (x : ℝ) = a then ⟨c, le_rfl, hcd.le⟩
  else if hxb : (x : ℝ) = b then ⟨d, hcd.le, le_rfl⟩
  else let t := e ⟨x, lt_of_le_of_ne x.property.1 (Ne.symm hxa),
      lt_of_le_of_ne x.property.2 hxb⟩
    ⟨t, t.property.1.le, t.property.2.le⟩

/-- The extension maps the left endpoint to the left endpoint. -/
theorem extendIoo_left {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) :
    extendIoo hcd e ⟨a, le_rfl, hab.le⟩ = ⟨c, le_rfl, hcd.le⟩ := by
  simp [extendIoo]

/-- The extension maps the right endpoint to the right endpoint. -/
theorem extendIoo_right {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) :
    extendIoo hcd e ⟨b, hab.le, le_rfl⟩ = ⟨d, hcd.le, le_rfl⟩ := by
  simp [extendIoo, ne_of_gt hab]

/-- The extension agrees with the original order isomorphism on the interior. -/
theorem extendIoo_interior {a b c d : ℝ} (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) (x : Set.Ioo a b) :
    (extendIoo hcd e ⟨x, x.property.1.le, x.property.2.le⟩ : ℝ) = e x := by
  simp [extendIoo, ne_of_gt x.property.1, ne_of_lt x.property.2]

/-- The endpoint extension is monotone. -/
theorem monotone_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Monotone (extendIoo hcd e) := by
  intro x y hxy
  by_cases hx : (x : ℝ) = a
  · have he : x = ⟨a, le_rfl, hab.le⟩ := Subtype.ext hx
    rw [he, extendIoo_left hab]
    exact (extendIoo hcd e y).property.1
  by_cases hy : (y : ℝ) = b
  · have he : y = ⟨b, hab.le, le_rfl⟩ := Subtype.ext hy
    rw [he, extendIoo_right hab]
    exact (extendIoo hcd e x).property.2
  have hxlo : a < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
  have hyhi : (y : ℝ) < b := lt_of_le_of_ne y.property.2 hy
  have hxhi : (x : ℝ) < b := lt_of_le_of_lt hxy hyhi
  have hylo : a < (y : ℝ) := lt_of_lt_of_le hxlo hxy
  change (extendIoo hcd e x : ℝ) ≤ extendIoo hcd e y
  rw [extendIoo_interior hcd e ⟨x, hxlo, hxhi⟩,
    extendIoo_interior hcd e ⟨y, hylo, hyhi⟩]
  exact e.monotone hxy

/-- The endpoint extension is surjective. -/
theorem surjective_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Function.Surjective (extendIoo hcd e) := by
  intro y
  by_cases hyc : (y : ℝ) = c
  · refine ⟨⟨a, le_rfl, hab.le⟩, ?_⟩
    rw [extendIoo_left hab]
    exact Subtype.ext hyc.symm
  by_cases hyd : (y : ℝ) = d
  · refine ⟨⟨b, hab.le, le_rfl⟩, ?_⟩
    rw [extendIoo_right hab]
    exact Subtype.ext hyd.symm
  let y' : Set.Ioo c d := ⟨y, lt_of_le_of_ne y.property.1 (Ne.symm hyc),
    lt_of_le_of_ne y.property.2 hyd⟩
  let x := e.symm y'
  refine ⟨⟨x, x.property.1.le, x.property.2.le⟩, Subtype.ext ?_⟩
  rw [extendIoo_interior]
  exact congrArg Subtype.val (e.apply_symm_apply y')

/-- The endpoint extension is continuous. -/
theorem continuous_extendIoo {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (e : Set.Ioo a b ≃o Set.Ioo c d) : Continuous (extendIoo hcd e) :=
  (monotone_extendIoo hab hcd e).continuous_of_surjective (surjective_extendIoo hab hcd e)

end OrderIso
