import MovingSofa.Convex.CombinationProperties
import MovingSofa.Curve.SmoothIntervalPaths
import MovingSofa.Geometry.HallwaySupport

/-!
# The outer corner of a convex body as a path of bounded variation

The outer corner of the rotating supporting hallway of a convex body `K` is
`h_K(t) • u_t + h_K(t + π/2) • v_t`.  Support values are Lipschitz in the angle and bounded on a
compact interval, so this expression is a Lipschitz, hence continuous bounded-variation, path on
every compact interval of angles; and it is convex-linear in `K` because support values are.
These are the two hypotheses of Mamikon convexity for the middle summand of the sofa area.
-/

noncomputable section

open scoped unitInterval

namespace MovingSofa

/-- The outer corner of a convex body traces a continuous path of bounded variation over every
compact interval of angles. -/
theorem exists_outerCornerBV (K : ConvexBody Point) (a b : ℝ) :
    ∃ γ : ContinuousBVPaths a b, ∀ s : Set.Icc a b,
      γ.val s = (rotatingHallwayParts (K : Set Point) ((s : ℝ) : Real.Angle)).outerCorner := by
  set C := sSup (norm '' (K : Set Point))
  have hC0 : 0 ≤ C := Real.sSup_nonneg (by rintro _ ⟨p, -, rfl⟩; exact norm_nonneg p)
  have hlipn : ∀ x y : ℝ, |supportValue (K : Set Point) (x : Real.Angle) -
      supportValue (K : Set Point) (y : Real.Angle)| ≤ C * |x - y| :=
    abs_supportValue_sub_le_of_isCompact K.nonempty K.isCompact
  have hlipt : ∀ x y : ℝ,
      |supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle) -
        supportValue (K : Set Point) ((y + Real.pi / 2 : ℝ) : Real.Angle)| ≤ C * |x - y| := by
    intro x y
    simpa only [add_sub_add_right_eq_sub] using hlipn (x + Real.pi / 2) (y + Real.pi / 2)
  have hcont : Continuous fun x : ℝ ↦
      supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle) :=
    (continuous_supportValue_real K).comp (continuous_id.add_const _)
  obtain ⟨Mn, hMn⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    (continuous_supportValue_real K).continuousOn
  obtain ⟨Mt, hMt⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc a b)
    hcont.continuousOn
  set M := max (max Mn Mt) 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMn' : ∀ x ∈ Set.Icc a b, |supportValue (K : Set Point) (x : Real.Angle)| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      (hMn x hx).trans ((le_max_left Mn Mt).trans (le_max_left _ 0))
  have hMt' : ∀ x ∈ Set.Icc a b,
      |supportValue (K : Set Point) ((x + Real.pi / 2 : ℝ) : Real.Angle)| ≤ M := by
    intro x hx
    simpa only [Real.norm_eq_abs] using
      (hMt x hx).trans ((le_max_right Mn Mt).trans (le_max_left _ 0))
  exact ⟨continuousBVOfLipschitz _ (lipschitzOnWith_frameCombination
      (D := ⟨2 * (C + M), by linarith⟩) le_rfl hM0 hlipn hlipt hMn' hMt').to_restrict,
    fun s ↦ (outerCorner_eq_support_sum K (s : ℝ)).symm⟩

/-- The outer-corner paths of a convex body may be chosen convex-linearly in the body.  The
barycentric operation on paths is `bvPathCombination`, spelled out here because it is defined
downstream of this module. -/
theorem exists_outerCornerBV_convexLinear (a b : ℝ) :
    ∃ γ : ConvexBody Point → ContinuousBVPaths a b,
      (∀ (K : ConvexBody Point) (s : Set.Icc a b), (γ K).val s =
        (rotatingHallwayParts (K : Set Point) ((s : ℝ) : Real.Angle)).outerCorner) ∧
      IsConvexLinear convexBodyCombination
        (fun r x y ↦ (1 - (r : ℝ)) • x + (r : ℝ) • y) γ := by
  choose γ hγ using fun K : ConvexBody Point ↦ exists_outerCornerBV K a b
  refine ⟨γ, hγ, fun t K L ↦ Subtype.ext (funext fun s ↦ ?_)⟩
  show (γ (convexBodyCombination t K L)).val s =
    ((1 - (t : ℝ)) • (γ K).val + (t : ℝ) • (γ L).val) s
  rw [hγ, show ((1 - (t : ℝ)) • (γ K).val + (t : ℝ) • (γ L).val) s =
      (1 - (t : ℝ)) • (γ K).val s + (t : ℝ) • (γ L).val s from rfl, hγ, hγ]
  simp only [outerCorner_eq_support_sum, supportValue_convexBodyCombination]
  module

end MovingSofa
