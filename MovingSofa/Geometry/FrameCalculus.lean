import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import MovingSofa.Geometry.Support

noncomputable section

namespace MovingSofa

theorem hasDerivAt_normalVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ normalVector (s : Real.Angle))
      (tangentVector (t : Real.Angle)) t := by
  have h : HasDerivAt (fun s : ℝ ↦ (![Real.cos s, Real.sin s] : Fin 2 → ℝ))
      (![-Real.sin t, Real.cos t] : Fin 2 → ℝ) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos t
    · exact Real.hasDerivAt_sin t
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h

theorem hasDerivAt_tangentVector (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ tangentVector (s : Real.Angle))
      (-normalVector (t : Real.Angle)) t := by
  have h : HasDerivAt (fun s : ℝ ↦ (![-Real.sin s, Real.cos s] : Fin 2 → ℝ))
      (![-Real.cos t, -Real.sin t] : Fin 2 → ℝ) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (Real.hasDerivAt_sin t).neg
    · exact Real.hasDerivAt_cos t
  convert (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t h using 1
  · rfl
  · ext i
    fin_cases i <;> rfl

/-- The angular unit-normal parametrization is one-Lipschitz. -/
theorem lipschitzWith_normalVector_real :
    LipschitzWith 1 (fun t : ℝ ↦ normalVector (t : Real.Angle)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hasDerivAt_normalVector t).differentiableAt)
  intro t
  rw [(hasDerivAt_normalVector t).deriv]
  change ‖tangentVector (t : Real.Angle)‖ ≤ (1 : ℝ)
  rw [norm_tangentVector]

/-- The angular unit-tangent parametrization is one-Lipschitz. -/
theorem lipschitzWith_tangentVector_real :
    LipschitzWith 1 (fun t : ℝ ↦ tangentVector (t : Real.Angle)) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t ↦ (hasDerivAt_tangentVector t).differentiableAt)
  intro t
  rw [(hasDerivAt_tangentVector t).deriv]
  change ‖-normalVector (t : Real.Angle)‖ ≤ (1 : ℝ)
  rw [norm_neg, norm_normalVector_real]

/-- A combination of the rotating frame whose coefficients are globally Lipschitz and bounded on a
set is Lipschitz on that set. -/
theorem lipschitzOnWith_frameCombination {f g : ℝ → ℝ} {C M : ℝ} {D : NNReal} {s : Set ℝ}
    (hD : 2 * (C + M) ≤ (D : ℝ)) (hM : 0 ≤ M)
    (hf : ∀ x y : ℝ, |f x - f y| ≤ C * |x - y|) (hg : ∀ x y : ℝ, |g x - g y| ≤ C * |x - y|)
    (hfM : ∀ x ∈ s, |f x| ≤ M) (hgM : ∀ x ∈ s, |g x| ≤ M) :
    LipschitzOnWith D (fun x : ℝ ↦ f x • normalVector (x : Real.Angle) +
      g x • tangentVector (x : Real.Angle)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hframe (u v : ℝ) : dist (normalVector (u : Real.Angle)) (normalVector (v : Real.Angle)) ≤
      |u - v| ∧ dist (tangentVector (u : Real.Angle)) (tangentVector (v : Real.Angle)) ≤
        |u - v| := by
    constructor
    · simpa [Real.dist_eq] using lipschitzWith_normalVector_real.dist_le_mul u v
    · simpa [Real.dist_eq] using lipschitzWith_tangentVector_real.dist_le_mul u v
  have hpair (p q : ℝ) (u w : Point) (hu : ‖u‖ = 1) (hq : |q| ≤ M)
      (huw : dist u w ≤ |x - y|) : dist (p • u) (q • w) ≤ |p - q| + M * |x - y| := by
    have h1 : dist (p • u) (q • u) ≤ |p - q| := by
      simpa [hu, Real.dist_eq] using dist_pair_smul p q u
    have h2 : dist (q • u) (q • w) ≤ M * |x - y| := by
      refine (dist_smul_pair q u w).trans ?_
      rw [Real.dist_eq, sub_zero]
      exact mul_le_mul hq huw dist_nonneg hM
    exact (dist_triangle _ _ _).trans (add_le_add h1 h2)
  have h1 := hpair (f x) (f y) (normalVector (x : Real.Angle)) (normalVector (y : Real.Angle))
    (norm_normalVector_real x) (hfM y hy) (hframe x y).1
  have h2 := hpair (g x) (g y) (tangentVector (x : Real.Angle)) (tangentVector (y : Real.Angle))
    (norm_tangentVector _) (hgM y hy) (hframe x y).2
  have htri := dist_add_add_le (f x • normalVector (x : Real.Angle))
    (g x • tangentVector (x : Real.Angle)) (f y • normalVector (y : Real.Angle))
    (g y • tangentVector (y : Real.Angle))
  have hfxy := hf x y
  have hgxy := hg x y
  have hd : 2 * (C + M) * |x - y| ≤ (D : ℝ) * |x - y| :=
    mul_le_mul_of_nonneg_right hD (abs_nonneg _)
  rw [Real.dist_eq]
  linarith

/-- The angular derivative of a fixed normal projection is its tangent projection. -/
theorem hasDerivAt_inner_normalVector (A : Point) (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ inner ℝ A (normalVector (u : Real.Angle)))
      (inner ℝ A (tangentVector (t : Real.Angle))) t := by
  simpa using (hasDerivAt_const t A).inner ℝ (hasDerivAt_normalVector t)

/-- A contact point in a normal direction has the support derivative as tangent coordinate. -/
theorem exists_contact_of_hasDerivAt {s : Set Point} (hcomp : IsCompact s)
    (hne : s.Nonempty) {t d : ℝ}
    (hd : HasDerivAt (fun u : ℝ ↦ supportValue s (u : Real.Angle)) d t) :
    ∃ A ∈ s, inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) ∧
      inner ℝ A (tangentVector (t : Real.Angle)) = d := by
  obtain ⟨A, hA, hmax, -⟩ := hcomp.exists_sSup_image_eq_and_ge
    (f := fun p : Point ↦ inner ℝ p (normalVector (t : Real.Angle))) hne
    (continuous_inner.comp (continuous_id.prodMk continuous_const)).continuousOn
  have hAt : inner ℝ A (normalVector (t : Real.Angle)) = supportValue s (t : Real.Angle) := by
    simpa only [supportValue] using hmax.symm
  refine ⟨A, hA, hAt, ?_⟩
  set F : ℝ → ℝ := fun u ↦ supportValue s (u : Real.Angle) -
    inner ℝ A (normalVector (u : Real.Angle)) with hF
  have hFmin : IsLocalMin F t := by
    filter_upwards with u
    have h1 : inner ℝ A (normalVector (u : Real.Angle)) ≤ supportValue s (u : Real.Angle) :=
      inner_le_supportValue_of_isCompact hcomp hA _
    simp only [hF, hAt, sub_self]
    linarith
  have hFderiv : HasDerivAt F (d - inner ℝ A (tangentVector (t : Real.Angle))) t :=
    hd.sub (hasDerivAt_inner_normalVector A t)
  have := hFmin.hasDerivAt_eq_zero hFderiv
  linarith
end MovingSofa
