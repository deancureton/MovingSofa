import MovingSofa.Analysis.BoundedVariation
import MovingSofa.ForMathlib.BoundedVariation
import Mathlib.Analysis.Calculus.ContDiff.RCLike

noncomputable section

namespace MovingSofa

/-- A continuously differentiable planar path on a compact interval has continuous
bounded-variation coordinates. -/
def continuousBVOfContDiffOn {a b : ℝ} (f : ℝ → Point)
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b)) : ContinuousBVPaths a b := by
  refine ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf.continuousOn, ?_⟩
  obtain ⟨C, hC⟩ := hf.exists_lipschitzOnWith (by norm_num) (convex_Icc a b) isCompact_Icc
  have hid : BoundedVariationOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ := by
    apply MonotoneOn.boundedVariationOn (C := |a| + |b|)
      (show MonotoneOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ from
        fun _ _ _ _ h ↦ h)
    intro t _
    apply abs_le.mpr
    constructor
    · linarith [t.property.1, neg_abs_le a, abs_nonneg b]
    · linarith [t.property.2, le_abs_self b, abs_nonneg a]
  have hpath := hC.comp_boundedVariationOn (fun t _ ↦ t.property) hid
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hpath

/-- A Lipschitz planar path on a compact interval has continuous bounded-variation coordinates. -/
def continuousBVOfLipschitz {a b : ℝ} (f : Set.Icc a b → Point)
    {C : NNReal} (hf : LipschitzWith C f) : ContinuousBVPaths a b := by
  refine ⟨f, hf.continuous, ?_⟩
  have hid : BoundedVariationOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ := by
    apply MonotoneOn.boundedVariationOn (C := |a| + |b|)
      (show MonotoneOn (fun t : Set.Icc a b ↦ (t : ℝ)) Set.univ from
        fun _ _ _ _ h ↦ h)
    intro t _
    apply abs_le.mpr
    constructor
    · linarith [t.property.1, neg_abs_le a, abs_nonneg b]
    · linarith [t.property.2, le_abs_self b, abs_nonneg a]
  have hpath : BoundedVariationOn f Set.univ := by
    exact hf.comp_boundedVariationOn
      (show BoundedVariationOn (id : Set.Icc a b → Set.Icc a b) Set.univ from hid)
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hpath

/-- A coordinate of an interval path has bounded variation on a closed subinterval on which the
path agrees with a continuously differentiable function. -/
theorem boundedVariationOn_coord_Icc_of_contDiffOn {a b : ℝ} (g : Set.Icc a b → Point)
    {l r : ℝ} (hl : a ≤ l) (hlr : l ≤ r) (hr : r ≤ b) {F : ℝ → Point}
    (hF : ContDiffOn ℝ 1 F (Set.Icc l r))
    (hgF : ∀ t : Set.Icc l r, g ⟨t.val, hl.trans t.2.1, t.2.2.trans hr⟩ = F t.val)
    (i : Fin 2) :
    BoundedVariationOn (fun t : Set.Icc a b ↦ g t i)
      (Set.Icc ⟨l, hl, hlr.trans hr⟩ ⟨r, hl.trans hlr, hr⟩) := by
  set ι : Set.Icc l r → Set.Icc a b := fun t ↦ ⟨t.val, hl.trans t.2.1, t.2.2.trans hr⟩
  have hmono : MonotoneOn ι Set.univ := fun _ _ _ _ h ↦ h
  have himg : ι '' Set.univ =
      Set.Icc (⟨l, hl, hlr.trans hr⟩ : Set.Icc a b) ⟨r, hl.trans hlr, hr⟩ := by
    ext x
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨t.2.1, t.2.2⟩
    · intro hx
      exact ⟨⟨x.val, hx.1, hx.2⟩, Set.mem_univ _, Subtype.ext rfl⟩
  show eVariationOn _ _ ≠ ⊤
  rw [← himg, ← eVariationOn.comp_eq_of_monotoneOn _ ι hmono]
  have hfun : ((fun t : Set.Icc a b ↦ g t i) ∘ ι) = fun t : Set.Icc l r ↦ F t.val i := by
    funext t
    exact congrArg (fun p : Point ↦ p i) (hgF t)
  rw [hfun]
  exact (continuousBVOfContDiffOn F hF).property.2 i

/-- Gluing two continuously differentiable pieces along a shared endpoint gives a continuous
path of bounded variation. -/
def continuousBVOfContDiffOnIccUnionIcc {a b c : ℝ} (f : ℝ → Point) (hab : a ≤ b) (hbc : b ≤ c)
    (h₁ : ContDiffOn ℝ 1 f (Set.Icc a b)) (h₂ : ContDiffOn ℝ 1 f (Set.Icc b c)) :
    ContinuousBVPaths a c := by
  have hf : ContinuousOn f (Set.Icc a c) := by
    rw [← Set.Icc_union_Icc_eq_Icc hab hbc]
    exact h₁.continuousOn.union_of_isClosed h₂.continuousOn isClosed_Icc isClosed_Icc
  refine ⟨fun t ↦ f t, continuousOn_iff_continuous_domRestrict.mp hf, fun i ↦ ?_⟩
  refine BoundedVariationOn.univ_of_Icc_endpoints (hab.trans hbc)
    (BoundedVariationOn.Icc_union_Icc
      (show (⟨a, le_rfl, hab.trans hbc⟩ : Set.Icc a c) ≤ ⟨b, hab, hbc⟩ from hab)
      (show (⟨b, hab, hbc⟩ : Set.Icc a c) ≤ ⟨c, hab.trans hbc, le_rfl⟩ from hbc)
      (boundedVariationOn_coord_Icc_of_contDiffOn _ le_rfl hab hbc h₁ (fun _ ↦ rfl) i)
      (boundedVariationOn_coord_Icc_of_contDiffOn _ hab hbc le_rfl h₂ (fun _ ↦ rfl) i))

end MovingSofa
