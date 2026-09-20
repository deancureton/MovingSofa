import MovingSofa.Cap.Special.Domain

noncomputable section

open scoped unitInterval

namespace MovingSofa

def IsCapTailCombination (t : I) (X Y Z : CapTailSpace) : Prop :=
  Z.cap.val.val = convexBodyCombination t X.cap.val.val Y.cap.val.val ∧
    Z.rightBody = convexBodyCombination t X.rightBody Y.rightBody ∧
    Z.leftBody = convexBodyCombination t X.leftBody Y.leftBody

def capTailCombination (t : I) (X Y : CapTailSpace) : CapTailSpace := by
  classical
  exact if h : ∃ Z, IsCapTailCombination t X Y Z then h.choose else X

theorem capTail_isConvexDomain :
    (∀ t X Y, IsCapTailCombination t X Y (capTailCombination t X Y)) ∧
    IsConvexDomain.{0, 0} capTailCombination := by
  -- A cap-tail triple is determined by its three convex bodies.
  have hext : ∀ X Y : CapTailSpace, X.cap = Y.cap → X.rightBody = Y.rightBody →
      X.leftBody = Y.leftBody → X = Y := by
    intro X Y hcap hright hleft
    revert hcap hright hleft
    obtain ⟨c₁, r₁, l₁, -, -, -, -, -, -⟩ := X
    obtain ⟨c₂, r₂, l₂, -, -, -, -, -, -⟩ := Y
    intro hcap hright hleft
    subst hcap; subst hright; subst hleft
    rfl
  -- Minkowski interpolation is monotone in both of its convex-body arguments.
  have hmono : ∀ (t : I) (A B C D : ConvexBody Point), (A : Set Point) ⊆ (C : Set Point) →
      (B : Set Point) ⊆ (D : Set Point) →
      (convexBodyCombination t A B : Set Point) ⊆
        (convexBodyCombination t C D : Set Point) := by
    intro t A B C D hAC hBD z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := (mem_convexBodyCombination_iff t A B z).1 hz
    exact (mem_convexBodyCombination_iff t C D _).2 ⟨x, hAC hx, y, hBD hy, rfl⟩
  -- ### The cap-tail conditions are closed under componentwise Minkowski interpolation
  have hclosed : ∀ (t : I) (X Y : CapTailSpace), ∃ Z, IsCapTailCombination t X Y Z := by
    intro t X Y
    have hKval : (specialCapCombination t X.cap Y.cap).val.val =
        convexBodyCombination t X.cap.val.val Y.cap.val.val :=
      specialCap_isConvexDomain.1 t X.cap Y.cap
    have hlin : ∀ (K L : ConvexBody Point) (a : Real.Angle),
        supportValue (convexBodyCombination t K L) a =
          (1 - (t : ℝ)) * supportValue K a + (t : ℝ) * supportValue L a :=
      fun K L ↦ (convexBody_maps_linear t K L).1
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
    have hb : ∀ a b c d : ℝ, a + b ≤ 1 → c + d ≤ 1 →
        ((1 - (t : ℝ)) * a + (t : ℝ) * c) + ((1 - (t : ℝ)) * b + (t : ℝ) * d) ≤ 1 := by
      intro a b c d h₁ h₂
      nlinarith [mul_le_mul_of_nonneg_left h₁ ht1, mul_le_mul_of_nonneg_left h₂ ht0]
    have he : ∀ a b c d : ℝ, a + b = 1 → c + d = 1 →
        ((1 - (t : ℝ)) * a + (t : ℝ) * c) + ((1 - (t : ℝ)) * b + (t : ℝ) * d) = 1 := by
      intro a b c d h₁ h₂
      linear_combination (1 - (t : ℝ)) * h₁ + (t : ℝ) * h₂
    refine ⟨⟨specialCapCombination t X.cap Y.cap,
      convexBodyCombination t X.rightBody Y.rightBody,
      convexBodyCombination t X.leftBody Y.leftBody,
      ?_, ?_, ?_, ?_, ?_, ?_⟩, hKval, rfl, rfl⟩
    · rw [hKval]
      exact hmono t _ _ _ _ X.right_subset Y.right_subset
    · rw [hKval]
      exact hmono t _ _ _ _ X.left_subset Y.left_subset
    · intro s hs
      rw [hKval, hlin, hlin]
      exact hb _ _ _ _ (X.right_bound s hs) (Y.right_bound s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact he _ _ _ _ (X.right_eq s hs) (Y.right_eq s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact hb _ _ _ _ (X.left_bound s hs) (Y.left_bound s hs)
    · intro s hs
      rw [hKval, hlin, hlin]
      exact he _ _ _ _ (X.left_eq s hs) (Y.left_eq s hs)
  -- ### The totalized selection therefore always matches
  have h1 : ∀ (t : I) (X Y : CapTailSpace),
      IsCapTailCombination t X Y (capTailCombination t X Y) := by
    intro t X Y
    have h := hclosed t X Y
    rw [capTailCombination, dite_eq_left h]
    exact h.choose_spec
  refine ⟨h1, ?_⟩
  -- ### The convex-domain structure is inherited from three copies of the body domain
  obtain ⟨V, e, hinj, -, hcomb⟩ := convexBody_isConvexDomain
  refine ⟨ModuleCat.of ℝ (V × V × V),
    fun X ↦ (e X.cap.val.val, e X.rightBody, e X.leftBody), ?_, ?_, ?_⟩
  · intro X Y h
    simp only [Prod.mk.injEq] at h
    exact hext X Y (Subtype.ext (Subtype.ext (hinj h.1))) (hinj h.2.1) (hinj h.2.2)
  · rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩ a b ha hb hab
    have hb1 : b ≤ 1 := by linarith
    have hba : 1 - b = a := by linarith
    obtain ⟨hc, hr, hl⟩ := h1 ⟨b, hb, hb1⟩ X Y
    refine ⟨capTailCombination ⟨b, hb, hb1⟩ X Y, ?_⟩
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hba] using (congrArg e hc).trans (hcomb ⟨b, hb, hb1⟩ _ _)
    · simpa only [hba] using (congrArg e hr).trans (hcomb ⟨b, hb, hb1⟩ _ _)
    · simpa only [hba] using (congrArg e hl).trans (hcomb ⟨b, hb, hb1⟩ _ _)
  · intro t X Y
    obtain ⟨hc, hr, hl⟩ := h1 t X Y
    simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk.injEq]
    exact ⟨(congrArg e hc).trans (hcomb t _ _), (congrArg e hr).trans (hcomb t _ _),
      (congrArg e hl).trans (hcomb t _ _)⟩

end MovingSofa
