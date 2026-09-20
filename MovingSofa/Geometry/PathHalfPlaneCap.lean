import MovingSofa.Cap.Basic
import MovingSofa.Geometry.Parallelogram
import MovingSofa.Geometry.Support
import MovingSofa.ForMathlib.Analysis.InnerProductSpace.Box

noncomputable section

namespace MovingSofa

def outerPathConstraintSet (x : Set.Icc (0 : ℝ) (Real.pi / 2) → Point) : Set Point :=
  {q | 0 ≤ q 1 ∧ ∀ t,
    inner ℝ q (normalVector (t.val : Real.Angle)) ≤
      inner ℝ (x t) (normalVector (t.val : Real.Angle)) + 1 ∧
    inner ℝ q (tangentVector (t.val : Real.Angle)) ≤
      inner ℝ (x t) (tangentVector (t.val : Real.Angle)) + 1}

theorem outerPathConstraintSet_isCap
    (x : Set.Icc (0 : ℝ) (Real.pi / 2) → Point)
    (hx : x ⟨0, le_rfl, by positivity⟩ = 0)
    (hbottom : ∃ p ∈ outerPathConstraintSet x, p 1 = 0)
    (htop : ∃ p ∈ outerPathConstraintSet x, p 1 = 1) :
    ∃ K : ConvexBody Point, (K : Set Point) = outerPathConstraintSet x ∧
      IsCap (Real.pi / 2) K := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hxO : x ⟨0, le_rfl, hpi⟩ = 0 := hx
  -- half-plane representation with cap-admissible normals
  obtain ⟨C, hCnormals, hrep⟩ :
      ∃ C : Set (Real.Angle × ℝ),
        (∀ c ∈ C, c.1 ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles (Real.pi / 2)) ∪
          capLowerNormals (Real.pi / 2)) ∧
        outerPathConstraintSet x = ⋂ c ∈ C, normalHalfPlane c.1 c.2 false false := by
    refine ⟨{(((3 * Real.pi / 2 : ℝ) : Real.Angle), (0 : ℝ))} ∪
      ((Set.range fun t : Set.Icc (0 : ℝ) (Real.pi / 2) ↦
          (((t.val : ℝ) : Real.Angle),
            inner ℝ (x t) (normalVector ((t.val : ℝ) : Real.Angle)) + 1)) ∪
        (Set.range fun t : Set.Icc (0 : ℝ) (Real.pi / 2) ↦
          (((t.val + Real.pi / 2 : ℝ) : Real.Angle),
            inner ℝ (x t) (tangentVector ((t.val : ℝ) : Real.Angle)) + 1))), ?_, ?_⟩
    · rintro c (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl ⟨t.val, Or.inl ⟨t.2.1, t.2.2⟩, rfl⟩
      · exact Or.inl ⟨t.val + Real.pi / 2,
          Or.inr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩, rfl⟩
    · ext q
      simp only [Set.mem_iInter, Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
      constructor
      · rintro ⟨hq0, hqt⟩ c (rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩)
        · show inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
          rw [inner_normalVector_three_pi_div_two]
          linarith
        · exact (hqt t).1
        · show inner ℝ q (normalVector ((t.val + Real.pi / 2 : ℝ) : Real.Angle)) ≤ _
          rw [normalVector_add_pi_div_two_real]
          exact (hqt t).2
      · intro hq
        refine ⟨?_, fun t ↦ ⟨?_, ?_⟩⟩
        · have h : inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0 :=
            hq _ (Or.inl rfl)
          rw [inner_normalVector_three_pi_div_two] at h
          linarith
        · exact hq _ (Or.inr (Or.inl ⟨t, rfl⟩))
        · have h : inner ℝ q (normalVector ((t.val + Real.pi / 2 : ℝ) : Real.Angle)) ≤
              inner ℝ (x t) (tangentVector ((t.val : ℝ) : Real.Angle)) + 1 :=
            hq _ (Or.inr (Or.inr ⟨t, rfl⟩))
          rwa [normalVector_add_pi_div_two_real] at h
  -- the constraints at the two endpoints confine the set to a bounded rectangle
  have hxbox : ∀ q ∈ outerPathConstraintSet x,
      x ⟨Real.pi / 2, hpi, le_rfl⟩ 0 - 1 ≤ q 0 ∧ q 0 ≤ 1 ∧ 0 ≤ q 1 ∧ q 1 ≤ 1 := by
    rintro q ⟨hq0, hqt⟩
    have h0n : inner ℝ q (normalVector ((0 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨0, le_rfl, hpi⟩) (normalVector ((0 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨0, le_rfl, hpi⟩).1
    have h0t : inner ℝ q (tangentVector ((0 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨0, le_rfl, hpi⟩) (tangentVector ((0 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨0, le_rfl, hpi⟩).2
    have hTt : inner ℝ q (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤
        inner ℝ (x ⟨Real.pi / 2, hpi, le_rfl⟩)
          (tangentVector ((Real.pi / 2 : ℝ) : Real.Angle)) + 1 :=
      (hqt ⟨Real.pi / 2, hpi, le_rfl⟩).2
    rw [hxO, inner_zero_left, inner_normalVector_zero] at h0n
    rw [hxO, inner_zero_left, inner_tangentVector_zero] at h0t
    rw [inner_tangentVector_pi_div_two, inner_tangentVector_pi_div_two] at hTt
    exact ⟨by linarith, by linarith, hq0, by linarith⟩
  obtain ⟨pb, hpb, hpb1⟩ := hbottom
  obtain ⟨pt, hpt, hpt1⟩ := htop
  obtain ⟨K, hKset⟩ : ∃ K : ConvexBody Point, (K : Set Point) = outerPathConstraintSet x := by
    refine ⟨{ carrier := outerPathConstraintSet x
              convex' := ?_
              isCompact' := ?_
              nonempty' := ⟨pb, hpb⟩ }, rfl⟩
    · rw [hrep]
      exact convex_iInter fun c ↦ convex_iInter fun _ ↦ convex_normalHalfPlane c.1 c.2 false
    · refine Metric.isCompact_iff_isClosed_bounded.2 ⟨?_, ?_⟩
      · rw [hrep]
        exact isClosed_iInter fun c ↦ isClosed_iInter fun _ ↦
          isClosed_normalHalfPlane c.1 c.2 false
      · refine (EuclideanSpace.isBounded_coordinate_rectangle
          (x ⟨Real.pi / 2, hpi, le_rfl⟩ 0 - 1) 1 0 1).subset fun q hq ↦ ?_
        obtain ⟨h1, h2, h3, h4⟩ := hxbox q hq
        exact ⟨h1, h2, h3, h4⟩
  -- the strip inclusion and the two contacts fix the four normalized support values
  have hsvTop : supportValue (K : Set Point) ((Real.pi / 2 : ℝ) : Real.Angle) = 1 := by
    refine le_antisymm (supportValue_le_of_subset_normalHalfPlane K _ 1 fun q hq ↦ ?_) ?_
    · show inner ℝ q (normalVector ((Real.pi / 2 : ℝ) : Real.Angle)) ≤ 1
      rw [inner_normalVector_pi_div_two]
      rw [hKset] at hq
      exact (hxbox q hq).2.2.2
    · have h := inner_le_supportValue K (hKset ▸ hpt) ((Real.pi / 2 : ℝ) : Real.Angle)
      rwa [inner_normalVector_pi_div_two, hpt1] at h
  have hsvBot : supportValue (K : Set Point) ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    refine le_antisymm (supportValue_le_of_subset_normalHalfPlane K _ 0 fun q hq ↦ ?_) ?_
    · show inner ℝ q (normalVector ((3 * Real.pi / 2 : ℝ) : Real.Angle)) ≤ 0
      rw [inner_normalVector_three_pi_div_two]
      rw [hKset] at hq
      linarith [(hxbox q hq).2.2.1]
    · have h := inner_le_supportValue K (hKset ▸ hpb) ((3 * Real.pi / 2 : ℝ) : Real.Angle)
      rwa [inner_normalVector_three_pi_div_two, hpb1, neg_zero] at h
  have hang : ((Real.pi / 2 + Real.pi : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
    congr 1
    ring
  exact ⟨K, hKset, by positivity, le_rfl, hsvTop, hsvTop, by rw [hang]; exact hsvBot, hsvBot,
    C, hCnormals, hKset.trans hrep⟩

end MovingSofa
