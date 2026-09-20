import MovingSofa.Cap.Basic
import MovingSofa.Classical.Area
import MovingSofa.Geometry.Reflection

noncomputable section

namespace MovingSofa

/-- Image of a convex body under the cap reflection. -/
def reflectedBody (ω : ℝ) (K : ConvexBody Point) : ConvexBody Point where
  carrier := capReflection ω '' (K : Set Point)
  convex' := K.convex.linear_image (capReflection ω).toLinearEquiv.toLinearMap
  isCompact' := K.isCompact.image (capReflection ω).continuous
  nonempty' := K.nonempty.image _

/-- Support values of a reflected body are indexed by reflected normal angles. -/
theorem supportValue_reflectedBody (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    supportValue (reflectedBody ω K) a =
      supportValue K (reflectedAngle ω a) := by
  unfold supportValue
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, (inner_capReflection_normalVector ω q a).symm⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨capReflection ω q, ⟨q, hq, rfl⟩,
      inner_capReflection_normalVector ω q a⟩

/-- A reflected normal remains among the allowed cap normals. -/
theorem reflectedAngle_mem_capNormals {ω : ℝ} (a : Real.Angle)
    (ha : a ∈ ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
      capLowerNormals ω) :
    reflectedAngle ω a ∈
      ((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω := by
  rcases ha with ha | ha
  · obtain ⟨t, ht, rfl⟩ := ha
    left
    refine ⟨ω + Real.pi / 2 - t, ?_, (reflectedAngle_coe ω t).symm⟩
    rcases ht with ht | ht
    · right
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · left
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · right
    simp only [capLowerNormals, Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with rfl | rfl
    · right
      rw [reflectedAngle_coe]
      have hperiod :
          (((-Real.pi / 2 : ℝ) : Real.Angle)) =
            (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by
        calc
          (((-Real.pi / 2 : ℝ) : Real.Angle)) =
              (((-Real.pi / 2 + 2 * Real.pi : ℝ) : Real.Angle)) := by
                rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
          _ = (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by congr 1; ring
      convert hperiod using 1
      all_goals ring_nf
    · left
      rw [reflectedAngle_coe]
      have hperiod :
          (((ω - Real.pi : ℝ) : Real.Angle)) =
            (((ω + Real.pi : ℝ) : Real.Angle)) := by
        calc
          (((ω - Real.pi : ℝ) : Real.Angle)) =
              (((ω - Real.pi + 2 * Real.pi : ℝ) : Real.Angle)) := by
                rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
          _ = (((ω + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
      convert hperiod using 1
      all_goals ring_nf

/-- Reflect a half-plane presentation when its allowed normals are transported. -/
theorem HasHalfPlaneRepresentation.reflectedBody {ω : ℝ}
    {K : ConvexBody Point} {N N' : Set Real.Angle}
    (hK : HasHalfPlaneRepresentation K N)
    (hN : ∀ a ∈ N, reflectedAngle ω a ∈ N') :
    HasHalfPlaneRepresentation (reflectedBody ω K) N' := by
  obtain ⟨C, hCN, hKC⟩ := hK
  let ρ : Real.Angle × ℝ → Real.Angle × ℝ :=
    fun c ↦ (reflectedAngle ω c.1, c.2)
  refine ⟨ρ '' C, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact hN c.1 (hCN c hc)
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simp only [Set.mem_iInter]
      intro c hc
      obtain ⟨d, hd, rfl⟩ := hc
      change inner ℝ (capReflection ω q)
        (normalVector (reflectedAngle ω d.1)) ≤ d.2
      rw [inner_capReflection_normalVector, reflectedAngle_involutive]
      rw [hKC] at hq
      exact Set.mem_iInter.mp (Set.mem_iInter.mp hq d) hd
    · intro hp
      refine ⟨capReflection ω p, ?_, capReflection_involutive ω p⟩
      rw [hKC]
      simp only [Set.mem_iInter]
      intro c hc
      have hpc := Set.mem_iInter.mp
        (Set.mem_iInter.mp hp (ρ c)) ⟨c, hc, rfl⟩
      change inner ℝ p (normalVector (reflectedAngle ω c.1)) ≤ c.2 at hpc
      change inner ℝ (capReflection ω p) (normalVector c.1) ≤ c.2
      rw [inner_capReflection_normalVector]
      exact hpc

/-- Reflection preserves the standard cap half-plane presentation. -/
theorem reflectedBody_halfPlaneRepresentation {ω : ℝ}
    (K : ConvexBody Point)
    (hK : HasHalfPlaneRepresentation K
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω)) :
    HasHalfPlaneRepresentation (reflectedBody ω K)
      (((fun t : ℝ ↦ (t : Real.Angle)) '' capUpperAngles ω) ∪
        capLowerNormals ω) :=
  hK.reflectedBody fun a ha ↦ reflectedAngle_mem_capNormals a ha

/-- Reflection exchanges the normalized upper normal at `ω` with the vertical normal. -/
theorem reflectedAngle_at_omega (ω : ℝ) :
    reflectedAngle ω (ω : Real.Angle) =
      ((Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection exchanges the vertical normal with the normalized upper normal at `ω`. -/
theorem reflectedAngle_at_pi_div_two (ω : ℝ) :
    reflectedAngle ω ((Real.pi / 2 : ℝ) : Real.Angle) =
      (ω : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection exchanges the two lower cap normals. -/
theorem reflectedAngle_at_omega_add_pi (ω : ℝ) :
    reflectedAngle ω ((ω + Real.pi : ℝ) : Real.Angle) =
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  have hperiod :
      (((-Real.pi / 2 : ℝ) : Real.Angle)) =
        (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by
    calc
      (((-Real.pi / 2 : ℝ) : Real.Angle)) =
          (((-Real.pi / 2 + 2 * Real.pi : ℝ) : Real.Angle)) := by
            rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      _ = (((3 * Real.pi / 2 : ℝ) : Real.Angle)) := by congr 1; ring
  convert hperiod using 1
  all_goals ring_nf

/-- Reflection exchanges the two lower cap normals. -/
theorem reflectedAngle_at_three_pi_div_two (ω : ℝ) :
    reflectedAngle ω ((3 * Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω + Real.pi : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  have hperiod :
      (((ω - Real.pi : ℝ) : Real.Angle)) =
        (((ω + Real.pi : ℝ) : Real.Angle)) := by
    calc
      (((ω - Real.pi : ℝ) : Real.Angle)) =
          (((ω - Real.pi + 2 * Real.pi : ℝ) : Real.Angle)) := by
            rw [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
      _ = (((ω + Real.pi : ℝ) : Real.Angle)) := by congr 1; ring
  convert hperiod using 1
  all_goals ring_nf

/-- Reflection preserves the normalized cap conditions. -/
theorem reflectedBody_isCap {ω : ℝ} (K : CapSpace ω) :
    IsCap ω (reflectedBody ω K.val) := by
  rcases K.property with ⟨hω0, hωle, hω, hpi, hlowω, hlowpi, hrepr⟩
  refine ⟨hω0, hωle, ?_, ?_, ?_, ?_,
    reflectedBody_halfPlaneRepresentation K.val hrepr⟩
  · rw [supportValue_reflectedBody, reflectedAngle_at_omega, hpi]
  · rw [supportValue_reflectedBody, reflectedAngle_at_pi_div_two, hω]
  · rw [supportValue_reflectedBody, reflectedAngle_at_omega_add_pi, hlowpi]
  · rw [supportValue_reflectedBody, reflectedAngle_at_three_pi_div_two, hlowω]

/-- The cap reflection preserves the lower fan. -/
theorem capReflection_image_capFan (ω : ℝ) :
    capReflection ω '' capFan ω = capFan ω := by
  unfold capFan
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_normalHalfPlane,
    capReflection_image_normalHalfPlane,
    reflectedAngle_at_omega, reflectedAngle_at_pi_div_two,
    Set.inter_comm]

/-- Reflection sends the complementary normal to its paired normal. -/
theorem reflectedAngle_sub (ω t : ℝ) :
    reflectedAngle ω ((ω - t : ℝ) : Real.Angle) =
      ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection sends the complementary paired normal back to the original normal. -/
theorem reflectedAngle_sub_add_pi_div_two (ω t : ℝ) :
    reflectedAngle ω ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) =
      (t : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection sends a paired normal to the complementary normal. -/
theorem reflectedAngle_add_pi_div_two (ω t : ℝ) :
    reflectedAngle ω ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω - t : ℝ) : Real.Angle) := by
  rw [reflectedAngle_coe]
  congr 1
  ring

/-- Reflection transports inward quadrants at complementary angles. -/
theorem innerQuadrant_reflection (ω t : ℝ) (K : ConvexBody Point) :
    innerQuadrant (reflectedBody ω K) t =
      capReflection ω '' innerQuadrant K (ω - t) := by
  unfold innerQuadrant
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_normalHalfPlane,
    capReflection_image_normalHalfPlane,
    supportValue_reflectedBody, supportValue_reflectedBody,
    reflectedAngle_sub, reflectedAngle_sub_add_pi_div_two,
    reflectedAngle_add_pi_div_two, reflectedAngle_coe, Set.inter_comm]
  congr 2
  congr 1
  ring_nf

/-- The preimage and image of a set agree under the involutive cap reflection. -/
theorem capReflection_preimage_eq_image (ω : ℝ) (S : Set Point) :
    capReflection ω ⁻¹' S = capReflection ω '' S := by
  ext p
  constructor
  · intro hp
    exact ⟨capReflection ω p, hp, capReflection_involutive ω p⟩
  · rintro ⟨q, hq, rfl⟩
    simpa only [Set.mem_preimage, capReflection_involutive] using hq

/-- The cap reflection preserves the real Lebesgue area of measurable sets. -/
theorem area_image_capReflection (ω : ℝ) (S : Set Point)
    (hS : MeasurableSet S) :
    ClassicalResults.area (capReflection ω '' S) = ClassicalResults.area S := by
  change (MeasureTheory.volume (capReflection ω '' S)).toReal =
    (MeasureTheory.volume S).toReal
  rw [← capReflection_preimage_eq_image]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving (capReflection ω)).measure_preimage
    hS.nullMeasurableSet

/-- The vertical reflection of a body has mirrored support values. -/
theorem supportValue_reflectedBody_pi_div_two (K : ConvexBody Point) (u : ℝ) :
    supportValue (reflectedBody (Real.pi / 2) K : Set Point) (u : Real.Angle) =
      supportValue (K : Set Point) ((Real.pi - u : ℝ) : Real.Angle) := by
  have hang : ((Real.pi / 2 + Real.pi / 2 - u : ℝ) : Real.Angle) =
      ((Real.pi - u : ℝ) : Real.Angle) := by congr 1; ring
  rw [supportValue_reflectedBody, reflectedAngle_coe, hang]

/-- The vertical reflection mirrors normal projections. -/
theorem inner_capReflection_pi_div_two (p : Point) (u : ℝ) :
    inner ℝ (capReflection (Real.pi / 2) p) (normalVector (u : Real.Angle)) =
      inner ℝ p (normalVector ((Real.pi - u : ℝ) : Real.Angle)) := by
  have hang : ((Real.pi / 2 + Real.pi / 2 - u : ℝ) : Real.Angle) =
      ((Real.pi - u : ℝ) : Real.Angle) := by congr 1; ring
  rw [inner_capReflection_normalVector, reflectedAngle_coe, hang]
end MovingSofa
