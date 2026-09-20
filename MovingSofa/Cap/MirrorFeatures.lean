import MovingSofa.Cap.Reflection
import MovingSofa.Cap.Connectedness
import MovingSofa.Analysis.SurfaceMeasure.Segment
import MovingSofa.Analysis.SurfaceMeasure.Regularity

noncomputable section

open MeasureTheory

namespace MovingSofa

private theorem mirrorReflection_eq_capReflection (ω : ℝ)
    (hω0 : 0 < ω) (hωle : ω ≤ Real.pi / 2) :
    mirrorReflection ω = capReflection ω := by
  change stripTopReflection ω = capReflection ω
  exact stripTopReflection_eq_capReflection ω hω0 hωle

private theorem capReflection_rotationMap (ω s : ℝ) (p : Point) :
    capReflection ω (rotationMap (s : Real.Angle) p) =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) := by
  have hang : (ω : Real.Angle) - (s : Real.Angle) =
      ((ω - s : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_sub]
  ext i
  fin_cases i
  · change capReflection ω (rotationMap (s : Real.Angle) p) 0 =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) 0
    rw [capReflection_apply_zero]
    rw [← hang]
    simp [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply,
      coordinateSwap]
    rw [hang, Real.Angle.sin_coe, Real.Angle.cos_coe, Real.sin_sub, Real.cos_sub]
    ring
  · change capReflection ω (rotationMap (s : Real.Angle) p) 1 =
      rotationMap ((ω - s : ℝ) : Real.Angle) (coordinateSwap p) 1
    rw [capReflection_apply_one]
    rw [← hang]
    simp [rotationMap, Orientation.rotation_apply, rightAngleRotation_apply,
      coordinateSwap]
    rw [hang, Real.Angle.sin_coe, Real.Angle.cos_coe, Real.sin_sub, Real.cos_sub]
    ring

private theorem capReflection_normal_at_complement (ω t : ℝ) :
    capReflection ω (normalVector ((ω - t : ℝ) : Real.Angle)) =
      tangentVector (t : Real.Angle) := by
  rw [capReflection_normalVector]
  have hang : ω + Real.pi / 2 - (ω - t) = t + Real.pi / 2 := by ring
  rw [hang]
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

private theorem capReflection_tangent_at_complement (ω t : ℝ) :
    capReflection ω (tangentVector ((ω - t : ℝ) : Real.Angle)) =
      normalVector (t : Real.Angle) := by
  rw [capReflection_tangentVector]
  have hang : ω + Real.pi / 2 - (ω - t) = t + Real.pi / 2 := by ring
  rw [hang]
  ext i
  fin_cases i <;> simp [normalVector, tangentVector, frame,
    Real.Angle.sin_add_pi_div_two, Real.Angle.cos_add_pi_div_two]

private theorem supportValue_reflected_at (ω t : ℝ) (K : ConvexBody Point) :
    supportValue (reflectedBody ω K) (t : Real.Angle) =
      supportValue K ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) := by
  rw [supportValue_reflectedBody, reflectedAngle_coe]
  congr 2
  ring

private theorem supportValue_reflected_at_add_pi_div_two (ω t : ℝ)
    (K : ConvexBody Point) :
    supportValue (reflectedBody ω K) ((t + Real.pi / 2 : ℝ) : Real.Angle) =
      supportValue K ((ω - t : ℝ) : Real.Angle) := by
  rw [supportValue_reflectedBody, reflectedAngle_coe]
  congr 2
  ring

private theorem supportingPlacement_reflection (ω t : ℝ)
    (K : ConvexBody Point) (q : Point) :
    supportingPlacement (reflectedBody ω K) (t : Real.Angle) (coordinateSwap q) =
      capReflection ω (supportingPlacement K ((ω - t : ℝ) : Real.Angle) q) := by
  unfold supportingPlacement
  rw [map_add, map_add, map_smul, map_smul,
    capReflection_rotationMap]
  have hrot : ω - (ω - t) = t := by ring
  have htadd : (t : Real.Angle) + ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
  have hsadd : ((ω - t : ℝ) : Real.Angle) +
      ((Real.pi / 2 : ℝ) : Real.Angle) =
      ((ω - t + Real.pi / 2 : ℝ) : Real.Angle) := by
    rw [← Real.Angle.coe_add]
  rw [hrot, supportValue_reflected_at,
    htadd, supportValue_reflected_at_add_pi_div_two, hsadd,
    capReflection_normal_at_complement,
    capReflection_tangent_at_complement]
  module

private theorem coordinateSwap_involutive (p : Point) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  fin_cases i <;> simp [coordinateSwap]

private theorem coordinateSwap_image_hallway :
    coordinateSwap '' hallway = hallway := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, ⟨h.2.1, h.2.2, h.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
    · exact Or.inl ⟨b, a, ⟨h.2.2, h.1, h.2.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
  · intro hp
    refine ⟨coordinateSwap p, ?_, coordinateSwap_involutive p⟩
    rcases hp with ⟨a, b, h, rfl⟩ | ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, ⟨h.2.1, h.2.2, h.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩
    · exact Or.inl ⟨b, a, ⟨h.2.2, h.1, h.2.1⟩, by
        ext i
        fin_cases i <;> simp [coordinateSwap]⟩

private theorem coordinateSwap_image_eq_preimage (s : Set Point) :
    coordinateSwap '' s = coordinateSwap ⁻¹' s := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    change coordinateSwap (coordinateSwap q) ∈ s
    rwa [coordinateSwap_involutive]
  · intro hp
    exact ⟨coordinateSwap p, hp, coordinateSwap_involutive p⟩

private theorem coordinateSwap_image_outerQuadrant :
    coordinateSwap '' hallwayParts.outerQuadrant = hallwayParts.outerQuadrant := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_innerQuadrant :
    coordinateSwap '' hallwayParts.innerQuadrant = hallwayParts.innerQuadrant := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_a :
    coordinateSwap '' hallwayParts.a = hallwayParts.c := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_c :
    coordinateSwap '' hallwayParts.c = hallwayParts.a := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_b :
    coordinateSwap '' hallwayParts.b = hallwayParts.d := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_d :
    coordinateSwap '' hallwayParts.d = hallwayParts.b := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap]

private theorem coordinateSwap_image_bRay :
    coordinateSwap '' hallwayParts.bRay = hallwayParts.dRay := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem coordinateSwap_image_dRay :
    coordinateSwap '' hallwayParts.dRay = hallwayParts.bRay := by
  rw [coordinateSwap_image_eq_preimage]
  ext p
  simp [hallwayParts, coordinateSwap, and_comm]

private theorem supportingPlacement_image_reflection (ω t : ℝ)
    (K : ConvexBody Point) (s : Set Point) :
    supportingPlacement (reflectedBody ω K) (t : Real.Angle) ''
        (coordinateSwap '' s) =
      capReflection ω ''
        (supportingPlacement K ((ω - t : ℝ) : Real.Angle) '' s) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext q
  exact supportingPlacement_reflection ω t K q

private theorem supportingHallway_reflection (ω t : ℝ)
    (K : ConvexBody Point) :
    supportingHallway (reflectedBody ω K) (t : Real.Angle) =
      capReflection ω '' supportingHallway K ((ω - t : ℝ) : Real.Angle) := by
  unfold supportingHallway
  nth_rewrite 1 [← coordinateSwap_image_hallway]
  exact supportingPlacement_image_reflection ω t K hallway

private theorem rotatingHallwayParts_reflection (ω t : ℝ)
    (K : ConvexBody Point) :
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).innerCorner =
        capReflection ω
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).innerCorner ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).outerCorner =
        capReflection ω
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).outerCorner ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).outerQuadrant =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).outerQuadrant ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).innerQuadrant =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).innerQuadrant ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).a =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).c ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).c =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).a ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).b =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).d ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).d =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).b ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).bRay =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).dRay ∧
    (rotatingHallwayParts (reflectedBody ω K) (t : Real.Angle)).dRay =
        capReflection ω ''
          (rotatingHallwayParts K ((ω - t : ℝ) : Real.Angle)).bRay := by
  have hzero : coordinateSwap (0 : Point) = 0 := by
    ext i
    fin_cases i <;> simp [coordinateSwap]
  have hone : coordinateSwap (!₂[1, 1] : Point) = !₂[1, 1] := by
    ext i
    fin_cases i <;> simp [coordinateSwap]
  unfold rotatingHallwayParts
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hallwayParts]
    rw [← hzero]
    exact supportingPlacement_reflection ω t K 0
  · simp only [hallwayParts]
    nth_rewrite 1 [← hone]
    exact supportingPlacement_reflection ω t K !₂[1, 1]
  · nth_rewrite 1 [← coordinateSwap_image_outerQuadrant]
    exact supportingPlacement_image_reflection ω t K hallwayParts.outerQuadrant
  · nth_rewrite 1 [← coordinateSwap_image_innerQuadrant]
    exact supportingPlacement_image_reflection ω t K hallwayParts.innerQuadrant
  · nth_rewrite 1 [← coordinateSwap_image_c]
    exact supportingPlacement_image_reflection ω t K hallwayParts.c
  · nth_rewrite 1 [← coordinateSwap_image_a]
    exact supportingPlacement_image_reflection ω t K hallwayParts.a
  · nth_rewrite 1 [← coordinateSwap_image_d]
    exact supportingPlacement_image_reflection ω t K hallwayParts.d
  · nth_rewrite 1 [← coordinateSwap_image_b]
    exact supportingPlacement_image_reflection ω t K hallwayParts.b
  · nth_rewrite 1 [← coordinateSwap_image_dRay]
    exact supportingPlacement_image_reflection ω t K hallwayParts.dRay
  · nth_rewrite 1 [← coordinateSwap_image_bRay]
    exact supportingPlacement_image_reflection ω t K hallwayParts.bRay

private theorem exposedEdge_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    exposedEdge (reflectedBody ω K) a =
      capReflection ω '' exposedEdge K (reflectedAngle ω a) := by
  ext p
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hp⟩
    refine ⟨q, ⟨hq, ?_⟩, rfl⟩
    change inner ℝ (capReflection ω q) (normalVector a) =
      supportValue (reflectedBody ω K) a at hp
    change inner ℝ q (normalVector (reflectedAngle ω a)) =
      supportValue K (reflectedAngle ω a)
    rw [← inner_capReflection_normalVector ω q a,
      ← supportValue_reflectedBody ω K a]
    exact hp
  · rintro ⟨q, ⟨hq, hp⟩, rfl⟩
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    change inner ℝ (capReflection ω q) (normalVector a) =
      supportValue (reflectedBody ω K) a
    rw [inner_capReflection_normalVector, supportValue_reflectedBody]
    exact hp

private theorem exposedEdgeHeights_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    (fun p ↦ inner ℝ p (tangentVector a)) '' exposedEdge (reflectedBody ω K) a =
      -((fun p ↦ inner ℝ p (tangentVector (reflectedAngle ω a))) ''
        exposedEdge K (reflectedAngle ω a)) := by
  rw [exposedEdge_reflection]
  ext x
  simp only [Set.mem_image, Set.mem_neg]
  constructor
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨q, hq, ?_⟩
    rw [inner_capReflection_tangentVector, neg_neg]
  · rintro ⟨q, hq, hq_inner⟩
    refine ⟨capReflection ω q, ⟨q, hq, rfl⟩, ?_⟩
    rw [inner_capReflection_tangentVector, hq_inner, neg_neg]

private theorem edgeVertices_reflection (ω : ℝ) (K : ConvexBody Point)
    (a : Real.Angle) :
    edgeVertices (reflectedBody ω K) a =
      (capReflection ω (edgeVertices K (reflectedAngle ω a)).2,
        capReflection ω (edgeVertices K (reflectedAngle ω a)).1) := by
  unfold edgeVertices
  dsimp only
  rw [supportValue_reflectedBody, exposedEdgeHeights_reflection,
    Real.sSup_neg, Real.sInf_neg]
  apply Prod.ext <;> dsimp only
  · rw [map_add, map_smul, map_smul, capReflection_normalVector_angle,
      capReflection_tangentVector_angle, reflectedAngle_involutive]
    module
  · rw [map_add, map_smul, map_smul, capReflection_normalVector_angle,
      capReflection_tangentVector_angle, reflectedAngle_involutive]
    module

private theorem capVertices_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capVertices P t =
      ((capReflection ω (capVertices K (ω - t)).2.2,
        capReflection ω (capVertices K (ω - t)).2.1),
       (capReflection ω (capVertices K (ω - t)).1.2,
        capReflection ω (capVertices K (ω - t)).1.1)) := by
  dsimp only
  unfold capVertices
  rw [edgeVertices_reflection, edgeVertices_reflection]
  dsimp only
  rw [reflectedAngle_coe, reflectedAngle_coe]
  congr 1 <;> ring_nf

private theorem capReflection_normal_zero (ω : ℝ) :
    capReflection ω (normalVector 0) = tangentVector (ω : Real.Angle) := by
  simpa using capReflection_normal_at_complement ω ω

private theorem capReflection_tangent_omega (ω : ℝ) :
    capReflection ω (tangentVector (ω : Real.Angle)) = normalVector 0 := by
  simpa using capReflection_tangent_at_complement ω 0

private theorem wedgeEndpoints_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    wedgeEndpoints P t =
      (capReflection ω (wedgeEndpoints K (ω - t)).2,
        capReflection ω (wedgeEndpoints K (ω - t)).1) := by
  dsimp only
  unfold wedgeEndpoints
  rw [supportValue_reflected_at, supportValue_reflected_at_add_pi_div_two]
  apply Prod.ext <;> dsimp only
  · rw [map_smul, capReflection_tangent_omega]
    congr 2; ring_nf
  · rw [map_smul, capReflection_normal_zero]

private theorem wedgeGaps_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    wedgeGaps P t = ((wedgeGaps K (ω - t)).2, (wedgeGaps K (ω - t)).1) := by
  dsimp only
  unfold wedgeGaps
  rw [capVertices_reflection K 0, capVertices_reflection K ω,
    wedgeEndpoints_reflection K t]
  dsimp only
  apply Prod.ext <;> dsimp only
  · rw [← map_sub, ← capReflection_tangent_omega,
      (capReflection ω).inner_map_map]
    simp
  · rw [← map_sub, ← capReflection_normal_zero,
      (capReflection ω).inner_map_map]
    simp

private theorem capWedge_reflection {ω : ℝ} (K : CapSpace ω) (t : ℝ) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capWedge P t = capReflection ω '' capWedge K (ω - t) := by
  dsimp only
  unfold capWedge
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_capFan,
    (rotatingHallwayParts_reflection ω t K.val).2.2.2.1]

private theorem iUnion_innerQuadrant_reflection {ω : ℝ} (K : CapSpace ω) :
    (⋃ t ∈ Set.Ioo 0 ω, innerQuadrant (reflectedBody ω K.val) t) =
      capReflection ω '' (⋃ s ∈ Set.Ioo 0 ω, innerQuadrant K.val s) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    rcases ht with ⟨ht0, htω⟩
    rw [innerQuadrant_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨ω - t, ⟨by linarith, by linarith⟩, hq⟩, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    rcases hs with ⟨hs0, hsω⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨ω - s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [innerQuadrant_reflection]
    exact ⟨q, by simpa, rfl⟩

private theorem capNiche_reflection {ω : ℝ} (K : CapSpace ω) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capNiche P = capReflection ω '' capNiche K := by
  dsimp only
  unfold capNiche
  rw [Set.image_inter (capReflection ω).injective,
    capReflection_image_capFan, ← iUnion_innerQuadrant_reflection]

private theorem iUnion_exposedEdge_reflection {ω : ℝ} (K : CapSpace ω) :
    (⋃ t ∈ Set.Icc 0 (ω + Real.pi / 2),
        exposedEdge (reflectedBody ω K.val) (t : Real.Angle)) =
      capReflection ω ''
        (⋃ s ∈ Set.Icc 0 (ω + Real.pi / 2),
          exposedEdge K.val (s : Real.Angle)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht, hp⟩ := Set.mem_iUnion₂.mp hp
    rcases ht with ⟨ht0, htω⟩
    rw [exposedEdge_reflection] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q, Set.mem_iUnion₂.mpr ⟨ω + Real.pi / 2 - t,
      ⟨by linarith, by linarith⟩, ?_⟩, rfl⟩
    simpa only [reflectedAngle_coe] using hq
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, hq⟩ := Set.mem_iUnion₂.mp hq
    rcases hs with ⟨hs0, hsω⟩
    apply Set.mem_iUnion₂.mpr
    refine ⟨ω + Real.pi / 2 - s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [exposedEdge_reflection]
    refine ⟨q, ?_, rfl⟩
    rw [reflectedAngle_coe]
    convert hq using 1; ring_nf

private theorem capUpperBoundary_reflection {ω : ℝ} (K : CapSpace ω) :
    let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
    capUpperBoundary P = capReflection ω '' capUpperBoundary K := by
  dsimp only
  unfold capUpperBoundary
  exact iUnion_exposedEdge_reflection K

private def reflectedAngleEquiv (ω : ℝ) : Real.Angle ≃ᵐ Real.Angle :=
  MeasurableEquiv.ofInvolutive (reflectedAngle ω)
    (reflectedAngle_involutive ω) (by unfold reflectedAngle; fun_prop)

private theorem reflectedAngle_add_pi (ω : ℝ) (a : Real.Angle) :
    reflectedAngle ω (a + (Real.pi : Real.Angle)) =
      reflectedAngle ω a + (Real.pi : Real.Angle) := by
  have hpi : -(Real.pi : Real.Angle) = (Real.pi : Real.Angle) :=
    neg_eq_iff_add_eq_zero.mpr Real.Angle.coe_pi_add_coe_pi
  unfold reflectedAngle
  rw [sub_eq_add_neg, neg_add_rev, hpi]
  abel

private theorem isSegmentPresentation_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    IsSegmentPresentation (reflectedBody ω K)
      (capReflection ω d.1, capReflection ω d.2.1, reflectedAngle ω d.2.2) := by
  refine ⟨fun h ↦ hd.1 ((capReflection ω).injective h), ?_, ?_⟩
  · change capReflection ω '' (K : Set Point) =
      segment ℝ (capReflection ω d.1) (capReflection ω d.2.1)
    rw [hd.2.1]
    exact image_segment ℝ
      (capReflection ω).toLinearEquiv.toLinearMap.toAffineMap d.1 d.2.1
  · rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map]
    exact hd.2.2

private theorem reflectedBody_reflectedBody (ω : ℝ) (K : ConvexBody Point) :
    reflectedBody ω (reflectedBody ω K) = K := by
  apply ConvexBody.ext
  ext p
  constructor
  · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [capReflection_involutive] using hr
  · intro hp
    exact ⟨capReflection ω p, ⟨p, hp, rfl⟩, capReflection_involutive ω p⟩

private theorem subsingleton_reflectedBody_iff (ω : ℝ) (K : ConvexBody Point) :
    ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton ↔
      (K : Set Point).Subsingleton := by
  constructor
  · intro hP p hp q hq
    apply (capReflection ω).injective
    exact hP ⟨p, hp, rfl⟩ ⟨q, hq, rfl⟩
  · intro hK _
    rintro ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hK hp hq]

private theorem exists_segmentPresentation_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) :
    (∃ d, IsSegmentPresentation (reflectedBody ω K) d) ↔
      ∃ d, IsSegmentPresentation K d := by
  constructor
  · rintro ⟨d, hd⟩
    have h := isSegmentPresentation_reflectedBody ω (reflectedBody ω K) d hd
    rw [reflectedBody_reflectedBody] at h
    exact ⟨_, h⟩
  · rintro ⟨d, hd⟩
    exact ⟨_, isSegmentPresentation_reflectedBody ω K d hd⟩

private theorem surfaceAreaMeasure_reflectedBody_of_subsingleton (ω : ℝ)
    (K : ConvexBody Point) (hK : (K : Set Point).Subsingleton) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  have hP : ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    rw [hK hp hq]
  rw [surfaceAreaMeasure_eq_zero_of_subsingleton (reflectedBody ω K) hP,
    surfaceAreaMeasure_eq_zero_of_subsingleton K hK, Measure.map_zero]

private theorem surfaceAreaMeasure_reflectedBody_of_segmentPresentation (ω : ℝ)
    (K : ConvexBody Point) (d : Point × Point × Real.Angle)
    (hd : IsSegmentPresentation K d) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  rw [surfaceAreaMeasure_eq_segmentPresentation (reflectedBody ω K)
      (capReflection ω d.1, capReflection ω d.2.1, reflectedAngle ω d.2.2)
      (isSegmentPresentation_reflectedBody ω K d hd),
    surfaceAreaMeasure_eq_segmentPresentation K d hd,
    MeasureTheory.Measure.map_smul _ (reflectedAngleEquiv ω).measurable.aemeasurable,
    MeasureTheory.Measure.map_add _ _ (reflectedAngleEquiv ω).measurable,
    MeasureTheory.Measure.map_dirac, MeasureTheory.Measure.map_dirac,
    (capReflection ω).dist_map]
  change ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac (reflectedAngle ω d.2.2) +
        Measure.dirac (reflectedAngle ω d.2.2 + (Real.pi : Real.Angle))) =
    ENNReal.ofReal (dist d.1 d.2.1) •
      (Measure.dirac (reflectedAngle ω d.2.2) +
        Measure.dirac (reflectedAngle ω (d.2.2 + (Real.pi : Real.Angle))))
  rw [reflectedAngle_add_pi]

private theorem isExteriorNormal_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) (p : Point) (a : Real.Angle) :
    IsExteriorNormal (reflectedBody ω K) (capReflection ω p) (reflectedAngle ω a) ↔
      IsExteriorNormal K p a := by
  constructor
  · intro h q hq
    have h' := h (capReflection ω q) ⟨q, hq, rfl⟩
    rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map] at h'
    exact h'
  · intro h _
    rintro ⟨q, hq, rfl⟩
    rw [← map_sub, ← capReflection_normalVector_angle,
      (capReflection ω).inner_map_map]
    exact h q hq

private theorem mem_regularBoundary_reflectedBody_iff (ω : ℝ)
    (K : ConvexBody Point) (p : Point) :
    capReflection ω p ∈ regularBoundary (reflectedBody ω K) ↔
      p ∈ regularBoundary K := by
  have hfront : capReflection ω p ∈ frontier ((reflectedBody ω K : ConvexBody Point) : Set Point) ↔
      p ∈ frontier (K : Set Point) := by
    change capReflection ω p ∈ frontier (capReflection ω '' (K : Set Point)) ↔ _
    have himage : capReflection ω '' frontier (K : Set Point) =
        frontier (capReflection ω '' (K : Set Point)) :=
      (capReflection ω).toHomeomorph.image_frontier (K : Set Point)
    rw [← himage]
    constructor
    · rintro ⟨q, hq, hpq⟩
      have hqp : q = p := (capReflection ω).injective hpq
      simpa only [hqp] using hq
    · exact fun hp ↦ ⟨p, hp, rfl⟩
  have hunique :
      (∃! b, IsExteriorNormal (reflectedBody ω K) (capReflection ω p) b) ↔
        ∃! a, IsExteriorNormal K p a := by
    constructor
    · rintro ⟨b, hb, hub⟩
      have hbK : IsExteriorNormal K p (reflectedAngle ω b) := by
        apply (isExteriorNormal_reflectedBody_iff ω K p (reflectedAngle ω b)).mp
        simpa only [reflectedAngle_involutive] using hb
      refine ⟨reflectedAngle ω b, hbK, ?_⟩
      intro c hc
      have hcL := (isExteriorNormal_reflectedBody_iff ω K p c).mpr hc
      have hcb : reflectedAngle ω c = b := hub _ hcL
      calc
        c = reflectedAngle ω (reflectedAngle ω c) :=
          (reflectedAngle_involutive ω c).symm
        _ = reflectedAngle ω b := congrArg (reflectedAngle ω) hcb
    · rintro ⟨a, ha, hua⟩
      refine ⟨reflectedAngle ω a,
        (isExteriorNormal_reflectedBody_iff ω K p a).mpr ha, ?_⟩
      intro b hb
      have hbK : IsExteriorNormal K p (reflectedAngle ω b) := by
        apply (isExteriorNormal_reflectedBody_iff ω K p (reflectedAngle ω b)).mp
        simpa only [reflectedAngle_involutive] using hb
      have hba : reflectedAngle ω b = a := hua _ hbK
      calc
        b = reflectedAngle ω (reflectedAngle ω b) :=
          (reflectedAngle_involutive ω b).symm
        _ = reflectedAngle ω a := congrArg (reflectedAngle ω) hba
  simp only [regularBoundary, Set.mem_ofPred_eq]
  exact and_congr hfront hunique

private theorem exteriorNormalAngle_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) (p : Point) (hp : p ∈ regularBoundary K) :
    exteriorNormalAngle (reflectedBody ω K) (capReflection ω p) =
      reflectedAngle ω (exteriorNormalAngle K p) := by
  have hP := (mem_regularBoundary_reflectedBody_iff ω K p).mpr hp
  have huK : ∃! a, IsExteriorNormal K p a := hp.2
  have huP : ∃! a,
      IsExteriorNormal (reflectedBody ω K) (capReflection ω p) a := hP.2
  have hnK : IsExteriorNormal K p (exteriorNormalAngle K p) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left huK]
    generalize_proofs h
    exact h.choose_spec
  have hnP : IsExteriorNormal (reflectedBody ω K) (capReflection ω p)
      (exteriorNormalAngle (reflectedBody ω K) (capReflection ω p)) := by
    unfold exteriorNormalAngle
    rw [dite_eq_left huP]
    generalize_proofs _ h
    exact h.choose_spec
  exact huP.unique hnP ((isExteriorNormal_reflectedBody_iff ω K p _).mpr hnK)

private theorem regularBoundary_reflectedBody (ω : ℝ) (K : ConvexBody Point) :
    regularBoundary (reflectedBody ω K) =
      capReflection ω '' regularBoundary K := by
  ext q
  constructor
  · intro hq
    refine ⟨capReflection ω q, ?_, capReflection_involutive ω q⟩
    apply (mem_regularBoundary_reflectedBody_iff ω K (capReflection ω q)).mp
    simpa only [capReflection_involutive] using hq
  · rintro ⟨p, hp, rfl⟩
    exact (mem_regularBoundary_reflectedBody_iff ω K p).mpr hp

private theorem map_hausdorffMeasure_restrict_regularBoundary (ω : ℝ)
    (K : ConvexBody Point) :
    Measure.map (capReflection ω)
        ((Measure.hausdorffMeasure 1).restrict (regularBoundary K)) =
      (Measure.hausdorffMeasure 1).restrict
        (regularBoundary (reflectedBody ω K)) := by
  rw [regularBoundary_reflectedBody]
  let e := (capReflection ω).toHomeomorph.toMeasurableEquiv
  have hrestrict := e.restrict_map (Measure.hausdorffMeasure 1)
    (capReflection ω '' regularBoundary K)
  change (Measure.map (capReflection ω) (Measure.hausdorffMeasure 1)).restrict
      (capReflection ω '' regularBoundary K) =
    Measure.map (capReflection ω)
      ((Measure.hausdorffMeasure 1).restrict
        (capReflection ω ⁻¹' (capReflection ω '' regularBoundary K))) at hrestrict
  have hmap : Measure.map (capReflection ω) (Measure.hausdorffMeasure 1) =
      Measure.hausdorffMeasure 1 :=
    (capReflection ω).toIsometryEquiv.map_hausdorffMeasure 1
  rw [hmap] at hrestrict
  have hpre : capReflection ω ⁻¹' (capReflection ω '' regularBoundary K) =
      regularBoundary K := by
    exact Set.preimage_image_eq _ (capReflection ω).injective
  rw [hpre] at hrestrict
  exact hrestrict.symm

private theorem reflectedAngle_preimage_eq_image (ω : ℝ)
    (E : Set Real.Angle) :
    reflectedAngle ω ⁻¹' E = reflectedAngle ω '' E := by
  ext a
  constructor
  · intro ha
    exact ⟨reflectedAngle ω a, ha, reflectedAngle_involutive ω a⟩
  · rintro ⟨b, hb, rfl⟩
    simpa only [Set.mem_preimage, reflectedAngle_involutive] using hb

private theorem surfaceAreaMeasure_reflectedBody (ω : ℝ)
    (K : ConvexBody Point) :
    surfaceAreaMeasure (reflectedBody ω K) =
      Measure.map (reflectedAngleEquiv ω) (surfaceAreaMeasure K) := by
  by_cases hsub : (K : Set Point).Subsingleton
  · exact surfaceAreaMeasure_reflectedBody_of_subsingleton ω K hsub
  by_cases hseg : ∃ d, IsSegmentPresentation K d
  · obtain ⟨d, hd⟩ := hseg
    exact surfaceAreaMeasure_reflectedBody_of_segmentPresentation ω K d hd
  have hsubP : ¬ ((reflectedBody ω K : ConvexBody Point) : Set Point).Subsingleton :=
    fun h ↦ hsub ((subsingleton_reflectedBody_iff ω K).mp h)
  have hsegP : ¬ ∃ d, IsSegmentPresentation (reflectedBody ω K) d :=
    fun h ↦ hseg ((exists_segmentPresentation_reflectedBody_iff ω K).mp h)
  let μK := (Measure.hausdorffMeasure 1).restrict (regularBoundary K)
  let μP := (Measure.hausdorffMeasure 1).restrict
    (regularBoundary (reflectedBody ω K))
  have hμ : Measure.map (capReflection ω) μK = μP :=
    map_hausdorffMeasure_restrict_regularBoundary ω K
  have haeK : AEMeasurable (exteriorNormalAngle K) μK :=
    aemeasurable_exteriorNormalAngle_restrict_regularBoundary K _
  have haeP : AEMeasurable (exteriorNormalAngle (reflectedBody ω K)) μP :=
    aemeasurable_exteriorNormalAngle_restrict_regularBoundary (reflectedBody ω K) _
  simp only [surfaceAreaMeasure, hsub, hseg, hsubP, hsegP, ↓reduceIte]
  change Measure.map (exteriorNormalAngle (reflectedBody ω K)) μP =
    Measure.map (reflectedAngleEquiv ω)
      (Measure.map (exteriorNormalAngle K) μK)
  rw [← hμ]
  have haeP' : AEMeasurable (exteriorNormalAngle (reflectedBody ω K))
      (Measure.map (capReflection ω) μK) := by
    rwa [hμ]
  rw [AEMeasurable.map_map_of_aemeasurable haeP'
      (capReflection ω).continuous.measurable.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable
      (reflectedAngleEquiv ω).measurable.aemeasurable haeK]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_regularBoundary K)] with p hp
  exact exteriorNormalAngle_reflectedBody ω K p hp

theorem cap_mirror_features {ω : ℝ} (K : CapSpace ω) :
    ∃ P : CapSpace ω,
      (P.val : Set Point) = mirrorReflection ω '' (K.val : Set Point) ∧
      (∀ t ∈ Set.Icc 0 ω,
        supportingHallway (P.val : Set Point) (t : Real.Angle) =
        mirrorReflection ω '' supportingHallway (K.val : Set Point) ((ω - t : ℝ) : Real.Angle) ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).innerCorner = mirrorReflection ω (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).innerCorner ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).outerCorner = mirrorReflection ω (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).outerCorner ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).outerQuadrant = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).outerQuadrant ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).innerQuadrant = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).innerQuadrant ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).a = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).c ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).c = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).a ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).b = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).d ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).d = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).b ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).bRay = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).dRay ∧
        (rotatingHallwayParts (P.val : Set Point) (t : Real.Angle)).dRay = mirrorReflection ω '' (rotatingHallwayParts (K.val : Set Point) ((ω - t : ℝ) : Real.Angle)).bRay ∧
        (capVertices P t).1.1 = mirrorReflection ω (capVertices K (ω - t)).2.2 ∧
        (capVertices P t).1.2 = mirrorReflection ω (capVertices K (ω - t)).2.1 ∧
        (capVertices P t).2.1 = mirrorReflection ω (capVertices K (ω - t)).1.2 ∧
        (capVertices P t).2.2 = mirrorReflection ω (capVertices K (ω - t)).1.1) ∧
      (∀ t ∈ Set.Ioo 0 ω,
        (wedgeEndpoints P t).1 = mirrorReflection ω (wedgeEndpoints K (ω - t)).2 ∧
        (wedgeEndpoints P t).2 = mirrorReflection ω (wedgeEndpoints K (ω - t)).1 ∧
        (wedgeGaps P t).1 = (wedgeGaps K (ω - t)).2 ∧
        (wedgeGaps P t).2 = (wedgeGaps K (ω - t)).1 ∧
        capWedge P t = mirrorReflection ω '' capWedge K (ω - t)) ∧
      capUpperBoundary P = mirrorReflection ω '' capUpperBoundary K ∧
      capNiche P = mirrorReflection ω '' capNiche K ∧
      (∀ E : Set Real.Angle, MeasurableSet E →
        surfaceAreaMeasure P.val E = surfaceAreaMeasure K.val
          ((fun a : Real.Angle ↦ ((ω + Real.pi / 2 : ℝ) : Real.Angle) - a) '' E)) := by
  let P : CapSpace ω := ⟨reflectedBody ω K.val, reflectedBody_isCap K⟩
  have hM : mirrorReflection ω = capReflection ω :=
    mirrorReflection_eq_capReflection ω K.property.1 K.property.2.1
  refine ⟨P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change capReflection ω '' (K.val : Set Point) =
      mirrorReflection ω '' (K.val : Set Point)
    rw [hM]
  · intro t _
    rw [hM]
    have hh := supportingHallway_reflection ω t K.val
    have hp := rotatingHallwayParts_reflection ω t K.val
    have hv := capVertices_reflection K t
    rcases hp with ⟨hinner, houter, hQouter, hQinner, ha, hc, hb, hd, hbRay, hdRay⟩
    refine ⟨hh, hinner, houter, hQouter, hQinner, ha, hc, hb, hd, hbRay, hdRay,
      ?_, ?_, ?_, ?_⟩
    · simpa only [P] using congrArg (fun v ↦ v.1.1) hv
    · simpa only [P] using congrArg (fun v ↦ v.1.2) hv
    · simpa only [P] using congrArg (fun v ↦ v.2.1) hv
    · simpa only [P] using congrArg (fun v ↦ v.2.2) hv
  · intro t _
    rw [hM]
    have he := wedgeEndpoints_reflection K t
    have hg := wedgeGaps_reflection K t
    refine ⟨?_, ?_, ?_, ?_, capWedge_reflection K t⟩
    · simpa only [P] using congrArg Prod.fst he
    · simpa only [P] using congrArg Prod.snd he
    · simpa only [P] using congrArg Prod.fst hg
    · simpa only [P] using congrArg Prod.snd hg
  · rw [hM]
    exact capUpperBoundary_reflection K
  · rw [hM]
    exact capNiche_reflection K
  · intro E hE
    change surfaceAreaMeasure (reflectedBody ω K.val) E = _
    rw [surfaceAreaMeasure_reflectedBody,
      (reflectedAngleEquiv ω).map_apply]
    change surfaceAreaMeasure K.val (reflectedAngle ω ⁻¹' E) = _
    rw [reflectedAngle_preimage_eq_image]
    rfl

end MovingSofa
