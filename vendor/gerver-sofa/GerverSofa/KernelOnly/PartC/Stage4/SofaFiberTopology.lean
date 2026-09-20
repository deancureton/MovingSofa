import GerverSofa.KernelOnly.PartC.Stage4.SofaConvexityFacts
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import GerverSofa.KernelOnly.PartC.Stage4.NicheFrontierTopology

/-!
# Part C Stage 4: vertical-fibre topology of the fixed sofa

The argument in this file is independent of any Jordan-curve theorem.  The
cap is compact and convex.  Its removed niche is a strict vertical subgraph.
Consequently every nonempty vertical section of the complement is an interval.
Moreover, a highest point of each cap section survives: if it belonged to the
strict subgraph, one of the certified graph points would be a still higher cap
point.  Thus the horizontal projections of the cap and sofa agree.  A compact
map with connected fibres over that connected projection closes connectedness.
-/

noncomputable section

namespace GerverSofa
namespace PartC
namespace Stage4

open Set
open Stage2

private theorem physical_cos_diff_nonneg {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) :
    0 ≤ Real.cos (t - s) := by
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
  · have hsT := hs.2
    have ht0 := ht.1
    dsimp [T] at hsT
    linarith
  · have hs0 := hs.1
    have htT := ht.2
    dsimp [T] at htT
    linarith

private theorem phi_upper_twentieth_fiber :
    params.phi ≤ (1 / 20 : ℝ) := by
  have h := phi_bounds.2
  norm_num at h ⊢
  linarith

private theorem a1_lower_six_fifths_fiber :
    (6 / 5 : ℝ) ≤ params.a1 := by
  have h := Romik.a1_lower_bound_of_mem_box params_mem
  norm_num at h ⊢
  linarith

private theorem alphaBeta1_snd_nonneg_fiber {s : ℝ}
    (hs0 : 0 ≤ s) (hs20 : s ≤ (1 / 20 : ℝ)) :
    0 ≤ (Romik.alphaBeta1 params s).2 := by
  have hpi : s ≤ Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hsin0 : 0 ≤ Real.sin s :=
    Real.sin_nonneg_of_nonneg_of_le_pi hs0 hpi
  have hsinUpper := Real.sin_le hs0
  have hcosLower : 1 - s ^ 2 / 2 ≤ Real.cos s :=
    Real.one_sub_sq_div_two_le_cos
  have hcos0 : 0 ≤ Real.cos s := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [Real.pi_gt_three]
  have hquad : 0 ≤ s * ((1 / 20 : ℝ) - s) :=
    mul_nonneg hs0 (sub_nonneg.mpr hs20)
  have hcoef : (12 / 5 : ℝ) ≤ 2 * params.a1 := by
    nlinarith [a1_lower_six_fifths_fiber]
  have hmul : (12 / 5 : ℝ) * Real.cos s ≤
      2 * params.a1 * Real.cos s :=
    mul_le_mul_of_nonneg_right hcoef hcos0
  have ha2 := Romik.a2_eq_neg_quarter_of_equations params_equations
  dsimp [Romik.alphaBeta1]
  rw [ha2]
  nlinarith [hsinUpper, hcosLower, hquad, hmul]

/-- The early inner-contact coefficient is nonnegative on the whole `D`
parameter interval. -/
theorem beta_nonneg_on_D {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) params.theta) : 0 ≤ beta t := by
  by_cases hphi : t ≤ params.phi
  · have hs20 : t ≤ (1 / 20 : ℝ) :=
      le_trans hphi phi_upper_twentieth_fiber
    have h := alphaBeta1_snd_nonneg_fiber ht.1 hs20
    simpa [beta, alphaBetaAt, hphi] using h
  · have htPhysical : t ∈ Icc (0 : ℝ) T :=
      ⟨ht.1, le_trans ht.2 (le_trans theta_lt_eta.le
        (le_trans eta_lt_tau.le tau_le_T))⟩
    have hrho := Stage2.rhoA_nonneg htPhysical
    unfold Stage2.rhoA at hrho
    rw [if_neg hphi, if_pos ht.2] at hrho
    simp only [beta, alphaBetaAt, if_neg hphi, if_pos ht.2]
    dsimp [Romik.alphaBeta2]
    exact hrho

/-- Core path points are cap points. -/
theorem core_path_mem_K {t : ℝ} (ht : t ∈ Icc params.phi tau) :
    Romik.path params t ∈ K := by
  rw [Romik.mem_K0]
  refine ⟨path_core_y_nonneg ht, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  have ht' : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_pos.le ht.1, le_trans ht.2 tau_le_T⟩
  exact path_mem_outer_supports hs' ht'

/-- Every certified early `D` roof point lies in the cap. -/
theorem D_mem_K {t : ℝ} (ht : t ∈ Icc (0 : ℝ) params.theta) :
    D t ∈ K := by
  rw [Romik.mem_K0]
  refine ⟨D_y_nonneg ht, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  have ht' : t ∈ Icc (0 : ℝ) T :=
    ⟨ht.1, le_trans ht.2 (le_trans theta_lt_eta.le
      (le_trans eta_lt_tau.le tau_le_T))⟩
  have hcos := physical_cos_diff_nonneg hs' ht'
  have hbeta := beta_nonneg_on_D ht
  have hp := path_mem_outer_supports hs' ht'
  have hC := Stage3.supportC_direct t ht'
  constructor
  · have hpU := hp.1
    change dot (D t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    change dot (Romik.path params t) (u s) ≤
      dot (Romik.path params s) (u s) + 1 at hpU
    have hrel : dot (D t) (u s) =
        dot (Romik.path params t) (u s) - beta t * Real.cos (t - s) := by
      simp [D, dot, u, Real.cos_sub]
      ring
    rw [hrel]
    nlinarith [mul_nonneg hbeta hcos]
  · have hCV := (hC.2 s hs).2
    change dot (D t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    change dot (C t) (v s) ≤ dot (Romik.path params s) (v s) + 1 at hCV
    have hrel : dot (C t) (v s) =
        dot (D t) (v s) + Real.cos (t - s) := by
      simp [C, D, dot, u, v, Real.cos_sub]
      ring
    rw [hrel] at hCV
    linarith

/-- Every certified late `B` roof point lies in the cap. -/
theorem B_mem_K {t : ℝ} (ht : t ∈ Icc eta T) : B t ∈ K := by
  rw [Romik.mem_K0]
  refine ⟨B_y_nonneg ht, ?_⟩
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) T := by simpa [T] using hs
  have ht' : t ∈ Icc (0 : ℝ) T :=
    ⟨le_trans phi_pos.le (le_trans phi_lt_eta.le ht.1), ht.2⟩
  have hcos := physical_cos_diff_nonneg hs' ht'
  have halpha := alpha_nonpos ⟨le_trans phi_lt_eta.le ht.1, ht.2⟩
  have hp := path_mem_outer_supports hs' ht'
  have hA := Stage3.supportA_direct t ht'
  constructor
  · have hAU := (hA.2 s hs).1
    change dot (B t) (u s) ≤ dot (Romik.path params s) (u s) + 1
    change dot (A t) (u s) ≤ dot (Romik.path params s) (u s) + 1 at hAU
    have hrel : dot (A t) (u s) =
        dot (B t) (u s) + Real.cos (t - s) := by
      simp [A, B, dot, u, v, Real.cos_sub]
      ring
    rw [hrel] at hAU
    linarith
  · have hpV := hp.2
    change dot (B t) (v s) ≤ dot (Romik.path params s) (v s) + 1
    change dot (Romik.path params t) (v s) ≤
      dot (Romik.path params s) (v s) + 1 at hpV
    have hrel : dot (B t) (v s) =
        dot (Romik.path params t) (v s) + alpha t * Real.cos (t - s) := by
      simp [B, dot, v, Real.cos_sub]
      ring
    rw [hrel]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg halpha hcos]

/-- Every graph which forms the certified strict niche roof consists of cap
points. -/
theorem certified_roof_mem_K :
    (∀ t ∈ Icc (0 : ℝ) params.theta, D t ∈ K) ∧
    (∀ t ∈ Icc params.phi tau, Romik.path params t ∈ K) ∧
    (∀ t ∈ Icc eta T, B t ∈ K) :=
  ⟨fun t ht => D_mem_K ht,
    fun t ht => core_path_mem_K ht,
    fun t ht => B_mem_K ht⟩

/-- Strict vertical fills are downward closed along every nonnegative fibre. -/
theorem verticalFill_downward
    {f : ℝ → Point} {I : Set ℝ} {p q : Point}
    (hx : p.1 = q.1) (hp0 : 0 ≤ p.2) (hy : p.2 ≤ q.2)
    (hq : q ∈ verticalFill f I) : p ∈ verticalFill f I := by
  rcases hq with ⟨t, ht, hqx, hq0, hqtop⟩
  exact ⟨t, ht, hx.trans hqx, hp0, lt_of_le_of_lt hy hqtop⟩

/-- The union of the three strict graph fills is downward closed in each
nonnegative vertical fibre. -/
theorem certifiedNicheRegion_downward {p q : Point}
    (hx : p.1 = q.1) (hp0 : 0 ≤ p.2) (hy : p.2 ≤ q.2)
    (hq : q ∈ certifiedNicheRegion) : p ∈ certifiedNicheRegion := by
  rcases hq with (hD | hP) | hB
  · exact Or.inl (Or.inl (verticalFill_downward hx hp0 hy hD))
  · exact Or.inl (Or.inr (verticalFill_downward hx hp0 hy hP))
  · exact Or.inr (verticalFill_downward hx hp0 hy hB)

/-- The Gerver cap is compact. -/
theorem K_compact_direct : IsCompact K := by
  let box : Set Point :=
    Icc ((Romik.path params T).1 - 1) 1 ×ˢ Icc (0 : ℝ) 1
  have hbox : IsCompact box := isCompact_Icc.prod isCompact_Icc
  apply hbox.of_isClosed_subset (Romik.isClosed_K0 params)
  intro q hq
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact le_rfl
    · positivity
  have hT : T ∈ Icc (0 : ℝ) (Real.pi / 2) := by
    exact ⟨by dsimp [T]; positivity, by dsimp [T]; exact le_rfl⟩
  have hs0 := hq.2 0 h0
  have hsT := hq.2 T hT
  have hxhi : q.1 ≤ 1 := by
    have h := hs0.1
    simpa [supportHalfU, dot, u, pathZero] using h
  have hyhi : q.2 ≤ 1 := by
    have h := hs0.2
    simpa [supportHalfV, dot, v, pathZero] using h
  have hxlo : (Romik.path params T).1 - 1 ≤ q.1 := by
    have h := hsT.2
    simp [supportHalfV, dot, v, T] at h
    dsimp [T] at ⊢
    linarith
  exact ⟨⟨hxlo, hxhi⟩, ⟨hq.1, hyhi⟩⟩

/-- The fixed sofa is compact, as the difference of the compact cap and the
open union of forbidden quadrants. -/
theorem G_compact_direct : IsCompact G := by
  change IsCompact (Romik.sofa params)
  rw [Romik.sofa_eq_K0_diff_innerUnion]
  exact K_compact_direct.diff (Romik.isOpen_innerUnion params)

private def KVerticalSection (x : ℝ) : Set Point :=
  K ∩ {q | q.1 = x}

private theorem KVerticalSection_compact (x : ℝ) :
    IsCompact (KVerticalSection x) := by
  apply K_compact_direct.inter_right
  exact isClosed_singleton.preimage continuous_fst

/-- Every cap fibre has a highest point, and that point survives removal of
the strict niche. -/
theorem exists_G_point_over_K {q : Point} (hq : q ∈ K) :
    ∃ p ∈ G, p.1 = q.1 := by
  let F := KVerticalSection q.1
  have hFcompact : IsCompact F := KVerticalSection_compact q.1
  have hFne : F.Nonempty := ⟨q, hq, rfl⟩
  rcases hFcompact.exists_isMaxOn hFne continuous_snd.continuousOn with
    ⟨p, hpF, hpmax⟩
  have hpK : p ∈ K := hpF.1
  have hpx : p.1 = q.1 := hpF.2
  refine ⟨p, ⟨hpK, ?_⟩, hpx⟩
  intro hpN
  rw [niche_eq_certifiedNicheRegion] at hpN
  rcases hpN with (hD | hP) | hB
  · rcases hD with ⟨t, ht, hx, _hy0, hylt⟩
    have hwK := D_mem_K ht
    have hwF : D t ∈ F := ⟨hwK, hx.symm.trans hpx⟩
    exact (not_lt_of_ge (hpmax hwF)) hylt
  · rcases hP with ⟨t, ht, hx, _hy0, hylt⟩
    have hwK := core_path_mem_K ht
    have hwF : Romik.path params t ∈ F := ⟨hwK, hx.symm.trans hpx⟩
    exact (not_lt_of_ge (hpmax hwF)) hylt
  · rcases hB with ⟨t, ht, hx, _hy0, hylt⟩
    have hwK := B_mem_K ht
    have hwF : B t ∈ F := ⟨hwK, hx.symm.trans hpx⟩
    exact (not_lt_of_ge (hpmax hwF)) hylt

/-- Removing the strict niche does not change the horizontal projection. -/
theorem fst_image_G_eq_fst_image_K :
    Prod.fst '' G = Prod.fst '' K := by
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    exact ⟨q, hq.1, rfl⟩
  · rintro x ⟨q, hq, rfl⟩
    rcases exists_G_point_over_K hq with ⟨p, hp, hpx⟩
    exact ⟨p, hp, hpx⟩

/-- A vertical section of the fixed sofa. -/
def GVerticalSection (x : ℝ) : Set Point :=
  {q | q ∈ G ∧ q.1 = x}

/-- Every vertical section of `G` is convex. -/
theorem GVerticalSection_convex (x : ℝ) :
    Convex ℝ (GVerticalSection x) := by
  intro p hp q hq a b ha hb hab
  have hpK : p ∈ K := hp.1.1
  have hqK : q ∈ K := hq.1.1
  have hzK := K_convex_direct hpK hqK ha hb hab
  have hzx : (a • p + b • q).1 = x := by
    change a * p.1 + b * q.1 = x
    rw [hp.2, hq.2]
    calc
      a * x + b * x = (a + b) * x := by ring
      _ = x := by rw [hab, one_mul]
  refine ⟨⟨hzK, ?_⟩, hzx⟩
  intro hzN
  have hzR : a • p + b • q ∈ certifiedNicheRegion := by
    rw [← niche_eq_certifiedNicheRegion]
    exact hzN
  rcases le_total p.2 q.2 with hpq | hqp
  · have hpz : p.2 ≤ (a • p + b • q).2 := by
      change p.2 ≤ a * p.2 + b * q.2
      calc
        p.2 = a * p.2 + b * p.2 := by
          calc
            p.2 = (a + b) * p.2 := by rw [hab, one_mul]
            _ = a * p.2 + b * p.2 := by ring
        _ ≤ a * p.2 + b * q.2 :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hpq hb)
    have hpR := certifiedNicheRegion_downward
      (hp.2.trans hzx.symm) hpK.1 hpz hzR
    exact hp.1.2 (by
      rw [niche_eq_certifiedNicheRegion]
      exact hpR)
  · have hqz : q.2 ≤ (a • p + b • q).2 := by
      change q.2 ≤ a * p.2 + b * q.2
      calc
        q.2 = a * q.2 + b * q.2 := by
          calc
            q.2 = (a + b) * q.2 := by rw [hab, one_mul]
            _ = a * q.2 + b * q.2 := by ring
        _ ≤ a * p.2 + b * q.2 :=
          add_le_add (mul_le_mul_of_nonneg_left hqp ha) le_rfl
    have hqR := certifiedNicheRegion_downward
      (hq.2.trans hzx.symm) hqK.1 hqz hzR
    exact hq.1.2 (by
      rw [niche_eq_certifiedNicheRegion]
      exact hqR)

/-- Each nonempty vertical section is connected. -/
theorem GVerticalSection_connected {x : ℝ}
    (hne : (GVerticalSection x).Nonempty) :
    IsConnected (GVerticalSection x) :=
  (GVerticalSection_convex x).isConnected hne

private def GProjection : Set ℝ := Prod.fst '' G

private def projectG : G → GProjection := fun q =>
  ⟨q.1.1, ⟨q.1, q.2, rfl⟩⟩

private theorem projectG_continuous : Continuous projectG := by
  exact (continuous_fst.comp continuous_subtype_val).subtype_mk _

private theorem projectG_surjective : Function.Surjective projectG := by
  rintro ⟨x, q, hq, hqx⟩
  refine ⟨⟨q, hq⟩, ?_⟩
  apply Subtype.ext
  exact hqx

private theorem projectG_fiber_connected (x : GProjection) :
    IsConnected (projectG ⁻¹' {x}) := by
  have hsectionNe : (GVerticalSection x.1).Nonempty := by
    rcases x.2 with ⟨q, hq, hqx⟩
    exact ⟨q, hq, hqx⟩
  have hsection := GVerticalSection_connected hsectionNe
  letI : ConnectedSpace (GVerticalSection x.1) :=
    isConnected_iff_connectedSpace.mp hsection
  let e : GVerticalSection x.1 → G := fun q => ⟨q.1, q.2.1⟩
  have he : Continuous e := by
    exact continuous_subtype_val.subtype_mk _
  have hrange : Set.range e = projectG ⁻¹' {x} := by
    ext q
    constructor
    · rintro ⟨z, rfl⟩
      apply Set.mem_preimage.mpr
      apply Set.mem_singleton_iff.mpr
      apply Subtype.ext
      exact z.2.2
    · intro hq
      have hx : q.1.1 = x.1 := by
        have := Set.mem_singleton_iff.mp hq
        exact congrArg Subtype.val this
      exact ⟨⟨q.1, q.2, hx⟩, rfl⟩
  rw [← hrange]
  exact isConnected_range he

/-- Connectedness of the fixed Gerver sofa by compact connected fibres. -/
theorem G_connected_by_vertical_fibers : IsConnected G := by
  have hprojK : IsConnected (Prod.fst '' K) :=
    K_connected_direct.image Prod.fst continuous_fst.continuousOn
  have hproj : IsConnected GProjection := by
    simpa [GProjection, fst_image_G_eq_fst_image_K] using hprojK
  letI : CompactSpace G := isCompact_iff_compactSpace.mp G_compact_direct
  letI : ConnectedSpace GProjection := isConnected_iff_connectedSpace.mp hproj
  have hquot : Topology.IsQuotientMap projectG :=
    Topology.IsQuotientMap.of_surjective_continuous
      projectG_surjective projectG_continuous
  have hpre : IsConnected (projectG ⁻¹' (Set.univ : Set GProjection)) :=
    Topology.IsCoinducing.isConnected_preimage_of_isClosed
      projectG_fiber_connected hquot.isCoinducing isClosed_univ isConnected_univ
  have huniv : IsConnected (Set.univ : Set G) := by simpa using hpre
  have hspace : ConnectedSpace G := connectedSpace_iff_univ.mpr huniv
  exact isConnected_iff_connectedSpace.mpr hspace

end Stage4
end PartC
end GerverSofa
