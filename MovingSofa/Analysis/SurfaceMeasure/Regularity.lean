import MovingSofa.Analysis.SurfaceMeasure.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section

open MeasureTheory

namespace MovingSofa

private instance : CompactSpace Real.Angle :=
  AddCircle.homeomorphCircle'.symm.compactSpace

/-- The unit normal depends continuously on its angle. -/
theorem continuous_normalVector_angle :
    Continuous normalVector := by
  let c : Real.Angle → (i : Fin 2) → ℝ := fun t i ↦
    Fin.cases t.cos (fun _ ↦ t.sin) i
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Real.Angle.continuous_cos
    · exact Real.Angle.continuous_sin
  have heq : normalVector = (fun t ↦ WithLp.toLp 2 (c t)) := by
    funext t
    ext i
    fin_cases i <;> rfl
  rw [heq]
  exact (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin 2 ↦ ℝ)).comp hc

private theorem isClosed_isExteriorNormal (K : ConvexBody Point) :
    IsClosed {z : Point × Real.Angle | IsExteriorNormal K z.1 z.2} := by
  change IsClosed {z : Point × Real.Angle |
    ∀ q ∈ (K : Set Point), inner ℝ (q - z.1) (normalVector z.2) ≤ 0}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro _
  apply isClosed_le
  · exact (continuous_const.sub continuous_fst).inner
      (continuous_normalVector_angle.comp continuous_snd)
  · exact continuous_const

private def normalGraph (K : ConvexBody Point) : Set (Point × Real.Angle) :=
  {z | z.1 ∈ frontier (K : Set Point) ∧ IsExteriorNormal K z.1 z.2}

private theorem isCompact_normalGraph (K : ConvexBody Point) :
    IsCompact (normalGraph K) := by
  have hfront : IsCompact (frontier (K : Set Point)) := by
    apply K.isCompact.of_isClosed_subset isClosed_frontier
    simpa only [K.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (K : Set Point) ⊆ closure (K : Set Point))
  have hclosed : IsClosed (normalGraph K) := by
    exact (isClosed_frontier.preimage continuous_fst).inter (isClosed_isExteriorNormal K)
  apply (hfront.prod isCompact_univ).of_isClosed_subset
  · exact hclosed
  · rintro ⟨p, a⟩ ⟨hp, _⟩
    exact ⟨hp, Set.mem_univ a⟩

private def normalDomain (K : ConvexBody Point) : Set Point :=
  Prod.fst '' normalGraph K

private theorem isCompact_normalDomain (K : ConvexBody Point) :
    IsCompact (normalDomain K) :=
  (isCompact_normalGraph K).image continuous_fst

private def separatedNormalPairs (K : ConvexBody Point) (n : ℕ) :
    Set (Point × (Real.Angle × Real.Angle)) :=
  {z | z.1 ∈ frontier (K : Set Point) ∧
    IsExteriorNormal K z.1 z.2.1 ∧ IsExteriorNormal K z.1 z.2.2 ∧
      (1 : ℝ) / (n + 1) ≤ dist z.2.1 z.2.2}

private theorem isCompact_separatedNormalPairs (K : ConvexBody Point) (n : ℕ) :
    IsCompact (separatedNormalPairs K n) := by
  have hfront : IsCompact (frontier (K : Set Point)) := by
    apply K.isCompact.of_isClosed_subset isClosed_frontier
    simpa only [K.isClosed.closure_eq] using
      (frontier_subset_closure : frontier (K : Set Point) ⊆ closure (K : Set Point))
  have hrel₁ : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      IsExteriorNormal K z.1 z.2.1} :=
    (isClosed_isExteriorNormal K).preimage
      (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have hrel₂ : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      IsExteriorNormal K z.1 z.2.2} :=
    (isClosed_isExteriorNormal K).preimage
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hsep : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      (1 : ℝ) / (n + 1) ≤ dist z.2.1 z.2.2} := by
    exact isClosed_le continuous_const
      ((continuous_fst.comp continuous_snd).dist (continuous_snd.comp continuous_snd))
  have hfclosed : IsClosed {z : Point × (Real.Angle × Real.Angle) |
      z.1 ∈ frontier (K : Set Point)} :=
    isClosed_frontier.preimage continuous_fst
  have hclosed : IsClosed (separatedNormalPairs K n) := by
    have h := ((hfclosed.inter hrel₁).inter hrel₂).inter hsep
    simpa only [separatedNormalPairs, Set.inter_def, Set.mem_ofPred_eq, and_assoc] using h
  apply (hfront.prod (isCompact_univ.prod isCompact_univ)).of_isClosed_subset hclosed
  rintro ⟨p, a, b⟩ ⟨hp, _⟩
  exact ⟨hp, Set.mem_univ _, Set.mem_univ _⟩

private def separatedNormalPoints (K : ConvexBody Point) (n : ℕ) : Set Point :=
  Prod.fst '' separatedNormalPairs K n

private theorem isCompact_separatedNormalPoints (K : ConvexBody Point) (n : ℕ) :
    IsCompact (separatedNormalPoints K n) :=
  (isCompact_separatedNormalPairs K n).image continuous_fst

private theorem regularBoundary_eq_normalDomain_sdiff_iUnion (K : ConvexBody Point) :
    regularBoundary K = normalDomain K \ ⋃ n, separatedNormalPoints K n := by
  ext p
  constructor
  · rintro ⟨hp, a, ha, hua⟩
    refine ⟨⟨(p, a), ⟨hp, ha⟩, rfl⟩, ?_⟩
    intro hnonunique
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hnonunique
    obtain ⟨⟨q, b, c⟩, ⟨_, hb, hc, hdist⟩, rfl⟩ := hn
    rw [hua b hb, hua c hc, dist_self] at hdist
    have hpos : 0 < (1 : ℝ) / (n + 1) := by positivity
    linarith
  · rintro ⟨hdom, hnot⟩
    obtain ⟨⟨q, a⟩, ⟨hp, ha⟩, hqp⟩ := hdom
    change q = p at hqp
    subst q
    refine ⟨hp, a, ha, ?_⟩
    intro b hb
    by_contra hba
    have hdpos : 0 < dist a b := dist_pos.mpr (Ne.symm hba)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hdpos
    apply hnot
    apply Set.mem_iUnion.mpr
    refine ⟨n, ⟨(p, (a, b)), ?_, rfl⟩⟩
    exact ⟨hp, ha, hb, hn.le⟩

/-- Points with a unique exterior normal form a Borel set. -/
theorem measurableSet_regularBoundary (K : ConvexBody Point) :
    MeasurableSet (regularBoundary K) := by
  rw [regularBoundary_eq_normalDomain_sdiff_iUnion]
  exact (isCompact_normalDomain K).measurableSet.diff
    (MeasurableSet.iUnion fun n ↦ (isCompact_separatedNormalPoints K n).measurableSet)

/-- The exterior normal varies continuously on the regular boundary. -/
theorem continuousOn_exteriorNormalAngle_regularBoundary (K : ConvexBody Point) :
    ContinuousOn (exteriorNormalAngle K) (regularBoundary K) := by
  have hnormal (p : Point) (hp : p ∈ regularBoundary K) :
      IsExteriorNormal K p (exteriorNormalAngle K p) := by
    rcases hp.2 with ⟨a, ha, hua⟩
    dsimp only [exteriorNormalAngle]
    split
    · rename_i h
      exact h.exists.choose_spec
    · rename_i h
      exact (h ⟨a, ha, hua⟩).elim
  have hunique (p : Point) (hp : p ∈ regularBoundary K) (a : Real.Angle)
      (ha : IsExteriorNormal K p a) : a = exteriorNormalAngle K p := by
    rcases hp.2 with ⟨b, hb, hub⟩
    exact (hub a ha).trans (hub _ (hnormal p hp)).symm
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_of_isClosed_graph
  have hgraph : Function.graph ((regularBoundary K).domRestrict (exteriorNormalAngle K)) =
      {z : (regularBoundary K) × Real.Angle | IsExteriorNormal K z.1 z.2} := by
    ext z
    constructor
    · intro hz
      change exteriorNormalAngle K z.1 = z.2 at hz
      change IsExteriorNormal K z.1 z.2
      rw [← hz]
      exact hnormal z.1 z.1.2
    · intro hz
      change exteriorNormalAngle K z.1 = z.2
      exact (hunique z.1 z.1.2 z.2 hz).symm
  rw [hgraph]
  exact (isClosed_isExteriorNormal K).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- The exterior normal is measurable for any measure restricted to the regular boundary. -/
theorem aemeasurable_exteriorNormalAngle_restrict_regularBoundary
    (K : ConvexBody Point) (μ : Measure Point) :
    AEMeasurable (exteriorNormalAngle K) (μ.restrict (regularBoundary K)) :=
  aemeasurable_restrict_of_measurable_subtype (measurableSet_regularBoundary K)
    (continuousOn_exteriorNormalAngle_regularBoundary K).domRestrict.measurable

end MovingSofa
