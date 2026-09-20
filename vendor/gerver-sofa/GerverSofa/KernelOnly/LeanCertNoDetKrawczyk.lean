import GerverSofa.KernelOnly.LeanCertGerverCorrespondence

/-!
# Determinant-free checked Krawczyk endgame

For a square system, the usual explicit determinant test on the preconditioner
is redundant once `‖I - YJ‖ < 1` is known: at any point in the box,
`YJ = 1 - T` with `‖T‖ < 1`, hence `YJ` is a unit by the Neumann-series
theorem.  Therefore `Y` is surjective, hence injective in finite dimension.

This matters computationally in dimension 22 because Mathlib's generic
Leibniz determinant is the wrong algorithm for a huge exact rational matrix.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

/-!
## Kernel-reducible finite interval sums

LeanCert's public `intervalRatMatVec` uses `Finset.sum` with a local
proof-transported `AddCommMonoid IntervalRat`.  That is semantically sound, but
closed `decide +kernel` computations can get stuck reducing the transported
typeclass instance.

We keep LeanCert's interval operations and mathematical semantics, but package
this one finite sum by structural recursion on `Fin n`.  Mathlib's existing
`Fin.sum_univ_succ` is the semantic bridge to the ordinary real finite sum.
-/

/-- A finite interval sum that reduces by structural recursion, with no
`AddCommMonoid IntervalRat` instance involved in computation. -/
def kernelIntervalFinSum : {n : Nat} → (Fin n → IntervalRat) → IntervalRat
  | 0, _ => IntervalRat.singleton 0
  | n + 1, f =>
      IntervalRat.add (f 0)
        (kernelIntervalFinSum (fun j : Fin n => f j.succ))

/-- Semantic soundness of the kernel-reducible finite interval sum. -/
theorem mem_kernelIntervalFinSum :
    ∀ (n : Nat) (x : Fin n → ℝ) (I : Fin n → IntervalRat),
      (∀ i, x i ∈ I i) →
      (∑ i, x i) ∈ kernelIntervalFinSum I := by
  intro n
  induction n with
  | zero =>
      intro x I h
      simp [kernelIntervalFinSum, IntervalRat.mem_def, IntervalRat.singleton]
  | succ n ih =>
      intro x I h
      rw [Fin.sum_univ_succ]
      exact IntervalRat.mem_add (h 0)
        (ih (fun j : Fin n => x j.succ)
          (fun j : Fin n => I j.succ)
          (fun j => h j.succ))

/-- Kernel-reducible exact interval matrix-vector product. -/
def kernelIntervalRatMatVec {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (v : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i =>
    kernelIntervalFinSum
      (fun j => IntervalRat.scale (Y i j) (v j))

/-!
## Kernel-reducible point values at the Newton center

LeanCert's ordinary rational evaluator uses `sinComputableReduced` and
`cosComputableReduced`.  Those are mathematically excellent general-purpose
routines, but their period-reduction step computes a rational floor.  On the
closed Gerver certificates that floor can prevent `decide +kernel` from
normalizing an otherwise entirely rational proposition.

For the exact Gerver expression fragment (`ADConstSupported`) we therefore use
a tiny point evaluator that is identical on algebraic operations and named
constants, but calls the already-proved *unreduced* Taylor enclosures
`sinComputable` and `cosComputable`.  These enclosures are globally sound for
arbitrary real arguments; argument reduction is an optimization, not a
soundness requirement.  This keeps the Newton-center calculation purely in
kernel-reducible rational arithmetic without changing the mathematical map.
-/

/-- A kernel-reducible interval for π, using the exact project interval
whose semantic soundness is already proved in `TranscendentalSoundness`.

The generic LeanCert `MathConst.interval` route is mathematically sound, but
its named-constant machinery does not always normalize far enough for closed
`decide +kernel` comparisons.  Reusing the project's already-certified exact
rational π endpoints removes only that reduction bottleneck; it does not
change the represented real constant or weaken any enclosure. -/
def kernelPiInterval : IntervalRat :=
  { lo := ExactReplay.piI.lo
    hi := ExactReplay.piI.hi
    le := by
      norm_num [ExactReplay.piI, ExactReplay.q] }

/-- The true real π lies in the kernel-reducible π interval. -/
theorem real_pi_mem_kernelPiInterval : Real.pi ∈ kernelPiInterval := by
  simpa [kernelPiInterval, IntervalRat.mem_def, RatInterval.Contains] using
    ExactReplay.piI_contains_pi

/-- Named constants for the point evaluator.  π takes the specialized
kernel-reducible path; every other LeanCert named constant keeps LeanCert's
public certified interval unchanged. -/
def kernelNamedConstInterval (c : MathConst) : IntervalRat :=
  if c = .pi then kernelPiInterval else c.interval

/-- Point evaluator for the everywhere-defined Gerver expression fragment.
Unsupported constructors are deliberately mapped to `{0}`; the soundness
lemma below is only stated for `ADConstSupported`, whose constructors are all
handled explicitly. -/
def kernelPointEvalCore (e : Expr) (ρ : IntervalEnv)
    (depth : Nat) : IntervalRat :=
  match e with
  | .const q => IntervalRat.singleton q
  | .var idx => ρ idx
  | .add a b => IntervalRat.add
      (kernelPointEvalCore a ρ depth) (kernelPointEvalCore b ρ depth)
  | .mul a b => IntervalRat.mul
      (kernelPointEvalCore a ρ depth) (kernelPointEvalCore b ρ depth)
  | .neg a => IntervalRat.neg (kernelPointEvalCore a ρ depth)
  | .exp a => IntervalRat.expComputable
      (kernelPointEvalCore a ρ depth) depth
  | .sin a => IntervalRat.sinComputable
      (kernelPointEvalCore a ρ depth) depth
  | .cos a => IntervalRat.cosComputable
      (kernelPointEvalCore a ρ depth) depth
  | .namedConst c => kernelNamedConstInterval c
  | _ => IntervalRat.singleton 0

/-- Soundness of the kernel-reducible point evaluator on exactly the Gerver
fragment.  In the sine/cosine cases this uses LeanCert's global Taylor
correctness theorems directly, so no period-reduction hypothesis is needed. -/
theorem eval_mem_kernelPointEvalCore {e : Expr}
    (h : ADConstSupported e)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv)
    (hmem : envMem ρReal ρInt) (depth : Nat) :
    Expr.eval ρReal e ∈ kernelPointEvalCore e ρInt depth := by
  induction h with
  | const q =>
      simp only [Expr.eval_const, kernelPointEvalCore]
      exact IntervalRat.mem_singleton q
  | var idx =>
      simp only [Expr.eval_var, kernelPointEvalCore]
      exact hmem idx
  | add _ _ iha ihb =>
      simp only [Expr.eval_add, kernelPointEvalCore]
      exact IntervalRat.mem_add iha ihb
  | mul _ _ iha ihb =>
      simp only [Expr.eval_mul, kernelPointEvalCore]
      exact IntervalRat.mem_mul iha ihb
  | neg _ ih =>
      simp only [Expr.eval_neg, kernelPointEvalCore]
      exact IntervalRat.mem_neg ih
  | exp _ ih =>
      simp only [Expr.eval_exp, kernelPointEvalCore]
      exact IntervalRat.mem_expComputable ih depth
  | sin _ ih =>
      simp only [Expr.eval_sin, kernelPointEvalCore]
      exact IntervalRat.mem_sinComputable ih depth
  | cos _ ih =>
      simp only [Expr.eval_cos, kernelPointEvalCore]
      exact IntervalRat.mem_cosComputable ih depth
  | namedConst c =>
      simp only [Expr.eval_namedConst, kernelPointEvalCore]
      by_cases hc : c = .pi
      · subst c
        simp only [kernelNamedConstInterval, if_pos rfl]
        simpa using real_pi_mem_kernelPiInterval
      · simp only [kernelNamedConstInterval, if_neg hc]
        exact c.mem_interval

/-- Taylor depth used only for the Newton-center point values.
The reduced system has coordinates at scale about `10^-15`; the 22D system
contains substantially thinner coordinates.  Depth 26 is the smallest retained value after an exact-rational replay of all
22 normalized Newton-center images that still leaves the direct self-map
strictly inside the unit box.  It materially reduces kernel rational size
compared with depth 27/34 while leaving the Jacobian evaluator and its
already-passing certificates untouched. -/
def kernelCenterTaylorDepth (n : Nat) : Nat :=
  if n ≤ 4 then 20 else 26

/-- Point-value enclosures for a square system at a rational center. -/
def pointEvalIntervalsKernel {n : Nat}
    (F : Fin n → Expr) (m : Fin n → ℚ)
    (_cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => kernelPointEvalCore (F i) (pointIntervalEnv m)
    (kernelCenterTaylorDepth n)

/-- Every real system coordinate at the rational center lies in the
kernel-reducible point enclosure. -/
theorem systemEval_mem_pointEvalIntervalsKernel_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (m : Fin n → ℚ) (cfg : EvalConfig) (i : Fin n) :
    systemEval F (fun j => (m j : ℝ)) i ∈
      pointEvalIntervalsKernel F m cfg i := by
  change Expr.eval (finEnv (fun j => (m j : ℝ))) (F i) ∈
    kernelPointEvalCore (F i) (pointIntervalEnv m)
      (kernelCenterTaylorDepth n)
  exact eval_mem_kernelPointEvalCore (h i)
    (finEnv (fun j => (m j : ℝ))) (pointIntervalEnv m)
    (finEnv_ratCast_mem_pointIntervalEnv m) (kernelCenterTaylorDepth n)

/-- Kernel-reducible version of LeanCert's Newton-center enclosure. -/
def kernelNewtonCenterInterval {n : Nat}
    (F : Fin n → Expr) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i =>
    IntervalRat.sub (IntervalRat.singleton (m i))
      (kernelIntervalRatMatVec Y (pointEvalIntervalsKernel F m cfg) i)

/-- The real Newton center lies in the kernel-reducible enclosure. -/
theorem newtonMap_center_mem_kernel_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig) (i : Fin n) :
    newtonMap (Y.map fun q => (q : ℝ)) F
        (fun j => (m j : ℝ)) i ∈
      kernelNewtonCenterInterval F m Y cfg i := by
  apply IntervalRat.mem_sub
  · exact IntervalRat.mem_singleton (m i)
  · simp only [Matrix.mulVec, dotProduct, kernelIntervalRatMatVec]
    exact mem_kernelIntervalFinSum n
      (fun j => (Y i j : ℝ) * systemEval F (fun k => (m k : ℝ)) j)
      (fun j => IntervalRat.scale (Y i j) (pointEvalIntervalsKernel F m cfg j))
      (fun j =>
        IntervalRat.mem_scale (Y i j)
          (systemEval_mem_pointEvalIntervalsKernel_const F h m cfg j))

/-- Same checked self-map enclosure as before, now with a kernel-reducible
finite interval sum at the Newton center. -/
def imageEnclosureWithQ {n : Nat}
    (F : Fin n → Expr) (X : Fin n → IntervalRat)
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (cfg : EvalConfig) (q : ℚ) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (kernelNewtonCenterInterval F m Y cfg i)
    (symmetricInterval (q * boxRadius X m))

theorem mapsTo_of_bound_and_enclosure {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithQ F X m Y cfg q i) (X i) = true) :
    Set.MapsTo (newtonMap (Y.map fun r => (r : ℝ)) F)
      (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  have hdiff :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ (q : ℝ) * ‖x - mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt
    · intro z hz
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) z‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X z hz cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound
    · exact hm
    · exact hx
  have hr0 : 0 ≤ boxRadius X m := boxRadius_nonneg X m
  have hnorm :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ ((q * boxRadius X m : ℚ) : ℝ) := by
    calc
      _ ≤ (q : ℝ) * ‖x - mr‖ := hdiff
      _ ≤ (q : ℝ) * (boxRadius X m : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_sub_center_le_boxRadius hx)
          (by exact_mod_cast hq0)
      _ = _ := by push_cast; rfl
  have hcoord :
      |(newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i|
        ≤ ((q * boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr :
      (newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i ∈
        symmetricInterval (q * boxRadius X m) := by
    rw [abs_le] at hcoord
    simpa [symmetricInterval, IntervalRat.mem_def,
      abs_of_nonneg (mul_nonneg hq0 hr0)] using hcoord
  have hcenter := newtonMap_center_mem_kernel_const F hsupp m Y cfg i
  have himage :
      newtonMap (Y.map fun r => (r : ℝ)) F x i ∈
        imageEnclosureWithQ F X m Y cfg q i := by
    have hadd := IntervalRat.mem_add hcenter herr
    simpa [imageEnclosureWithQ, mr, Pi.sub_apply] using hadd
  exact intervalStrictInside_sound (hencl i) _ himage

theorem preconditioner_injective_of_bound_lt_one {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (hq :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) < 1) :
    Function.Injective
      (fun v : Fin n → ℝ => (Y.map fun r => (r : ℝ)).mulVec v) := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun r => (r : ℝ)
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  let J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fderiv ℝ (systemEval F) mr
  let A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := matrixCLM Yr
  let T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fderiv ℝ (newtonMap Yr F) mr
  have hTle :
      ‖T‖ ≤
        (intervalMatrixBound
          (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) := by
    exact newtonMap_fderiv_norm_le_const Y F hsupp X mr hm cfg
  have hTlt : ‖T‖ < 1 := lt_of_le_of_lt hTle (by exact_mod_cast hq)
  let S : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := 1 - T
  have hunitS : IsUnit S := by
    dsimp [S]
    exact isUnit_one_sub_of_norm_lt_one hTlt
  have hbijS : Function.Bijective ⇑S :=
    (ContinuousLinearMap.isUnit_iff_bijective).mp hunitS

  have hF : HasFDerivAt (systemEval F) J mr :=
    (systemEval_differentiable_const F hsupp).differentiableAt.hasFDerivAt
  have hAJ : HasFDerivAt (fun x => A (systemEval F x)) (A.comp J) mr :=
    A.hasFDerivAt.comp mr hF
  have hg : HasFDerivAt (newtonMap Yr F)
      (ContinuousLinearMap.id ℝ _ - A.comp J) mr := by
    change HasFDerivAt (fun z => z - A (systemEval F z)) _ mr
    exact (hasFDerivAt_id mr).sub hAJ
  have hT :
      T = ContinuousLinearMap.id ℝ _ - A.comp J := hg.fderiv
  have hS : S = A.comp J := by
    dsimp [S]
    rw [hT, ContinuousLinearMap.one_def]
    abel
  have hsurjComp : Function.Surjective ⇑(A.comp J) := by
    rw [← hS]
    exact hbijS.2
  have hsurjA : Function.Surjective ⇑A := by
    intro y
    obtain ⟨x, hx⟩ := hsurjComp y
    refine ⟨J x, ?_⟩
    simpa only [ContinuousLinearMap.comp_apply] using hx
  have hsurjLin : Function.Surjective ⇑A.toLinearMap := hsurjA
  have hinjLin : Function.Injective ⇑A.toLinearMap :=
    (LinearMap.injective_iff_surjective (f := A.toLinearMap)).2 hsurjLin
  intro x y hxy
  apply hinjLin
  change (Y.map fun r => (r : ℝ)).mulVec x =
    (Y.map fun r => (r : ℝ)).mulVec y
  exact hxy

theorem fixedPoint_iff_systemZero_of_injective {n : Nat}
    (F : Fin n → Expr) (Y : Matrix (Fin n) (Fin n) ℚ)
    (hinj : Function.Injective
      (fun v : Fin n → ℝ => (Y.map fun r => (r : ℝ)).mulVec v))
    (x : Fin n → ℝ) :
    newtonMap (Y.map fun r => (r : ℝ)) F x = x ↔ SystemZero F x := by
  let Yr : Matrix (Fin n) (Fin n) ℝ := Y.map fun r => (r : ℝ)
  constructor
  · intro hfix
    have hmul : Yr.mulVec (systemEval F x) = 0 := by
      funext i
      have hi := congrFun hfix i
      change x i - Yr.mulVec (systemEval F x) i = x i at hi
      exact sub_eq_self.mp hi
    have hz : systemEval F x = 0 := hinj (by simpa [Yr] using hmul)
    intro i
    exact congrFun hz i
  · intro hz
    have hs : systemEval F x = 0 := by
      funext i
      exact hz i
    funext i
    simp [newtonMap, hs]

theorem uniqueSystemZero_of_certified_contraction {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithQ F X m Y cfg q i) (X i) = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  have hmap := mapsTo_of_bound_and_enclosure
    F hsupp X m hm Y cfg q hq0 hbound hencl
  have hactualLt :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) < 1 :=
    lt_of_le_of_lt hbound hq1
  have hinj := preconditioner_injective_of_bound_lt_one
    F hsupp X m hm Y cfg hactualLt
  have hfixed := contraction_unique_fixedPoint_in_finBox X
    (fun i => (m i : ℝ)) hm
    (newtonMap (Y.map fun r => (r : ℝ)) F)
    hmap (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    (fun x _ =>
      (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt)
    (fun x hx => by
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) x‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X x hx cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound)
  refine ⟨hfixed.choose, ⟨hfixed.choose_spec.1.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj hfixed.choose).mp
      hfixed.choose_spec.1.2⟩, ?_⟩
  intro y hy
  exact hfixed.unique ⟨hy.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj y).mpr hy.2⟩
    hfixed.choose_spec.1


/-!
## Cached Newton-center values for large closed systems

For the direct 22D Gerver certificate, recomputing all 22 transcendental
point values inside every image-row proposition creates a very large kernel
reduction.  The following variant accepts independently checked point-value
enclosures.  It changes no mathematics: each cached interval is accompanied
by a kernel proof that the corresponding real system value lies in it.
-/

/-- Endpoint inclusion between two rational intervals. -/
def intervalContained (I J : IntervalRat) : Prop :=
  J.lo ≤ I.lo ∧ I.hi ≤ J.hi

theorem mem_of_intervalContained {x : ℝ} {I J : IntervalRat}
    (hx : x ∈ I) (hIJ : intervalContained I J) : x ∈ J := by
  change J.lo ≤ I.lo ∧ I.hi ≤ J.hi at hIJ
  rw [IntervalRat.mem_def] at hx ⊢
  have hlo : (J.lo : ℝ) ≤ (I.lo : ℝ) := by
    exact_mod_cast hIJ.1
  have hhi : (I.hi : ℝ) ≤ (J.hi : ℝ) := by
    exact_mod_cast hIJ.2
  exact ⟨hlo.trans hx.1, hx.2.trans hhi⟩

/-- Newton-center enclosure from externally supplied, proof-carrying point
value intervals. -/
def kernelNewtonCenterIntervalWithValues {n : Nat}
    (m : Fin n → ℚ) (Y : Matrix (Fin n) (Fin n) ℚ)
    (V : Fin n → IntervalRat) : Fin n → IntervalRat :=
  fun i =>
    IntervalRat.sub (IntervalRat.singleton (m i))
      (kernelIntervalRatMatVec Y V i)

theorem newtonMap_center_mem_kernel_values {n : Nat}
    (F : Fin n → Expr) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (V : Fin n → IntervalRat)
    (hV : ∀ j, systemEval F (fun k => (m k : ℝ)) j ∈ V j)
    (i : Fin n) :
    newtonMap (Y.map fun q => (q : ℝ)) F
        (fun j => (m j : ℝ)) i ∈
      kernelNewtonCenterIntervalWithValues m Y V i := by
  apply IntervalRat.mem_sub
  · exact IntervalRat.mem_singleton (m i)
  · simp only [Matrix.mulVec, dotProduct, kernelIntervalRatMatVec]
    exact mem_kernelIntervalFinSum n
      (fun j => (Y i j : ℝ) * systemEval F (fun k => (m k : ℝ)) j)
      (fun j => IntervalRat.scale (Y i j) (V j))
      (fun j => IntervalRat.mem_scale (Y i j) (hV j))

/-- Self-map enclosure built from independently certified center values. -/
def imageEnclosureWithValuesQ {n : Nat}
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (Y : Matrix (Fin n) (Fin n) ℚ) (V : Fin n → IntervalRat)
    (q : ℚ) : Fin n → IntervalRat :=
  fun i => IntervalRat.add (kernelNewtonCenterIntervalWithValues m Y V i)
    (symmetricInterval (q * boxRadius X m))

theorem mapsTo_of_bound_and_values_enclosure {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (V : Fin n → IntervalRat)
    (hV : ∀ j, systemEval F (fun k => (m k : ℝ)) j ∈ V j)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithValuesQ X m Y V q i) (X i) = true) :
    Set.MapsTo (newtonMap (Y.map fun r => (r : ℝ)) F)
      (finBoxSet X) (finBoxSet X) := by
  intro x hx i
  let mr : Fin n → ℝ := fun i => (m i : ℝ)
  have hdiff :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ (q : ℝ) * ‖x - mr‖ := by
    apply (finBoxSet_convex X).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z hz
      exact (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt
    · intro z hz
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) z‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X z hz cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound
    · exact hm
    · exact hx
  have hr0 : 0 ≤ boxRadius X m := boxRadius_nonneg X m
  have hnorm :
      ‖newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr‖
        ≤ ((q * boxRadius X m : ℚ) : ℝ) := by
    calc
      _ ≤ (q : ℝ) * ‖x - mr‖ := hdiff
      _ ≤ (q : ℝ) * (boxRadius X m : ℝ) :=
        mul_le_mul_of_nonneg_left (norm_sub_center_le_boxRadius hx)
          (by exact_mod_cast hq0)
      _ = _ := by push_cast; rfl
  have hcoord :
      |(newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i|
        ≤ ((q * boxRadius X m : ℚ) : ℝ) :=
    (norm_le_pi_norm _ i).trans hnorm
  have herr :
      (newtonMap (Y.map fun r => (r : ℝ)) F x -
          newtonMap (Y.map fun r => (r : ℝ)) F mr) i ∈
        symmetricInterval (q * boxRadius X m) := by
    rw [abs_le] at hcoord
    simpa [symmetricInterval, IntervalRat.mem_def,
      abs_of_nonneg (mul_nonneg hq0 hr0)] using hcoord
  have hcenter := newtonMap_center_mem_kernel_values F m Y V hV i
  have himage :
      newtonMap (Y.map fun r => (r : ℝ)) F x i ∈
        imageEnclosureWithValuesQ X m Y V q i := by
    have hadd := IntervalRat.mem_add hcenter herr
    simpa [imageEnclosureWithValuesQ, mr, Pi.sub_apply] using hadd
  exact intervalStrictInside_sound (hencl i) _ himage

theorem uniqueSystemZero_of_certified_contraction_values {n : Nat}
    (F : Fin n → Expr) (hsupp : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (m : Fin n → ℚ)
    (hm : FinBoxMem (fun i => (m i : ℝ)) X)
    (Y : Matrix (Fin n) (Fin n) ℚ) (cfg : EvalConfig)
    (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hbound :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) ≤ q)
    (V : Fin n → IntervalRat)
    (hV : ∀ j, systemEval F (fun k => (m k : ℝ)) j ∈ V j)
    (hencl : ∀ i,
      intervalStrictInside (imageEnclosureWithValuesQ X m Y V q i) (X i) = true) :
    ∃! x, FinBoxMem x X ∧ SystemZero F x := by
  have hmap := mapsTo_of_bound_and_values_enclosure
    F hsupp X m hm Y cfg q hq0 hbound V hV hencl
  have hactualLt :
      intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) < 1 :=
    lt_of_le_of_lt hbound hq1
  have hinj := preconditioner_injective_of_bound_lt_one
    F hsupp X m hm Y cfg hactualLt
  have hfixed := contraction_unique_fixedPoint_in_finBox X
    (fun i => (m i : ℝ)) hm
    (newtonMap (Y.map fun r => (r : ℝ)) F)
    hmap (q : ℝ) (by exact_mod_cast hq0) (by exact_mod_cast hq1)
    (fun x _ =>
      (newtonMap_differentiable_const (Y.map fun r => (r : ℝ)) F hsupp).differentiableAt)
    (fun x hx => by
      calc
        ‖fderiv ℝ (newtonMap (Y.map fun r => (r : ℝ)) F) x‖
            ≤ (intervalMatrixBound
                (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) :=
          newtonMap_fderiv_norm_le_const Y F hsupp X x hx cfg
        _ ≤ (q : ℝ) := by exact_mod_cast hbound)
  refine ⟨hfixed.choose, ⟨hfixed.choose_spec.1.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj hfixed.choose).mp
      hfixed.choose_spec.1.2⟩, ?_⟩
  intro y hy
  exact hfixed.unique ⟨hy.1,
    (fixedPoint_iff_systemZero_of_injective F Y hinj y).mpr hy.2⟩
    hfixed.choose_spec.1

end PartALeanCert
end GerverSofa
