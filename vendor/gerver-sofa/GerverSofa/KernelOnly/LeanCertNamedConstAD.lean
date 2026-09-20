import LeanCert.Engine.RootFinding.Krawczyk

/-!
# Minimal named-constant extension of LeanCert's AD soundness layer

LeanCert's computable total dual evaluator already evaluates
`Expr.namedConst c` as `DualInterval.ofMathConst c`, whose derivative component
is the singleton interval `{0}`.  Its public `ADSupported` predicate, however,
does not currently include `namedConst`.

The Gerver systems necessarily contain the exact constant `Real.pi`.  This file
adds exactly one missing syntactic case -- differentiable named mathematical
constants -- while reusing LeanCert's existing evaluator, interval Jacobian,
matrix norm machinery, Newton map, and contraction theorem unchanged.

No interval arithmetic is reimplemented here.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine
open LeanCert.Engine.Optimization

/-- The LeanCert AD fragment plus named mathematical constants.
Every constructor here is everywhere differentiable. -/
inductive ADConstSupported : Expr → Prop where
  | const (q : ℚ) : ADConstSupported (.const q)
  | var (idx : Nat) : ADConstSupported (.var idx)
  | add {a b : Expr} :
      ADConstSupported a → ADConstSupported b → ADConstSupported (.add a b)
  | mul {a b : Expr} :
      ADConstSupported a → ADConstSupported b → ADConstSupported (.mul a b)
  | neg {a : Expr} : ADConstSupported a → ADConstSupported (.neg a)
  | exp {a : Expr} : ADConstSupported a → ADConstSupported (.exp a)
  | sin {a : Expr} : ADConstSupported a → ADConstSupported (.sin a)
  | cos {a : Expr} : ADConstSupported a → ADConstSupported (.cos a)
  | namedConst (c : MathConst) : ADConstSupported (.namedConst c)

/-- Computable recognition of the exact fragment used by the Gerver models. -/
def checkADConstSupported : Expr → Bool
  | .const _ | .var _ | .namedConst _ => true
  | .add a b | .mul a b => checkADConstSupported a && checkADConstSupported b
  | .neg a | .exp a | .sin a | .cos a => checkADConstSupported a
  | _ => false

theorem checkADConstSupported_correct {e : Expr}
    (h : checkADConstSupported e = true) : ADConstSupported e := by
  induction e with
  | const q => exact .const q
  | var i => exact .var i
  | add a b iha ihb =>
      simp only [checkADConstSupported, Bool.and_eq_true] at h
      exact .add (iha h.1) (ihb h.2)
  | mul a b iha ihb =>
      simp only [checkADConstSupported, Bool.and_eq_true] at h
      exact .mul (iha h.1) (ihb h.2)
  | neg a ih =>
      exact .neg (ih h)
  | exp a ih =>
      exact .exp (ih h)
  | sin a ih =>
      exact .sin (ih h)
  | cos a ih =>
      exact .cos (ih h)
  | namedConst c =>
      exact .namedConst c
  | inv _ _ | log _ _ | atan _ _ | arsinh _ _ | atanh _ _ | sinc _ _
    | erf _ _ | sinh _ _ | cosh _ _ | tanh _ _ | sqrt _ _ =>
      simp [checkADConstSupported] at h

theorem ADConstSupported.toCore {e : Expr} (h : ADConstSupported e) :
    ExprSupportedCore e := by
  induction h with
  | const q => exact .const q
  | var i => exact .var i
  | add _ _ iha ihb => exact .add iha ihb
  | mul _ _ iha ihb => exact .mul iha ihb
  | neg _ ih => exact .neg ih
  | exp _ ih => exact .exp ih
  | sin _ ih => exact .sin ih
  | cos _ ih => exact .cos ih
  | namedConst c => exact .namedConst c

/-- Dual-evaluator domain validity is likewise automatic for this fragment. -/
theorem ADConstSupported.domainValidDual {e : Expr} (h : ADConstSupported e)
    (ρ : DualEnv) (cfg : EvalConfig) : evalDomainValidDual e ρ cfg := by
  induction h with
  | const _ => trivial
  | var _ => trivial
  | add _ _ iha ihb => exact ⟨iha, ihb⟩
  | mul _ _ iha ihb => exact ⟨iha, ihb⟩
  | neg _ ih => exact ih
  | exp _ ih => exact ih
  | sin _ ih => exact ih
  | cos _ ih => exact ih
  | namedConst _ => trivial

/-! ## Calculus layer -/

theorem evalFin_differentiable_const {n : Nat} (e : Expr)
    (h : ADConstSupported e) :
    Differentiable ℝ (evalFin (n := n) e) := by
  induction h with
  | const q =>
      rw [show evalFin (n := n) (.const q) =
        (fun _ : Fin n → ℝ => (q : ℝ)) from rfl]
      exact differentiable_const _
  | var i =>
      by_cases hi : i < n
      · rw [show evalFin (n := n) (.var i) =
          (fun x : Fin n → ℝ => x ⟨i, hi⟩) by
            funext x
            simp [evalFin, finEnv, hi]]
        exact differentiable_apply _
      · rw [show evalFin (n := n) (.var i) =
          (fun _ : Fin n → ℝ => 0) by
            funext x
            simp [evalFin, finEnv, hi]]
        exact differentiable_const _
  | add _ _ iha ihb =>
      rw [show evalFin (n := n) (.add _ _) =
        evalFin (n := n) _ + evalFin (n := n) _ from rfl]
      exact iha.add ihb
  | mul _ _ iha ihb =>
      rw [show evalFin (n := n) (.mul _ _) =
        evalFin (n := n) _ * evalFin (n := n) _ from rfl]
      exact iha.mul ihb
  | neg _ ih =>
      rw [show evalFin (n := n) (.neg _) = -evalFin (n := n) _ from rfl]
      exact ih.neg
  | exp _ ih =>
      rw [show evalFin (n := n) (.exp _) =
        Real.exp ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_exp.comp ih
  | sin _ ih =>
      rw [show evalFin (n := n) (.sin _) =
        Real.sin ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_sin.comp ih
  | cos _ ih =>
      rw [show evalFin (n := n) (.cos _) =
        Real.cos ∘ evalFin (n := n) _ from rfl]
      exact Real.differentiable_cos.comp ih
  | namedConst c =>
      rw [show evalFin (n := n) (.namedConst c) =
        (fun _ : Fin n → ℝ => c.toReal) from rfl]
      exact differentiable_const _

theorem evalAlong_differentiable_const (e : Expr) (h : ADConstSupported e)
    (ρ : Nat → ℝ) (idx : Nat) :
    Differentiable ℝ (Expr.evalAlong e ρ idx) := by
  induction h with
  | const q =>
      simp only [Expr.evalAlong_const']
      exact differentiable_const _
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active]
        exact differentiable_id
      · simp only [Expr.evalAlong_var_passive _ _ _ hi]
        exact differentiable_const _
  | add _ _ iha ihb =>
      simp only [Expr.evalAlong_add]
      exact iha.add ihb
  | mul _ _ iha ihb =>
      simp only [Expr.evalAlong_mul]
      exact iha.mul ihb
  | neg _ ih =>
      simp only [Expr.evalAlong_neg]
      exact ih.neg
  | exp _ ih =>
      simp only [Expr.evalAlong_exp]
      exact Real.differentiable_exp.comp ih
  | sin _ ih =>
      simp only [Expr.evalAlong_sin]
      exact Real.differentiable_sin.comp ih
  | cos _ ih =>
      simp only [Expr.evalAlong_cos]
      exact Real.differentiable_cos.comp ih
  | namedConst c =>
      rw [show Expr.evalAlong (.namedConst c) ρ idx =
        (fun _ : ℝ => c.toReal) from rfl]
      exact differentiable_const _

/-- LeanCert's computable total AD derivative theorem, extended by the single
missing `namedConst` case. The computed interval is unchanged. -/
theorem evalDualTotalCore_der_correct_idx_const
    (e : Expr) (h : ADConstSupported e)
    (ρReal : Nat → ℝ) (ρInt : IntervalEnv) (idx : Nat)
    (hρ : ∀ i, ρReal i ∈ ρInt i)
    (x : ℝ) (hx : x ∈ ρInt idx) (cfg : EvalConfig) :
    deriv (Expr.evalAlong e ρReal idx) x ∈
      (LeanCert.Internal.AD.evalTotalCore e
        (mkDualEnvCore ρInt idx) cfg).der := by
  have hmem : ∀ i, Expr.updateVar ρReal idx x i ∈
      (mkDualEnvCore ρInt idx i).val := by
    simpa only [mkDualEnvCore, mkDualEnv] using
      (updateVar_mem_mkDualEnv_val ρReal ρInt idx x hx hρ)
  induction h generalizing x with
  | const q =>
      simp only [Expr.evalAlong_const', deriv_const,
        LeanCert.Internal.AD.evalTotalCore, DualInterval.const]
      exact_mod_cast IntervalRat.mem_singleton 0
  | var i =>
      by_cases hi : i = idx
      · subst i
        simp only [Expr.evalAlong_var_active, LeanCert.Internal.AD.evalTotalCore,
          mkDualEnvCore, ↓reduceIte, DualInterval.varActive, deriv_id]
        exact_mod_cast IntervalRat.mem_singleton 1
      · simp only [Expr.evalAlong_var_passive _ _ _ hi, deriv_const,
          LeanCert.Internal.AD.evalTotalCore, mkDualEnvCore, if_neg hi,
          DualInterval.varPassive]
        exact_mod_cast IntervalRat.mem_singleton 0
  | add ha hb iha ihb =>
      have hda := evalAlong_differentiable_const _ ha ρReal idx
      have hdb := evalAlong_differentiable_const _ hb ρReal idx
      simp only [Expr.evalAlong_add_pi, deriv_add (hda x) (hdb x),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.add]
      exact IntervalRat.mem_add (iha x hx hmem) (ihb x hx hmem)
  | mul ha hb iha ihb =>
      have hda := evalAlong_differentiable_const _ ha ρReal idx
      have hdb := evalAlong_differentiable_const _ hb ρReal idx
      simp only [Expr.evalAlong_mul_pi, deriv_mul (hda x) (hdb x),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.mul]
      have hvalA := LeanCert.Engine.evalDualTotalCore_val_correct _ ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      have hvalB := LeanCert.Engine.evalDualTotalCore_val_correct _ hb.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (hb.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_add
        (IntervalRat.mem_mul (iha x hx hmem) hvalB)
        (IntervalRat.mem_mul hvalA (ihb x hx hmem))
  | neg ha ih =>
      have hd := evalAlong_differentiable_const _ ha ρReal idx
      simp only [Expr.evalAlong_neg_pi, deriv.neg,
        LeanCert.Internal.AD.evalTotalCore, DualInterval.neg]
      exact IntervalRat.mem_neg (ih x hx hmem)
  | @exp a ha ih =>
      have hd := evalAlong_differentiable_const a ha ρReal idx
      simp only [Expr.evalAlong_exp, deriv_exp (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.expCore]
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct a ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_mul
        (IntervalRat.mem_expComputable hval cfg.taylorDepth) (ih x hx hmem)
  | @sin a ha ih =>
      have hd := evalAlong_differentiable_const a ha ρReal idx
      simp only [Expr.evalAlong_sin, deriv_sin (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.sinCore]
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct a ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_mul
        (IntervalRat.mem_cosComputable hval cfg.taylorDepth) (ih x hx hmem)
  | @cos a ha ih =>
      have hd := evalAlong_differentiable_const a ha ρReal idx
      simp only [Expr.evalAlong_cos, deriv_cos (hd.differentiableAt),
        LeanCert.Internal.AD.evalTotalCore, DualInterval.cosCore]
      have hval := LeanCert.Engine.evalDualTotalCore_val_correct a ha.toCore
        (Expr.updateVar ρReal idx x) (mkDualEnvCore ρInt idx) cfg hmem
        (ha.domainValidDual (mkDualEnvCore ρInt idx) cfg)
      exact IntervalRat.mem_mul
        (IntervalRat.mem_neg
          (IntervalRat.mem_sinComputable hval cfg.taylorDepth))
        (ih x hx hmem)
  | namedConst c =>
      rw [show Expr.evalAlong (.namedConst c) ρReal idx =
        (fun _ : ℝ => c.toReal) from rfl]
      simpa [LeanCert.Internal.AD.evalTotalCore, DualInterval.ofMathConst] using
        (IntervalRat.mem_singleton (0 : ℚ))

/-! ## Krawczyk calculus adapters retaining LeanCert's data path -/

theorem fderiv_single_eq_deriv_evalAlong_const {n : Nat}
    (e : Expr) (h : ADConstSupported e)
    (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (evalFin (n := n) e) x (Pi.single j 1) =
      deriv (Expr.evalAlong e (finEnv x) j.val) (x j) := by
  have hout : HasFDerivAt (evalFin (n := n) e)
      (fderiv ℝ (evalFin (n := n) e) (Function.update x j (x j)))
      (Function.update x j (x j)) :=
    (evalFin_differentiable_const (n := n) e h).differentiableAt.hasFDerivAt
  have hcomp := hout.comp_hasDerivAt (x j) (hasDerivAt_update x j (x j))
  rw [Function.update_eq_self] at hcomp
  have heq : (evalFin (n := n) e ∘ Function.update x j) =
      Expr.evalAlong e (finEnv x) j.val := by
    funext t
    simp only [Function.comp_apply, evalFin, Expr.evalAlong_eq]
    rw [finEnv_update]
  rw [heq] at hcomp
  exact hcomp.deriv.symm

theorem systemEval_differentiable_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i)) :
    Differentiable ℝ (systemEval F) := by
  rw [differentiable_pi]
  intro i
  exact evalFin_differentiable_const (F i) (h i)

theorem jacobianAt_apply_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (x : Fin n → ℝ) (i j : Fin n) :
    jacobianAt F x i j =
      deriv (Expr.evalAlong (F i) (finEnv x) j.val) (x j) := by
  rw [jacobianAt, LinearMap.toMatrix'_apply]
  change fderiv ℝ (systemEval F) x (Pi.single j 1) i = _
  rw [show systemEval F = (fun x i => evalFin (F i) x) from rfl]
  have hpi := fderiv_pi (𝕜 := ℝ) (x := x)
    (φ := fun i => evalFin (F i))
    (fun i => (evalFin_differentiable_const (F i) (h i)).differentiableAt)
  rw [hpi]
  simp only [ContinuousLinearMap.coe_pi']
  exact fderiv_single_eq_deriv_evalAlong_const (F i) (h i) x j

theorem jacobianAt_mem_intervalJacobian_const {n : Nat}
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (x : Fin n → ℝ)
    (hx : FinBoxMem x X) (cfg : EvalConfig) (i j : Fin n) :
    jacobianAt F x i j ∈ intervalJacobian F X cfg i j := by
  rw [jacobianAt_apply_const F h x i j]
  exact evalDualTotalCore_der_correct_idx_const (F i) (h i)
    (finEnv x) (finBoxEnv X) j.val (finEnv_mem_finBoxEnv hx)
    (x j) (by
      simpa only [finBoxEnv, j.isLt, dite_true] using hx j) cfg

theorem newtonMap_differentiable_const {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i)) :
    Differentiable ℝ (newtonMap Y F) := by
  have hY : Differentiable ℝ (fun x => matrixCLM Y (systemEval F x)) :=
    (matrixCLM Y).differentiable.comp (systemEval_differentiable_const F h)
  rw [show newtonMap Y F =
      id - (fun x => matrixCLM Y (systemEval F x)) by
        funext x
        rfl]
  exact differentiable_id.sub hY

theorem newtonMap_fderiv_matrix_const {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℝ)
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (x : Fin n → ℝ) :
    LinearMap.toMatrix' (fderiv ℝ (newtonMap Y F) x).toLinearMap =
      1 - Y * jacobianAt F x := by
  have hF : HasFDerivAt (systemEval F) (fderiv ℝ (systemEval F) x) x :=
    (systemEval_differentiable_const F h).differentiableAt.hasFDerivAt
  have hY := (matrixCLM Y).hasFDerivAt.comp x hF
  have hg : HasFDerivAt (newtonMap Y F)
      (ContinuousLinearMap.id ℝ _ -
        (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)) x := by
    change HasFDerivAt (fun z => z - matrixCLM Y (systemEval F z)) _ x
    exact (hasFDerivAt_id x).sub hY
  rw [hg.fderiv]
  change LinearMap.toMatrix' ((ContinuousLinearMap.id ℝ _ -
    (matrixCLM Y).comp (fderiv ℝ (systemEval F) x)).toLinearMap) = _
  rw [ContinuousLinearMap.toLinearMap_sub]
  change LinearMap.toMatrix' (1 -
    (matrixCLM Y).toLinearMap.comp
      (fderiv ℝ (systemEval F) x).toLinearMap) = _
  rw [map_sub, LinearMap.toMatrix'_one, LinearMap.toMatrix'_comp]
  have hmatY : LinearMap.toMatrix' (matrixCLM Y).toLinearMap = Y := by
    change LinearMap.toMatrix' (Matrix.mulVecLin Y) = Y
    exact LinearMap.toMatrix'_toLin' Y
  rw [hmatY]
  rfl

theorem newtonMap_fderiv_norm_le_const {n : Nat}
    (Y : Matrix (Fin n) (Fin n) ℚ)
    (F : Fin n → Expr) (h : ∀ i, ADConstSupported (F i))
    (X : Fin n → IntervalRat) (x : Fin n → ℝ)
    (hx : FinBoxMem x X) (cfg : EvalConfig) :
    ‖fderiv ℝ (newtonMap (Y.map fun q => (q : ℝ)) F) x‖ ≤
      (intervalMatrixBound
        (preconditionedJacobian Y (intervalJacobian F X cfg)) : ℝ) := by
  rw [← Matrix.linfty_opNorm_toMatrix]
  rw [newtonMap_fderiv_matrix_const
    (Y.map fun q => (q : ℝ)) F h x]
  apply matrix_norm_le_intervalMatrixBound
  exact mem_preconditionedJacobian Y (jacobianAt F x)
    (intervalJacobian F X cfg)
    (jacobianAt_mem_intervalJacobian_const F h X x hx cfg)

end PartALeanCert
end GerverSofa
