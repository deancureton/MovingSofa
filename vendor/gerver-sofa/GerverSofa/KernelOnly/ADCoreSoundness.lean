import GerverSofa.KernelOnly.TranscendentalSoundness
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Zip
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Structural soundness of first-order interval automatic differentiation

The executable `ExactReplay.D` object stores a value interval and one interval
for every first partial derivative.  This file supplies the reusable semantic
induction for all constructors actually used by the 4D and 22D certificates.
The concrete systems are handled in a separate module by instantiating these
constructor theorems.
-/

noncomputable section

namespace GerverSofa

open RatInterval

/-! ## Smooth scalar models -/

/-- A scalar function together with its coordinate gradient and a proof that
those coordinates are the actual partial derivatives.  The derivative witness
is stored as `RealDerivativeAt`, a first-principles real difference-quotient
limit.  Constructor proofs temporarily move through Mathlib's `HasDerivAt`
API and immediately return to this instance-stable semantic proposition. -/
structure ScalarModel (n : Nat) where
  value : Vec n → ℝ
  gradient : Vec n → Vec n
  hasDeriv_update : ∀ x j,
    RealDerivativeAt (fun t : ℝ => value (Function.update x j t))
      (gradient x j) (x j)

namespace ScalarModel

/-- Constant scalar model. -/
def const (n : Nat) (c : ℝ) : ScalarModel n where
  value := fun _ => c
  gradient := fun _ _ => 0
  hasDeriv_update := by
    intro x j
    simpa only [RealDerivativeAt, smul_eq_mul] using
      (hasDerivAt_const (x j) c).tendsto_slope_zero

/-- Coordinate projection. -/
def var (n : Nat) (k : Fin n) : ScalarModel n where
  value := fun x => x k
  gradient := fun _ j => if j = k then 1 else 0
  hasDeriv_update := by
    intro x j
    by_cases h : j = k
    · subst k
      have hid : RealDerivativeAt (fun t : ℝ => t) 1 (x j) := by
        simpa only [RealDerivativeAt, smul_eq_mul] using
          (hasDerivAt_id' (x j)).tendsto_slope_zero
      convert hid using 1 <;> simp
    · have hkj : k ≠ j := Ne.symm h
      simpa only [RealDerivativeAt, Function.update_of_ne hkj, if_neg h,
        smul_eq_mul] using (hasDerivAt_const (x j) (x k)).tendsto_slope_zero

/-- Pointwise addition. -/
def add {n : Nat} (f g : ScalarModel n) : ScalarModel n where
  value := fun x => f.value x + g.value x
  gradient := fun x j => f.gradient x j + g.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hgh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => g.value (Function.update x j t))
        (f' := g.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            g.hasDeriv_update x j)
    simpa only [RealDerivativeAt, smul_eq_mul] using
      (hfh.fun_add hgh).tendsto_slope_zero

/-- Pointwise negation. -/
def neg {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => -f.value x
  gradient := fun x j => -f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    simpa only [RealDerivativeAt, smul_eq_mul] using
      hfh.fun_neg.tendsto_slope_zero

/-- Pointwise subtraction. -/
def sub {n : Nat} (f g : ScalarModel n) : ScalarModel n :=
  add f (neg g)

/-- Pointwise multiplication. -/
def mul {n : Nat} (f g : ScalarModel n) : ScalarModel n where
  value := fun x => f.value x * g.value x
  gradient := fun x j =>
    f.gradient x j * g.value x + f.value x * g.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hgh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => g.value (Function.update x j t))
        (f' := g.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            g.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      (hfh.fun_mul hgh).tendsto_slope_zero

/-- Rational scaling. -/
def scale {n : Nat} (a : ℚ) (f : ScalarModel n) : ScalarModel n where
  value := fun x => (a : ℝ) * f.value x
  gradient := fun x j => (a : ℝ) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hs := HasDerivAt.const_mul (a : ℝ) hfh
    simpa only [RealDerivativeAt, smul_eq_mul] using hs.tendsto_slope_zero

/-- Sine composition. -/
def sin {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => Real.sin (f.value x)
  gradient := fun x j => Real.cos (f.value x) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      hfh.sin.tendsto_slope_zero

/-- Cosine composition. -/
def cos {n : Nat} (f : ScalarModel n) : ScalarModel n where
  value := fun x => Real.cos (f.value x)
  gradient := fun x j => -Real.sin (f.value x) * f.gradient x j
  hasDeriv_update := by
    intro x j
    have hfh :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := fun t : ℝ => f.value (Function.update x j t))
        (f' := f.gradient x j) (x := x j)).2 (by
          simpa only [RealDerivativeAt, smul_eq_mul] using
            f.hasDeriv_update x j)
    have hupd : Function.update x j (x j) = x :=
      Function.update_eq_self j x
    simpa only [RealDerivativeAt, smul_eq_mul, hupd] using
      hfh.cos.tendsto_slope_zero

instance {n : Nat} : Add (ScalarModel n) := ⟨add⟩
instance {n : Nat} : Neg (ScalarModel n) := ⟨neg⟩
instance {n : Nat} : Sub (ScalarModel n) := ⟨sub⟩
instance {n : Nat} : Mul (ScalarModel n) := ⟨mul⟩
instance {n : Nat} : HMul ℚ (ScalarModel n) (ScalarModel n) := ⟨scale⟩

/-! The executable systems are written with notation, while constructor-level
    soundness lemmas produce the named operations above.  These tiny simp
    bridges make that definitional equality explicit without unfolding the
    proof-carrying structures themselves. -/
@[simp] theorem add_notation {n : Nat} (f g : ScalarModel n) :
    f + g = add f g := rfl

@[simp] theorem neg_notation {n : Nat} (f : ScalarModel n) :
    -f = neg f := rfl

@[simp] theorem sub_notation {n : Nat} (f g : ScalarModel n) :
    f - g = sub f g := rfl

@[simp] theorem mul_notation {n : Nat} (f g : ScalarModel n) :
    f * g = mul f g := rfl

@[simp] theorem scale_notation {n : Nat} (a : ℚ) (f : ScalarModel n) :
    a * f = scale a f := rfl

@[simp] theorem add_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (f + g).value x = f.value x + g.value x := rfl

@[simp] theorem neg_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (-f).value x = -f.value x := rfl

@[simp] theorem sub_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (f - g).value x = f.value x - g.value x := rfl

@[simp] theorem mul_value {n : Nat} (f g : ScalarModel n) (x : Vec n) :
    (f * g).value x = f.value x * g.value x := rfl

@[simp] theorem scale_value {n : Nat} (a : ℚ) (f : ScalarModel n) (x : Vec n) :
    (a * f).value x = (a : ℝ) * f.value x := rfl

@[simp] theorem sin_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (sin f).value x = Real.sin (f.value x) := rfl

@[simp] theorem cos_value {n : Nat} (f : ScalarModel n) (x : Vec n) :
    (cos f).value x = Real.cos (f.value x) := rfl

end ScalarModel

namespace ExactReplay.D

/-! Matching notation bridges for the executable dual intervals. -/
@[simp] theorem add_notation (x y : ExactReplay.D) :
    x + y = addD x y := rfl

@[simp] theorem neg_notation (x : ExactReplay.D) :
    -x = negD x := rfl

@[simp] theorem sub_notation (x y : ExactReplay.D) :
    x - y = subD x y := rfl

@[simp] theorem mul_notation (x y : ExactReplay.D) :
    x * y = mulD x y := rfl

@[simp] theorem scale_notation (a : ℚ) (x : ExactReplay.D) :
    a * x = scaleD a x := rfl

end ExactReplay.D

/-! ## Semantic relation for the executable dual interval -/

/-- An executable dual interval encloses a smooth scalar model on a set. -/
structure DSoundOn {n : Nat} (X : Set (Vec n))
    (d : ExactReplay.D) (f : ScalarModel n) : Prop where
  value_sound : ∀ x ∈ X, Contains d.val (f.value x)
  derivative_length : d.der.length = n
  derivative_sound : ∀ x ∈ X, ∀ j : Fin n,
    Contains (d.der.getD j.1 ExactReplay.zeroI) (f.gradient x j)

/-! ## List access lemmas used by the AD constructors -/

private theorem getD_map_of_lt
    {α β : Type*} (f : α → β) (xs : List α)
    (i : Nat) (h : i < xs.length) (da : α) (db : β) :
    (xs.map f).getD i db = f (xs.getD i da) := by
  have hmap : i < (xs.map f).length := by simpa using h
  rw [List.getD_eq_getElem (xs.map f) db hmap]
  rw [List.getD_eq_getElem xs da h]
  simp

private theorem getD_zipWith_of_lt
    {α β γ : Type*} (f : α → β → γ)
    (xs : List α) (ys : List β) (i : Nat)
    (hx : i < xs.length) (hy : i < ys.length)
    (da : α) (db : β) (dc : γ) :
    (List.zipWith f xs ys).getD i dc =
      f (xs.getD i da) (ys.getD i db) := by
  have hz : i < (List.zipWith f xs ys).length := by
    simpa only [List.length_zipWith] using (lt_min hx hy)
  rw [List.getD_eq_getElem (List.zipWith f xs ys) dc hz]
  rw [List.getD_eq_getElem xs da hx]
  rw [List.getD_eq_getElem ys db hy]
  simp

/-! ## Constructor soundness -/

/-- Exact interval constant. -/
theorem DSoundOn.const {n : Nat} {X : Set (Vec n)}
    {z : RatInterval} {c : ℝ} (hc : Contains z c) :
    DSoundOn X (ExactReplay.D.const z n) (ScalarModel.const n c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact hc
  · simp [ExactReplay.D.const]
  · intro x hx j
    simp [ExactReplay.D.const, ExactReplay.zeroI, ScalarModel.const,
      RatInterval.Contains, RatInterval.point]

/-- Rational point constant. -/
theorem DSoundOn.pointConst {n : Nat} {X : Set (Vec n)} (q : ℚ) :
    DSoundOn X (ExactReplay.D.pointConst q n)
      (ScalarModel.const n (q : ℝ)) := by
  apply DSoundOn.const
  exact (RatInterval.contains_point_iff q (q : ℝ)).2 rfl

/-- Coordinate variable read from an enclosing input interval. -/
theorem DSoundOn.varD {n : Nat} {X : Set (Vec n)}
    (input : RatInterval) (k : Fin n)
    (hinput : ∀ x ∈ X, Contains input (x k)) :
    DSoundOn X (ExactReplay.D.varD input k.1 n) (ScalarModel.var n k) := by
  refine ⟨hinput, ?_, ?_⟩
  · simp [ExactReplay.D.varD]
  · intro x hx j
    have hj : j.1 < (List.range n).length := by simpa using j.2
    change Contains
      (((List.range n).map
        (fun m => RatInterval.point (if m = k.1 then 1 else 0))).getD
          j.1 ExactReplay.zeroI)
      (if j = k then 1 else 0)
    rw [getD_map_of_lt (fun m => RatInterval.point (if m = k.1 then 1 else 0))
      (List.range n) j.1 hj 0 ExactReplay.zeroI]
    have hjrange : (List.range n).getD j.1 0 = j.1 := by
      rw [List.getD_eq_getElem (List.range n) 0 hj]
      simp
    rw [hjrange]
    by_cases hjk : j = k
    · subst k
      simp [ExactReplay.zeroI, RatInterval.Contains, RatInterval.point]
    · have hval : j.1 ≠ k.1 := by
        intro hval
        exact hjk (Fin.ext hval)
      simp [hjk, hval, ExactReplay.zeroI, RatInterval.Contains, RatInterval.point]

/-- Addition constructor. -/
theorem DSoundOn.add {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.addD dx dy) (ScalarModel.add f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_add (hx.value_sound x hX) (hy.value_sound x hX)
  · simp [ExactReplay.D.addD, hx.derivative_length, hy.derivative_length]
  · intro x hX j
    have hjx : j.1 < dx.der.length := by simpa [hx.derivative_length] using j.2
    have hjy : j.1 < dy.der.length := by simpa [hy.derivative_length] using j.2
    change Contains
      ((List.zipWith RatInterval.add dx.der dy.der).getD j.1 ExactReplay.zeroI)
      (f.gradient x j + g.gradient x j)
    rw [getD_zipWith_of_lt RatInterval.add dx.der dy.der j.1 hjx hjy
      ExactReplay.zeroI ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_add
      (hx.derivative_sound x hX j) (hy.derivative_sound x hX j)

/-- Negation constructor. -/
theorem DSoundOn.neg {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f) :
    DSoundOn X (ExactReplay.D.negD d) (ScalarModel.neg f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_neg (h.value_sound x hX)
  · simp [ExactReplay.D.negD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simpa [h.derivative_length] using j.2
    change Contains
      ((d.der.map RatInterval.neg).getD j.1 ExactReplay.zeroI)
      (-f.gradient x j)
    rw [getD_map_of_lt RatInterval.neg d.der j.1 hj
      ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_neg (h.derivative_sound x hX j)

/-- Subtraction constructor. -/
theorem DSoundOn.sub {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.subD dx dy) (ScalarModel.sub f g) := by
  simpa [ExactReplay.D.subD, ScalarModel.sub] using hx.add hy.neg

/-- Multiplication constructor and product rule. -/
theorem DSoundOn.mul {n : Nat} {X : Set (Vec n)}
    {dx dy : ExactReplay.D} {f g : ScalarModel n}
    (hx : DSoundOn X dx f) (hy : DSoundOn X dy g) :
    DSoundOn X (ExactReplay.D.mulD dx dy) (ScalarModel.mul f g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_mul (hx.value_sound x hX) (hy.value_sound x hX)
  · simp [ExactReplay.D.mulD, hx.derivative_length, hy.derivative_length]
  · intro x hX j
    have hjx : j.1 < dx.der.length := by simpa [hx.derivative_length] using j.2
    have hjy : j.1 < dy.der.length := by simpa [hy.derivative_length] using j.2
    change Contains
      ((List.zipWith
        (fun ddx ddy => RatInterval.add (RatInterval.mul ddx dy.val)
          (RatInterval.mul dx.val ddy))
        dx.der dy.der).getD j.1 ExactReplay.zeroI)
      (f.gradient x j * g.value x + f.value x * g.gradient x j)
    rw [getD_zipWith_of_lt
      (fun ddx ddy => RatInterval.add (RatInterval.mul ddx dy.val)
        (RatInterval.mul dx.val ddy))
      dx.der dy.der j.1 hjx hjy ExactReplay.zeroI ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_add
      (RatInterval.contains_mul (hx.derivative_sound x hX j)
        (hy.value_sound x hX))
      (RatInterval.contains_mul (hx.value_sound x hX)
        (hy.derivative_sound x hX j))

/-- Rational scaling constructor. -/
theorem DSoundOn.scale {n : Nat} {X : Set (Vec n)}
    (a : ℚ) {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f) :
    DSoundOn X (ExactReplay.D.scaleD a d) (ScalarModel.scale a f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact RatInterval.contains_scale (h.value_sound x hX)
  · simp [ExactReplay.D.scaleD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simpa [h.derivative_length] using j.2
    change Contains
      ((d.der.map (ExactReplay.scale a)).getD j.1 ExactReplay.zeroI)
      ((a : ℝ) * f.gradient x j)
    rw [getD_map_of_lt (ExactReplay.scale a) d.der j.1 hj
      ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_scale (h.derivative_sound x hX j)

/-- Sine constructor and chain rule. -/
theorem DSoundOn.sin {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f)
    (hphysical : ∀ x ∈ X, 0 ≤ f.value x ∧ f.value x ≤ Real.pi / 2) :
    DSoundOn X (ExactReplay.D.sinD d) (ScalarModel.sin f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact ExactReplay.sinI_contains (h.value_sound x hX)
      (hphysical x hX).1 (hphysical x hX).2
  · simp [ExactReplay.D.sinD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simpa [h.derivative_length] using j.2
    change Contains
      ((d.der.map (RatInterval.mul (ExactReplay.cosI d.val))).getD
        j.1 ExactReplay.zeroI)
      (Real.cos (f.value x) * f.gradient x j)
    rw [getD_map_of_lt (RatInterval.mul (ExactReplay.cosI d.val)) d.der
      j.1 hj ExactReplay.zeroI ExactReplay.zeroI]
    exact RatInterval.contains_mul
      (ExactReplay.cosI_contains (h.value_sound x hX)
        (hphysical x hX).1 (hphysical x hX).2)
      (h.derivative_sound x hX j)

/-- Cosine constructor and chain rule. -/
theorem DSoundOn.cos {n : Nat} {X : Set (Vec n)}
    {d : ExactReplay.D} {f : ScalarModel n}
    (h : DSoundOn X d f)
    (hphysical : ∀ x ∈ X, 0 ≤ f.value x ∧ f.value x ≤ Real.pi / 2) :
    DSoundOn X (ExactReplay.D.cosD d) (ScalarModel.cos f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hX
    exact ExactReplay.cosI_contains (h.value_sound x hX)
      (hphysical x hX).1 (hphysical x hX).2
  · simp [ExactReplay.D.cosD, h.derivative_length]
  · intro x hX j
    have hj : j.1 < d.der.length := by simpa [h.derivative_length] using j.2
    change Contains
      ((d.der.map (fun z => RatInterval.neg
        (RatInterval.mul (ExactReplay.sinI d.val) z))).getD
        j.1 ExactReplay.zeroI)
      (-Real.sin (f.value x) * f.gradient x j)
    rw [getD_map_of_lt (fun z => RatInterval.neg
      (RatInterval.mul (ExactReplay.sinI d.val) z)) d.der
      j.1 hj ExactReplay.zeroI ExactReplay.zeroI]
    simpa only [neg_mul] using
      RatInterval.contains_neg (RatInterval.contains_mul
        (ExactReplay.sinI_contains (h.value_sound x hX)
          (hphysical x hX).1 (hphysical x hX).2)
        (h.derivative_sound x hX j))

end GerverSofa
