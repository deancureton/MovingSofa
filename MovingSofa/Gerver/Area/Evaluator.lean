import MovingSofa.Gerver.Area.Grid
import MovingSofa.Gerver.Area.TrigEnclosure

/-!
# Soundness of the contact evaluator

`GerverAreaCert.evalZ s z kind` evaluates one of the five phase formulas of Gerver's sofa,
and one of its four contact curves, on an interval of rotation angles.  This module proves
that it encloses the analytic value: `gerverBranch_eq` identifies the branch that the
piecewise vendor definitions `GerverSofa.Romik.path` and `GerverSofa.PartC.alphaBetaAt`
select, the five per-stage lemmas verify the phase formulas and the two velocity
coefficients against `GerverSofa.Romik.path1 … path5` and
`GerverSofa.Romik.alphaBeta1 … alphaBeta5`, and `evalZ_sound` assembles them through the
coordinate dictionary `fromPlane_paperGerverContacts`.  `contactZ_sound` and
`evalZ_interval_sound` specialise this to a grid angle and to a whole grid subinterval.
-/

noncomputable section

namespace MovingSofa

open GerverAreaCert

/-! ### The contact evaluator -/

/-- The five certified phase maps, selected by stage index. -/
def gerverBranchPath : ℕ → ℝ → GerverSofa.Point
  | 1 => GerverSofa.Romik.path1 GerverSofa.PartB.params
  | 2 => GerverSofa.Romik.path2 GerverSofa.PartB.params
  | 3 => GerverSofa.Romik.path3 GerverSofa.PartB.params
  | 4 => GerverSofa.Romik.path4 GerverSofa.PartB.params
  | _ => GerverSofa.Romik.path5 GerverSofa.PartB.params

/-- The five certified velocity-coefficient pairs, selected by stage index. -/
def gerverBranchAlphaBeta : ℕ → ℝ → GerverSofa.Point
  | 1 => GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params
  | 2 => GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params
  | 3 => GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params
  | 4 => GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params
  | _ => GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params

/-- On a grid angle of stage `s` both piecewise definitions select branch `s`. -/
theorem gerverBranch_eq (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {x : ℝ}
    (hxhi : x ≤ gerverStageTime s) (hxlo : 2 ≤ s → gerverStageTime (s - 1) < x) :
    GerverSofa.Romik.path GerverSofa.PartB.params x = gerverBranchPath s x ∧
      GerverSofa.PartC.alphaBetaAt x = gerverBranchAlphaBeta s x := by
  have o12 : GerverSofa.PartB.params.phi < GerverSofa.PartB.params.theta := by
    have := gerverStageTime_lt_succ 1 (by norm_num)
    rwa [gerverStageTime_one, gerverStageTime_two] at this
  have o23 : GerverSofa.PartB.params.theta < GerverSofa.PartC.eta := by
    have := gerverStageTime_lt_succ 2 (by norm_num)
    rwa [gerverStageTime_two, gerverStageTime_three] at this
  have o34 : GerverSofa.PartC.eta < GerverSofa.PartC.tau := by
    have := gerverStageTime_lt_succ 3 (by norm_num)
    rwa [gerverStageTime_three, gerverStageTime_four] at this
  have hpath : GerverSofa.Romik.path GerverSofa.PartB.params x =
      if x ≤ GerverSofa.PartB.params.phi then
        GerverSofa.Romik.path1 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartB.params.theta then
        GerverSofa.Romik.path2 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.eta then
        GerverSofa.Romik.path3 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.tau then
        GerverSofa.Romik.path4 GerverSofa.PartB.params x
      else GerverSofa.Romik.path5 GerverSofa.PartB.params x := rfl
  have hab : GerverSofa.PartC.alphaBetaAt x =
      if x ≤ GerverSofa.PartB.params.phi then
        GerverSofa.Romik.alphaBeta1 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartB.params.theta then
        GerverSofa.Romik.alphaBeta2 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.eta then
        GerverSofa.Romik.alphaBeta3 GerverSofa.PartB.params x
      else if x ≤ GerverSofa.PartC.tau then
        GerverSofa.Romik.alphaBeta4 GerverSofa.PartB.params x
      else GerverSofa.Romik.alphaBeta5 GerverSofa.PartB.params x := rfl
  interval_cases s
  · rw [gerverStageTime_one] at hxhi
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_two] at hxhi
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := by
      have := hxlo (by norm_num)
      rw [gerverStageTime_one] at this
      exact not_le.mpr this
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_right h1, ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_three] at hxhi
    have h2 : GerverSofa.PartB.params.theta < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_two] at this
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_left hxhi]; rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_left hxhi]; rfl
  · rw [gerverStageTime_four] at hxhi
    have h3 : GerverSofa.PartC.eta < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_three] at this
    have h2 : GerverSofa.PartB.params.theta < x := o23.trans h3
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_left hxhi]
      rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_left hxhi]
      rfl
  · have h4 : GerverSofa.PartC.tau < x := by
      have := hxlo (by norm_num)
      rwa [gerverStageTime_four] at this
    have h3 : GerverSofa.PartC.eta < x := o34.trans h4
    have h2 : GerverSofa.PartB.params.theta < x := o23.trans h3
    have h1 : ¬ x ≤ GerverSofa.PartB.params.phi := not_le.mpr (o12.trans h2)
    refine ⟨?_, ?_⟩
    · rw [hpath, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_right (not_le.mpr h4)]
      rfl
    · rw [hab, ite_eq_right h1, ite_eq_right (not_le.mpr h2), ite_eq_right (not_le.mpr h3),
        ite_eq_right (not_le.mpr h4)]
      rfl

/-- Transport an enclosure along an equality of the enclosed real number. -/
private theorem contains_of_eq_real {z : SI} {a b : ℝ} (hab : a = b) (h : SI.Contains z a) :
    SI.Contains z b := hab ▸ h

open SI in
/-- Stage-1 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage1_sound {z : SI} {x : ℝ}
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 1 z 0).1 (gerverBranchPath 1 x).1 ∧
      SI.Contains (evalZ 1 z 0).2 (gerverBranchPath 1 x).2 ∧
      SI.Contains (evalZ 1 z 2).1
        ((gerverBranchPath 1 x).1 - (gerverBranchAlphaBeta 1 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 1 z 2).2
        ((gerverBranchPath 1 x).2 + (gerverBranchAlphaBeta 1 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 1 z 4).1
        ((gerverBranchPath 1 x).1 - (gerverBranchAlphaBeta 1 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 1 z 4).2
        ((gerverBranchPath 1 x).2 - (gerverBranchAlphaBeta 1 x).2 * Real.sin x) := by
  obtain ⟨hk11, hk12, -, -, -, -, -, -, -, -, ha1, ha2, -⟩ := contains_params
  have hf := contains_add (contains_add (contains_mul ha1 hcos) (contains_mul ha2 hsin))
    (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hg := contains_add (contains_add (contains_mul (contains_neg ha2) hcos)
    (contains_mul ha1 hsin)) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hal := contains_add (contains_add (contains_mul (contains_imul (-2) ha1) hsin)
    (contains_mul (contains_imul 2 ha2) hcos)) (contains_ratI (a := 1) (b := 2) (by norm_num))
  have hbe := contains_add (contains_add (contains_mul (contains_imul 2 ha1) hcos)
    (contains_mul (contains_imul 2 ha2) hsin)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk11
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk12
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path1,
      GerverSofa.Romik.alphaBeta1, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-2 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage2_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 2 z 0).1 (gerverBranchPath 2 x).1 ∧
      SI.Contains (evalZ 2 z 0).2 (gerverBranchPath 2 x).2 ∧
      SI.Contains (evalZ 2 z 2).1
        ((gerverBranchPath 2 x).1 - (gerverBranchAlphaBeta 2 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 2 z 2).2
        ((gerverBranchPath 2 x).2 + (gerverBranchAlphaBeta 2 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 2 z 4).1
        ((gerverBranchPath 2 x).1 - (gerverBranchAlphaBeta 2 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 2 z 4).2
        ((gerverBranchPath 2 x).2 - (gerverBranchAlphaBeta 2 x).2 * Real.sin x) := by
  obtain ⟨-, -, hk21, hk22, -, -, -, -, -, -, -, -, hb1, hb2, -⟩ := contains_params
  have hf := contains_add (contains_add
    (contains_divn (b := 4) (by norm_num) (contains_neg (contains_mul hz hz)))
    (contains_mul hb1 hz)) hb2
  have hg := contains_add (contains_add (contains_divn (b := 2) (by norm_num) hz)
    (contains_neg hb1)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hal := contains_add (contains_add (contains_ratI (a := 1) (b := 1) (by norm_num))
    (contains_imul 2 hb1)) (contains_neg hz)
  have hbe := contains_add hf (contains_ratI (a := 1) (b := 2) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk21
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk22
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path2,
      GerverSofa.Romik.alphaBeta2, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-3 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage3_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 3 z 0).1 (gerverBranchPath 3 x).1 ∧
      SI.Contains (evalZ 3 z 0).2 (gerverBranchPath 3 x).2 ∧
      SI.Contains (evalZ 3 z 2).1
        ((gerverBranchPath 3 x).1 - (gerverBranchAlphaBeta 3 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 3 z 2).2
        ((gerverBranchPath 3 x).2 + (gerverBranchAlphaBeta 3 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 3 z 4).1
        ((gerverBranchPath 3 x).1 - (gerverBranchAlphaBeta 3 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 3 z 4).2
        ((gerverBranchPath 3 x).2 - (gerverBranchAlphaBeta 3 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, hk31, hk32, -, -, -, -, -, -, -, -, hc1, hc2, -⟩ := contains_params
  have hf := contains_sub hc1 hz
  have hg := contains_add hc2 hz
  have hal := contains_add (contains_ratI (a := -1) (b := 1) (by norm_num)) (contains_neg hg)
  have hbe := contains_add (contains_ratI (a := 1) (b := 1) (by norm_num)) hf
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk31
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk32
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
    simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path3,
      GerverSofa.Romik.alphaBeta3, GerverSofa.Romik.addK, GerverSofa.Romik.rot] <;>
    push_cast <;> ring

open SI in
/-- Stage-4 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage4_sound {z : SI} {x : ℝ} (hz : SI.Contains z x)
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 4 z 0).1 (gerverBranchPath 4 x).1 ∧
      SI.Contains (evalZ 4 z 0).2 (gerverBranchPath 4 x).2 ∧
      SI.Contains (evalZ 4 z 2).1
        ((gerverBranchPath 4 x).1 - (gerverBranchAlphaBeta 4 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 4 z 2).2
        ((gerverBranchPath 4 x).2 + (gerverBranchAlphaBeta 4 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 4 z 4).1
        ((gerverBranchPath 4 x).1 - (gerverBranchAlphaBeta 4 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 4 z 4).2
        ((gerverBranchPath 4 x).2 - (gerverBranchAlphaBeta 4 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, -, -, hk41, hk42, -, -, -, -, -, -, -, -, hd1, hd2, -⟩ := contains_params
  have hf := contains_add (contains_add
    (contains_neg (contains_divn (b := 2) (by norm_num) hz)) hd1)
    (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hg := contains_add (contains_add
    (contains_divn (b := 4) (by norm_num) (contains_neg (contains_mul hz hz)))
    (contains_mul hd1 hz)) hd2
  have hal := contains_add (contains_neg hg) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hbe := contains_add (contains_add (contains_imul 2 hd1)
    (contains_ratI (a := -1) (b := 1) (by norm_num))) (contains_neg hz)
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk41
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk42
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path4,
      GerverSofa.Romik.alphaBeta4, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

open SI in
/-- Stage-5 interval soundness of the phase map and of the two velocity offsets. -/
private theorem evalZ_stage5_sound {z : SI} {x : ℝ}
    (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ 5 z 0).1 (gerverBranchPath 5 x).1 ∧
      SI.Contains (evalZ 5 z 0).2 (gerverBranchPath 5 x).2 ∧
      SI.Contains (evalZ 5 z 2).1
        ((gerverBranchPath 5 x).1 - (gerverBranchAlphaBeta 5 x).1 * Real.sin x) ∧
      SI.Contains (evalZ 5 z 2).2
        ((gerverBranchPath 5 x).2 + (gerverBranchAlphaBeta 5 x).1 * Real.cos x) ∧
      SI.Contains (evalZ 5 z 4).1
        ((gerverBranchPath 5 x).1 - (gerverBranchAlphaBeta 5 x).2 * Real.cos x) ∧
      SI.Contains (evalZ 5 z 4).2
        ((gerverBranchPath 5 x).2 - (gerverBranchAlphaBeta 5 x).2 * Real.sin x) := by
  obtain ⟨-, -, -, -, -, -, -, -, hk51, hk52, -, -, -, -, -, -, -, -, he1, he2, -⟩ :=
    contains_params
  have hf := contains_add (contains_add (contains_mul he1 hcos) (contains_mul he2 hsin))
    (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hg := contains_add (contains_add (contains_mul (contains_neg he2) hcos)
    (contains_mul he1 hsin)) (contains_ratI (a := -1) (b := 1) (by norm_num))
  have hal := contains_add (contains_add (contains_ratI (a := 1) (b := 1) (by norm_num))
    (contains_mul (contains_imul (-2) he1) hsin)) (contains_mul (contains_imul 2 he2) hcos)
  have hbe := contains_add (contains_add (contains_mul (contains_imul 2 he1) hcos)
    (contains_mul (contains_imul 2 he2) hsin)) (contains_ratI (a := -1) (b := 2) (by norm_num))
  have hx := contains_add (contains_sub (contains_mul hcos hf) (contains_mul hsin hg)) hk51
  have hy := contains_add (contains_add (contains_mul hsin hf) (contains_mul hcos hg)) hk52
  refine ⟨contains_of_eq_real ?_ hx, contains_of_eq_real ?_ hy,
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hal hsin)),
    contains_of_eq_real ?_ (contains_add hy (contains_mul hal hcos)),
    contains_of_eq_real ?_ (contains_sub hx (contains_mul hbe hcos)),
    contains_of_eq_real ?_ (contains_sub hy (contains_mul hbe hsin))⟩ <;>
  · simp only [gerverBranchPath, gerverBranchAlphaBeta, GerverSofa.Romik.path5,
      GerverSofa.Romik.alphaBeta5, GerverSofa.Romik.addK, GerverSofa.Romik.rot]
    push_cast
    ring

/-- Per-stage soundness of the phase-map evaluation, i.e. of the `kind = 0` output.
Pure interval arithmetic against `GerverSofa.Romik.path1 … path5`: five cases, each a chain
of `SI.contains_*` applications on top of `contains_params`, `hsin` and `hcos`. -/
theorem evalZ_zero_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ s z 0).1 (gerverBranchPath s x).1 ∧
      SI.Contains (evalZ s z 0).2 (gerverBranchPath s x).2 := by
  interval_cases s
  · exact ⟨(evalZ_stage1_sound hsin hcos).1, (evalZ_stage1_sound hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage2_sound hz hsin hcos).1, (evalZ_stage2_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage3_sound hz hsin hcos).1, (evalZ_stage3_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage4_sound hz hsin hcos).1, (evalZ_stage4_sound hz hsin hcos).2.1⟩
  · exact ⟨(evalZ_stage5_sound hsin hcos).1, (evalZ_stage5_sound hsin hcos).2.1⟩

/-- Per-stage soundness of the `B` and `D` offsets, i.e. of the two velocity
coefficients `α` and `β` against `GerverSofa.Romik.alphaBeta1 … alphaBeta5`.  Note
`evalZ s z 1 = evalZ s z 2` shifted by `(cos x, sin x)` and
`evalZ s z 3 = evalZ s z 4` shifted by `(-sin x, cos x)`, so the remaining two kinds need no
separate stage analysis. -/
theorem evalZ_offset_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hsin : SI.Contains (trigZ z).1 (Real.sin x))
    (hcos : SI.Contains (trigZ z).2 (Real.cos x)) :
    SI.Contains (evalZ s z 2).1
        ((gerverBranchPath s x).1 - (gerverBranchAlphaBeta s x).1 * Real.sin x) ∧
      SI.Contains (evalZ s z 2).2
        ((gerverBranchPath s x).2 + (gerverBranchAlphaBeta s x).1 * Real.cos x) ∧
      SI.Contains (evalZ s z 4).1
        ((gerverBranchPath s x).1 - (gerverBranchAlphaBeta s x).2 * Real.cos x) ∧
      SI.Contains (evalZ s z 4).2
        ((gerverBranchPath s x).2 - (gerverBranchAlphaBeta s x).2 * Real.sin x) := by
  interval_cases s
  · exact (evalZ_stage1_sound hsin hcos).2.2
  · exact (evalZ_stage2_sound hz hsin hcos).2.2
  · exact (evalZ_stage3_sound hz hsin hcos).2.2
  · exact (evalZ_stage4_sound hz hsin hcos).2.2
  · exact (evalZ_stage5_sound hsin hcos).2.2

/-- Soundness of the executable phase/contact evaluator: on the branch that the
piecewise definitions select, the interval evaluation encloses both coordinates of the
selected curve.  Reduces to `gerverBranch_eq`, `evalZ_zero_sound`, `evalZ_offset_sound`,
`trigZ_sound` and the coordinate dictionary
`fromPlane_paperGerverContacts` (`GerverSofa.u t = (cos t, sin t)`,
`GerverSofa.v t = (-sin t, cos t)`). -/
theorem evalZ_sound (s : ℕ) (hs1 : 1 ≤ s) (hs5 : s ≤ 5) {z : SI} {x : ℝ}
    (hz : SI.Contains z x) (hx0 : 0 ≤ x) (hxT : x ≤ Real.pi / 2)
    (hxhi : x ≤ gerverStageTime s) (hxlo : 2 ≤ s → gerverStageTime (s - 1) < x)
    (kind : ℕ) (hk : kind ≤ 4) :
    SI.Contains (evalZ s z kind).1 (gerverContactPoint kind x 0) ∧
      SI.Contains (evalZ s z kind).2 (gerverContactPoint kind x 1) := by
  have hx2 : x ≤ 2 := by linarith [Real.pi_lt_d2]
  obtain ⟨hsin, hcos⟩ := trigZ_sound hz hx0 hx2
  obtain ⟨hp, hab⟩ := gerverBranch_eq s hs1 hs5 hxhi hxlo
  obtain ⟨h0x, h0y⟩ := evalZ_zero_sound s hs1 hs5 hz hsin hcos
  obtain ⟨h2x, h2y, h4x, h4y⟩ := evalZ_offset_sound s hs1 hs5 hz hsin hcos
  have ht : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx0, hxT⟩
  -- The four contact curves in terms of the branch phase map and coefficients.
  set P : ℝ × ℝ := gerverBranchPath s x with hPdef
  set AB : ℝ × ℝ := gerverBranchAlphaBeta s x with hABdef
  have hpath1 : (GerverSofa.Romik.path GerverSofa.PartB.params x).1 = P.1 := by rw [hp]
  have hpath2 : (GerverSofa.Romik.path GerverSofa.PartB.params x).2 = P.2 := by rw [hp]
  have hal : (GerverSofa.PartC.alphaBetaAt x).1 = AB.1 := by rw [hab]
  have hbe : (GerverSofa.PartC.alphaBetaAt x).2 = AB.2 := by rw [hab]
  have hdA1 : gerverContactPoint 1 x 0 = P.1 - AB.1 * Real.sin x + Real.cos x := by
    have h' : gerverContactPoint 1 x 0 = (GerverSofa.PartC.A x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 0)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).1 + (GerverSofa.u x).1 = _
    rw [hpath1, hal]
    show P.1 + AB.1 * (-Real.sin x) + Real.cos x = _
    ring
  have hdA2 : gerverContactPoint 1 x 1 = P.2 + AB.1 * Real.cos x + Real.sin x := by
    have h' : gerverContactPoint 1 x 1 = (GerverSofa.PartC.A x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 0)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).2 + (GerverSofa.u x).2 = _
    rw [hpath2, hal]
    show P.2 + AB.1 * Real.cos x + Real.sin x = _
    ring
  have hdB1 : gerverContactPoint 2 x 0 = P.1 - AB.1 * Real.sin x := by
    have h' : gerverContactPoint 2 x 0 = (GerverSofa.PartC.B x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 1)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).1 = _
    rw [hpath1, hal]
    show P.1 + AB.1 * (-Real.sin x) = _
    ring
  have hdB2 : gerverContactPoint 2 x 1 = P.2 + AB.1 * Real.cos x := by
    have h' : gerverContactPoint 2 x 1 = (GerverSofa.PartC.B x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 1)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 +
      (GerverSofa.PartC.alphaBetaAt x).1 * (GerverSofa.v x).2 = _
    rw [hpath2, hal]
    rfl
  have hdC1 : gerverContactPoint 3 x 0 = P.1 - AB.2 * Real.cos x - Real.sin x := by
    have h' : gerverContactPoint 3 x 0 = (GerverSofa.PartC.C x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 2)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).1 + (GerverSofa.v x).1 = _
    rw [hpath1, hbe]
    show P.1 - AB.2 * Real.cos x + -Real.sin x = _
    ring
  have hdC2 : gerverContactPoint 3 x 1 = P.2 - AB.2 * Real.sin x + Real.cos x := by
    have h' : gerverContactPoint 3 x 1 = (GerverSofa.PartC.C x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 2)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).2 + (GerverSofa.v x).2 = _
    rw [hpath2, hbe]
    rfl
  have hdD1 : gerverContactPoint 4 x 0 = P.1 - AB.2 * Real.cos x := by
    have h' : gerverContactPoint 4 x 0 = (GerverSofa.PartC.D x).1 :=
      congrArg Prod.fst (fromPlane_paperGerverContacts x ht 3)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).1 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).1 = _
    rw [hpath1, hbe]
    rfl
  have hdD2 : gerverContactPoint 4 x 1 = P.2 - AB.2 * Real.sin x := by
    have h' : gerverContactPoint 4 x 1 = (GerverSofa.PartC.D x).2 :=
      congrArg Prod.snd (fromPlane_paperGerverContacts x ht 3)
    rw [h']
    show (GerverSofa.Romik.path GerverSofa.PartB.params x).2 -
      (GerverSofa.PartC.alphaBetaAt x).2 * (GerverSofa.u x).2 = _
    rw [hpath2, hbe]
    rfl
  have hd01 : gerverContactPoint 0 x 0 = P.1 := hpath1
  have hd02 : gerverContactPoint 0 x 1 = P.2 := hpath2
  -- The `A` and `C` outputs are the `B` and `D` outputs shifted by the frame vectors.
  have eA1 : (evalZ s z 1).1 = SI.add (evalZ s z 2).1 (trigZ z).2 := rfl
  have eA2 : (evalZ s z 1).2 = SI.add (evalZ s z 2).2 (trigZ z).1 := rfl
  have eC1 : (evalZ s z 3).1 = SI.sub (evalZ s z 4).1 (trigZ z).1 := rfl
  have eC2 : (evalZ s z 3).2 = SI.add (evalZ s z 4).2 (trigZ z).2 := rfl
  interval_cases kind
  · exact ⟨hd01 ▸ h0x, hd02 ▸ h0y⟩
  · refine ⟨?_, ?_⟩
    · rw [hdA1, eA1]
      exact SI.contains_add h2x hcos
    · rw [hdA2, eA2]
      exact SI.contains_add h2y hsin
  · exact ⟨hdB1 ▸ h2x, hdB2 ▸ h2y⟩
  · refine ⟨?_, ?_⟩
    · rw [hdC1, eC1]
      exact SI.contains_sub h4x hsin
    · rw [hdC2, eC2]
      exact SI.contains_add h4y hcos
  · exact ⟨hdD1 ▸ h4x, hdD2 ▸ h4y⟩

/-- The left endpoint of the branch selected at the right end of a grid subinterval
does not exceed the left end of that subinterval. -/
theorem stageTime_pred_le_gerverGridTime (m : ℕ) (hm : m + 1 ≤ 5 * NN)
    (h2 : 2 ≤ stageOf (m + 1)) :
    gerverStageTime (stageOf (m + 1) - 1) ≤ gerverGridTime m := by
  have hNN : 0 < NN := by norm_num [NN]
  rw [stageOf] at h2 ⊢
  split_ifs at h2 ⊢ with h
  · have hd : 2 ≤ (m + 1) / NN := by
      rcases le_max_iff.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hk : (m + 1) / NN * NN = m + 1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have hstep : ((m + 1) / NN - 1) * NN = m + 1 - NN := by rw [Nat.sub_one_mul, hk]
    have hle : ((m + 1) / NN - 1) * NN ≤ m := by rw [hstep]; omega
    rw [max_eq_right (Nat.le_of_succ_le hd), ← gerverGridTime_mul_NN ((m + 1) / NN - 1)]
    exact gerverGridTime_le_of_le hle (by omega)
  · rw [Nat.add_sub_cancel]
    have hle1 : (m + 1) / NN * NN ≤ m + 1 := Nat.div_mul_le_self (m + 1) NN
    have hne : (m + 1) / NN * NN ≠ m + 1 := by
      intro he
      exact h (by rw [← he]; exact Nat.mul_mod_left _ _)
    have hle : (m + 1) / NN * NN ≤ m := Nat.lt_succ_iff.mp (lt_of_le_of_ne hle1 hne)
    rw [← gerverGridTime_mul_NN ((m + 1) / NN)]
    exact gerverGridTime_le_of_le hle (by omega)

/-- The evaluator at a grid angle. -/
theorem contactZ_sound (m : ℕ) (hm : m ≤ 5 * NN) (kind : ℕ) (hk : kind ≤ 4) :
    SI.Contains (contactZ m kind).1 (gerverContactPoint kind (gerverGridTime m) 0) ∧
      SI.Contains (contactZ m kind).2 (gerverContactPoint kind (gerverGridTime m) 1) := by
  obtain ⟨h1, h5⟩ := stageOf_mem m hm
  obtain ⟨hg0, hgT⟩ := gerverGridTime_mem_Icc m hm
  exact evalZ_sound (stageOf m) h1 h5 (ttZ_sound m hm) hg0 hgT
    (gerverGridTime_le_stageTime m hm) (fun h ↦ stageTime_lt_gerverGridTime m hm h) kind hk

/-- The evaluator over a whole grid subinterval, on the branch selected at its right
endpoint (which is the branch of every angle in the half-open subinterval). -/
theorem evalZ_interval_sound (m : ℕ) (hm : m + 1 ≤ 5 * NN) (kind : ℕ) (hk : kind ≤ 4)
    {x : ℝ} (hx : x ∈ Set.Ioc (gerverGridTime m) (gerverGridTime (m + 1))) :
    SI.Contains (evalZ (stageOf (m + 1))
        ⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ kind).1 (gerverContactPoint kind x 0) ∧
      SI.Contains (evalZ (stageOf (m + 1))
        ⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ kind).2 (gerverContactPoint kind x 1) := by
  have hmm : m ≤ 5 * NN := by omega
  obtain ⟨hxl, hxr⟩ := hx
  obtain ⟨h1, h5⟩ := stageOf_mem (m + 1) hm
  obtain ⟨hg0, -⟩ := gerverGridTime_mem_Icc m hmm
  obtain ⟨-, hgT⟩ := gerverGridTime_mem_Icc (m + 1) hm
  have hM := SI.Mpos
  have hz : SI.Contains (⟨(ttZ m).lo, (ttZ (m + 1)).hi⟩ : SI) x := by
    obtain ⟨ha, -⟩ := ttZ_sound m hmm
    obtain ⟨-, hb⟩ := ttZ_sound (m + 1) hm
    exact ⟨ha.trans (mul_le_mul_of_nonneg_left hxl.le hM.le),
      (mul_le_mul_of_nonneg_left hxr hM.le).trans hb⟩
  refine evalZ_sound (stageOf (m + 1)) h1 h5 hz (hg0.trans hxl.le) (hxr.trans hgT)
    (hxr.trans (gerverGridTime_le_stageTime (m + 1) hm)) (fun h2 ↦ ?_) kind hk
  exact lt_of_le_of_lt (stageTime_pred_le_gerverGridTime m hm h2) hxl

end MovingSofa
