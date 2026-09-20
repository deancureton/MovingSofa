import GerverSofa.KernelOnly.LeanCertNoDetKrawczyk

/-!
# LeanCert Gerver numerical core

Only shared definitions and lightweight list lemmas live here.
The expensive 22D kernel checks are split into one Lake module per row.
-/

noncomputable section

namespace GerverSofa
namespace PartALeanCert

open LeanCert.Core
open LeanCert.Engine

def cfg : EvalConfig := {}

def reducedPJ : Matrix (Fin 4) (Fin 4) IntervalRat :=
  preconditionedJacobian reducedY
    (intervalJacobian reducedExpr (unitBox (n := 4)) cfg)

def fullPJ : Matrix (Fin 22) (Fin 22) IntervalRat :=
  preconditionedJacobian fullY
    (intervalJacobian fullExpr (unitBox (n := 22)) cfg)

theorem qTarget_pos : (0 : ℚ) < qTarget := by norm_num [qTarget]
theorem qTarget_nonneg : (0 : ℚ) ≤ qTarget := qTarget_pos.le
theorem qTarget_lt_one : qTarget < (1 : ℚ) := by norm_num [qTarget]

/-- Assemble a bound from independently kernel-checked rows without re-running AD. -/
theorem foldl_max_lt {xs : List ℚ} {a q : ℚ}
    (ha : a < q) (hxs : ∀ x ∈ xs, x < q) :
    xs.foldl max a < q := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons x xs ih =>
      simp only [List.foldl_cons]
      apply ih
      · exact max_lt ha (hxs x (by simp))
      · intro y hy
        exact hxs y (by simp [hy])

theorem matrixBound_lt_of_rows {n : Nat}
    (A : Matrix (Fin n) (Fin n) IntervalRat) (q : ℚ)
    (hq0 : 0 < q)
    (hrows : ∀ i : Fin n, intervalMatrixRowBound A i < q) :
    intervalMatrixBound A < q := by
  unfold intervalMatrixBound
  apply foldl_max_lt hq0
  intro x hx
  rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
  exact hrows i

/-! ## Proof-carrying cache for the 22 Newton-center residuals

These deliberately simple rational intervals are much wider than the actual
point residuals, but still narrow enough after the scaled preconditioner to
leave a large self-map margin.  Each coordinate is checked independently in a
separate module before it is used by the final contraction theorem.
-/
def fullPointCacheList : List IntervalRat := [
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 0 1, q 3 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 0 1, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 1 100000000000000000000000000000, q 1 25000000000000000000000000000, by norm_num [q]⟩,
  ⟨q 0 1, q 3 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 1 50000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 50000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 25000000000000000000000, q 1 20000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 20000000000000000000000, q 1 25000000000000000000000, by norm_num [q]⟩,
  ⟨q (-1) 100000000000000000000000000000, q 3 100000000000000000000000000000, by norm_num [q]⟩,
  ⟨q (-3) 100000000000000000000000000000, q 1 100000000000000000000000000000, by norm_num [q]⟩
]

def fullPointCache (i : Fin 22) : IntervalRat :=
  fullPointCacheList.getD i.1 (IntervalRat.singleton 0)

def fullImageCachedQ (i : Fin 22) : IntervalRat :=
  imageEnclosureWithValuesQ (unitBox (n := 22)) (zeroCenter (n := 22))
    fullY fullPointCache qTarget i

def reducedImageQ (i : Fin 4) : IntervalRat :=
  imageEnclosureWithQ reducedExpr (unitBox (n := 4))
    (zeroCenter (n := 4)) reducedY cfg qTarget i

theorem reduced_center_mem :
    FinBoxMem (fun i : Fin 4 => ((zeroCenter (n := 4) i : ℚ) : ℝ))
      (unitBox (n := 4)) := by
  intro i
  simp [zeroCenter, unitBox, IntervalRat.mem_def]

theorem full_center_mem :
    FinBoxMem (fun i : Fin 22 => ((zeroCenter (n := 22) i : ℚ) : ℝ))
      (unitBox (n := 22)) := by
  intro i
  simp [zeroCenter, unitBox, IntervalRat.mem_def]

end PartALeanCert
end GerverSofa
