import MovingSofa.Cap.Basic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

open Filter
open scoped Topology

namespace MovingSofa

/-- The interior points of the uniform angular grid. -/
def uniformAngleSet (ω : ℝ) (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2)
    (n : ℕ) (hn : 2 ≤ n) : AngleSet where
  angle := ω
  angle_pos := hω
  angle_le := hω'
  directions := (Finset.Ioo 0 n).image (fun i : ℕ ↦ (i : ℝ) / n * ω)
  nonempty := by
    apply Finset.Nonempty.image
    exact ⟨1, by simp; omega⟩
  interior := by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hi, hin⟩ := Finset.mem_Ioo.mp hi
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hi' : (0 : ℝ) < i := by exact_mod_cast hi
    have hin' : (i : ℝ) < n := by exact_mod_cast hin
    refine ⟨mul_pos (div_pos hi' hn') hω, ?_⟩
    exact (mul_lt_mul_of_pos_right ((div_lt_one hn').2 hin') hω).trans_eq (one_mul ω)

/-- A divisible grid refines the original grid. -/
theorem uniformAngleSet_directions_mono_of_dvd (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hmn : m ∣ n) :
    (uniformAngleSet ω hω hω' m hm).directions ⊆
      (uniformAngleSet ω hω hω' n hn).directions := by
  obtain ⟨k, rfl⟩ := hmn
  intro t ht
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨hj0, hjm⟩ := Finset.mem_Ioo.mp hj
  have hk : 0 < k := by nlinarith
  apply Finset.mem_image.mpr
  refine ⟨j * k, Finset.mem_Ioo.mpr ⟨Nat.mul_pos hj0 hk,
    Nat.mul_lt_mul_of_pos_right hjm hk⟩, ?_⟩
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  rw [mul_div_mul_right _ _ hk']

/-- Monotone dyadic grids have nested directions. -/
theorem uniformAngleSet_directions_mono_of_dyadic (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : Monotone n) (hdyadic : ∀ i, ∃ k : ℕ, n i = 2 ^ k)
    {i j : ℕ} (hij : i ≤ j) :
    (uniformAngleSet ω hω hω' (n i) (hn i)).directions ⊆
      (uniformAngleSet ω hω hω' (n j) (hn j)).directions := by
  apply uniformAngleSet_directions_mono_of_dvd
  obtain ⟨a, ha⟩ := hdyadic i
  obtain ⟨b, hb⟩ := hdyadic j
  have hab : a ≤ b := by
    apply (pow_le_pow_iff_right₀ (by norm_num : 1 < (2 : ℕ))).mp
    simpa only [← ha, ← hb] using hmono hij
  rw [ha, hb]
  exact pow_dvd_pow 2 hab

/-- An interval longer than the mesh contains a grid direction. -/
theorem exists_uniformAngleSet_mem_Ioo (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ) (hn : 2 ≤ n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ ω) (hmesh : ω / n < b - a) :
    ∃ t ∈ (uniformAngleSet ω hω hω' n hn).directions, t ∈ Set.Ioo a b := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let j := ⌊a * n / ω⌋₊ + 1
  have hjpos : 0 < j := by dsimp [j]; omega
  have hfloor := Nat.floor_le (show 0 ≤ a * n / ω by positivity)
  have hfloor' := Nat.lt_floor_add_one (a * n / ω)
  have hjlo : a < (j : ℝ) / n * ω := by
    have h : a * n < (j : ℝ) * ω := by
      apply (div_lt_iff₀ hω).mp
      simpa only [j, Nat.cast_add, Nat.cast_one] using hfloor'
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hnpos).mpr h
  have hjhi : (j : ℝ) / n * ω ≤ a + ω / n := by
    have h : ((j : ℝ) - 1) * ω ≤ a * n := by
      apply (le_div_iff₀ hω).mp
      simpa only [j, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hfloor
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hnpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hnpos.ne']
    nlinarith
  have hjb : (j : ℝ) / n * ω < b := hjhi.trans_lt (by linarith)
  have hjn : j < n := by
    have h : (j : ℝ) / n < 1 := (mul_lt_mul_iff_left₀ hω).mp (by simpa using hjb.trans_le hb)
    exact_mod_cast (div_lt_one hnpos).mp h
  refine ⟨(j : ℝ) / n * ω, Finset.mem_image.mpr ⟨j, Finset.mem_Ioo.mpr ⟨hjpos, hjn⟩, rfl⟩,
    hjlo, hjb⟩

/-- An increasing sequence of grids eventually meets each interior open interval. -/
theorem eventually_exists_uniformAngleSet_mem_Ioo (ω : ℝ) (hω : 0 < ω)
    (hω' : ω ≤ Real.pi / 2) (n : ℕ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hmono : StrictMono n) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ ω) :
    ∀ᶠ i in atTop, ∃ t ∈ (uniformAngleSet ω hω hω' (n i) (hn i)).directions,
      t ∈ Set.Ioo a b := by
  have hlim : Tendsto (fun i ↦ ω / (n i : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ω).comp hmono.tendsto_atTop
  filter_upwards [hlim.eventually_lt_const (sub_pos.mpr hab)] with i hi
  exact exists_uniformAngleSet_mem_Ioo ω hω hω' (n i) (hn i) ha hb hi


end MovingSofa
