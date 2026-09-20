import MovingSofa.Gerver.AreaCertificate
import MovingSofa.Gerver.StageRegularity

/-!
# Stage endpoints, grid angles and branch selection

The certificate subdivides each of the five analytic stages of Gerver's sofa into
`NN = 64` equal parts.  This module carries the real-valued mirror of that grid:
`gerverStageTime` re-indexes the six stage endpoints by a natural number,
`gerverGridTime m` is the `m`-th grid angle, `gerverContactPoint` is the dictionary of the
four contact curves and the ambient path, and `GerverAreaCert.stageOf m` is the analytic
branch that the piecewise definitions select at the `m`-th angle.  The soundness statements
`endZ_sound` and `ttZ_sound` say that the integer data of the certificate encloses these
real quantities; the remaining lemmas are the order facts the evaluator needs.
-/

noncomputable section

namespace MovingSofa

open GerverAreaCert

/-- The six stage endpoints indexed by a natural number, constant past `5`. -/
def gerverStageTime (s : ℕ) : ℝ := gerverStageTimes ⟨min 5 s, by omega⟩

/-- The real grid angle at index `m`, mirroring `GerverAreaCert.ttZ`. -/
def gerverGridTime (m : ℕ) : ℝ :=
  (((NN - m % NN : ℕ) : ℝ) * gerverStageTime (m / NN) +
    ((m % NN : ℕ) : ℝ) * gerverStageTime (m / NN + 1)) / (NN : ℝ)

/-- The curve selected by a certificate `kind`: `0` the path, `1` `A`, `2` `B`, `3` `C`,
`4` `D`. -/
def gerverContactPoint : ℕ → ℝ → Point
  | 0 => paperGerverPath
  | 1 => fun t ↦ paperGerverContacts t 0
  | 2 => fun t ↦ paperGerverContacts t 1
  | 3 => fun t ↦ paperGerverContacts t 2
  | _ => fun t ↦ paperGerverContacts t 3

/-- The rotation interval starts at the first stage endpoint `0`. -/
theorem gerverStageTime_zero : gerverStageTime 0 = 0 := gerverStageTimes_zero

/-- The first stage ends at `φ`. -/
theorem gerverStageTime_one : gerverStageTime 1 = GerverSofa.PartB.params.phi :=
  gerverStageTimes_one

/-- The second stage ends at `θ`. -/
theorem gerverStageTime_two : gerverStageTime 2 = GerverSofa.PartB.params.theta :=
  gerverStageTimes_two

/-- The third stage ends at `η = π / 2 - θ`. -/
theorem gerverStageTime_three : gerverStageTime 3 = GerverSofa.PartC.eta :=
  gerverStageTimes_three

/-- The fourth stage ends at `τ = π / 2 - φ`. -/
theorem gerverStageTime_four : gerverStageTime 4 = GerverSofa.PartC.tau :=
  gerverStageTimes_four

/-- The fifth stage ends at `π / 2`. -/
theorem gerverStageTime_five : gerverStageTime 5 = Real.pi / 2 := gerverStageTimes_five

/-! ### Order properties of the stage endpoints and the grid -/

/-- The five stage endpoints are strictly increasing. -/
theorem gerverStageTime_lt_succ (s : ℕ) (hs : s < 5) :
    gerverStageTime s < gerverStageTime (s + 1) := by
  refine gerverStageTimes_strictMono ?_
  simp only [Fin.mk_lt_mk]
  omega

/-- Past index `5` the `ℕ`-indexed stage endpoint is constantly `π / 2`. -/
private theorem gerverStageTime_of_five_le {s : ℕ} (hs : 5 ≤ s) :
    gerverStageTime s = Real.pi / 2 := by
  simp only [gerverStageTime, min_eq_left hs]
  exact gerverStageTimes_five

/-- The stage-endpoint enclosure at every index, including those past `5`. -/
private theorem endZ_sound_all (s : ℕ) : SI.Contains (endZ s) (gerverStageTime s) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hphi, htheta⟩ :=
    contains_params
  rcases s with _ | _ | _ | _ | _ | _ | n
  · rw [gerverStageTime_zero]
    exact SI.contains_zero
  · rw [gerverStageTime_one]
    exact hphi
  · rw [gerverStageTime_two]
    exact htheta
  · rw [show gerverStageTime 3 = Real.pi / 2 - GerverSofa.PartB.params.theta from
      gerverStageTime_three]
    exact SI.contains_sub contains_piHalfZ htheta
  · rw [show gerverStageTime 4 = Real.pi / 2 - GerverSofa.PartB.params.phi from
      gerverStageTime_four]
    exact SI.contains_sub contains_piHalfZ hphi
  · rw [gerverStageTime_five]
    exact contains_piHalfZ
  · rw [gerverStageTime_of_five_le (s := n + 6) (by omega)]
    exact contains_piHalfZ

/-- The integer stage endpoints enclose the real ones. -/
theorem endZ_sound (s : ℕ) (hs : s ≤ 5) : SI.Contains (endZ s) (gerverStageTime s) := by
  interval_cases s <;> exact endZ_sound_all _

/-- The integer grid angles enclose the real ones. -/
theorem ttZ_sound (m : ℕ) (hm : m ≤ 5 * NN) : SI.Contains (ttZ m) (gerverGridTime m) := by
  have hNN : (0 : ℤ) < (NN : ℤ) := by norm_num [NN]
  have hdiv : m / NN ≤ 5 := by
    rw [show NN = 64 from rfl] at hm ⊢
    omega
  have key : SI.Contains
      (SI.add (SI.imul ((NN - m % NN : ℕ) : ℤ) (endZ (m / NN)))
        (SI.imul ((m % NN : ℕ) : ℤ) (endZ (m / NN + 1))))
      (((NN - m % NN : ℕ) : ℝ) * gerverStageTime (m / NN) +
        ((m % NN : ℕ) : ℝ) * gerverStageTime (m / NN + 1)) := by
    refine SI.contains_add ?_ ?_
    · have h := SI.contains_imul ((NN - m % NN : ℕ) : ℤ) (endZ_sound (m / NN) hdiv)
      rwa [Int.cast_natCast] at h
    · have h := SI.contains_imul ((m % NN : ℕ) : ℤ) (endZ_sound_all (m / NN + 1))
      rwa [Int.cast_natCast] at h
  have hcast : (((NN : ℤ)) : ℝ) = (NN : ℝ) := by push_cast; ring
  rw [gerverGridTime, ← hcast]
  exact SI.contains_divn hNN key

/-- The grid step is uniform across stage joins. -/
theorem gerverGridTime_succ_sub (m : ℕ) :
    gerverGridTime (m + 1) - gerverGridTime m =
      (gerverStageTime (m / NN + 1) - gerverStageTime (m / NN)) / (NN : ℝ) := by
  have hNNR : (0 : ℝ) < (NN : ℝ) := by norm_num [NN]
  have hr : m % NN < NN := Nat.mod_lt _ (by norm_num [NN])
  have hsplit : ((m + 1) % NN = m % NN + 1 ∧ (m + 1) / NN = m / NN) ∨
      (m % NN + 1 = NN ∧ (m + 1) % NN = 0 ∧ (m + 1) / NN = m / NN + 1) := by
    rw [show NN = 64 from rfl]
    omega
  rcases hsplit with ⟨hmod, hdiv⟩ | ⟨hfull, hmod, hdiv⟩
  · rw [gerverGridTime, gerverGridTime, hmod, hdiv,
      Nat.cast_sub (by omega : m % NN + 1 ≤ NN), Nat.cast_sub hr.le]
    push_cast
    field_simp
    ring
  · rw [gerverGridTime, gerverGridTime, hmod, hdiv, Nat.cast_sub hr.le]
    have hrR : ((m % NN : ℕ) : ℝ) = (NN : ℝ) - 1 := by
      have : ((m % NN + 1 : ℕ) : ℝ) = ((NN : ℕ) : ℝ) := by rw [hfull]
      push_cast at this
      linarith
    rw [hrR]
    simp only [Nat.sub_zero]
    push_cast
    field_simp
    ring

/-- The grid angles are strictly increasing. -/
theorem gerverGridTime_lt_succ (m : ℕ) (hm : m < 5 * NN) :
    gerverGridTime m < gerverGridTime (m + 1) := by
  have hNNR : (0 : ℝ) < (NN : ℝ) := by norm_num [NN]
  have hlt : m / NN < 5 := (Nat.div_lt_iff_lt_mul (by norm_num [NN])).mpr hm
  have hstep := gerverGridTime_succ_sub m
  have hstage := gerverStageTime_lt_succ (m / NN) hlt
  have hpos : 0 < (gerverStageTime (m / NN + 1) - gerverStageTime (m / NN)) / (NN : ℝ) :=
    div_pos (by linarith) hNNR
  linarith

/-- Strict monotonicity of the grid angles below the top index, from `gerverGridTime_lt_succ`. -/
theorem gerverGridTime_lt_of_lt {m n : ℕ} (hmn : m < n) (hn : n ≤ 5 * NN) :
    gerverGridTime m < gerverGridTime n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hmn with h | h
    · exact (ih h (by omega)).trans (gerverGridTime_lt_succ n (by omega))
    · subst h
      exact gerverGridTime_lt_succ m (by omega)

/-- Weak monotonicity of the grid angles below the top index, from `gerverGridTime_lt_succ`. -/
theorem gerverGridTime_le_of_le {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ 5 * NN) :
    gerverGridTime m ≤ gerverGridTime n := by
  rcases eq_or_lt_of_le hmn with rfl | h
  · exact le_rfl
  · exact (gerverGridTime_lt_of_lt h hn).le

/-- The grid angle at a stage boundary is the stage endpoint itself. -/
theorem gerverGridTime_mul_NN (s : ℕ) : gerverGridTime (s * NN) = gerverStageTime s := by
  have hNN : 0 < NN := by norm_num [NN]
  have hne : (NN : ℝ) ≠ 0 := by norm_num [NN]
  rw [gerverGridTime, Nat.mul_mod_left, Nat.mul_div_cancel _ hNN]
  simp only [Nat.sub_zero, Nat.cast_zero, zero_mul, add_zero]
  exact mul_div_cancel_left₀ _ hne

/-- The grid starts at `0`. -/
theorem gerverGridTime_zero : gerverGridTime 0 = 0 := by
  have h := gerverGridTime_mul_NN 0
  rw [zero_mul] at h
  rw [h, gerverStageTime_zero]

/-- The grid ends at `π / 2`. -/
theorem gerverGridTime_top : gerverGridTime (5 * NN) = Real.pi / 2 := by
  rw [gerverGridTime_mul_NN 5, gerverStageTime_five]

/-- Every grid angle lies in the rotation interval. -/
theorem gerverGridTime_mem_Icc (m : ℕ) (hm : m ≤ 5 * NN) :
    gerverGridTime m ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := by
  refine ⟨?_, ?_⟩
  · rw [← gerverGridTime_zero]
    exact gerverGridTime_le_of_le (Nat.zero_le m) hm
  · rw [← gerverGridTime_top]
    exact gerverGridTime_le_of_le hm le_rfl

/-- The branch index is one of the five stages. -/
theorem stageOf_mem (m : ℕ) (hm : m ≤ 5 * NN) : 1 ≤ stageOf m ∧ stageOf m ≤ 5 := by
  have hNN : 0 < NN := by norm_num [NN]
  have hd : m / NN ≤ 5 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
  rw [stageOf]
  split_ifs with h
  · exact ⟨le_max_left _ _, max_le (by omega) hd⟩
  · have hmlt : m < 5 * NN := by
      rcases lt_or_eq_of_le hm with h' | h'
      · exact h'
      · subst h'; exact absurd (Nat.mul_mod_left 5 NN) h
    have hd4 : m / NN < 5 := (Nat.div_lt_iff_lt_mul hNN).mpr hmlt
    exact ⟨Nat.le_add_left 1 _, hd4⟩

/-- The grid angle does not exceed the right endpoint of its branch. -/
theorem gerverGridTime_le_stageTime (m : ℕ) (hm : m ≤ 5 * NN) :
    gerverGridTime m ≤ gerverStageTime (stageOf m) := by
  have hNN : 0 < NN := by norm_num [NN]
  rw [stageOf]
  split_ifs with h
  · have hmm : m / NN * NN = m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have key : gerverGridTime m = gerverStageTime (m / NN) := by
      have h' := gerverGridTime_mul_NN (m / NN)
      rwa [hmm] at h'
    rcases Nat.eq_zero_or_pos (m / NN) with h0 | h0
    · have hm0 : m = 0 := by rw [← hmm, h0, zero_mul]
      rw [h0, show max 1 0 = 1 from rfl, hm0, gerverGridTime_zero]
      have h01 := gerverStageTime_lt_succ 0 (by norm_num)
      rw [gerverStageTime_zero] at h01
      exact h01.le
    · rw [max_eq_right h0, key]
  · have hmlt : m < 5 * NN := by
      rcases lt_or_eq_of_le hm with h' | h'
      · exact h'
      · subst h'; exact absurd (Nat.mul_mod_left 5 NN) h
    have hd4 : m / NN < 5 := (Nat.div_lt_iff_lt_mul hNN).mpr hmlt
    have hlt : m < (m / NN + 1) * NN := (Nat.div_lt_iff_lt_mul hNN).mp (Nat.lt_succ_self _)
    have hub : (m / NN + 1) * NN ≤ 5 * NN := Nat.mul_le_mul_right NN hd4
    calc gerverGridTime m ≤ gerverGridTime ((m / NN + 1) * NN) :=
          gerverGridTime_le_of_le hlt.le hub
      _ = gerverStageTime (m / NN + 1) := gerverGridTime_mul_NN _

/-- The grid angle strictly exceeds the left endpoint of its branch, except on the
first branch. -/
theorem stageTime_lt_gerverGridTime (m : ℕ) (hm : m ≤ 5 * NN) (h2 : 2 ≤ stageOf m) :
    gerverStageTime (stageOf m - 1) < gerverGridTime m := by
  have hNN : 0 < NN := by norm_num [NN]
  have hd5 : m / NN ≤ 5 := Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact hm)
  rw [stageOf] at h2 ⊢
  split_ifs at h2 ⊢ with h
  · have hd : 2 ≤ m / NN := by
      rcases le_max_iff.mp h2 with h' | h'
      · exact absurd h' (by norm_num)
      · exact h'
    have hpos : 0 < m / NN := lt_of_lt_of_le (by norm_num) hd
    have hmm : m / NN * NN = m := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h)
    have key : gerverGridTime m = gerverStageTime (m / NN) := by
      have h' := gerverGridTime_mul_NN (m / NN)
      rwa [hmm] at h'
    rw [max_eq_right (Nat.le_of_succ_le hd), key]
    have h4 : m / NN - 1 < 5 := lt_of_le_of_lt (Nat.sub_le_sub_right hd5 1) (by norm_num)
    have hlt := gerverStageTime_lt_succ (m / NN - 1) h4
    rwa [Nat.sub_add_cancel hpos] at hlt
  · rw [Nat.add_sub_cancel]
    have hle : m / NN * NN ≤ m := Nat.div_mul_le_self m NN
    have hne : m / NN * NN ≠ m := by
      intro he
      exact h (by rw [← he]; exact Nat.mul_mod_left _ _)
    have key : gerverGridTime (m / NN * NN) = gerverStageTime (m / NN) := gerverGridTime_mul_NN _
    rw [← key]
    exact gerverGridTime_lt_of_lt (lt_of_le_of_ne hle hne) hm

end MovingSofa
