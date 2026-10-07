import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingTheta_CX5

set_option autoImplicit false

/-! # CH12-S61 G2a: the diagonal choice of `α` for `singleModel_S61`

Given thresholds `J m` (for every accuracy level `m`, all dyadic windows `j ≥ J m` satisfy the
predicate `P m j`), there is a positive, eventually antitone `α` tending to 0, with `α t = 1/m` and
`P m (dyadicIndex T t)` for every `t ≥ start`.  (`P m j` will be: `η_j ≤ δ_m`, `ν_j ≥ max K m`,
`ρ_j ≥ R_m`, `4 B η_j < 1/m`.) -/

noncomputable section
open Set Filter Topology

namespace GC.LongTime.Ch12

theorem dyadicIndex_mono_S61 {T : ℝ} (hT : 0 < T) {s t : ℝ} (hs : T ≤ s) (hst : s ≤ t) :
    dyadicIndex_CX5 T s ≤ dyadicIndex_CX5 T t :=
  le_dyadicIndex_CX5 hT _ ((dyadicIndex_mem_CX5 hT hs).1.trans hst)

theorem exists_diagonal_alpha_S61 {T : ℝ} (hT : 0 < T) (P : ℕ → ℕ → Prop)
    (hP : ∀ m : ℕ, ∃ J : ℕ, ∀ j, J ≤ j → P m j) :
    ∃ (start : ℝ) (α : ℝ → ℝ), T ≤ start ∧ (∀ t, 0 < α t) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T' : ℝ, ∀ t, T' ≤ t → α t < ε) ∧
      ∀ t, start ≤ t → ∃ m : ℕ, 1 ≤ m ∧ α t = 1 / (m : ℝ) ∧ P m (dyadicIndex_CX5 T t) := by
  classical
  choose J hJ using hP
  let J' : ℕ → ℕ := fun m => m + (Finset.range (m + 1)).sup J
  have hJJ : ∀ m, J m ≤ J' m := fun m =>
    (Finset.le_sup (f := J) (Finset.self_mem_range_succ m)).trans (Nat.le_add_left _ _)
  have hJm : ∀ m, m ≤ J' m := fun m => Nat.le_add_right _ _
  let M : ℕ → ℕ := fun n => Nat.findGreatest (fun m => J' m ≤ n) n
  let α : ℝ → ℝ := fun t => 1 / ((max 1 (M (dyadicIndex_CX5 T t)) : ℕ) : ℝ)
  have hMge : ∀ (m n : ℕ), J' m ≤ n → m ≤ M n := fun m n h =>
    Nat.le_findGreatest ((hJm m).trans h) h
  have hMspec : ∀ n, 1 ≤ M n → J' (M n) ≤ n := fun n h =>
    Nat.findGreatest_of_ne_zero (P := fun m => J' m ≤ n) rfl (by omega)
  have hMmono : ∀ n n', n ≤ n' → M n ≤ M n' := fun n n' h =>
    Nat.findGreatest_mono (P := fun m => J' m ≤ n) (Q := fun m => J' m ≤ n')
      (fun m hm => hm.trans h) h
  have hstart_idx : ∀ t, dyadicTime_CX5 T (J' 1) ≤ t → J' 1 ≤ dyadicIndex_CX5 T t :=
    fun t ht => le_dyadicIndex_CX5 hT _ ht
  have hT_le : T ≤ dyadicTime_CX5 T (J' 1) := by
    simpa using (dyadicTime_strictMono_CX5 hT).monotone (Nat.zero_le (J' 1))
  have hM1 : ∀ t, dyadicTime_CX5 T (J' 1) ≤ t → 1 ≤ M (dyadicIndex_CX5 T t) := fun t ht =>
    hMge 1 _ (hstart_idx t ht)
  refine ⟨dyadicTime_CX5 T (J' 1), α, hT_le, fun t => ?_, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < ((max 1 (M (dyadicIndex_CX5 T t)) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_pos (le_max_left _ _)
    exact one_div_pos.2 this
  · intro s hs t ht hst
    have hs' : T ≤ s := hT_le.trans hs
    have hM : max 1 (M (dyadicIndex_CX5 T s)) ≤ max 1 (M (dyadicIndex_CX5 T t)) :=
      max_le_max le_rfl (hMmono _ _ (dyadicIndex_mono_S61 hT hs' hst))
    have hpos : (0 : ℝ) < ((max 1 (M (dyadicIndex_CX5 T s)) : ℕ) : ℝ) := by
      exact_mod_cast lt_of_lt_of_le one_pos (le_max_left _ _)
    exact one_div_le_one_div_of_le hpos (by exact_mod_cast hM)
  · intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨dyadicTime_CX5 T (J' (N + 1)), fun t ht => ?_⟩
    have hN1 : N + 1 ≤ M (dyadicIndex_CX5 T t) := hMge _ _ (le_dyadicIndex_CX5 hT _ ht)
    have hpos : (0 : ℝ) < ((N : ℝ) + 1) := by positivity
    refine lt_of_le_of_lt ?_ hN
    have : ((N + 1 : ℕ) : ℝ) ≤ ((max 1 (M (dyadicIndex_CX5 T t)) : ℕ) : ℝ) := by
      exact_mod_cast hN1.trans (le_max_right _ _)
    exact one_div_le_one_div_of_le (by exact_mod_cast hpos) (by simpa using this)
  · intro t ht
    have h1 := hM1 t ht
    refine ⟨M (dyadicIndex_CX5 T t), h1, ?_, hJ _ _ ((hJJ _).trans (hMspec _ h1))⟩
    simp only [α, max_eq_right h1]

end GC.LongTime.Ch12
