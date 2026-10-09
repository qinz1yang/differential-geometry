import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDecay

/-!
S-CH11-FIX6 port（astra `History/PreparedSpatialLargerBallAccuracy` 的 elaboration 修补；陈述 / 定义 /
证明逐字不变）：两处 `diagonal_delta_antitone S … (le_max_left _ _)`（期望 `max 0 x ∈ Ici 0`，
`le_max_left` 不能穿过 `Set.Ici` 的 `Membership` 统一）→ `(Set.mem_Ici.mpr (le_max_left _ _))`。
-/

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace GC.GeneralFlow.PreparedSpatialChain
universe u

open private state_delta_compat diagonal_delta_antitone from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.PreparedSpatialDecay

/-- The same diagonal agrees with any full state that already covers the time.
A common later state avoids comparing the observation index with the block index. -/
private theorem diagonal_delta_eq_state
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (n : ℕ) (s : ℝ)
    (hs : s ≤ preparedSpatialHorizon n) :
    (CutoffParameters.diagonal (fun k => (S.observation k).parameters)).delta s =
      (S.state n).parameters.delta s := by
  change (S.state (Nat.ceil s + 1)).parameters.delta s =
    (S.state n).parameters.delta s
  have hceil : s ≤ preparedSpatialHorizon (Nat.ceil s + 1) :=
    (Nat.le_ceil s).trans (nat_lt_three_pow (Nat.ceil s)).le
  exact (state_delta_compat S (Nat.ceil s + 1) (max n (Nat.ceil s + 1))
    (le_max_right _ _) s hceil).symm.trans
      (state_delta_compat S n (max n (Nat.ceil s + 1)) (le_max_left _ _) s hs)

/-- A numerical cutoff for the same actual observation diagonal. -/
def diagonalLargerBallAccuracy
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (A _t : ℝ) : ℝ :=
  2 * (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
    (max 0 (A / 4))

/-- The actual selected accuracy on the left-open, right-closed geometric block. -/
theorem diagonal_delta_eq_accuracy_on_block
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g) (n : ℕ) (s : ℝ)
    (hs : preparedSpatialHorizon n < s) (hsB : s ≤ (3 : ℝ) ^ n) :
    (CutoffParameters.diagonal (fun k => (S.observation k).parameters)).delta s =
      S.accuracy n := by
  rw [diagonal_delta_eq_state S (n + 1) s hsB]
  exact (S.successor n).delta_after s hs

/-- One geometric delay pays the quarter drop, including zero and block endpoints. -/
theorem diagonal_delta_quarter_lag
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hdrop : ∀ n : ℕ, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (s : ℝ) (hs : 0 ≤ s) :
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
        (3 * max 1 s) ≤
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta s / 4 := by
  let q := CutoffParameters.diagonal (fun k => (S.observation k).parameters)
  change q.delta (3 * max 1 s) ≤ q.delta s / 4
  have hex : ∃ n : ℕ, s ≤ (3 : ℝ) ^ n :=
    ⟨Nat.ceil s, (Nat.le_ceil s).trans (nat_lt_three_pow (Nat.ceil s)).le⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, s ≤ (3 : ℝ) ^ n ∧
      ∀ m : ℕ, m < n → ¬ s ≤ (3 : ℝ) ^ m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  cases n with
  | zero =>
    have hs1 : s ≤ 1 := by simpa only [pow_zero] using hn
    have hthree : q.delta 3 = S.accuracy 1 := by
      exact diagonal_delta_eq_accuracy_on_block S 1 3 (by norm_num [preparedSpatialHorizon])
        (by norm_num)
    have hone : (S.state 1).parameters.delta 1 = q.delta 1 :=
      (diagonal_delta_eq_state S 1 1 (by norm_num [preparedSpatialHorizon])).symm
    have hdrop1 : S.accuracy 1 ≤ q.delta 1 / 4 := by
      simpa only [preparedSpatialHorizon, pow_zero, hone] using hdrop 1
    have hanti : q.delta 1 ≤ q.delta s := diagonal_delta_antitone S hs (by norm_num) hs1
    rw [max_eq_left hs1, mul_one, hthree]
    linarith
  | succ n =>
    have hsLower : (3 : ℝ) ^ n < s := lt_of_not_ge (hmin n (Nat.lt_succ_self n))
    have hs1 : 1 ≤ s := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)).trans hsLower.le
    have hafter : preparedSpatialHorizon (n + 2) < 3 * s := by
      change (3 : ℝ) ^ (n + 1) < 3 * s
      rw [pow_succ]
      nlinarith
    have hupper : 3 * s ≤ (3 : ℝ) ^ (n + 2) := by
      change 3 * s ≤ (3 : ℝ) ^ ((n + 1) + 1)
      rw [pow_succ]
      nlinarith
    have htarget : q.delta (3 * s) = S.accuracy (n + 2) :=
      diagonal_delta_eq_accuracy_on_block S (n + 2) (3 * s) hafter hupper
    have hsource : q.delta s = S.accuracy (n + 1) :=
      diagonal_delta_eq_accuracy_on_block S (n + 1) s hsLower hn
    have hcheckpoint :
        (S.state (n + 2)).parameters.delta ((3 : ℝ) ^ (n + 1)) =
          S.accuracy (n + 1) := by
      apply (S.successor (n + 1)).delta_after
      change (3 : ℝ) ^ n < (3 : ℝ) ^ (n + 1)
      rw [pow_succ]
      have hp : (0 : ℝ) < 3 ^ n := pow_pos (by norm_num) n
      nlinarith
    have hstep : S.accuracy (n + 2) ≤ S.accuracy (n + 1) / 4 := by
      simpa only [preparedSpatialHorizon, hcheckpoint] using hdrop (n + 2)
    rw [max_eq_right hs1, htarget, hsource]
    exact hstep

/-- Positivity, both monotonicities, the strict diagonal and the numerical eligibility bound. -/
theorem diagonalLargerBallAccuracy_spec
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hdrop : ∀ n : ℕ, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4) :
    (∀ A t : ℝ, 0 < A → 0 ≤ t → 0 < S.diagonalLargerBallAccuracy A t) ∧
    (∀ A : ℝ, 0 < A → AntitoneOn (S.diagonalLargerBallAccuracy A) (Ici 0)) ∧
    (∀ t : ℝ, 0 ≤ t →
      AntitoneOn (fun A => S.diagonalLargerBallAccuracy A t) (Ioi 0)) ∧
    (∀ t : ℝ, 0 < t →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta t <
        S.diagonalLargerBallAccuracy (2 * t) (2 * t)) ∧
    ∀ A s : ℝ, 0 < A → 0 ≤ s →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta s <
        S.diagonalLargerBallAccuracy A s → A < 12 * max 1 s := by
  let q := CutoffParameters.diagonal (fun n => (S.observation n).parameters)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A _ _ _
    exact mul_pos (by norm_num) (q.delta_pos _ (le_max_left _ _))
  · intro _ _ _ _ _ _ _
    exact le_rfl
  · intro _ _ A _ B _ hAB
    change 2 * q.delta (max 0 (B / 4)) ≤ 2 * q.delta (max 0 (A / 4))
    have harg : max 0 (A / 4) ≤ max 0 (B / 4) :=
      max_le_max le_rfl (by linarith)
    exact mul_le_mul_of_nonneg_left
      (diagonal_delta_antitone S (Set.mem_Ici.mpr (le_max_left _ _))
        (Set.mem_Ici.mpr (le_max_left _ _)) harg)
      (by norm_num)
  · intro t ht
    change q.delta t < 2 * q.delta (max 0 ((2 * t) / 4))
    have harg : max 0 ((2 * t) / 4) ≤ t := max_le ht.le (by linarith)
    have hanti := diagonal_delta_antitone S (le_max_left 0 ((2 * t) / 4)) ht.le harg
    have hpos := q.delta_pos (max 0 ((2 * t) / 4)) (le_max_left _ _)
    linarith
  · intro A s _ hs hsmall
    change q.delta s < 2 * q.delta (max 0 (A / 4)) at hsmall
    by_contra hA
    have hlarge : 12 * max 1 s ≤ A := le_of_not_gt hA
    have harg : 3 * max 1 s ≤ max 0 (A / 4) := by
      have hmax := le_max_right 0 (A / 4)
      linarith
    have hnonneg : 0 ≤ 3 * max 1 s := by
      have hm : (0 : ℝ) ≤ max 1 s := le_trans (by norm_num) (le_max_left _ _)
      positivity
    have hanti := diagonal_delta_antitone S hnonneg (Set.mem_Ici.mpr (le_max_left _ _)) harg
    have hlag := diagonal_delta_quarter_lag S hdrop s hs
    have hpos := q.delta_pos s hs
    change q.delta (3 * max 1 s) ≤ q.delta s / 4 at hlag
    linarith

/-- Eligibility at a birth in this block bounds its requested numerical radius factor. -/
theorem diagonalLargerBallAccuracy_birth_block_bound
    {pBase : CutoffParameters} {C : ClosedBirthConstants}
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    (S : PreparedSpatialChain pBase C P g)
    (hdrop : ∀ n : ℕ, S.accuracy n ≤
      (S.state n).parameters.delta (preparedSpatialHorizon n) / 4)
    (m : ℕ) (A s : ℝ) (hA : 0 < A) (hs : 0 ≤ s) (hsB : s ≤ (3 : ℝ) ^ m)
    (hsmall :
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta s <
        S.diagonalLargerBallAccuracy A s) :
    A < 12 * (3 : ℝ) ^ m := by
  have hAblock := (diagonalLargerBallAccuracy_spec S hdrop).2.2.2.2 A s hA hs hsmall
  have hmax : max 1 s ≤ (3 : ℝ) ^ m :=
    max_le (one_le_pow₀ (by norm_num)) hsB
  exact hAblock.trans_le (mul_le_mul_of_nonneg_left hmax (by norm_num))

end GC.GeneralFlow.PreparedSpatialChain
