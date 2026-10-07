import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.RadiusAntitoneC11RA

set_option autoImplicit false

/-!
# S-CH11-REPROVE-A (G3)：S7 背书（larger-ball accuracy 的数值律）+ eligibility 界

**背书** [V 逐项对照 `SH/PreparedSpatialLargerBallAccuracy.lean`]：
* astra 的 `diagonalLargerBallAccuracy S A _t = 2 * D.delta (max 0 (A/4))`（`D` = observation
  diagonal）与 SKEL 的 `diagonalAccuracy_C11S δ A _ = 2 * δ (max 0 (A/4))` **同形**
  （`diagonalAccuracy_eq_C11RA`，`rfl`）；
* astra `diagonalLargerBallAccuracy_spec` 的前四个合取项（正性、两个 antitone、`δ t < α (2t) (2t)`）与
  `LargerBallAccuracySupply_C11S` 的四条**逐字对应**；SKEL 的 `largerBallAccuracySupply_diagonal_C11S` 只用
  δ antitone（astra 也只用 `diagonal_delta_antitone`），所以 S7 由 S1 的 antitone 一步给出
  （`largerBallAccuracy_of_chain_C11RA`）。**不需要 astra 的 `hdrop`**。

**eligibility 界**（astra spec 的第 5 个合取项，SKEL 的 S7 没有收；`PreparedSpatialQualitySurgery` 的
quality surgery 用它把 larger-ball 的 `A` 限制在 `12 · max 1 s` 之内，S8 / P6 的证明可能用到）：
* `eligibility_of_quarterLag_C11RA`：`δ` antitone 且「3 倍时间 quarter lag」`δ (3 max 1 s) ≤ δ s / 4` ⇒
  `δ s < α A s → A < 12 · max 1 s`（参数级，reference：`:111` 第 5 个合取项）；
* `chain_quarter_lag_C11RA`：3 进时钟（`0, 1, 3, 9, …`）的链上，块值 `a n` 满足 `a (n+1) ≤ a n / 4` ⇒
  quarter lag（reference：`:52 diagonal_delta_quarter_lag`；astra 的 `hdrop` 在 `n ≥ 1` 时恰为此条）；
* `chain_eligibility_C11RA`：两者合成到 tuple 的 `q`。

consumer：step 链上 S7（`stepChain_S7_C11RA`）；显式 `δ = 1/(2(t+1)²)` 的参数同时满足 eligibility 的全部前提
（`quadParameters_eligibility_C11RA`，非空真）。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter

namespace GC.LongTime.Ch11

/-! ## S7 背书 -/

/-- 对角 accuracy 与 astra `diagonalLargerBallAccuracy` 同形：`α(A, t) = 2 δ(max 0 (A/4))`。 -/
theorem diagonalAccuracy_eq_C11RA (δ : ℝ → ℝ) (A t : ℝ) :
    diagonalAccuracy_C11S δ A t = 2 * δ (max 0 (A / 4)) := rfl

/-- 链上 S7：S1 的 antitone（G1）⇒ 对角 α 满足 `LargerBallAccuracySupply_C11S`。 -/
theorem largerBallAccuracy_of_chain_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (L n).delta (Ici 0))
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, E n < t → (L (n + 1)).delta t = a n)
    (ha : ∀ n : ℕ, a n ≤ 1 / ((n : ℝ) + 2))
    (q : CutoffParameters)
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.delta t = (L (n + 1)).delta t) :
    LargerBallAccuracySupply_C11S q.delta (diagonalAccuracy_C11S q.delta) :=
  largerBallAccuracySupply_diagonal_C11S q
    (accuracyDecay_of_chain_C11RA E hElt hEge L hpast hanti a hafter ha q hq).1

/-! ## eligibility 界（参数级） -/

/-- quarter lag ⇒ eligibility：`δ s < α A s` 迫使 `A < 12 · max 1 s`
（reference：`diagonalLargerBallAccuracy_spec` 第 5 个合取项）。 -/
theorem eligibility_of_quarterLag_C11RA {δ : ℝ → ℝ} (hpos : ∀ t, 0 ≤ t → 0 < δ t)
    (hanti : AntitoneOn δ (Ici 0)) (hlag : ∀ s : ℝ, 0 ≤ s → δ (3 * max 1 s) ≤ δ s / 4)
    (A s : ℝ) (hs : 0 ≤ s) (hsmall : δ s < diagonalAccuracy_C11S δ A s) :
    A < 12 * max 1 s := by
  by_contra hcon
  have hlarge : 12 * max 1 s ≤ A := le_of_not_gt hcon
  have hm1 : 1 ≤ max 1 s := le_max_left 1 s
  have harg : 3 * max 1 s ≤ max 0 (A / 4) := by
    have hmax := le_max_right 0 (A / 4)
    linarith
  have hmono := hanti (mem_Ici.2 (by linarith : (0 : ℝ) ≤ 3 * max 1 s))
    (mem_Ici.2 (le_max_left 0 (A / 4))) harg
  have hlag' := hlag s hs
  have hpos' := hpos s hs
  change δ s < 2 * δ (max 0 (A / 4)) at hsmall
  linarith

/-! ## 3 进时钟链：块值与 quarter lag -/

/-- 3 进 horizon：`0, 1, 3, 9, …`（astra `preparedSpatialHorizon`）。 -/
def clock3_C11RA : ℕ → ℝ
  | 0 => 0
  | n + 1 => (3 : ℝ) ^ n

theorem nat_lt_three_pow_C11RA (n : ℕ) : (n : ℝ) < (3 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem clock3_lt_C11RA (n : ℕ) : clock3_C11RA n < clock3_C11RA (n + 1) := by
  cases n with
  | zero => norm_num [clock3_C11RA]
  | succ k =>
    change (3 : ℝ) ^ k < (3 : ℝ) ^ (k + 1)
    exact pow_lt_pow_right₀ (by norm_num) (Nat.lt_succ_self k)

theorem clock3_ge_C11RA (n : ℕ) : (n : ℝ) ≤ clock3_C11RA (n + 1) :=
  (nat_lt_three_pow_C11RA n).le

/-- 任意时钟：块 `(E n, E (n+1)]` 上 diagonal δ 恒为 `a n`
（reference：`diagonal_delta_eq_accuracy_on_block`）。 -/
theorem chain_diagonal_delta_block_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, E n < t → (L (n + 1)).delta t = a n)
    (n : ℕ) {s : ℝ} (hs1 : E n < s) (hs2 : s ≤ E (n + 1)) :
    (CutoffParameters.diagonal fun k => L (k + 1)).delta s = a n := by
  have hsm : s ≤ E (Nat.ceil s + 1) := (Nat.le_ceil s).trans (hEge (Nat.ceil s))
  have h1 := chain_compat_C11RA E hElt L hpast (Nat.ceil s + 1) (max (n + 1) (Nat.ceil s + 1))
    (le_max_right _ _) s hsm
  have h2 := chain_compat_C11RA E hElt L hpast (n + 1) (max (n + 1) (Nat.ceil s + 1))
    (le_max_left _ _) s hs2
  change (L (Nat.ceil s + 1)).delta s = a n
  rw [← h1.1, h2.1]
  exact hafter n s hs1

/-- 3 进时钟链的 quarter lag：块值 `a (n+1) ≤ a n / 4` ⇒ `D.δ (3 max 1 s) ≤ D.δ s / 4`
（reference：`SH/PreparedSpatialLargerBallAccuracy.lean:52 diagonal_delta_quarter_lag`）。 -/
theorem chain_quarter_lag_C11RA (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ clock3_C11RA n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (L n).delta (Ici 0))
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, clock3_C11RA n < t → (L (n + 1)).delta t = a n)
    (hdrop : ∀ n : ℕ, a (n + 1) ≤ a n / 4) (s : ℝ) (hs : 0 ≤ s) :
    (CutoffParameters.diagonal fun k => L (k + 1)).delta (3 * max 1 s) ≤
      (CutoffParameters.diagonal fun k => L (k + 1)).delta s / 4 := by
  have hD := chain_diagonal_delta_antitone_C11RA clock3_C11RA clock3_lt_C11RA clock3_ge_C11RA L
    hpast hanti
  have hblock := fun (n : ℕ) (s : ℝ) (h1 : clock3_C11RA n < s) (h2 : s ≤ clock3_C11RA (n + 1)) =>
    chain_diagonal_delta_block_C11RA clock3_C11RA clock3_lt_C11RA clock3_ge_C11RA L hpast a
      hafter n h1 h2
  by_cases hs1 : s ≤ 1
  · have hmax : max 1 s = 1 := max_eq_left hs1
    have h3 := hblock 1 3 (by norm_num [clock3_C11RA]) (by norm_num [clock3_C11RA])
    have h1' := hblock 0 1 (by norm_num [clock3_C11RA]) (by norm_num [clock3_C11RA])
    have hle := hD (mem_Ici.2 hs) (mem_Ici.2 (zero_le_one)) hs1
    have hd := hdrop 0
    rw [hmax, mul_one, h3]
    linarith
  · have hs1' : 1 < s := lt_of_not_ge hs1
    have hex : ∃ n : ℕ, s ≤ (3 : ℝ) ^ n :=
      ⟨Nat.ceil s, (Nat.le_ceil s).trans (nat_lt_three_pow_C11RA _).le⟩
    obtain ⟨n, hn, hmin⟩ : ∃ n : ℕ, s ≤ (3 : ℝ) ^ n ∧ ∀ m : ℕ, m < n → ¬ s ≤ (3 : ℝ) ^ m :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    cases n with
    | zero =>
      rw [pow_zero] at hn
      exact absurd hs1' (not_lt.2 hn)
    | succ k =>
      have hlow : (3 : ℝ) ^ k < s := lt_of_not_ge (hmin k (Nat.lt_succ_self k))
      have hmax : max 1 s = s := max_eq_right hs1'.le
      have hsrc := hblock (k + 1) s (by simpa only [clock3_C11RA] using hlow)
        (by simpa only [clock3_C11RA] using hn)
      have htgt := hblock (k + 2) (3 * s)
        (by
          change (3 : ℝ) ^ (k + 1) < 3 * s
          rw [pow_succ]
          linarith)
        (by
          change 3 * s ≤ (3 : ℝ) ^ (k + 1 + 1)
          rw [pow_succ _ (k + 1)]
          linarith)
      have hd := hdrop (k + 1)
      rw [hmax, htgt, hsrc]
      linarith

/-- tuple 的 `q`（按 observation 与 diagonal 一致）在 3 进时钟链上满足 eligibility 界。 -/
theorem chain_eligibility_C11RA (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ clock3_C11RA n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (L n).delta (Ici 0))
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, clock3_C11RA n < t → (L (n + 1)).delta t = a n)
    (hdrop : ∀ n : ℕ, a (n + 1) ≤ a n / 4)
    (q : CutoffParameters)
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.delta t = (L (n + 1)).delta t)
    (A s : ℝ) (hs : 0 ≤ s) (hsmall : q.delta s < diagonalAccuracy_C11S q.delta A s) :
    A < 12 * max 1 s := by
  have hD := chain_diagonal_delta_antitone_C11RA clock3_C11RA clock3_lt_C11RA clock3_ge_C11RA L
    hpast hanti
  have hqeq := fun (t : ℝ) (ht : 0 ≤ t) => chain_q_eq_diagonal_C11RA L q hq ht
  have hqanti : AntitoneOn q.delta (Ici 0) := by
    intro s' hs' t' ht' hst'
    rw [hqeq t' ht', hqeq s' hs']
    exact hD hs' ht' hst'
  refine eligibility_of_quarterLag_C11RA q.delta_pos hqanti (fun s' hs' => ?_) A s hs hsmall
  have hnn : 0 ≤ 3 * max 1 s' := by
    have : (1 : ℝ) ≤ max 1 s' := le_max_left 1 s'
    linarith
  rw [hqeq _ hnn, hqeq _ hs']
  exact chain_quarter_lag_C11RA L hpast hanti a hafter hdrop s' hs'

/-! ## Consumers -/

/-- **Consumer（G3，S7）**：step 链的 diagonal 满足 `LargerBallAccuracySupply_C11S`（与 S1 同一链）。 -/
theorem stepChain_S7_C11RA :
    LargerBallAccuracySupply_C11S
      (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)).delta
      (diagonalAccuracy_C11S (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)).delta) :=
  largerBallAccuracySupply_diagonal_C11S _ stepChain_accuracyDecay_C11RA.1

/-- 非空真：`δ(t) = 1/(2(t+1)²)` 的参数（`sampleParameters_C11S` 只换 δ）。 -/
def quadParameters_C11RA : CutoffParameters :=
  { sampleParameters_C11S with
    delta := fun t => 1 / (2 * (t + 1) ^ 2)
    delta_pos := fun t ht => by positivity
    delta_lt_one := fun t ht => by
      rw [div_lt_one (by positivity)]
      nlinarith }

theorem quadParameters_antitone_C11RA : AntitoneOn quadParameters_C11RA.delta (Ici 0) := by
  intro s hs t _ hst
  simp only [mem_Ici] at hs
  change 1 / (2 * (t + 1) ^ 2) ≤ 1 / (2 * (s + 1) ^ 2)
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem quadParameters_quarterLag_C11RA (s : ℝ) (hs : 0 ≤ s) :
    quadParameters_C11RA.delta (3 * max 1 s) ≤ quadParameters_C11RA.delta s / 4 := by
  have hm1 : 1 ≤ max 1 s := le_max_left 1 s
  have hms : s ≤ max 1 s := le_max_right 1 s
  change 1 / (2 * (3 * max 1 s + 1) ^ 2) ≤ 1 / (2 * (s + 1) ^ 2) / 4
  rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
  nlinarith

/-- **Consumer（G3，eligibility）**：显式参数 `δ = 1/(2(t+1)²)` 满足 eligibility 的全部前提，
于是 `δ s < α A s ⇒ A < 12 · max 1 s`。 -/
theorem quadParameters_eligibility_C11RA (A s : ℝ) (hs : 0 ≤ s)
    (hsmall : quadParameters_C11RA.delta s <
      diagonalAccuracy_C11S quadParameters_C11RA.delta A s) :
    A < 12 * max 1 s :=
  eligibility_of_quarterLag_C11RA quadParameters_C11RA.delta_pos quadParameters_antitone_C11RA
    quadParameters_quarterLag_C11RA A s hs hsmall

end GC.LongTime.Ch11
