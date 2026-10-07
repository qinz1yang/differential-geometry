import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12SuppliesNonempty_C11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffParameterGluing

set_option autoImplicit false

/-!
# S-CH11-REPROVE-A (G1)：S1 = `AccuracyDecaySupply_C11S q.delta` 的参数级重证

astra 里 S1 来自 narrow tuple `exists_surgery_with_spatial_control_and_decay` 的两个 δ 条款
（`AntitoneOn q.delta (Ici 0)` 与 `Tendsto q.delta atTop (𝓝 0)`），而它们又来自
`PreparedSpatialChain` 的 diagonal 参数 `diagonal (fun n => (S.observation n).parameters)`：
`ST/CutoffAccuracyGluing.lean`（`diagonal_delta_antitone`）、`SH/PreparedSpatialDecay.lean`
（`state_delta_compat`、`diagonal_delta_at_three_pow`、`diagonal_delta_tendsto`）。`PreparedSpatialChain`
的闭包永久 reference-only，所以这里把证明里**真正用到的参数级性质**写成显式 binder 的通用引理
（不新建结构、不绑定 `3^n` 时钟：任意严格递增的 horizon 序列 `E` 且 `n ≤ E (n+1)`）：

* `diagonal_delta_antitone_C11RA` / `spliceAfter_delta_antitone_C11RA`：W8 `CutoffParameterGluing`
  只有 `neckRadius` 版，这里补 δ 版（reference 逐行同证明）；
* `accuracyDecaySupply_of_small_values_C11RA`、`tendsto_of_accuracyDecaySupply_C11RA`：S1 ⇔
  「antitone + 任意小的值」/「antitone + `Tendsto`」（SKEL 已有 `Tendsto ⇒ S1` 方向）；
* `chain_compat_C11RA`（= `state_delta_compat`，同时带 `neckRadius`、`protectedRadius`）、
  `chain_diagonal_delta_at_E_C11RA`（= `diagonal_delta_at_three_pow`）、
  `chain_accuracy_small_values_C11RA`（= `diagonal_delta_tendsto` 的 ε–N 部分）；
* **主定理** `accuracyDecay_of_chain_C11RA`：链 `L : ℕ → CutoffParameters`（`L n` = 第 n 个 state 的参数）
  满足 `parameters_past`、每个 `L n` 的 δ antitone、`E n` 之后 δ 取常值 `a n ≤ 1/(n+2)`；任何与
  `diagonal (fun n => L (n+1))` 在 `[0,n]` 上按 observation `n` 一致的 `q`（tuple 的 `hpref` 形）满足
  `AntitoneOn q.delta (Ici 0) ∧ Tendsto q.delta atTop (𝓝 0) ∧ AccuracyDecaySupply_C11S q.delta`
  = ASM 的 W1 中 S1 对应的三个合取项；
* consumer：显式 step 链 `stepChain_C11RA`（`δ_n(t) = 1/(min ⌈t⌉ n + 2)`）满足主定理的全部前提（非空真）。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter

namespace GC.LongTime.Ch11

/-! ## 对角 / splice 的 δ antitone -/

/-- prefix-compatible 的 antitone δ 序列的对角是 antitone
（reference：`ST/CutoffAccuracyGluing.lean:13 diagonal_delta_antitone`）。 -/
theorem diagonal_delta_antitone_C11RA (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).delta t = (p n).delta t)
    (hanti : ∀ n : ℕ, AntitoneOn (p n).delta (Icc (0 : ℝ) (n : ℝ))) :
    AntitoneOn (CutoffParameters.diagonal p).delta (Ici 0) := by
  intro s hs t ht hst
  change (p (Nat.ceil t)).delta t ≤ (p (Nat.ceil s)).delta s
  rw [hcompat (Nat.ceil s) (Nat.ceil t) (Nat.ceil_mono hst) s ⟨hs, Nat.le_ceil s⟩]
  exact hanti (Nat.ceil t) ⟨hs, hst.trans (Nat.le_ceil t)⟩ ⟨ht, Nat.le_ceil t⟩ hst

/-- 在 join `T` 处用实际不等式 `q.delta T ≤ p.delta T` 拼接 δ
（reference：`ST/CutoffAccuracyGluing.lean:24 spliceAfter_delta_antitone`）。 -/
theorem spliceAfter_delta_antitone_C11RA (p q : CutoffParameters) (T : ℝ)
    (hp : AntitoneOn p.delta (Icc 0 T))
    (hq : AntitoneOn q.delta (Ici T))
    (hjoin : q.delta T ≤ p.delta T) :
    AntitoneOn (p.spliceAfter q T).delta (Ici 0) := by
  intro s hs t ht hst
  change (if t ≤ T then p.delta t else q.delta t) ≤
    if s ≤ T then p.delta s else q.delta s
  by_cases hsT : s ≤ T
  · by_cases htT : t ≤ T
    · rw [ite_eq_left htT, ite_eq_left hsT]
      exact hp ⟨hs, hsT⟩ ⟨ht, htT⟩ hst
    · rw [ite_eq_right htT, ite_eq_left hsT]
      have hTt : T ≤ t := (lt_of_not_ge htT).le
      exact (hq (show T ∈ Ici T from le_refl T) hTt hTt).trans
        (hjoin.trans (hp ⟨hs, hsT⟩ ⟨hs.trans hsT, le_rfl⟩ hsT))
  · have hTt : T < t := (lt_of_not_ge hsT).trans_le hst
    rw [ite_eq_right (not_le.mpr hTt), ite_eq_right hsT]
    exact hq (lt_of_not_ge hsT).le hTt.le hst

/-! ## S1 的实分析核心：antitone + 任意小的值 ⇔ decay / `Tendsto` -/

/-- antitone 且取到任意小的值（在某个 `T ≥ 0`）⇒ A12 的 δ 条款（不需要正性）。 -/
theorem accuracyDecaySupply_of_small_values_C11RA {δ : ℝ → ℝ}
    (hanti : AntitoneOn δ (Ici 0))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧ δ T < ε) :
    AccuracyDecaySupply_C11S δ := by
  refine ⟨hanti, fun ε hε => ?_⟩
  obtain ⟨T, hT, hδ⟩ := hsmall ε hε
  exact ⟨T, fun t ht => (hanti (mem_Ici.2 hT) (mem_Ici.2 (hT.trans ht.le)) ht.le).trans_lt hδ⟩

/-- S1 ⇒ `Tendsto δ atTop (𝓝 0)`（`accuracyDecaySupply_of_tendsto_C11S` 的逆向，需要 `δ > 0`）。 -/
theorem tendsto_of_accuracyDecaySupply_C11RA {δ : ℝ → ℝ} (hpos : ∀ t, 0 ≤ t → 0 < δ t)
    (hdec : AccuracyDecaySupply_C11S δ) : Tendsto δ atTop (nhds 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨B, hB⟩ := hdec.2 ε hε
  refine ⟨max B 0 + 1, fun t ht => ?_⟩
  have hmax : max B 0 < t := lt_of_lt_of_le (lt_add_one _) ht
  rw [Real.dist_eq, sub_zero, abs_of_pos (hpos t ((le_max_right B 0).trans hmax.le))]
  exact hB t ((le_max_left B 0).trans_lt hmax)

/-! ## 参数链：`L n` = 第 n 个 state 的参数，`E n` = 它的 horizon -/

/-- `parameters_past`（`PreparedSpatialSuccessor.parameters_past`）的 `m ≤ n` 版
（reference：`SH/PreparedSpatialDecay.lean:16 state_delta_compat`，这里同时带两个半径）。 -/
theorem chain_compat_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht : t ≤ E m) :
    (L n).delta t = (L m).delta t ∧ (L n).neckRadius t = (L m).neckRadius t ∧
      (L n).protectedRadius t = (L m).protectedRadius t := by
  have hmono : Monotone E := monotone_nat_of_le_succ fun k => (hElt k).le
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨rfl, rfl, rfl⟩
  | succ n hmn ih =>
    have h := hpast n t (ht.trans (hmono hmn))
    exact ⟨h.1.trans ih.1, h.2.1.trans ih.2.1, h.2.2.trans ih.2.2⟩

/-- diagonal 的 prefix-compatibility：observation `m` 与 `n` 在 `[0, m]` 上一致
（`m ≤ E (m+1)` 保证 `[0,m]` 落在 `L (m+1)` 的 horizon 内）。 -/
theorem chain_diagonal_compat_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (m : ℝ)) :
    (L (m + 1)).delta t = (L (n + 1)).delta t ∧
      (L (m + 1)).neckRadius t = (L (n + 1)).neckRadius t ∧
      (L (m + 1)).protectedRadius t = (L (n + 1)).protectedRadius t := by
  have h := chain_compat_C11RA E hElt L hpast (m + 1) (n + 1) (Nat.add_le_add_right hmn 1) t
    (ht.2.trans (hEge m))
  exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- 链的 diagonal δ antitone（reference：`SH/PreparedSpatialDecay.lean:34 diagonal_delta_antitone`）。 -/
theorem chain_diagonal_delta_antitone_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (L n).delta (Ici 0)) :
    AntitoneOn (CutoffParameters.diagonal fun n => L (n + 1)).delta (Ici 0) :=
  diagonal_delta_antitone_C11RA _
    (fun m n hmn t ht => (chain_diagonal_compat_C11RA E hElt hEge L hpast m n hmn t ht).1)
    (fun n _ hs _ ht hst => hanti (n + 1) hs.1 ht.1 hst)

/-- 链的 diagonal δ 在 checkpoint `E (n+1)` 取到 `a n`
（reference：`SH/PreparedSpatialDecay.lean:41 diagonal_delta_at_three_pow`，`E (n+1) = 3^n`）。 -/
theorem chain_diagonal_delta_at_E_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, E n < t → (L (n + 1)).delta t = a n)
    (n : ℕ) :
    (CutoffParameters.diagonal fun k => L (k + 1)).delta (E (n + 1)) = a n := by
  have hnat : n ≤ Nat.ceil (E (n + 1)) := by
    have h : (n : ℝ) ≤ (Nat.ceil (E (n + 1)) : ℝ) := (hEge n).trans (Nat.le_ceil _)
    exact_mod_cast h
  have hcompat := chain_compat_C11RA E hElt L hpast (n + 1) (Nat.ceil (E (n + 1)) + 1)
    (Nat.add_le_add_right hnat 1) (E (n + 1)) le_rfl
  change (L (Nat.ceil (E (n + 1)) + 1)).delta (E (n + 1)) = a n
  rw [hcompat.1]
  exact hafter n _ (hElt n)

/-- checkpoint 上 `a n ≤ 1/(n+2)` ⇒ diagonal δ 取到任意小的值
（reference：`diagonal_delta_tendsto` 里的 `exists_nat_one_div_lt` 段）。 -/
theorem chain_accuracy_small_values_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, E n < t → (L (n + 1)).delta t = a n)
    (ha : ∀ n : ℕ, a n ≤ 1 / ((n : ℝ) + 2)) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧
      (CutoffParameters.diagonal fun k => L (k + 1)).delta T < ε := by
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨E (n + 1), (Nat.cast_nonneg n).trans (hEge n), ?_⟩
  rw [chain_diagonal_delta_at_E_C11RA E hElt hEge L hpast a hafter n]
  calc a n ≤ 1 / ((n : ℝ) + 2) := ha n
    _ ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le (by positivity) (by linarith)
    _ < ε := hn

/-- tuple 的 `q`（与 diagonal 在 `[0,n]` 上按 observation `n` 一致，`hpref` 形）在 `t ≥ 0` 处等于 diagonal。 -/
theorem chain_q_eq_diagonal_C11RA (L : ℕ → CutoffParameters) (q : CutoffParameters)
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.delta t = (L (n + 1)).delta t)
    {t : ℝ} (ht : 0 ≤ t) :
    q.delta t = (CutoffParameters.diagonal fun k => L (k + 1)).delta t :=
  hq (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩

/-- **G1 主定理（S1）**：链满足 `parameters_past`、δ antitone、`E n` 之后 δ ≡ `a n ≤ 1/(n+2)`，
则任何按 observation 与 diagonal 一致的 `q` 满足 W1 里 S1 的三个合取项。 -/
theorem accuracyDecay_of_chain_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
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
    AntitoneOn q.delta (Ici 0) ∧ Tendsto q.delta atTop (nhds 0) ∧
      AccuracyDecaySupply_C11S q.delta := by
  have hD := chain_diagonal_delta_antitone_C11RA E hElt hEge L hpast hanti
  have hsmall := chain_accuracy_small_values_C11RA E hElt hEge L hpast a hafter ha
  have hDdec := accuracyDecaySupply_of_small_values_C11RA hD hsmall
  have hDlim := tendsto_of_accuracyDecaySupply_C11RA
    (CutoffParameters.diagonal fun k => L (k + 1)).delta_pos hDdec
  have hqanti : AntitoneOn q.delta (Ici 0) := by
    intro s hs t ht hst
    rw [chain_q_eq_diagonal_C11RA L q hq ht, chain_q_eq_diagonal_C11RA L q hq hs]
    exact hD hs ht hst
  have hqlim : Tendsto q.delta atTop (nhds 0) := by
    refine hDlim.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (chain_q_eq_diagonal_C11RA L q hq ht).symm
  exact ⟨hqanti, hqlim, accuracyDecaySupply_of_tendsto_C11S hqanti hqlim⟩

/-! ## Consumer：显式 step 链满足全部前提（非空真） -/

/-- step 链的 δ：`δ_n(t) = 1/(min ⌈t⌉ n + 2)`。 -/
def stepChainDelta_C11RA (n : ℕ) (t : ℝ) : ℝ := 1 / (((min (Nat.ceil t) n : ℕ) : ℝ) + 2)

/-- step 链：`SurgerySuppliesC11S` 的样本参数，只换 δ（半径沿用 `1/(t+1)`）。 -/
def stepChain_C11RA (n : ℕ) : CutoffParameters :=
  { sampleParameters_C11S with
    delta := stepChainDelta_C11RA n
    delta_pos := fun t _ => by
      unfold stepChainDelta_C11RA
      positivity
    delta_lt_one := fun t _ => by
      unfold stepChainDelta_C11RA
      rw [div_lt_one (by positivity)]
      have : (0 : ℝ) ≤ ((min (Nat.ceil t) n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith }

/-- step 链的 `parameters_past`（`E n = n`）。 -/
theorem stepChain_past_C11RA (n : ℕ) (t : ℝ) (ht : t ≤ (n : ℝ)) :
    (stepChain_C11RA (n + 1)).delta t = (stepChain_C11RA n).delta t ∧
      (stepChain_C11RA (n + 1)).neckRadius t = (stepChain_C11RA n).neckRadius t ∧
      (stepChain_C11RA (n + 1)).protectedRadius t = (stepChain_C11RA n).protectedRadius t := by
  refine ⟨?_, rfl, rfl⟩
  have hc : Nat.ceil t ≤ n := Nat.ceil_le.2 ht
  change 1 / (((min (Nat.ceil t) (n + 1) : ℕ) : ℝ) + 2) = 1 / (((min (Nat.ceil t) n : ℕ) : ℝ) + 2)
  rw [min_eq_left (hc.trans (Nat.le_succ n)), min_eq_left hc]

/-- step 链的每个 δ antitone。 -/
theorem stepChain_antitone_C11RA (n : ℕ) : AntitoneOn (stepChain_C11RA n).delta (Ici 0) := by
  intro s _ t _ hst
  change 1 / (((min (Nat.ceil t) n : ℕ) : ℝ) + 2) ≤ 1 / (((min (Nat.ceil s) n : ℕ) : ℝ) + 2)
  have hnat : min (Nat.ceil s) n ≤ min (Nat.ceil t) n := min_le_min_right n (Nat.ceil_mono hst)
  have hcast : ((min (Nat.ceil s) n : ℕ) : ℝ) ≤ ((min (Nat.ceil t) n : ℕ) : ℝ) :=
    Nat.cast_le.2 hnat
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- step 链在 `E n = n` 之后的常值：`1/(n+3)`。 -/
theorem stepChain_after_C11RA (n : ℕ) (t : ℝ) (ht : (n : ℝ) < t) :
    (stepChain_C11RA (n + 1)).delta t = 1 / ((n : ℝ) + 3) := by
  have hc : n < Nat.ceil t := Nat.lt_ceil.2 ht
  change 1 / (((min (Nat.ceil t) (n + 1) : ℕ) : ℝ) + 2) = 1 / ((n : ℝ) + 3)
  rw [min_eq_right (Nat.succ_le_of_lt hc)]
  push_cast
  ring_nf

/-- **Consumer（G1）**：step 链用主定理得到 S1 的三个合取项（`q :=` diagonal 本身，`hq` 来自
W8 的 `CutoffParameters.diagonal_eq_on_prefix`）。 -/
theorem stepChain_accuracyDecay_C11RA :
    AntitoneOn (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)).delta (Ici 0) ∧
      Tendsto (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)).delta atTop (nhds 0) ∧
      AccuracyDecaySupply_C11S
        (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)).delta :=
  accuracyDecay_of_chain_C11RA (fun n => (n : ℝ)) (fun n => by simp)
    (fun n => by simp) stepChain_C11RA stepChain_past_C11RA stepChain_antitone_C11RA
    (fun n => 1 / ((n : ℝ) + 3)) (fun n t ht => stepChain_after_C11RA n t ht)
    (fun n => one_div_le_one_div_of_le (by positivity) (by linarith))
    _ (fun n t ht =>
      (CutoffParameters.diagonal_eq_on_prefix (fun k => stepChain_C11RA (k + 1))
        (fun m n hmn t ht =>
          chain_diagonal_compat_C11RA (fun n => (n : ℝ)) (fun n => by simp) (fun n => by simp)
            stepChain_C11RA stepChain_past_C11RA m n hmn t ht) n ht).1)

end GC.LongTime.Ch11
