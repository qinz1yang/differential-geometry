import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurgeryParamCompatP6PC
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutoffAccuracyGluing

/-!
# 参数相容性的链上形，accuracy 版（O-CH11-PARAMCOMPAT G4，由 O-CH11-AUDITFIX 编入；后缀 `_P6PC`）

`P6SurgeryParamCompatP6PC.lean` 的 `paramCompat_of_chain_P6PC` 把树内 `PreparedSpatialChain` 的
diagonal 参数 `q := diagonal (S.observation ·).parameters` 归约到 band 内相邻比 `hstep`
（`q.delta x · r_j ≤ r_{j+1}`，`x` 在 band `j`）。本文件把 `hstep` 里的 `q.delta x` 换成 chain 自己的数据：

* `state_delta_compat_P6PC`：`(S.state n)` 的 `δ` 在 `t ≤ preparedSpatialHorizon m` 上与 `(S.state m)` 一致
  （树内 `private` `state_delta_compat` 的重证，`parameters_past` 归纳）；
* `diagonal_delta_antitone_P6PC`：diagonal `δ` 在 `[0, ∞)` 上 antitone（经
  `CutoffParameters.diagonal_delta_antitone`，逐 state `delta_antitone` + prefix compat）；
* `diagonal_delta_activation_P6PC`：diagonal `δ` 在步时 `(5/6)·3^k` 取 `S.accuracy k`（successor `k` 的
  `delta_after`）；
* **`paramCompat_of_chain_accuracy_P6PC`（PROVISIONAL[`h0`, `hacc`]）**：`SurgeryParamCompat_P6PC q θ`
  （`0 ≤ θ ≤ 3`）⟸ 首段 `δ(0)·r₀ ≤ r₁` + 相邻比 `accuracy k · r_{k+1} ≤ r_{k+2}`
  （`r_j = (S.state j).radius`）。
  band `k+1` 内 `δ` antitone 把 `q.delta x` 压到左步时的 `accuracy k`；
* consumer `hscale_of_chain_accuracy_P6PC`：chain 的 diagonal 参数 records + `h0` + `hacc` + Tn 行
  + 窗口比 ⇒ `exists_crossSlab_ceiling_CXJD` 的 `hscale` 槽逐字（经 `hscale_of_paramCompat_P6PC`）。

repair target 不变：`hacc` / `h0` 是 Perelman II Prop 5.1 量词序（先 `r_{m+1}`、后 `δ ≤ δ̄`）下构造可满足的
选择约束，但 `PreparedSpatialSuccessor` 只登记 `radius_le`（上界）与 `accuracy_le : accuracy n ≤ 1/(n+2)`，没有
`accuracy n` 与 `r_{n+2}/r_{n+1}` 的关系；owner = chain / successor 存在性。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Chain

variable {pBase : CutoffParameters} {C : GC.GeneralFlow.ClosedBirthConstants}
  {P : OrientedThreeStage.{u}} {g : P.Metric}

/-- `(S.state n)` 的 `δ` 在 `t ≤ preparedSpatialHorizon m` 上与 `(S.state m)` 一致（树内 `private`
`state_delta_compat` 的重证，parameters_past 归纳）。 -/
theorem state_delta_compat_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht : t ≤ GC.GeneralFlow.preparedSpatialHorizon m) :
    (S.state n).parameters.delta t = (S.state m).parameters.delta t := by
  have hclock : Monotone GC.GeneralFlow.preparedSpatialHorizon := by
    apply monotone_nat_of_le_succ
    intro k
    have h := (S.successor k).initial_prefix.1.horizon_le
    change (S.state k).history.horizon ≤ (S.state (k + 1)).history.horizon at h
    simpa only [(S.state k).horizon_eq, (S.state (k + 1)).horizon_eq] using h
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact ((S.successor n).parameters_past t (ht.trans (hclock hmn))).1.trans ih

/-- diagonal `δ` antitone（树内 `private` `diagonal_delta_antitone` 的重证）。 -/
theorem diagonal_delta_antitone_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g) :
    AntitoneOn (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
      (Ici 0) := by
  apply CutoffParameters.diagonal_delta_antitone
  · intro m n hmn t ht
    exact (state_delta_compat_P6PC S (m + 1) (n + 1) (Nat.add_le_add_right hmn 1)
      t (ht.2.trans (GC.GeneralFlow.nat_lt_three_pow m).le)).symm
  · intro n s hs t ht hst
    exact (S.state (n + 1)).delta_antitone hs.1 ht.1 hst

/-- diagonal `δ` 在步时 `(5/6)·3^k` 的值 = `S.accuracy k`（successor `k` 的 `delta_after`）。 -/
theorem diagonal_delta_activation_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    (k : ℕ) :
    (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
      ((5 / 6 : ℝ) * 3 ^ k) = S.accuracy k := by
  have hp : (0 : ℝ) < 3 ^ k := pow_pos (by norm_num) k
  have hk := nat_le_activation_P6PC k
  have hidx : k + 1 ≤ Nat.ceil ((5 / 6 : ℝ) * 3 ^ k) + 1 := by
    have h : k ≤ Nat.ceil ((5 / 6 : ℝ) * 3 ^ k) := by exact_mod_cast hk.trans (Nat.le_ceil _)
    omega
  have hle : (5 / 6 : ℝ) * 3 ^ k ≤ GC.GeneralFlow.preparedSpatialHorizon (k + 1) := by
    change (5 / 6 : ℝ) * 3 ^ k ≤ 3 ^ k
    linarith
  have hafter : GC.GeneralFlow.preparedSpatialHorizon k < (5 / 6 : ℝ) * 3 ^ k := by
    cases k with
    | zero =>
      change (0 : ℝ) < (5 / 6 : ℝ) * 3 ^ 0
      norm_num
    | succ j =>
      have hj : (0 : ℝ) < 3 ^ j := pow_pos (by norm_num) j
      change (3 : ℝ) ^ j < (5 / 6 : ℝ) * 3 ^ (j + 1)
      rw [pow_succ]
      linarith
  change (S.state (Nat.ceil ((5 / 6 : ℝ) * 3 ^ k) + 1)).parameters.delta ((5 / 6 : ℝ) * 3 ^ k) =
    S.accuracy k
  rw [state_delta_compat_P6PC S (k + 1) _ hidx _ hle]
  exact (S.successor k).delta_after _ hafter

/-- **合同的链上形，accuracy 版（PROVISIONAL[相邻比 `hacc` + 首段 `h0`]）**：树内 chain 的 diagonal 参数满足
`SurgeryParamCompat_P6PC q θ`（`0 ≤ θ ≤ 3`），前提只剩 chain 数据上的相邻比
`accuracy k · r_{k+1} ≤ r_{k+2}`（`r_j = (S.state j).radius`）与首段 `δ(0)·r₀ ≤ r₁`。
`δ` antitone 把 band 内的 `δ` 压到左步时的 `accuracy`（`diagonal_delta_activation_P6PC`）。
Perelman 量词序：`r_{k+1}`（activation `(5/6)·3^k`）与 `accuracy k` 同在 successor `k`；先 `r`、后
`δ ≤ δ̄(r)` 时加 `hacc` 只是把 `δ` 取小，构造上可满足，但树内 successor 未登记。 -/
theorem paramCompat_of_chain_accuracy_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ3 : θ ≤ 3)
    (h0 : (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta 0 *
      (S.state 0).radius ≤ (S.state 1).radius)
    (hacc : ∀ k, S.accuracy k * (S.state (k + 1)).radius ≤ (S.state (k + 2)).radius) :
    SurgeryParamCompat_P6PC
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)) θ := by
  refine paramCompat_of_chain_P6PC S hθ0 hθ3 fun j x hx0 _ hleft => ?_
  have hanti := diagonal_delta_antitone_P6PC S
  cases j with
  | zero =>
    have h := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx0) hx0
    exact (mul_le_mul_of_nonneg_right h (S.state 0).radius_pos.le).trans h0
  | succ k =>
    have hk := hleft k (Nat.lt_succ_self k)
    have hp : (0 : ℝ) ≤ (5 / 6 : ℝ) * 3 ^ k := by positivity
    have h := hanti (mem_Ici.mpr hp) (mem_Ici.mpr hx0) hk.le
    rw [diagonal_delta_activation_P6PC S k] at h
    exact (mul_le_mul_of_nonneg_right h (S.state (k + 1)).radius_pos.le).trans (hacc k)

/-- **G4 consumer（PROVISIONAL[`h0`, `hacc`]）**：chain 的 diagonal 参数 `q` 的 records + 首段 `h0` + 相邻比
`hacc` + hOpen8 Tn 行 `R ≤ ρ(Tn)⁻²` + `Tn ≤ θ·a` + 窗口 δ 小 ⇒ `exists_crossSlab_ceiling_CXJD` 的
`hscale` 逐字（合同由 `paramCompat_of_chain_accuracy_P6PC` 产出，喂 `hscale_of_paramCompat_P6PC`）。 -/
theorem hscale_of_chain_accuracy_P6PC (S : GC.GeneralFlow.PreparedSpatialChain pBase C P g)
    {H : ObservedHistory.{u}} {θ T₀ a Tn R r Qb : ℝ} (hθ0 : 0 ≤ θ) (hθ3 : θ ≤ 3)
    (h0 : (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta 0 *
      (S.state 0).radius ≤ (S.state 1).radius)
    (hacc : ∀ k, S.accuracy k * (S.state (k + 1)).radius ≤ (S.state (k + 2)).radius)
    (records : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ →
      GeometricCutoffRecord H e (CutoffParameters.diagonal (fun n => (S.observation n).parameters)))
    (hTn0 : 0 ≤ Tn) (hwin : Tn ≤ θ * a)
    (hTn : R ≤ ((CutoffParameters.diagonal
      (fun n => (S.observation n).parameters)).neckRadius Tn ^ 2)⁻¹)
    (hδ : ∀ e : Fin H.eventCount, T₀ ≤ H.time e.succ → a < H.time e.succ →
      (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).recenterConstant *
          (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
            (H.time e.succ) ≤ 1 / 2 ∧
        8 * Qb * (CutoffParameters.diagonal (fun n => (S.observation n).parameters)).delta
          (H.time e.succ) ^ 2 ≤ 1)
    (h3 : 3 / r ^ 2 ≤ 2 * (Qb * R)) (hQb : 0 ≤ Qb) :
    ∀ (e : Fin H.eventCount) (he : T₀ ≤ H.time e.succ) b, a < H.time e.succ →
      2 * max (3 / r ^ 2) (2 * (Qb * R)) < ((records e he).static b).neck.scale :=
  hscale_of_paramCompat_P6PC records (paramCompat_of_chain_accuracy_P6PC S hθ0 hθ3 h0 hacc) hθ0
    hTn0 hwin hTn hδ h3 hQb

end Chain

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
