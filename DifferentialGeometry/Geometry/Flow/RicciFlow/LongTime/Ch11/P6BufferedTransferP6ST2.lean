import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessUniformTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData

/-!
# S-c buffered fine-witness transfer 合同（R-C11-7 D-9 / D-10；O-CH11-STAB2 G1，后缀 `_P6ST2`）

设计：`docs/geometrization/chapter8/design-C11-buffered-transfer-20261007.md`。
D-9 的最小 transfer 合同冻结为两层 structure（event 层，`E : MetricCutCapEvent P Q a s`）：
* `BufferedFootprintData_P6ST2`：surviving identification `J`（`J p = q`）、固定 buffer `U ⊆ J.source`、
  `v n ∈ (a, s)`、`v n → s`、footprint 闭球（物理半径 `(8C1 + 3((ηout/2)⁻¹+7)√C2)/√Q_n`）⊆ `U`、
  `C^k` comparison（`MetricComparisonOn`，`k ≥ max 2 ⌈ηout⁻¹⌉`，任意 `δ` eventually）、`Q_n → Q₊ > 0`、
  基点梯度的真极限；全是 event 几何，不含左侧 Good。
* `BufferedTransferData_P6ST2`（`extends` 上者）：fine 精度 `ηfine ≤ neckModelTolerance (ηout/2)` 与
  eventually 的 finer witnesses（`capTubeHasNeckChart ηfine` ∧ `HasMargins m`，严格内缩余量）。
`g⁻ = J*g⁺` 不作字段（只被 `comparison` 的 producer 使用）；Slack 在本路线是定理（`δ(α,m,C1,C2,Q₊/2)` 先于 `n`）。

主定理 `spatialWitness_of_bufferedTransfer_P6ST2`（D-10 局部扰动，**0 binder**）：取一个足够大的 `n`，用 `J` 搬运
fine witness 的全部 support，由树内
`SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance` 逐字段检验；
梯度字段经真极限（非严格，保等号）。输出 `(ηout, C1out, C2out)`，`2C1 ≤ C1out`、`1000C2 ≤ C2out`。
`positive` / `round` 型 witness 不在本合同（`HasMargins` 只允许 neck / cap），见设计 §1 OPEN-C。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open Perelman.CanonicalNeighborhood.FiniteHorn

universe u

section Margins

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M}
  {eps eps' C1 C2 m : ℝ} {x : M}

/-- `HasMargins` 在提高精度参数（`monoEps`）下保持：`SpatialLocalCap.monoEps` 不改 `tube`、radius、domain。 -/
theorem hasMargins_monoEps_P6ST2 {W : SpatialCanonicalWitness g eps C1 C2 x} (h : W.HasMargins m)
    (heps : eps ≤ eps') (hsmall : eps' < 1 / 11) : (W.monoEps heps hsmall).HasMargins m := by
  obtain ⟨hshape, hrad, hin, hout, hdeep⟩ := h
  have halt : (W.monoEps heps hsmall).alternative =
      W.alternative.monoEps W.eps_pos heps hsmall := rfl
  refine ⟨?_, hrad, hin, hout, ?_⟩
  · rw [halt]
    rcases hshape with ⟨n, hn⟩ | ⟨c, d, hcd⟩
    · exact Or.inl ⟨_, by rw [hn]; rfl⟩
    · exact Or.inr ⟨_, d, by rw [hcd]; rfl⟩
  · intro c d heq
    rw [halt] at heq
    cases hW : W.alternative with
    | neck data =>
      rw [hW] at heq
      cases heq
    | cap data deep =>
      rw [hW] at heq
      change SpatialCanonicalAlternative.cap (data.monoEps heps hsmall) deep =
        SpatialCanonicalAlternative.cap c d at heq
      cases heq
      exact hdeep _ _ hW
    | positive whole data sec =>
      rw [hW] at heq
      cases heq
    | round whole data =>
      rw [hW] at heq
      cases heq

end Margins

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- **D-9 footprint 层（event 几何）**：`J : Ω⁻ ⇢ Ω⁺`（`J p = q`）、固定 buffer `U ⊆ J.source`、`v n ↑ s`、
footprint 闭球 ⊆ `U`、`C^k` comparison（阶 `k ≥ max 2 ⌈ηout⁻¹⌉`，任意 `δ > 0` eventually）、
归一化 `Q_n → Q₊ > 0`、基点梯度真极限。常数 `ηout, C1, C2`、margin `m ∈ (0, 1/2]`、阶 `k` 是参数——在选 `n` 之前固定。 -/
structure BufferedFootprintData_P6ST2 (E : MetricCutCapEvent P Q a s) (p : P.Carrier)
    (q : Q.Carrier) (ηout C1 C2 m : ℝ) (k : ℕ) where
  ηout_lt : ηout < 1 / 11
  one_le_C1 : 1 ≤ C1
  one_le_C2 : 1 ≤ C2
  m_pos : 0 < m
  m_le : m ≤ 1 / 2
  order_le : max 2 ⌈ηout⁻¹⌉₊ ≤ k
  /-- surviving identification（光滑部分）。 -/
  J : PartialDiffeomorph I3 I3 P.Carrier Q.Carrier ∞
  J_apply : J p = q
  /-- 固定 surviving buffer。 -/
  U : Opens P.Carrier
  U_sub : (U : Set P.Carrier) ⊆ J.source
  /-- 左侧时间序列 `v n ↑ s`。 -/
  v : ℕ → ℝ
  v_mem : ∀ n, v n ∈ Ioo a s
  v_tendsto : Tendsto v atTop (𝓝 s)
  Q_pos : 0 < metricScalarAt E.outputMetric q
  /-- normalization：`Q_n := R⁻(v n, p) → Q₊ := R⁺(s, q)`。 -/
  scalar_tendsto : Tendsto (fun n => metricScalarAt (E.incoming.flow.base.metric (v n)) p) atTop
    (𝓝 (metricScalarAt E.outputMetric q))
  /-- footprint：物理半径 `(8C1 + 3((ηout/2)⁻¹+7)√C2)/√Q_n` 的闭球在 buffer 内。 -/
  footprint : ∀ᶠ n in atTop,
    riemannianClosedBallOf (I := I3) (E.incoming.flow.base.metric (v n)) p
      ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
        Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (v n)) p)) ⊆ U
  /-- `C^k` convergence + chart control：`J*g⁺` 与 `g(v n)` 在 `U` 上 `C^k`-`δ` 接近（`g(v n)` 量）。 -/
  comparison : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
    Nonempty (MetricComparisonOn (fun _ => E.incoming.flow.base.metric (v n))
      (fun _ => E.outputMetric) J U {0} k δ)
  /-- 基点梯度（阶 3）的真极限：`dR_{g(v n)}(p) u → dR⁺(q) w`，`|u|_{g(v n)} → |w|_{g⁺}`。 -/
  gradient_tendsto : ∀ w : TangentSpace I3 q, ∃ u : TangentSpace I3 p,
    Tendsto (fun n => (show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
        (metricScalarAt (E.incoming.flow.base.metric (v n))) p u)) atTop
      (𝓝 (show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) q w)) ∧
    Tendsto (fun n => (E.incoming.flow.base.metric (v n)).inner p u u) atTop
      (𝓝 (E.outputMetric.inner q w w))

/-- **D-9 完整合同**：footprint 层 + fine 精度 `ηfine ≤ neckModelTolerance (ηout/2)` + eventually 的 finer
witnesses（`capTubeHasNeckChart ηfine` ∧ `HasMargins m`）。`0 < ηfine < ηout < 1/11` 见
`ηfine_lt_ηout`。 -/
structure BufferedTransferData_P6ST2 (E : MetricCutCapEvent P Q a s) (p : P.Carrier)
    (q : Q.Carrier) (ηfine ηout C1 C2 m : ℝ) (k : ℕ) extends
    E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k where
  ηfine_le : ηfine ≤ neckModelTolerance (ηout / 2)
  /-- finer witnesses `W_n` at `(v n, p)`，带严格内缩余量 `m`。 -/
  fine : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (v n)) ηfine
    C1 C2 p, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m

variable {E : MetricCutCapEvent P Q a s} {p : P.Carrier} {q : Q.Carrier}
  {ηfine ηout C1 C2 m : ℝ} {k : ℕ}

/-- **条件 inhabitant**：footprint 层 + fine 层字段 ⇒ 完整合同。 -/
def BufferedTransferData_P6ST2.ofFootprint_P6ST2
    (D : E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k)
    (hle : ηfine ≤ neckModelTolerance (ηout / 2))
    (hfine : ∀ᶠ n in atTop, ∃ W : SpatialCanonicalWitness (E.incoming.flow.base.metric (D.v n))
      ηfine C1 C2 p, W.capTubeHasNeckChart ηfine ∧ W.HasMargins m) :
    E.BufferedTransferData_P6ST2 p q ηfine ηout C1 C2 m k :=
  { D with ηfine_le := hle, fine := hfine }

/-- 归一化的比值形：`Q_n / Q₊ → 1`（D-9 的 `Q_m/Q₊ → 1`）。 -/
theorem BufferedFootprintData_P6ST2.ratio_tendsto_one
    (D : E.BufferedFootprintData_P6ST2 p q ηout C1 C2 m k) :
    Tendsto (fun n => metricScalarAt (E.incoming.flow.base.metric (D.v n)) p /
      metricScalarAt E.outputMetric q) atTop (𝓝 1) := by
  have h := D.scalar_tendsto.div_const (metricScalarAt E.outputMetric q)
  rwa [div_self D.Q_pos.ne'] at h

/-- 精度层级 `0 < ηfine < ηout < 1/11`（D-9）：由 `ηfine ≤ neckModelTolerance (ηout/2) ≤ ηout/2` 导出。 -/
theorem BufferedTransferData_P6ST2.ηfine_lt_ηout
    (D : E.BufferedTransferData_P6ST2 p q ηfine ηout C1 C2 m k) :
    0 < ηfine ∧ ηfine < ηout ∧ ηout < 1 / 11 := by
  obtain ⟨n, W, -, -⟩ := D.fine.exists
  have h0 : 0 < ηfine := W.eps_pos
  have h1 : ηfine ≤ ηout / 2 := D.ηfine_le.trans (neckModelTolerance_le _)
  exact ⟨h0, by linarith, D.ηout_lt⟩

/-- 目标点梯度界（真极限，非严格字段保等号）：eventually fine witness 的 `gradient` + `scalar_tendsto` +
`gradient_tendsto` ⇒ `|dR⁺_q w| ≤ C2' Q₊ √Q₊ |w|`，任意 `C2' ≥ C2`。 -/
theorem BufferedTransferData_P6ST2.gradient_bound
    (D : E.BufferedTransferData_P6ST2 p q ηfine ηout C1 C2 m k) {C2' : ℝ} (hC : C2 ≤ C2')
    (w : TangentSpace I3 q) :
    |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) q w)| ≤
      C2' * metricScalarAt E.outputMetric q * Real.sqrt (metricScalarAt E.outputMetric q) *
        Real.sqrt (E.outputMetric.inner q w w) := by
  obtain ⟨u, hu1, hu2⟩ := D.gradient_tendsto w
  have hev : ∀ᶠ n in atTop,
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ)
          (metricScalarAt (E.incoming.flow.base.metric (D.v n))) p u)| ≤
        C2 * metricScalarAt (E.incoming.flow.base.metric (D.v n)) p *
          Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p) *
          Real.sqrt ((E.incoming.flow.base.metric (D.v n)).inner p u u) := by
    filter_upwards [D.fine] with n hn
    obtain ⟨W, -, -⟩ := hn
    exact W.gradient u
  have hR := ((tendsto_const_nhds (x := C2)).mul D.scalar_tendsto).mul
    D.scalar_tendsto.sqrt
  have hlim := le_of_tendsto_of_tendsto hu1.abs (hR.mul hu2.sqrt) hev
  have hQ := D.Q_pos
  exact hlim.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC hQ.le) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

/-- **主定理（D-10 局部扰动，0 binder）**：buffered fine-witness transfer 合同 ⇒ post 点 `q` 处输出度量的
目标 witness `(ηout, C1out, C2out)`，带 `capTubeHasNeckChart ηout`。证明：`α = ηout/2`，先由树内
`exists_uniform_comparison_transport_tolerance` 取 `δ(α, m, C1, C2, Q₊/2)`（**选 `n` 之前**），再取一个足够大的
`n`（fine ∧ footprint ∧ comparison `δ` ∧ `Q₊/2 ≤ Q_n`），用 `J` 搬运 `W_n` 的全部 support；精度
`ηfine → neckModelTolerance α`（`monoEps`，margins 保持），阶 `k ↓ max 2 ⌈(2α)⁻¹⌉`，梯度由真极限。 -/
theorem spatialWitness_of_bufferedTransfer_P6ST2
    (D : E.BufferedTransferData_P6ST2 p q ηfine ηout C1 C2 m k) {C1out C2out : ℝ}
    (h1 : 2 * C1 ≤ C1out) (h2 : 1000 * C2 ≤ C2out) :
    ∃ W : SpatialCanonicalWitness E.outputMetric ηout C1out C2out q,
      W.capTubeHasNeckChart ηout := by
  obtain ⟨hf0, hf1, hf2⟩ := D.ηfine_lt_ηout
  have hα : 0 < ηout / 2 := by linarith
  have hsmall : 2 * (ηout / 2) < 1 / 11 := by linarith
  have hQ := D.Q_pos
  obtain ⟨δ, hδ, hT⟩ :=
    SpatialCanonicalWitness.exists_uniform_comparison_transport_tolerance (P := P.Carrier) hα
      hsmall D.m_pos D.m_le D.one_le_C1 D.one_le_C2 (half_pos hQ)
  have hlow : ∀ᶠ n in atTop, metricScalarAt E.outputMetric q / 2 ≤
      metricScalarAt (E.incoming.flow.base.metric (D.v n)) p :=
    D.scalar_tendsto.eventually (eventually_ge_nhds (half_lt_self hQ))
  obtain ⟨n, ⟨W, hWc, hWm⟩, hfoot, ⟨Cmp⟩, hQn⟩ :=
    (D.fine.and (D.footprint.and ((D.comparison δ hδ).and hlow))).exists
  have hle : ηfine ≤ neckModelTolerance (ηout / 2) := D.ηfine_le
  have hnt : neckModelTolerance (ηout / 2) < 1 / 11 :=
    (neckModelTolerance_le _).trans_lt (by linarith)
  have hW'c := hWc.mono_eps hle hnt hle hnt
  have hW'm := hasMargins_monoEps_P6ST2 hWm hle hnt
  have h2α : 2 * (ηout / 2) = ηout := by ring
  have hord : max 2 ⌈(2 * (ηout / 2))⁻¹⌉₊ ≤ k := by
    rw [h2α]
    exact D.order_le
  have hcpt := (Geometry.Metric.isClosed_riemannianClosedBallOf
    (E.incoming.flow.base.metric (D.v n)) p
    ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt (E.incoming.flow.base.metric (D.v n)) p))).isCompact
  have hC2 : C2 ≤ C2out := by linarith [D.one_le_C2]
  have hgrad : ∀ w : TangentSpace I3 (D.J p),
      |(show ℝ from mfderiv I3 𝓘(ℝ, ℝ) (metricScalarAt E.outputMetric) (D.J p) w)| ≤
        C2out * metricScalarAt E.outputMetric (D.J p) *
          Real.sqrt (metricScalarAt E.outputMetric (D.J p)) *
          Real.sqrt (E.outputMetric.inner (D.J p) w w) := by
    rw [D.J_apply]
    exact D.gradient_bound hC2
  obtain ⟨Wo, hWo, -⟩ := hT (E.incoming.flow.base.metric (D.v n)) p (W.monoEps hle hnt) hW'c
    hW'm hQn D.U hcpt hfoot Q.Carrier E.outputMetric D.J D.U_sub
    (Cmp.mono (subset_refl _) hord le_rfl) C2out h2 hgrad
  rw [← h2α, ← D.J_apply]
  exact ⟨Wo.enlargeConstants h1 le_rfl, hWo.enlarge_constants h1 le_rfl⟩

end MetricCutCapEvent

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
