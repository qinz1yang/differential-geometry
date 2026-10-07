import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SurvivorJP6ST3
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventCutScaleProtection
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity

/-!
# S-c P-F：footprint 归约到 crossing 点的定量 terminal 半径（O-CH11-STAB3 G3，后缀 `_P6ST3`）

STAB2 合同最后一个字段 `footprint`（`∀ᶠ n, B̄_{g(v n)}(p, ρ_n) ⊆ U`，`ρ_n = c/√Q_n`，
`c := 8C1 + 3((ηout/2)⁻¹ + 7)√C2`）。树内 `RegularCrossing` / post-cover **不给半径**（D-9 第二问）。本文件：
* `eventually_footprint_of_terminalBall_P6ST3`（t 层）：terminal closed ball `B̄_ḡ(p, R)` 紧
  且 `R > (17/16)·c/√Q₊` ⇒ `t → s⁻` eventually
  `B̄_{g t}(p, c/√R_{g t}(p)) ⊆ val '' B_ḡ(p, R)`
  （树内 `eventually_riemannianBallOf_subset_image_closedBall` 的 `16/17` 系数 + `Q_t → Q₊`）。
* **`nonempty_footprintData_of_terminalBall_P6ST3`**（event 层合同，**PROVISIONAL**）：
  `RegularCrossing p q` + `Q₊ > 0` + 定量 terminal 半径（`B̄_ḡ(p, R)` 紧、⊆ surviving domain
  `{x | x.val ∈ interior (val '' old)}`、`R > (17/16)c/√Q₊`）⇒
  `Nonempty (BufferedFootprintData_P6ST2 …)`；`U := val '' B_ḡ(p, R)`、`K := val '' B̄_ḡ(p, R)`、
  `v n := s − (s − a)/(n + 2)` 全部构造。
* history 层（`GeometricCutoffRecord`）：surviving-domain 条件由 **terminal scalar 上界**生产
  （`subset_survivor_of_scalar_bound_P6ST3`：`R_ḡ ≤ L` 于 `B_ḡ(p, R')`、`R < R'`、
  `L` 低于 cut-neck 阈值 ⇒ `B̄_ḡ(p, R)` ⊆ surviving domain；
  树内 `subset_interior_old_of_scalar_upper_bound` + ball path-connected）；
  合同版 `nonempty_footprintData_of_scalarBall_P6ST3`。
  单 binder 版 `nonempty_footprintData_of_scalarBound_P6ST3`：ball 紧性由 old 紧**导出**
  （`isCompact_closedBall_of_subset_old_P6ST3`）。
剩余 binder（repair target，见 DELIVERIES G3 块）：只有 `hL`——terminal scalar 在 `B_ḡ(p, R')` 上 `≤ L`，
`R'√Q₊ > (17/16)c`，`L` 低于 cut-neck 阈值（terminal 时刻的 bounded-curvature-at-bounded-distance）+ `Q₊ > 0`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace MetricCutCapEvent

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ}

/-- slab 内趋于 `s` 的具体序列 `v n := s − (s − a)/(n + 2)`。 -/
theorem exists_slab_seq_P6ST3 (hlt : a < s) :
    ∃ v : ℕ → ℝ, (∀ n, v n ∈ Ioo a s) ∧ Tendsto v atTop (𝓝 s) := by
  have hsa : 0 < s - a := sub_pos.mpr hlt
  refine ⟨fun n => s - (s - a) / ((n : ℝ) + 2), fun n => ⟨?_, ?_⟩, ?_⟩
  · have h2 : (1 : ℝ) < (n : ℝ) + 2 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := div_lt_self hsa h2
    linarith
  · have : 0 < (s - a) / ((n : ℝ) + 2) := div_pos hsa (by positivity)
    linarith
  · have h : Tendsto (fun n : ℕ => (s - a) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h' := (tendsto_const_nhds (x := s)).sub h
    rwa [sub_zero] at h'

/-- **P-F（t 层）**：terminal closed ball `B̄_ḡ(p, R)` 紧、`R > (17/16)·c/√Q₊`（`Q₊ = R⁺(q) > 0`，
`c > 0`）⇒ `t → s⁻` eventually 物理 footprint `B̄_{g t}(p, c/√R_{g t}(p)) ⊆ val '' B_ḡ(p, R)`。 -/
theorem eventually_footprint_of_terminalBall_P6ST3 (E : MetricCutCapEvent P Q a s)
    (p : E.incoming.terminalRegularOpen) {q : Q.Carrier} (hcross : E.RegularCrossing p.val q)
    {c R : ℝ} (hc : 0 < c) (hQ : 0 < metricScalarAt E.outputMetric q)
    (hR : 17 / 16 * (c / Real.sqrt (metricScalarAt E.outputMetric q)) < R)
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R)) :
    ∀ᶠ t in 𝓝[<] s, riemannianClosedBallOf (I := I3) (E.incoming.flow.base.metric t) p.val
        (c / Real.sqrt (metricScalarAt (E.incoming.flow.base.metric t) p.val)) ⊆
      Subtype.val '' riemannianBallOf E.terminal.metric p R := by
  have : SigmaCompactSpace E.incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        E.incoming.terminalRegularOpen.isOpen)
  have hρ : 0 < c / Real.sqrt (metricScalarAt E.outputMetric q) :=
    div_pos hc (Real.sqrt_pos.mpr hQ)
  set ρ := c / Real.sqrt (metricScalarAt E.outputMetric q) with hρdef
  have hr0 : 0 < (17 / 16 * ρ + R) / 2 := by linarith
  have hrR : (17 / 16 * ρ + R) / 2 < R := by linarith
  have hρr : ρ < 16 * ((17 / 16 * ρ + R) / 2) / 17 := by linarith
  have hcptr : IsCompact (riemannianClosedBallOf E.terminal.metric p ((17 / 16 * ρ + R) / 2)) :=
    hcpt.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist E.terminal.metric p) continuous_const)
      (riemannianClosedBallOf_mono E.terminal.metric p hrR.le)
  have hball := E.terminal.eventually_riemannianBallOf_subset_image_closedBall p hr0 hcptr
  have hlim : Tendsto (fun t => c / Real.sqrt (metricScalarAt (E.incoming.flow.base.metric t)
      p.val)) (𝓝[<] s) (𝓝 ρ) := by
    have h := E.terminal.tendsto_metricScalarAt p
    rw [RegularCrossing.scalar_eq E hcross] at h
    exact tendsto_const_nhds.div h.sqrt (Real.sqrt_pos.mpr hQ).ne'
  filter_upwards [hball, hlim.eventually (gt_mem_nhds hρr)] with t ht hlt
  intro y hy
  have hy' : y ∈ riemannianBallOf (E.incoming.flow.base.metric t) p.val
      (16 * ((17 / 16 * ρ + R) / 2) / 17) :=
    lt_of_le_of_lt hy ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt)
  obtain ⟨x, hx, rfl⟩ := ht hy'
  exact ⟨x, lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hrR), rfl⟩

/-- **P-F 合同（event 层，PROVISIONAL）**：`RegularCrossing p q` + `Q₊ > 0` + crossing 点的定量 terminal
半径（`B̄_ḡ(p, R)` 紧、⊆ surviving domain、`R > (17/16)(8C1 + 3((ηout/2)⁻¹+7)√C2)/√Q₊`）+ 合同数值字段
⇒ STAB2 合同。`U`、`K`、`v`、`J`、全部字段构造。 -/
theorem nonempty_footprintData_of_terminalBall_P6ST3 {E : MetricCutCapEvent P Q a s}
    {p : E.incoming.terminalRegularOpen} {q : Q.Carrier} {ηout C1 C2 m R : ℝ} {k : ℕ}
    (hη0 : 0 < ηout) (hη : ηout < 1 / 11) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hk : max 2 ⌈ηout⁻¹⌉₊ ≤ k) (hcross : E.RegularCrossing p.val q)
    (hQ : 0 < metricScalarAt E.outputMetric q)
    (hR : 17 / 16 * ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt E.outputMetric q)) < R)
    (hcpt : IsCompact (riemannianClosedBallOf E.terminal.metric p R))
    (hsurv : riemannianClosedBallOf E.terminal.metric p R ⊆
      {x | x.val ∈ interior (Subtype.val '' E.old)}) :
    Nonempty (E.BufferedFootprintData_P6ST2 p.val q ηout C1 C2 m k) := by
  have : SigmaCompactSpace E.incoming.terminalRegularOpen :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        E.incoming.terminalRegularOpen.isOpen)
  have hc : 0 < 8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 := by
    have h1 : 0 < (ηout / 2)⁻¹ := inv_pos.mpr (by linarith)
    have h2 : 0 ≤ 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg C2)
    linarith
  obtain ⟨v, hv, hvt⟩ := exists_slab_seq_P6ST3 E.incoming.lt
  let U : Opens P.Carrier := ⟨Subtype.val '' riemannianBallOf E.terminal.metric p R,
    E.incoming.terminalRegularOpen.isOpen.isOpenMap_subtype_val _
      (isOpen_lt (continuous_riemannianEDist E.terminal.metric p) continuous_const)⟩
  have hUK : (U : Set P.Carrier) ⊆ Subtype.val '' riemannianClosedBallOf E.terminal.metric p R :=
    image_mono fun x hx => by
      change riemannianEDistOf E.terminal.metric p x ≤ ENNReal.ofReal R
      exact le_of_lt hx
  have hK : IsCompact (Subtype.val '' riemannianClosedBallOf E.terminal.metric p R) :=
    hcpt.image continuous_subtype_val
  have hKold : Subtype.val '' riemannianClosedBallOf E.terminal.metric p R ⊆
      interior (Subtype.val '' E.old) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hsurv hx
  exact nonempty_footprintData_of_crossing_P6ST3 hη hC1 hC2 hm0 hm1 hk hcross U hK hUK hKold
    v hv hvt hQ ((tendsto_nhdsLT_of_slab_P6ST3 hv hvt).eventually
      (E.eventually_footprint_of_terminalBall_P6ST3 p hcross hc hQ hR hcpt))

/-- old core 像的 `Ω`-preimage 紧（`old_compact`，`val '' old ⊆ Ω`）。 -/
theorem isCompact_preimage_old_P6ST3 (E : MetricCutCapEvent P Q a s) :
    IsCompact {x : E.incoming.terminalRegularOpen | x.val ∈ Subtype.val '' E.old} := by
  rw [Subtype.isCompact_iff]
  change IsCompact (Subtype.val '' (Subtype.val ⁻¹' (Subtype.val '' E.old)))
  rw [image_preimage_eq_of_subset (fun x hx =>
    ⟨⟨x, E.image_old_subset_terminalRegularOpen_P6ST3 hx⟩, rfl⟩)]
  exact E.old_compact.image continuous_subtype_val

/-- terminal closed ball 落在 old core 像内 ⇒ 紧（old 紧 + closed ball 闭）。 -/
theorem isCompact_closedBall_of_subset_old_P6ST3 (E : MetricCutCapEvent P Q a s)
    (p : E.incoming.terminalRegularOpen) {R : ℝ}
    (h : riemannianClosedBallOf E.terminal.metric p R ⊆
      {x | x.val ∈ Subtype.val '' E.old}) :
    IsCompact (riemannianClosedBallOf E.terminal.metric p R) :=
  E.isCompact_preimage_old_P6ST3.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist E.terminal.metric p) continuous_const) h

end MetricCutCapEvent

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {pp : CutoffParameters}

/-- **surviving domain ⇐ terminal scalar 上界**（history 层）：`R_ḡ ≤ L` 于 `B_ḡ(p, R')`（`L` 低于每个
cut-neck 阈值 `(1 − 4323δ_j)·scale_j`，`δ_j ≤ 1/2`）、`R < R'`、`p` 是 crossing 点 ⇒ `B̄_ḡ(p, R)` ⊆
surviving domain。树内 `subset_interior_old_of_scalar_upper_bound` +
`isPathConnected_riemannianBallOf`。 -/
theorem subset_survivor_of_scalar_bound_P6ST3 (Rc : GeometricCutoffRecord H i pp) {L R R' : ℝ}
    (hδ : ∀ j, Rc.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale)
    {p : (H.event i).incoming.terminalRegularOpen} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p.val q) (hRR : R < R') (hR' : 0 < R')
    (hL : ∀ z ∈ riemannianBallOf (H.event i).terminal.metric p R',
      metricScalarAt (H.event i).terminal.metric z ≤ L) :
    riemannianClosedBallOf (H.event i).terminal.metric p R ⊆
      {x | x.val ∈ interior (Subtype.val '' (H.event i).old)} := by
  have hpb : p ∈ riemannianBallOf (H.event i).terminal.metric p R' := by
    change riemannianEDistOf (H.event i).terminal.metric p p < ENNReal.ofReal R'
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hR'
  have hsub := Rc.subset_interior_old_of_scalar_upper_bound Rc.old_eq_retained hδ hscale
    (isPathConnected_riemannianBallOf (H.event i).terminal.metric p
      hR').isConnected.isPreconnected hL hpb hcross
  intro x hx
  exact hsub x (lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hR').mpr hRR))

/-- **P-F 合同（history 层，PROVISIONAL）**：`RegularCrossing p q` + `Q₊ > 0` + terminal ball 紧 +
terminal scalar 上界 `R_ḡ ≤ L` 于 `B_ḡ(p, R')`（`L` 低于 cut-neck 阈值）+ `R'` 的定量下界 ⇒ STAB2 合同。 -/
theorem nonempty_footprintData_of_scalarBall_P6ST3 (Rc : GeometricCutoffRecord H i pp)
    {ηout C1 C2 m L R R' : ℝ} {k : ℕ}
    (hη0 : 0 < ηout) (hη : ηout < 1 / 11) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hk : max 2 ⌈ηout⁻¹⌉₊ ≤ k)
    (hδ : ∀ j, Rc.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale)
    {p : (H.event i).incoming.terminalRegularOpen} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p.val q)
    (hQ : 0 < metricScalarAt (H.event i).outputMetric q)
    (hR : 17 / 16 * ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt (H.event i).outputMetric q)) < R) (hRR : R < R')
    (hcpt : IsCompact (riemannianClosedBallOf (H.event i).terminal.metric p R))
    (hL : ∀ z ∈ riemannianBallOf (H.event i).terminal.metric p R',
      metricScalarAt (H.event i).terminal.metric z ≤ L) :
    Nonempty ((H.event i).BufferedFootprintData_P6ST2 p.val q ηout C1 C2 m k) := by
  have hc : 0 < 8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 := by
    have h1 : 0 < (ηout / 2)⁻¹ := inv_pos.mpr (by linarith)
    have h2 : 0 ≤ 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg C2)
    linarith
  have hρ : 0 < (8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt (H.event i).outputMetric q) :=
    div_pos hc (Real.sqrt_pos.mpr hQ)
  have hR' : 0 < R' := by linarith
  exact MetricCutCapEvent.nonempty_footprintData_of_terminalBall_P6ST3 hη0 hη hC1 hC2 hm0 hm1 hk
    hcross hQ hR hcpt (Rc.subset_survivor_of_scalar_bound_P6ST3 hδ hscale hcross hRR hR' hL)

/-- **P-F 合同（history 层，单一 binder `hL`，PROVISIONAL）**：`RegularCrossing p q` + `Q₊ > 0` +
terminal scalar 上界 `R_ḡ ≤ L` 于 `B_ḡ(p, R')`（`R' > (17/16)(8C1 + 3((ηout/2)⁻¹+7)√C2)/√Q₊`，`L` 低于
cut-neck 阈值）⇒ STAB2 合同。ball 紧性**导出**（`B̄_ḡ(p, R) ⊆ B_ḡ(p, R') ⊆ interior (val '' old)`，old 紧）；
`R := ((17/16)ρ₊ + R')/2`。 -/
theorem nonempty_footprintData_of_scalarBound_P6ST3 (Rc : GeometricCutoffRecord H i pp)
    {ηout C1 C2 m L R' : ℝ} {k : ℕ}
    (hη0 : 0 < ηout) (hη : ηout < 1 / 11) (hC1 : 1 ≤ C1) (hC2 : 1 ≤ C2) (hm0 : 0 < m)
    (hm1 : m ≤ 1 / 2) (hk : max 2 ⌈ηout⁻¹⌉₊ ≤ k)
    (hδ : ∀ j, Rc.delta j ≤ 1 / 2)
    (hscale : ∀ j, L < (1 - 4323 * Rc.delta j) * (Rc.neck j).scale)
    {p : (H.event i).incoming.terminalRegularOpen} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p.val q)
    (hQ : 0 < metricScalarAt (H.event i).outputMetric q)
    (hR' : 17 / 16 * ((8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt (H.event i).outputMetric q)) < R')
    (hL : ∀ z ∈ riemannianBallOf (H.event i).terminal.metric p R',
      metricScalarAt (H.event i).terminal.metric z ≤ L) :
    Nonempty ((H.event i).BufferedFootprintData_P6ST2 p.val q ηout C1 C2 m k) := by
  have hc : 0 < 8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 := by
    have h1 : 0 < (ηout / 2)⁻¹ := inv_pos.mpr (by linarith)
    have h2 : 0 ≤ 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2 :=
      mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (Real.sqrt_nonneg C2)
    linarith
  set ρ := (8 * C1 + 3 * ((ηout / 2)⁻¹ + 7) * Real.sqrt C2) /
      Real.sqrt (metricScalarAt (H.event i).outputMetric q) with hρdef
  have hρ : 0 < ρ := div_pos hc (Real.sqrt_pos.mpr hQ)
  have hR0 : 17 / 16 * ρ < (17 / 16 * ρ + R') / 2 := by linarith
  have hRR : (17 / 16 * ρ + R') / 2 < R' := by linarith
  have hR'0 : 0 < R' := by linarith
  have hsurv := Rc.subset_survivor_of_scalar_bound_P6ST3 hδ hscale hcross hRR hR'0 hL
  have hcpt := (H.event i).isCompact_closedBall_of_subset_old_P6ST3 p
    (fun x hx => (interior_subset (s := Subtype.val '' (H.event i).old) (hsurv hx) :))
  exact Rc.nonempty_footprintData_of_scalarBall_P6ST3 hη0 hη hC1 hC2 hm0 hm1 hk hδ hscale hcross
    hQ hR0 hRR hcpt hL

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
