import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedSlabLocalizeP6ST4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HtransEventCXHT
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HbdLateP6HB
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MasterFlowCompatibility

/-!
# `hlocH` 的 producer：final slab 上的四型 transfer + 类型鸽笼（O-CH11-HLOCH G1，后缀 `_P6LH`）

`hbd_hor_late_P6HB` / `hbd_hor_jointPrefix_P6HP` 的 binder **`hlocH`**（horizon 支，坏点谓词 `¬∃ W η₁`，
**无 margins**）。G0 判定 (a) 可拼、0 binder，与 `hfoot` 不同病：
1. `0 < R_σ(y)` 是 hlocH 的显式前提（`Q_pos` obstruction 不出现）；
2. `σ = horizon` 时 `HasSpatialCanonicalTimeControl` 的时间合取 `v < horizon → …` 空真 ⇒
   `¬HSCTC ⟺ ¬∃ W (ε, C1, C2)`（chart）；
3. `(time last, horizon]` 上无 surgery：`J = id`，buffer = 整个紧流形（`finalSlab`，`MetricSmoothUpTo` 到端点），
   无 htube / footprint / 子列问题 ⇒ 对任意点量化无害；局部化点取 `z = y`。

结构：
* 逐点类型分类 = CX-HTRANS `alt_posOrRound_of_not_fineMarginGood_CXHT`（先入树，524480b050；不重证）：
  margin 层 `(ηN, max C1₁ 9 + √C2₁, 1200 C2₁, m)` 坏 ⇒ `η₁`-witness 的 alternative 是 positive 或 round
  （neck：STAB4 G1′；cap：CXCC）。
* `witness_of_frequently_positive_P6LH` / `witness_of_frequently_round_P6LH`：`J = id` 的
  whole-component transfer（STAB4 G3 / SCFIN G3 抽象版，`F = refl`，comparison 由 G5
  `closedSlab_eventually_comparison_P6ST4` 经 `MetricComparisonOn.mono` 限到 `comp(y)`），
  fine witness 只需 frequently。
* **`closedSlab_frequently_bad_P6LH`**：端点 `¬∃ W (ε, C1, C2)` ⇒ `t → σ⁻` frequently
  `¬∃ W (η₁, C1₁, C2₁)`（eventually margin-good 支用 G5 `spatialWitness_of_closedSlab_P6ST4`）。
* `closedSlab_localizedBad_noMargin_P6LH`：G5 kernel 的无 margin 坏点版（`LeftLocalizedBadAt_CXST`）。
* history adapter（`activeStage t = last` 的 HEq 运输 + `stageMetric_last_of_lt`）⇒
  **`hlocH_history_P6LH`**；**`hlocH_of_transfers_P6LH`**：结论 = hlocH 槽逐字。
  consumer：`hbd_hor_late_of_transfers_P6LH`。
数值前提（非 binder）：`0 < ε < 1/11`、`13000 η₁ ≤ neckModelTolerance (ε/2)`、
`η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊`、`2 (max C1₁ 9 + √C2₁) ≤ C1`、`1200000 C2₁ ≤ C2`
（D-15′ / CEIL3 §5 恰好给出，见 `P6HlocHD15P6LH`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function TopologicalSpace
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M] {g : SmoothRiemannianMetric I3 M} {x : M}

/-- witness 的半径常数 `1 ≤ C1`（`(√Q)⁻¹ ≤ radius ≤ C1/√Q`）。 -/
theorem one_le_radiusConstant_P6LH {eps C1 C2 : ℝ} (W : SpatialCanonicalWitness g eps C1 C2 x) :
    1 ≤ C1 := by
  have hsq : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr W.Q_pos
  have h := W.radius_lower.trans W.radius_upper
  rw [inv_eq_one_div, div_le_div_iff_of_pos_right hsq] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

namespace OrientedThreeStage.ClosedSlab

variable {P : OrientedThreeStage.{u}} {a σ : ℝ}

/-- **`J = id` positive 型 transfer（frequently）**：`t → σ⁻` frequently 的 positive 型
`(η₁, C1₁, C2₁)`-witness + 端点梯度界 ⇒ `(g σ, y)` 处 `(ε, C1, C2)` witness（chart）。 -/
theorem witness_of_frequently_positive_P6LH (S : P.ClosedSlab a σ) {y : P.Carrier}
    {ε η₁ C1₁ C2₁ C1 C2 : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (h1 : 2 * C1₁ ≤ C1) (h2 : 1000 * C2₁ ≤ C2)
    (hQ : 0 < metricScalarAt (S.flow.base.metric σ) y)
    (hgrad : ∀ w : TangentSpace ThreeModel y,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (S.flow.base.metric σ)) y w)| ≤
        C2 * metricScalarAt (S.flow.base.metric σ) y *
          Real.sqrt (metricScalarAt (S.flow.base.metric σ) y) *
          Real.sqrt ((S.flow.base.metric σ).inner y w w))
    (hpos : ∃ᶠ t in 𝓝[<] σ, ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ y,
      ∃ wh d sc, W.alternative = .positive wh d sc) :
    ∃ W : SpatialCanonicalWitness (S.flow.base.metric σ) ε C1 C2 y,
      W.capTubeHasNeckChart ε := by
  obtain ⟨δ, hδ, hδ1, hδθ, hδK, hδsec⟩ := exists_positiveDelta_P6ST4 hC2₁ (half_pos hQ)
  have hlow : ∀ᶠ t in 𝓝[<] σ, metricScalarAt (S.flow.base.metric σ) y / 2 ≤
      metricScalarAt (S.flow.base.metric t) y :=
    (S.tendsto_scalar_P6ST4 y).eventually (eventually_ge_nhds (half_lt_self hQ))
  obtain ⟨t, ⟨W, hW⟩, ⟨C⟩, hlo⟩ :=
    (hpos.and_eventually ((S.closedSlab_eventually_comparison_P6ST4 2 hδ).and hlow)).exists
  obtain ⟨W', hW', -, -⟩ := exists_positive_wholeComponent_transport_P6ST4 hC1₁ hC2₁
    (half_pos hQ) hδ.le hδ1 hδθ hδK hδsec (S.flow.base.metric t) y W hW hlo
    (S.flow.base.metric σ)
    (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier)
    le_rfl (fun _ _ => mem_univ _) (C.mono (subset_univ _) le_rfl le_rfl) hε0 hε1 h1 h2 hgrad
  exact ⟨W', hW'⟩

/-- **`J = id` round 型 transfer（frequently）**：`t → σ⁻` frequently 的 round 型 `(η₁, C1₁, C2₁)`-witness
+ 端点梯度界 ⇒ `(g σ, y)` 处 `(ε, C1, C2)` witness（`0 < η₁ < ε ≤ 1/2`、`η₁ ≤ bJS ⌈ε⁻¹⌉₊`）。 -/
theorem witness_of_frequently_round_P6LH (S : P.ClosedSlab a σ) {y : P.Carrier}
    {ε η₁ C1₁ C2₁ C1 C2 : ℝ} (hη0 : 0 < η₁) (hηlt : η₁ < ε) (hεhalf : ε ≤ 1 / 2)
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊) (hC1₁ : 1 ≤ C1₁) (hC2₁ : 1 ≤ C2₁)
    (h1 : 2 * C1₁ ≤ C1) (h2 : 1000 * C2₁ ≤ C2)
    (hQ : 0 < metricScalarAt (S.flow.base.metric σ) y)
    (hgrad : ∀ w : TangentSpace ThreeModel y,
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (metricScalarAt (S.flow.base.metric σ)) y w)| ≤
        C2 * metricScalarAt (S.flow.base.metric σ) y *
          Real.sqrt (metricScalarAt (S.flow.base.metric σ) y) *
          Real.sqrt ((S.flow.base.metric σ).inner y w w))
    (hround : ∃ᶠ t in 𝓝[<] σ, ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ y,
      ∃ wh R, W.alternative = .round wh R) :
    ∃ W : SpatialCanonicalWitness (S.flow.base.metric σ) ε C1 C2 y,
      W.capTubeHasNeckChart ε := by
  set order := ⌈ε⁻¹⌉₊ with horderdef
  set K := backgroundJetConstant ThreeSpace order * ((order : ℝ) + 1) with hKdef
  have hK : 0 < K := mul_pos (backgroundJetConstant_pos ThreeSpace order) (by positivity)
  set epsc := (ε - η₁) / K with hepscdef
  have hepsc : 0 < epsc := div_pos (by linarith) hK
  have hge : K * epsc ≤ ε - η₁ := by
    rw [hepscdef, mul_div_cancel₀ _ hK.ne']
  obtain ⟨δ, hδ, hδ1, hδθ, hδK, hδc⟩ :=
    exists_roundDelta_P6SF (max 2 order) hC2₁ (half_pos hQ) hepsc
  have hlow : ∀ᶠ t in 𝓝[<] σ, metricScalarAt (S.flow.base.metric σ) y / 2 ≤
      metricScalarAt (S.flow.base.metric t) y :=
    (S.tendsto_scalar_P6ST4 y).eventually (eventually_ge_nhds (half_lt_self hQ))
  obtain ⟨t, ⟨W, hW⟩, ⟨C⟩, hlo⟩ := (hround.and_eventually
    ((S.closedSlab_eventually_comparison_P6ST4 (max 2 order) hδ).and hlow)).exists
  have horderR : order ≤ ⌈η₁⁻¹⌉₊ := Nat.ceil_mono (inv_anti₀ hη0 hηlt.le)
  obtain ⟨W', hW', -, -⟩ := exists_round_wholeComponent_transport_P6SF hC1₁ hC2₁ (half_pos hQ)
    hδ.le hδ1 hδθ hδK hδc (S.flow.base.metric t) y W hW hlo (S.flow.base.metric σ)
    (DifferentialGeometry.PartialDiffeomorph.refl (I := ThreeModel) P.Carrier) (le_max_left _ _)
    (fun _ _ => mem_univ _) (C.mono (subset_univ _) le_rfl le_rfl) order horderR hη0 hsmall
    (le_max_right _ _) hge le_rfl hεhalf h1 h2 hgrad
  exact ⟨W', hW'⟩

/-- **类型鸽笼 + 四型 transfer（`J = id`）**：端点 `(g σ, y)` 无 `(ε, C1, C2)` witness（`R_σ(y) > 0`）⇒
`t → σ⁻` frequently `(g t, y)` 无 `(η₁, C1₁, C2₁)` witness（无 margins）。 -/
theorem closedSlab_frequently_bad_P6LH (S : P.ClosedSlab a σ) {y : P.Carrier}
    {ε η₁ C1₁ C2₁ C1 C2 : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 11)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊)
    (h1 : 2 * (max C1₁ 9 + Real.sqrt C2₁) ≤ C1) (h2 : 1200000 * C2₁ ≤ C2)
    (hQ : 0 < metricScalarAt (S.flow.base.metric σ) y)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric σ) ε C1 C2 y,
      W.capTubeHasNeckChart ε) :
    ∃ᶠ t in 𝓝[<] σ, ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ y,
      W.capTubeHasNeckChart η₁ := by
  intro hev
  have hgood : ∀ᶠ t in 𝓝[<] σ, ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ y,
      W.capTubeHasNeckChart η₁ := hev.mono fun _ hn => not_not.mp hn
  obtain ⟨t₀, W₀, -⟩ := hgood.exists
  have hη0 : 0 < η₁ := W₀.eps_pos
  have hC1₁ : 1 ≤ C1₁ := one_le_radiusConstant_P6LH W₀
  have hC2₁ : 1 ≤ C2₁ := W₀.one_le_comparison_constant
  have hNle : neckModelTolerance (ε / 2) ≤ ε / 2 := neckModelTolerance_le _
  have hηlt : η₁ < ε := by linarith
  have hsq : 0 ≤ Real.sqrt C2₁ := Real.sqrt_nonneg _
  have h1' : 2 * C1₁ ≤ C1 := by linarith [le_max_left C1₁ 9]
  have h2' : 1000 * C2₁ ≤ C2 := by linarith
  have hgrad := S.gradient_bound_of_eventually_P6ST4 y (by linarith : C2₁ ≤ C2) hQ.le fun u' => by
    filter_upwards [hgood] with t ht
    obtain ⟨W, -⟩ := ht
    exact W.gradient u'
  by_cases hMG : ∀ᶠ t in 𝓝[<] σ, ∃ W' : SpatialCanonicalWitness (S.flow.base.metric t)
      (neckModelTolerance (ε / 2)) (max C1₁ 9 + Real.sqrt C2₁) (1200 * C2₁) y,
      W'.capTubeHasNeckChart (neckModelTolerance (ε / 2)) ∧
        W'.HasMargins (min (1 / 20) (1 / (10 * C1₁ * Real.sqrt C2₁)))
  · have hden : 0 < 10 * C1₁ * Real.sqrt C2₁ :=
      mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith))
    exact hnot (S.spatialWitness_of_closedSlab_P6ST4 le_rfl hε
      (by linarith [le_max_right C1₁ 9]) (by linarith)
      (lt_min (by norm_num) (one_div_pos.mpr hden)) ((min_le_left _ _).trans (by norm_num))
      hQ hMG h1 (by linarith))
  · rw [not_eventually] at hMG
    have hwhole : ∃ᶠ t in 𝓝[<] σ,
        (∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ y,
          ∃ wh d sc, W.alternative = .positive wh d sc) ∨
        ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ y,
          ∃ wh R, W.alternative = .round wh R := by
      have hN : neckModelTolerance (ε / 2) < 1 / 11 := hNle.trans_lt (by linarith)
      refine (hMG.and_eventually hgood).mono fun t ht => ?_
      obtain ⟨hbad, W, hW⟩ := ht
      rcases alt_posOrRound_of_not_fineMarginGood_CXHT hη hN le_rfl le_rfl (min_le_left _ _)
        (min_le_right _ _) hbad W hW with hp | hr
      · exact Or.inl ⟨W, hp⟩
      · exact Or.inr ⟨W, hr⟩
    rcases frequently_or_distrib.mp hwhole with hp | hr
    · exact hnot (S.witness_of_frequently_positive_P6LH hε0 (by linarith) hC1₁ hC2₁ h1' h2' hQ
        hgrad hp)
    · exact hnot (S.witness_of_frequently_round_P6LH hη0 hηlt (by linarith) hsmall hC1₁ hC2₁ h1'
        h2' hQ hgrad hr)

/-- **`hlocH` 的无 margin 核（`J = id`）**：G5 `closedSlab_localizedBad_P6ST4` 的坏点谓词换成
`¬∃ W (η₁, C1₁, C2₁)`（无 margins）；局部化点 `z = y`，seed 点 `o` 不动。 -/
theorem closedSlab_localizedBad_noMargin_P6LH (S : P.ClosedSlab a σ) {y o : P.Carrier}
    {ε η₁ C1₁ C2₁ C1 C2 : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 11)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊)
    (h1 : 2 * (max C1₁ 9 + Real.sqrt C2₁) ≤ C1) (h2 : 1200000 * C2₁ ≤ C2)
    (hQ : 0 < metricScalarAt (S.flow.base.metric σ) y)
    (hnot : ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric σ) ε C1 C2 y,
      W.capTubeHasNeckChart ε) (L : ℝ) (hL : 0 < L) :
    LeftLocalizedBadAt_CXST (X := fun _ : ℝ => P.Carrier) (fun t : ℝ => t)
      (fun t z => ¬ ∃ W : SpatialCanonicalWitness (S.flow.base.metric t) η₁ C1₁ C2₁ z,
        W.capTubeHasNeckChart η₁)
      (fun t z => metricScalarAt (S.flow.base.metric t) z)
      (fun t z => riemannianEDistOf (I := ThreeModel) (S.flow.base.metric t) o z)
      σ (metricScalarAt (S.flow.base.metric σ) y) L
      (riemannianEDistOf (I := ThreeModel) (S.flow.base.metric σ) o y) := by
  intro δ hδ ε' hε'
  have hbad := S.closedSlab_frequently_bad_P6LH hε0 hε hη hsmall h1 h2 hQ hnot
  have hwin : ∀ᶠ t in 𝓝[<] σ, t ∈ Ioo (σ - δ) σ := Ioo_mem_nhdsLT (by linarith)
  have hratio : ∀ᶠ t in 𝓝[<] σ,
      |metricScalarAt (S.flow.base.metric t) y / metricScalarAt (S.flow.base.metric σ) y - 1| <
        ε' := by
    have h := (S.tendsto_scalar_P6ST4 y).div_const (metricScalarAt (S.flow.base.metric σ) y)
    rw [div_self hQ.ne'] at h
    exact (Metric.tendsto_nhds.mp h ε' hε').mono fun t ht => by
      rw [Real.dist_eq] at ht
      exact ht
  have hdist := S.closedSlab_eventually_edist_le_P6ST4 o y
    (by positivity : 0 < L / (4 * Real.sqrt (metricScalarAt (S.flow.base.metric σ) y)))
  obtain ⟨t, hb, ⟨hw, hr⟩, hdi⟩ := (hbad.and_eventually ((hwin.and hratio).and hdist)).exists
  exact ⟨t, y, hw.1, hw.2, hb, hr, hdi⟩

end OrientedThreeStage.ClosedSlab

namespace ObservedHistory

variable {H : ObservedHistory.{u}}

/-- `time last ≤ t` ⇒ `activeStage t = last`。 -/
theorem activeStage_eq_last_P6LH (t : Icc (0 : ℝ) H.horizon)
    (ht : H.time (Fin.last H.eventCount) ≤ (t : ℝ)) : H.activeStage t = Fin.last H.eventCount :=
  le_antisymm (Fin.le_last _) (H.le_activeStage t _ ht)

/-- final stage 运输：witness 存在性（stage 指标 `k = last`、点 HEq）。 -/
theorem final_witness_iff_P6LH (h : H.time (Fin.last H.eventCount) < H.horizon)
    {k : Fin (H.eventCount + 1)} (e : k = Fin.last H.eventCount) {τ : ℝ}
    {z : (H.stage k).Carrier} {z₀ : (H.stage (Fin.last H.eventCount)).Carrier} (hz : HEq z z₀)
    {η C1 C2 : ℝ} :
    (∃ W : SpatialCanonicalWitness (H.stageMetric k τ) η C1 C2 z, W.capTubeHasNeckChart η) ↔
      ∃ W : SpatialCanonicalWitness ((H.finalSlab h).flow.base.metric τ) η C1 C2 z₀,
        W.capTubeHasNeckChart η := by
  subst e
  obtain rfl := eq_of_heq hz
  rw [ObservedHistory.stageMetric_last_of_lt (h := h)]

/-- final stage 运输：scalar。 -/
theorem final_scalar_eq_P6LH (h : H.time (Fin.last H.eventCount) < H.horizon)
    {k : Fin (H.eventCount + 1)} (e : k = Fin.last H.eventCount) (τ : ℝ)
    {z : (H.stage k).Carrier} {z₀ : (H.stage (Fin.last H.eventCount)).Carrier}
    (hz : HEq z z₀) :
    metricScalarAt (H.stageMetric k τ) z =
      metricScalarAt ((H.finalSlab h).flow.base.metric τ) z₀ := by
  subst e
  obtain rfl := eq_of_heq hz
  rw [ObservedHistory.stageMetric_last_of_lt (h := h)]

/-- final stage 运输：距离。 -/
theorem final_edist_eq_P6LH (h : H.time (Fin.last H.eventCount) < H.horizon)
    {k : Fin (H.eventCount + 1)} (e : k = Fin.last H.eventCount) (τ : ℝ)
    {o z : (H.stage k).Carrier} {o₀ z₀ : (H.stage (Fin.last H.eventCount)).Carrier}
    (ho : HEq o o₀) (hz : HEq z z₀) :
    riemannianEDistOf (H.stageMetric k τ) o z =
      riemannianEDistOf (I := ThreeModel) ((H.finalSlab h).flow.base.metric τ) o₀ z₀ := by
  subst e
  obtain rfl := eq_of_heq ho
  obtain rfl := eq_of_heq hz
  rw [ObservedHistory.stageMetric_last_of_lt (h := h)]

/-- backward trace 的点只依赖 stage 指标。 -/
theorem trace_point_heq_P6LH {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (T : BackwardPointTrace H first last hle endpoint)
    {j k : Fin (H.eventCount + 1)} (e : j = k) (h1 : first ≤ j) (h2 : j ≤ last)
    (h1' : first ≤ k) (h2' : k ≤ last) : HEq (T.point j h1 h2) (T.point k h1' h2') := by
  subst e
  rfl

/-- **`hlocH` 的 history 层 producer**：任意 `ObservedHistory`，结论 = hlocH 槽内 `let H` 之后的部分逐字。 -/
theorem hlocH_history_P6LH (H : ObservedHistory.{u}) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {η₁ C1₁ C2₁ : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 11)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊)
    (h1 : 2 * (max C1₁ 9 + Real.sqrt C2₁) ≤ C1) (h2 : 1200000 * C2₁ ≤ C2) :
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            η₁ C1₁ C2₁ z, W.capTubeHasNeckChart η₁)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y) := by
  intro Tn aSeed haT pT seedTrace σ hsT has y hlast hσ haσ hR hbad L hL
  have hσle : H.time (Fin.last H.eventCount) ≤ (σ : ℝ) := by
    rw [hσ]
    exact H.time_le_horizon
  have hσj : H.activeStage σ = Fin.last H.eventCount := activeStage_eq_last_P6LH σ hσle
  obtain ⟨y₀, hy⟩ : ∃ y₀ : (H.stage (Fin.last H.eventCount)).Carrier, HEq y y₀ :=
    ⟨_, (cast_heq (congrArg (fun k => (H.stage k).Carrier) hσj) y).symm⟩
  obtain ⟨o₀, ho⟩ : ∃ o₀ : (H.stage (Fin.last H.eventCount)).Carrier,
      HEq (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
        (H.activeStage_mono hsT)) o₀ :=
    ⟨_, (cast_heq (congrArg (fun k => (H.stage k).Carrier) hσj) _).symm⟩
  have hReq := final_scalar_eq_P6LH hlast hσj (σ : ℝ) hy
  have hDeq := final_edist_eq_P6LH hlast hσj (σ : ℝ) ho hy
  have hQ : 0 < metricScalarAt ((H.finalSlab hlast).flow.base.metric σ) y₀ := by
    rw [← hReq]
    exact hR
  have hnot : ¬ ∃ W : SpatialCanonicalWitness ((H.finalSlab hlast).flow.base.metric σ) ε C1 C2 y₀,
      W.capTubeHasNeckChart ε := by
    intro hW
    refine hbad ⟨(final_witness_iff_P6LH (τ := (σ : ℝ)) hlast hσj hy).mpr hW, fun _ hlt => ?_⟩
    rw [hσ] at hlt
    exact absurd hlt (lt_irrefl _)
  have eR : metricScalarAt ((H.finalSlab hlast).flow.base.metric (σ : ℝ)) y₀ =
      metricScalarAt ((H.finalSlab hlast).flow.base.metric H.horizon) y₀ := by
    rw [hσ]
  have eD : riemannianEDistOf (I := ThreeModel) ((H.finalSlab hlast).flow.base.metric (σ : ℝ))
      o₀ y₀ = riemannianEDistOf (I := ThreeModel)
        ((H.finalSlab hlast).flow.base.metric H.horizon) o₀ y₀ := by
    rw [hσ]
  have eW : (∃ W : SpatialCanonicalWitness ((H.finalSlab hlast).flow.base.metric (σ : ℝ))
      ε C1 C2 y₀, W.capTubeHasNeckChart ε) ↔
      ∃ W : SpatialCanonicalWitness ((H.finalSlab hlast).flow.base.metric H.horizon)
        ε C1 C2 y₀, W.capTubeHasNeckChart ε := by
    rw [hσ]
  have hQ' : 0 < metricScalarAt ((H.finalSlab hlast).flow.base.metric H.horizon) y₀ := by
    rw [← eR]
    exact hQ
  have hK := (H.finalSlab hlast).closedSlab_localizedBad_noMargin_P6LH (o := o₀) hε0 hε hη
    hsmall h1 h2 hQ' (fun hW => hnot (eW.mpr hW)) L hL
  intro δ hδ ε' hε'
  have haσ' : (aSeed : ℝ) < σ := haσ
  have hmσ : max (H.time (Fin.last H.eventCount)) (aSeed : ℝ) < σ :=
    max_lt (hlast.trans_eq hσ.symm) haσ'
  obtain ⟨t, z, ht1, ht2, hb, hr, hd⟩ :=
    hK (min δ (σ - max (H.time (Fin.last H.eventCount)) (aSeed : ℝ)))
      (lt_min hδ (by linarith)) ε' hε'
  beta_reduce at ht1 ht2 hr hd
  rw [← eR] at hr hd
  rw [← eD] at hd
  have ht1' : (σ : ℝ) - min δ ((σ : ℝ) - max (H.time (Fin.last H.eventCount)) (aSeed : ℝ)) < t :=
    by linarith
  have ht2' : t < σ := by linarith
  have htm : max (H.time (Fin.last H.eventCount)) (aSeed : ℝ) < t := by
    linarith [min_le_right δ ((σ : ℝ) - max (H.time (Fin.last H.eventCount)) (aSeed : ℝ))]
  have htl : H.time (Fin.last H.eventCount) < t := (le_max_left _ _).trans_lt htm
  have hta : (aSeed : ℝ) < t := (le_max_right _ _).trans_lt htm
  have ht0 : 0 ≤ t := (H.time_nonneg _).trans htl.le
  have hth : t ≤ H.horizon := (ht2'.trans_eq hσ).le
  obtain ⟨tt, htt⟩ : ∃ tt : Icc (0 : ℝ) H.horizon, (tt : ℝ) = t := ⟨⟨t, ht0, hth⟩, rfl⟩
  subst htt
  have httj : H.activeStage tt = Fin.last H.eventCount := activeStage_eq_last_P6LH tt htl.le
  obtain ⟨z', hz⟩ : ∃ z' : (H.stageAt tt).Carrier, HEq z' z :=
    ⟨_, cast_heq (congrArg (fun k => (H.stage k).Carrier) httj.symm) z⟩
  have hcond : aSeed ≤ tt ∧ tt ≤ Tn := ⟨hta.le, (show tt ≤ σ from ht2'.le).trans hsT⟩
  have hpt : HEq (seedTrace.point (H.activeStage tt) (H.activeStage_mono hcond.1)
      (H.activeStage_mono hcond.2)) o₀ :=
    (trace_point_heq_P6LH seedTrace (httj.trans hσj.symm) _ _ _ _).trans ho
  have hWiff := final_witness_iff_P6LH (η := η₁) (C1 := C1₁) (C2 := C2₁) (τ := (tt : ℝ)) hlast
    httj hz
  have hRt := final_scalar_eq_P6LH hlast httj (tt : ℝ) hz
  have hDt := final_edist_eq_P6LH hlast httj (tt : ℝ) hpt hz
  refine ⟨tt, z', ?_, ht2', fun hW => hb (hWiff.mp hW), ?_, ?_⟩
  · linarith [min_le_left δ ((σ : ℝ) - max (H.time (Fin.last H.eventCount)) (aSeed : ℝ))]
  · beta_reduce
    rw [hRt, hReq]
    exact hr
  · beta_reduce
    rw [dite_eq_left hcond, hDt, hDeq, hReq]
    exact hd

end ObservedHistory

/-- **G1：`hlocH` 的 producer**：结论 = `hbd_hor_late_P6HB` / `hbd_hor_jointPrefix_P6HP` 的 `hlocH` 槽逐字；
0 binder，只有数值前提（D-15′ 下由 CEIL3 §5 给出，见 `P6HlocHD15P6LH`）。 -/
theorem hlocH_of_transfers_P6LH {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {η₁ C1₁ C2₁ : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 11)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊)
    (h1 : 2 * (max C1₁ 9 + Real.sqrt C2₁) ≤ C1) (h2 : 1200000 * C2₁ ≤ C2) :
    ∀ (nn : ℕ) (cc : ℝ) (hcc : 0 < cc),
      let H : ObservedHistory.{u} := ((F.tower.history nn).rescale_P6N cc hcc).toHistory
      ∀ (Tn aSeed : Icc (0 : ℝ) H.horizon) (haT : aSeed ≤ Tn) (pT : (H.stageAt Tn).Carrier)
        (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
          (H.activeStage_mono haT) pT)
        (σ : Icc (0 : ℝ) H.horizon) (hsT : σ ≤ Tn) (has : aSeed ≤ σ)
        (y : (H.stageAt σ).Carrier),
        H.time (Fin.last H.eventCount) < H.horizon → (σ : ℝ) = H.horizon → aSeed < σ →
        0 < metricScalarAt (H.stageMetric (H.activeStage σ) σ) y →
        ¬ H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime σ y →
        ∀ L : ℝ, 0 < L →
        LeftLocalizedBadAt_CXST (fun t : Icc (0 : ℝ) H.horizon => (t : ℝ))
          (fun t z => ¬ ∃ W : SpatialCanonicalWitness (H.stageMetric (H.activeStage t) t)
            η₁ C1₁ C2₁ z, W.capTubeHasNeckChart η₁)
          (fun t z => metricScalarAt (H.stageMetric (H.activeStage t) t) z)
          (fun t z => if h : aSeed ≤ t ∧ t ≤ Tn then
            riemannianEDistOf (H.stageMetric (H.activeStage t) t)
              (seedTrace.point (H.activeStage t) (H.activeStage_mono h.1)
                (H.activeStage_mono h.2)) z
            else 0)
          σ (metricScalarAt (H.stageMetric (H.activeStage σ) σ) y) L
          (riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
            (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
              (H.activeStage_mono hsT)) y) := by
  intro nn cc hcc
  exact ObservedHistory.hlocH_history_P6LH _ hε0 hε hη hsmall h1 h2

/-- **consumer**：`hbd_hor_late_P6HB` 的 `hlocH` 槽由 `hlocH_of_transfers_P6LH` 付清
（只剩 `hrerunF8`）；`hrerunF8` 与结论由 build-logs/scratch/O-CH11-HLOCH/gen_consumer.py
从 `P6HbdLateP6HB.lean:631–701` 逐字抽取。 -/
theorem hbd_hor_late_of_transfers_P6LH {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {η₁ C1₁ C2₁ : ℝ} {Ctime₁ : ℝ≥0} (hε0 : 0 < ε) (hε : ε < 1 / 11)
    (hη : 13000 * η₁ ≤ neckModelTolerance (ε / 2))
    (hsmall : η₁ ≤ backgroundJetSmallness ThreeSpace ⌈ε⁻¹⌉₊)
    (h1 : 2 * (max C1₁ 9 + Real.sqrt C2₁) ≤ C1) (h2 : 1200000 * C2₁ ≤ C2)
    (hrerunF8 :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl η₁ C1₁ C2₁ Ctime₁ (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).horizon) → False) :
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (Kh k).horizon ∧
          (σ k : ℝ) = (Kh k).horizon) → False :=
  ObservedHistory.hbd_hor_late_P6HB (Ctime₁ := Ctime₁)
    (hlocH_of_transfers_P6LH F hε0 hε hη hsmall h1 h2) hrerunF8

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
