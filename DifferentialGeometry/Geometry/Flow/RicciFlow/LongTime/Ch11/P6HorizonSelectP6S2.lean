import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HorizonExtP6S2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionGoodP6M

/-!
# (H) 视界类 G1b：`hgood` 拆分 + 旧视界坏点序列 ⇒ 扩张 history 的内点坏点（S-CH11-P6BND2，`_P6S2`）

R-C11-5 D-12 (ii)(iii)(iv)，接 `P6HorizonExtP6S2`（(i) 严格扩张 + 闭端点识别 + 旧坏点 ⇒ 新坏点）。

* `exists_strictMono_noHorizon_P6S2`：selection 的坏点 `σ n < horizon` 时位置四分只剩三类
  （event 内部 / final 内部 / stage 时刻）；视界类消失。stage 时刻类（`σ = time m`，即旧 history
  在 `σ_n` 处恰有 surgery seam）仍转 (S)——`exists_strictMono_interior_or_boundary_P6S` 的第三类 /
  `not_exists_witness_of_boundary_class_P6S`。
* **(iii)** `hwit_hderiv_of_selection_split_P6S2`：`hwit_hderiv_of_selection_P6M` 的 `hgood`（`v ≤ σ`
  处完整 Good）拆成 `hgoodS`（`v ≤ σ`，只要 spatial witness）与 `hgoodF`（仅 `v < σ`，完整 Good，含时间导数
  分量）。`v = σ` 处不再要时间导数——扩张 history 里 `σ_n` 是内点，该分量非空，旧 history 的 selection 给不出。
  `hwit` 只用 `hgoodS`，`hderiv` 只用 `hgoodF`；`hanchor0` 不在此链内（K-route `…_pre841_P6M` 里本就是
  独立 binder，由 `CrossingDepthExtension_P6L(2)` 供给），故"hanchor0 保留为独立输入"自动成立。`example`
  对原 `hwit_hderiv_of_selection_P6M` 的结论逐字对齐（原 hgood ⇒ 拆分前提）。
* **(ii)(iv)** `selection_of_horizon_bad_sequence_P6S2`：旧 history `Ko` 的坏点序列（任意时刻 `≤ Ko.horizon`，
  含视界）+ 严格扩张 `Rext`/`hext` ⇒ `Kh := 扩张 history` 上的 `selection_of_bad_sequence_P6X` 输出，外加
  `∀ n, σ n < (Kh n).horizon`。其余全部数据（records / native 常数 / κ / derivative window / seed）在
  `Kh n = history (n+1)` 上**原生**给出（K 层数据对每个 tower history 供给，`n ↦ n+1` 只放宽
  `n+1 ≤ …` 型下界）——不需要把旧侧 selection 数据逐项搬运（旧侧 selection 在视界处给不出完整 Good，
  搬运路线要重证整条 chain 与 trace / `Pre841Data` 搬运）。
* **(iv)** `false_of_selection_ext_P6S2` / `false_of_selection_horizon_P6S2`：旧侧（任意时刻 / 视界点）
  `¬Good_K` 序列 + 扩张 + **`hclose`**（`K'` 上「内点时刻坏点序列 ⇒ False」，即 K-route / 三类主形在扩张
  history 上的应用，由 P6 pipeline 供给）⇒ False。视界版经 `not_hasSpatialCanonicalTimeControl_iff_of_
  boundary_P6S` 把 `¬Good_K` 化为 `¬ spatial witness`，再 `ext_not_good_of_not_spatial_P6S2` 拉到 `K'`
  ——即"把 spatial witness 拉回旧 horizon 与 ¬spatial 矛盾"。tower 版 `…_tower_P6S2` 用 `T.successor n`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- 位置四分在 `σ < horizon` 时只剩三类（视界类消失）。 -/
theorem exists_position_of_lt_horizon_P6S2 (H : ObservedHistory.{u})
    (σ : Icc (0 : ℝ) H.horizon) (hlt : (σ : ℝ) < H.horizon) :
    (∃ j : Fin H.eventCount, H.time j.castSucc < (σ : ℝ) ∧ (σ : ℝ) < H.time j.succ) ∨
    (H.time (Fin.last H.eventCount) < (σ : ℝ) ∧ (σ : ℝ) < H.horizon) ∨
    (∃ m : Fin (H.eventCount + 1), (σ : ℝ) = H.time m) := by
  rcases H.exists_position_P6S σ with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h hlt.ne

/-- **子列版（视界类消失）**：坏点序列 `σ n < horizon` ⇒ 有子列整条落在 event 内部 / final 内部 /
stage 时刻三类之一。 -/
theorem exists_strictMono_noHorizon_P6S2 {Kh : ℕ → ObservedHistory.{u}}
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (hlt : ∀ n, (σ n : ℝ) < (Kh n).horizon) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ((∀ n, ∃ j : Fin (Kh (ψ n)).eventCount, (Kh (ψ n)).time j.castSucc < (σ (ψ n) : ℝ) ∧
          (σ (ψ n) : ℝ) < (Kh (ψ n)).time j.succ) ∨
        (∀ n, (Kh (ψ n)).time (Fin.last (Kh (ψ n)).eventCount) < (σ (ψ n) : ℝ) ∧
          (σ (ψ n) : ℝ) < (Kh (ψ n)).horizon) ∨
        (∀ n, ∃ m : Fin ((Kh (ψ n)).eventCount + 1), (σ (ψ n) : ℝ) = (Kh (ψ n)).time m)) := by
  obtain ⟨ψ, hψ, h | h | h | h⟩ := exists_strictMono_position_P6S σ
  · exact ⟨ψ, hψ, Or.inl h⟩
  · exact ⟨ψ, hψ, Or.inr (Or.inl h)⟩
  · exact ⟨ψ, hψ, Or.inr (Or.inr h)⟩
  · exact absurd (h 0) (hlt (ψ 0)).ne

/-- **(iii) `hgood` 拆分版**：`hwit_hderiv_of_selection_P6M` 的 `hgood`（`v ≤ σ` 完整 Good）拆成
`hgoodS`（`v ≤ σ`，spatial witness）与 `hgoodF`（`v < σ`，完整 Good）；结论逐字不变。 -/
theorem hwit_hderiv_of_selection_split_P6S2 {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgoodS : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2' z,
          W.capTubeHasNeckChart eps)
    (hgoodF : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (v : ℝ) < σ n → (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) ∧
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2)  := by
  refine ⟨fun D T hD hT => ?_, fun D T hD hT => ?_⟩
  · filter_upwards [eventually_window_scale_le_P6N hL T D, hwin T hT, hdist D T hD hT]
      with n hn hw hd
    intro x hx v hvt hTv _ _ tr hq
    have hav : aSeed n ≤ v := hw.trans hTv
    have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - T / R n :=
      sub_le_sub_left (div_le_div_of_nonneg_right hn.1 (hR n).le) _
    exact hgoodS n v hav hvt (hLθ.trans hTv) _ (hd x hx v hav hvt hTv tr) hq.le
  · filter_upwards [eventually_window_scale_le_P6N hL T D, hwin T hT, hdist D T hD hT]
      with n hn hw hd
    intro x hx v hvt hTv hvσ hage tr hq
    have hav : aSeed n ≤ v := hw.trans hTv
    have hLθ : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - T / R n :=
      sub_le_sub_left (div_le_div_of_nonneg_right hn.1 (hR n).le) _
    exact (hgoodF n v hav hvt hvσ (hLθ.trans hTv) _ (hd x hx v hav hvt hTv tr) hq.le).2 hage
      (hvσ.trans_le (σ n).2.2)

/-- **consumer**：原 `hwit_hderiv_of_selection_P6M` 的前提 `hgood` ⇒ 拆分前提（`.1` / 限制到 `v < σ`），
结论逐字对齐。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n))) :
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1' C2'
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps) ∧
    (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
      (v : ℝ) < σ n → (Kh n).time ((Kh n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
        ((Kh n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
          (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) →
        |derivWithin (fun v' => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v')
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)))
          (Iic (v : ℝ)) v| ≤
          Ctime' * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v)
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) ^ 2)  :=
  hwit_hderiv_of_selection_split_P6S2 Kh Tn aSeed σ haT hsT has p seedTrace y R L hR hL
    (fun n v hav hvs h z hd hq => (hgood n v hav hvs h z hd hq).1)
    (fun n v hav hvs _ h z hd hq => hgood n v hav hvs h z hd hq) hwin hdist

/-- **(ii)(iv) 旧坏点序列 ⇒ 扩张 history 的 selection 输出**：旧 history `Ko` 的坏点（`To n` 任意时刻，
含视界）经 `Rext`/`hext` 变成 `Kh` 的坏点（`ext_not_good_ext_of_not_good_P6S2`），喂
`selection_of_bad_sequence_P6X`；输出多一条 `∀ n, σ n < (Kh n).horizon`（`σ n ≤ Tn n ≤ ae n < horizon`）。
除 `hbad` 外所有前提与 P6X 逐字相同，原生在 `Kh` 上。 -/
theorem selection_of_horizon_bad_sequence_P6S2 {Kh Ko : ℕ → ObservedHistory.{u}}
    {ae : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
    (Rext : ∀ n, ((Kh n).restrict (ae n)).SamePresentation (Ko n))
    (hext : ∀ n, (ae n : ℝ) < (Kh n).horizon) (q : ℕ → CutoffParameters)
    {eps C1 C2 C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    {Ctime Ctime' : ℝ≥0} (hCtime : Ctime ≤ Ctime')
    (hanti : ∀ n, AntitoneOn (q n).neckRadius (Ici 0))
    (hcanonical : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      ∃ W : SpatialCanonicalWitness ((Kh n).stageMetric ((Kh n).activeStage v) v) eps C1 C2 z,
        W.capTubeHasNeckChart eps)
    (hderivative : ∀ n (v : Icc (0 : ℝ) (Kh n).horizon) (z : ((Kh n).stageAt v).Carrier),
      (Kh n).time ((Kh n).activeStage v) < (v : ℝ) → (v : ℝ) < (Kh n).horizon →
      ((q n).neckRadius v ^ 2)⁻¹ < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
      |derivWithin (fun t => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) t) z)
        (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z ^ 2)
    (Tn : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (r : ℕ → ℝ) (A : ℝ) (hr : ∀ n, 0 < r n) (hA : 0 < A)
    (aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (haSeed : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (x : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (hx : ∀ n, x n ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n))
      (pT n) (A * r n))
    (hR : ∀ n, 0 < metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n))
    (To : ∀ n, Icc (0 : ℝ) (Ko n).horizon) (xo : ∀ n, ((Ko n).stageAt (To n)).Carrier)
    (hbo : ∀ n, ¬ (Ko n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (To n) (xo n))
    (hTT : ∀ n, (Tn n : ℝ) = To n) (hxx : ∀ n, HEq (xo n) (x n))
    (hdiv : Tendsto (fun n => metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n))
      (Tn n)) (x n) * r n ^ 2) atTop atTop) :
    ∃ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n) (L : ℕ → ℝ),
      (∀ n, (σ n : ℝ) < (Kh n).horizon) ∧
      (∀ n, R n = metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)) ∧
      (∀ n, 0 < R n) ∧
      (∀ n, metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (x n) ≤
        R n) ∧
      (∀ n, R n ≤ ((q n).neckRadius (Tn n) ^ 2)⁻¹) ∧
      Tendsto L atTop atTop ∧
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (σ n) (y n)) ∧
      (∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
        ∀ z : ((Kh n).stageAt v).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
              ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
                ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
          (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) ∧
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) - T / R n) ∧
      Tendsto (fun n => R n * ((σ n : ℝ) - ((Tn n : ℝ) - r n ^ 2 / 2))) atTop atTop ∧
      Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop  := by
  have hbad : ∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' (Tn n) (x n) :=
    fun n => ext_not_good_ext_of_not_good_P6S2 (Rext n) (To n) (Tn n) (hTT n) (hxx n) (hbo n)
  obtain ⟨σ, y, Rr, hsT, has, L, h⟩ := selection_of_bad_sequence_P6X q hC1 hC2 hCtime hanti
    hcanonical hderivative Tn pT r A hr hA aSeed haT haSeed seedTrace x hx hR hbad hdiv
  refine ⟨σ, y, Rr, hsT, has, L, fun n => ?_, h⟩
  have hTa : (Tn n : ℝ) ≤ ae n := by
    rw [hTT n]
    exact (To n).2.2.trans (Rext n).horizon_eq.symm.le
  exact lt_of_le_of_lt ((hsT n).trans hTa) (hext n)

/-- **(iv) 装配（任意旧时刻）**：旧 history `Ko` 上任意时刻 `σo ≤ Ko.horizon` 的 `¬Good` 序列，
经严格扩张 `Rext`/`hext` 变成 `Kh` 上的内点坏点序列（`σ' < horizon`），再交给 `hclose`
（`Kh` 上「内点坏点序列 ⇒ False」，即 K-route / 三类主形在扩张 history 上的应用）。 -/
theorem false_of_selection_ext_P6S2 {Ko Kh : ℕ → ObservedHistory.{u}}
    {ae : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
    (Rext : ∀ n, ((Kh n).restrict (ae n)).SamePresentation (Ko n))
    (hext : ∀ n, (ae n : ℝ) < (Kh n).horizon) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (σo : ∀ n, Icc (0 : ℝ) (Ko n).horizon) (yo : ∀ n, ((Ko n).stageAt (σo n)).Carrier)
    (hselo : ∀ n, ¬ (Ko n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (σo n) (yo n))
    (hclose : ∀ (σ' : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y' : ∀ n, ((Kh n).stageAt (σ' n)).Carrier), (∀ n, (σ' n : ℝ) < (Kh n).horizon) →
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (σ' n) (y' n)) → False) :
    False := by
  let σ' : ∀ n, Icc (0 : ℝ) (Kh n).horizon := fun n =>
    ⟨σo n, (σo n).2.1, (σo n).2.2.trans (ext_horizon_le_P6S2 (Rext n))⟩
  choose y' hy' using fun n => ext_exists_point_P6S2 (Rext n) (σo n) (σ' n) rfl (yo n)
  exact hclose σ' y' (fun n => ext_lt_horizon_P6S2 (Rext n) (hext n) (σo n) (σ' n) rfl)
    (fun n => ext_not_good_ext_of_not_good_P6S2 (Rext n) (σo n) (σ' n) rfl (hy' n) (hselo n))

/-- **(iv) 视界类装配**：旧 history `Ko` 的坏点恰在视界 `σo n = (Ko n).horizon`。视界点上
`HasSpatialCanonicalTimeControl` 的时间导数分量空真，`¬Good_Ko` 即 `¬ spatial witness`
（`not_hasSpatialCanonicalTimeControl_iff_of_boundary_P6S`）；该 `¬ spatial` 经 `Rext` 拉到
`Kh` 的同一点（`ext_not_good_of_not_spatial_P6S2`），而 `Kh` 里它是内点（`hext`），交给 `hclose`。 -/
theorem false_of_selection_horizon_P6S2 {Ko Kh : ℕ → ObservedHistory.{u}}
    {ae : ∀ n, Icc (0 : ℝ) (Kh n).horizon}
    (Rext : ∀ n, ((Kh n).restrict (ae n)).SamePresentation (Ko n))
    (hext : ∀ n, (ae n : ℝ) < (Kh n).horizon) {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (σo : ∀ n, Icc (0 : ℝ) (Ko n).horizon) (yo : ∀ n, ((Ko n).stageAt (σo n)).Carrier)
    (hhor : ∀ n, (σo n : ℝ) = (Ko n).horizon)
    (hselo : ∀ n, ¬ (Ko n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (σo n) (yo n))
    (hclose : ∀ (σ' : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (y' : ∀ n, ((Kh n).stageAt (σ' n)).Carrier), (∀ n, (σ' n : ℝ) < (Kh n).horizon) →
      (∀ n, ¬ (Kh n).HasSpatialCanonicalTimeControl eps C1 C2 Ctime (σ' n) (y' n)) → False) :
    False := by
  let σ' : ∀ n, Icc (0 : ℝ) (Kh n).horizon := fun n =>
    ⟨σo n, (σo n).2.1, (σo n).2.2.trans (ext_horizon_le_P6S2 (Rext n))⟩
  choose y' hy' using fun n => ext_exists_point_P6S2 (Rext n) (σo n) (σ' n) rfl (yo n)
  have hsp : ∀ n, ¬ ∃ W : SpatialCanonicalWitness ((Ko n).stageMetric ((Ko n).activeStage (σo n))
      (σo n)) eps C1 C2 (yo n), W.capTubeHasNeckChart eps := fun n =>
    (not_hasSpatialCanonicalTimeControl_iff_of_boundary_P6S (Or.inr (hhor n))).mp (hselo n)
  exact hclose σ' y' (fun n => ext_lt_horizon_P6S2 (Rext n) (hext n) (σo n) (σ' n) rfl)
    (fun n => ext_not_good_of_not_spatial_P6S2 (Rext n) (σo n) (σ' n) rfl (hy' n) (hsp n))

section Tower

variable {P : OrientedThreeStage.{u}} {g : P.Metric} (T : RetainedCoreObservationTower P g)

/-- **tower 版（视界类）**：`Ko n := history n`、`Kh n := history (n+1)`、`Rext n := T.successor n`。 -/
theorem false_of_selection_horizon_tower_P6S2 {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (σo : ∀ n, Icc (0 : ℝ) (T.history n).toHistory.horizon)
    (yo : ∀ n, ((T.history n).toHistory.stageAt (σo n)).Carrier)
    (hhor : ∀ n, (σo n : ℝ) = (T.history n).toHistory.horizon)
    (hselo : ∀ n, ¬ (T.history n).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime
      (σo n) (yo n))
    (hclose : ∀ (σ' : ∀ n, Icc (0 : ℝ) (T.history (n + 1)).toHistory.horizon)
      (y' : ∀ n, ((T.history (n + 1)).toHistory.stageAt (σ' n)).Carrier),
      (∀ n, (σ' n : ℝ) < (T.history (n + 1)).toHistory.horizon) →
      (∀ n, ¬ (T.history (n + 1)).toHistory.HasSpatialCanonicalTimeControl eps C1 C2 Ctime
        (σ' n) (y' n)) → False) :
    False :=
  false_of_selection_horizon_P6S2 (fun n => T.successor n) (tower_ext_lt_horizon_P6S2 T) σo yo hhor
    hselo hclose

end Tower

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
