import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceProtectionCXSP

set_option autoImplicit false

/-!
# born cap 尺度在 seed 归一化下有界（O-CH11-SPINE-B G1b，后缀 `_C11SP`）

对 Codex native 交接"最实质数值缺口"的直接回应：`StandardCap/WindowPersistence:145–161`
的 `q₀ ≤ Cbirth·qcap` 是"在 qcap 归一化下持续整个 cap window"的 ODE 门槛；本页说明在
**seed 归一化**（`M = m·Q`）下不需要它。

**定理 `exists_bornCap_scale_le_four_mul_C11SP`**：沿实际 `BackwardPointTrace`，若终端标量
`≤ M`、且只在标量 `≥ q`（任意 `q ≤ M`，即 seed 门槛 `K1/r²`，与 qcap 无关）的点上有
`HasSpatialCanonicalTimeControl`（时间窗 `Ctime·M·(t − s) ≤ 1/2`），则 trace 在 `s` 之后
任一 birth `e.succ` 处若落在该事件 static cap 的内窗 `‖z‖ ≤ transitionEnd + 10`，必有
`neck.scale ≤ 4 M`。证明 = G19 `exists_trace_protection_of_good_suffix_CXSP` 的逆否
（first-exit 给 birth 处 `R ≤ 2M`，cap window 标量下界 `C11G` 给矛盾）。

**推论 `bornCap_jets_normalized_le_C11SP`**：G63 的 born-cap jets
`curvDerivNormSq j ≤ C_j² · qcap^{j+2}` 在 `qcap ≤ 4 m Q` 下变成
`≤ C_j² (4m)^{j+2} Q^{j+2}`，即 `Q` 归一化 jets 只依赖 `(C_j, m)`；`qcap/Q → 0` 只会更小。

**边界（诚实）**：`hgood`（沿 trace 的 TimeCore 时间控制）仍是输入——native 链要用
TimeCore 在 moving seed footprint 上付它，这需要 native 下的 surgery distance control
（guard 链在此花了 `nr ≤ r`；见 `build-logs/scratch/O-CH11-SPINE-B/native-route.md` B-iv）。
本页不声称 native 第一层 jets 已生产。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff NNReal

namespace GC.LongTime.Ch11

universe u

/-- **G1b（PROVED）**：seed 门槛（任意 `q ≤ M`）的 first-exit 迫使 trace 碰到的 born cap
满足 `neck.scale ≤ 4 M`；不需要 `q₀ ≤ Cbirth·qcap`。 -/
theorem exists_bornCap_scale_le_four_mul_C11SP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
        {p : (H.stageAt t).Carrier}
        (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) p)
        {params : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params),
        params.modelAccuracy ≤ ε₀ → 2 ≤ params.modelOrder →
        (∀ e b, ((records e).static b).hasCanonicalWindow) →
        StandardCap.transitionEnd + 10 < params.modelRadius →
        ∀ {ε C1 C2 q M s : ℝ} {Ctime : ℝ≥0}, 0 < M → q ≤ M →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          s < (v : ℝ) → (v : ℝ) < t →
          q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) →
        metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M →
        Ctime * M * ((t : ℝ) - s) ≤ 1 / 2 →
        ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t), s ≤ H.time e.succ →
          ∀ b (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 →
            ((records e).static b).window z =
              A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl →
            ((records e).static b).neck.scale ≤ 4 * M := by
  obtain ⟨ε₀, hε₀, hprot⟩ := BackwardPointTrace.exists_trace_protection_of_good_suffix_CXSP.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H a t hat p A params records hacc hm hcan hD ε C1 C2 q M s Ctime hM hqM hgood
    hscalar htime e hf hl hse b z hz hzEq
  by_contra hlt
  exact hprot hat A records hacc hm hcan hD hM hqM hgood hscalar htime e hf hl hse b
    (lt_of_not_ge hlt) ⟨z, hz, hzEq⟩

/-- **G1b 推论**：born-cap jets（G63 形 `X ≤ C² qcap^{j+2}`）在 `qcap ≤ 4 m Q` 下的
`Q` 归一化界，常数只依赖 `(C, m, j)`。 -/
theorem bornCap_jets_normalized_le_C11SP {X C qcap m Q : ℝ} (j : ℕ)
    (hq0 : 0 ≤ qcap) (hq : qcap ≤ 4 * (m * Q))
    (hX : X ≤ C ^ 2 * qcap ^ (j + 2)) :
    X ≤ C ^ 2 * (4 * m) ^ (j + 2) * Q ^ (j + 2) := by
  have hpow : qcap ^ (j + 2) ≤ (4 * (m * Q)) ^ (j + 2) := pow_le_pow_left₀ hq0 hq _
  calc X ≤ C ^ 2 * qcap ^ (j + 2) := hX
    _ ≤ C ^ 2 * (4 * (m * Q)) ^ (j + 2) :=
        mul_le_mul_of_nonneg_left hpow (sq_nonneg C)
    _ = C ^ 2 * (4 * m) ^ (j + 2) * Q ^ (j + 2) := by
        rw [← mul_assoc 4 m Q, mul_pow, mul_assoc]

end GC.LongTime.Ch11
