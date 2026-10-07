import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaDiagonalP6D2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841DefsC11K

/-!
# G0 与 S-CH11-PRE841 `Pre841Data_C11K` 的型对齐（O-CH11-P6D2 G0 补）

G0（`P6KappaDiagonalP6D2.lean`）把 (K-seq) 写成显式前提 `hK`；PRE841 G1 交付后，
`Pre841Data_C11K.volume_ge` 与 `hK` **逐字同形**（`κ := d.kappa`），于是
`exists_tracedKappa_of_kseq_P6D2 d.volume_ge` 直接给出 M8 / P6D 的 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace ObservedHistory

universe u

/-- **对齐**：`Pre841Data_C11K` ⇒ M8 binder（`ρnc ≤ σ`、`ρnc √R → ∞`、trace-local `hkappa`，
`κ = d.kappa`），经 G0 的带上界慢对角化；`d.volume_ge` 原样喂 `hK`。 -/
theorem exists_tracedKappa_le_of_pre841_P6D2 {H : ℕ → ObservedHistory.{u}}
    {t : ∀ n, Icc (0 : ℝ) (H n).horizon} {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ}
    {hR : ∀ n, 0 < R n} (d : GC.LongTime.Ch11.Pre841Data_C11K H t y R hR) (σ : ℕ → ℝ)
    (hσ : Tendsto (fun n => σ n * Real.sqrt (R n)) atTop atTop) :
    ∃ ρnc : ℕ → ℝ, (∀ n, ρnc n ≤ σ n) ∧
      Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop ∧
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (H n).horizon) (hvt : v ≤ t n), (t n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (H n) ((H n).activeStage v) ((H n).activeStage (t n))
          ((H n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (H n).isParabolicallyRmControlledBall v
            (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (d.kappa * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((H n).stageMetric ((H n).activeStage v) v)
              (tr.point ((H n).activeStage v) le_rfl ((H n).activeStage_mono hvt)) r'' :=
  exists_tracedKappa_le_P6D2 d.volume_ge σ hσ

/-- consumer：`Pre841` 数据直接喂 G0 的 `hK`（逐字同形），得无上界的 M8 binder。 -/
example {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
    {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}
    (d : GC.LongTime.Ch11.Pre841Data_C11K H t y R hR) :
    ∃ ρnc : ℕ → ℝ, Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop :=
  (exists_tracedKappa_of_kseq_P6D2 d.volume_ge).imp fun _ h => h.1

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
