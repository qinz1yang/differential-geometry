import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferLowCurv_S77
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

/-!
# CH12-S77, group 1b: slab-end continuity and the micro-scale form of the buffer estimate

* `slab_scalar_near_end_S77`: the scalar of a point on the last slab is continuous up to `s.time`
  (closed slab), so a bound `R(y, s.time) ≤ M` gives, for each `ε > 0`, a time `t₁ < s.time` of the slab with
  `R(y, t₁) ≤ M + ε` (to feed `buffer_lowcurv_S77`, whose hypothesis is at a time `t₁ < s.time`).
* `buffer_lowcurv_micro_S77`: at micro scale (`ρ < Λ · nominalRadius` of a recent event), the neck threshold
  condition `neckRadius(s.time)⁻² ≤ M` is automatic for `M = C₀ / ρ²`, `C₀ ≥ 1`
  (`micro_scale_le_neckRadius_O13` with `c = 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff NNReal Topology

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}

theorem slab_scalar_near_end_S77 (s : RegularSlice F.observation)
    (y : ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier)
    {M : ℝ} (hM : metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric s.time) y ≤ M) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ t₁ : ℝ, (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount) ≤ t₁ ∧
      t₁ < s.time ∧ metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric t₁) y ≤ M + ε := by
  have hlt := (sliceSlabR_O3 F s).lt
  have hcont : ContinuousWithinAt
      (fun v => metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric v) y)
      (Icc ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) s.time) s.time :=
    ((sliceSlabR_O3 F s).equation.scalarTime (K := Icc _ s.time)
      ⟨hlt.le, le_rfl⟩ (fun _ hv => hv) y).continuousWithinAt
  have hnear : ∀ᶠ v in 𝓝[Icc ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount))
      s.time] s.time, metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric v) y < M + ε :=
    hcont.eventually (Iio_mem_nhds (by linarith))
  have hI : Icc ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) s.time ∈
      𝓝[<] s.time := mem_of_superset (Ioo_mem_nhdsLT hlt) Ioo_subset_Icc_self
  have hnear' := hnear.filter_mono (nhdsWithin_le_of_mem hI)
  obtain ⟨t₁, h1, h2⟩ := (hnear'.and (Ioo_mem_nhdsLT hlt)).exists
  exact ⟨t₁, h2.1.le, h2.2, h1.le⟩

theorem buffer_lowcurv_micro_S77 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0)
    (hP2 : P2_O2 Hp Ctime) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ T : ℝ, 0 < T ∧ ∀ s : RegularSlice F.observation, T ≤ s.time → ∀ ρ : ℝ, 0 < ρ →
      (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
        ρ < Λ * (Hp.records n i).nominalRadius h) →
      ∀ C₀ : ℝ, 1 ≤ C₀ → ∀ t₁ : ℝ,
      (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount) ≤ t₁ → t₁ < s.time →
      ∀ (first : Fin ((sliceHistoryR_O3 F s).eventCount + 1))
        (hle : first ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
        (y : ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier)
        (A : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory first
          (Fin.last (sliceHistoryR_O3 F s).eventCount) hle y),
      metricScalarAt ((sliceSlabR_O3 F s).flow.base.metric t₁) y ≤ C₀ / ρ ^ 2 →
      4 * Ctime * (C₀ / ρ ^ 2) * (t₁ - (sliceHistoryR_O3 F s).time first) ≤ 1 →
      metricScalarAt ((sliceHistoryR_O3 F s).initialMetric first) (A.point first le_rfl hle) ≤
        4 * (C₀ / ρ ^ 2) := by
  obtain ⟨T, hT, hmic⟩ := micro_scale_le_neckRadius_O13 Hp Λ 1 hΛ one_pos
  refine ⟨T, hT, fun s hs ρ hρ hmicro C₀ hC₀ t₁ hlt ht₁ first hle y A hy htime => ?_⟩
  have hρn : ρ ≤ Hp.parameters.neckRadius s.time := by
    simpa using hmic s hs ρ hmicro
  have hrad := Hp.parameters.neckRadius_pos s.time s.positive.le
  have hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ C₀ / ρ ^ 2 := by
    calc (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (ρ ^ 2)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_left₀ hρ.le hρn 2)
      _ = 1 / ρ ^ 2 := one_div _ |>.symm
      _ ≤ C₀ / ρ ^ 2 := by gcongr
  exact buffer_lowcurv_S77 Hp s Ctime hP2 (by positivity) hq hlt ht₁ first hle y A hy htime

end GC.LongTime.Ch12
