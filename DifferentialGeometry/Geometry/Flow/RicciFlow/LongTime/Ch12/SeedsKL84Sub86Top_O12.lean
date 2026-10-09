import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84Sub86Spatial_O10
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CanonicalNbhdLarge_S22
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MacroWholeBallWbd01

/-!
# CH12-O12: spatial step of KL Sublemma 86.3 on the slice top (G2b, part 1)

`slice_top_scalar_le_of_almost_euclidean_O12`: on a regular slice, at the slice top
metric `g_top = s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time`
(the metric of `hG2` / `hG2c`), if `r0 ≤ neckRadius(t)` and every subball of
`B(x0, r0)` is `(1-ε)`-Euclidean (`ε ≤ 3/4`), then `R ≤ A / r0²` on `B(x0, 3 r0 / 4)`.
This is `scalar_le_of_almost_euclidean_O10` with the profile canonical neighbourhoods
transported to the slice by `slice_canonical_above_neck_S22`, and the stage index
`activeStage (sliceTop_S8 s) = Fin.last` (`activeStage_at_horizon`).

Source: Kleiner–Lott, G&T 12 (2008), Sublemma 86.3 (spatial part), as recorded in
DELIVERIES [RESULT] CH12-O6 / [FROZEN] CH12-O10 (the book is not on this machine).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch12

universe u

theorem slice_top_scalar_le_of_almost_euclidean_O12 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ s : GC.LongTime.RegularSlice F.observation,
      ∀ (x0 : (s.history.stageAt (sliceTop_S8 s)).Carrier) {r0 : ℝ}, 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius s.time → ∀ {ε : ℝ}, ε ≤ 3 / 4 →
        (∀ z ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0 r0,
          ∀ b : ℝ, 0 < b → b ≤ r0 →
            ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤
              ballVolume (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
                z b) →
        ∀ y ∈ riemannianBallOf
            (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time) x0
            (3 * r0 / 4),
          metricScalarAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s)) s.time)
            y ≤ A / r0 ^ 2 := by
  obtain ⟨A, hA, hS⟩ := scalar_le_of_almost_euclidean_O10.{u} Hp.C1 Hp.C2
  refine ⟨A, hA, fun s => ?_⟩
  have gen : ∀ j : Fin (s.history.eventCount + 1), s.history.activeStage (sliceTop_S8 s) = j →
      ∀ (x0 : (s.history.stage j).Carrier) {r0 : ℝ}, 0 < r0 →
        r0 ≤ Hp.parameters.neckRadius s.time → ∀ {ε : ℝ}, ε ≤ 3 / 4 →
        (∀ z ∈ riemannianBallOf (s.history.stageMetric j s.time) x0 r0, ∀ b : ℝ, 0 < b → b ≤ r0 →
          ENNReal.ofReal ((1 - ε) * euclideanUnitBallVolume 3 * b ^ 3) ≤
            ballVolume (s.history.stageMetric j s.time) z b) →
        ∀ y ∈ riemannianBallOf (s.history.stageMetric j s.time) x0 (3 * r0 / 4),
          metricScalarAt (s.history.stageMetric j s.time) y ≤ A / r0 ^ 2 := by
    intro j hj
    have hj' : Fin.last s.history.eventCount = j := s.history.activeStage_at_horizon.symm.trans hj
    subst hj'
    intro x0 r0 hr0 hrad ε hε hEuc y hy
    have hg : RiemannianMetricComplete (I := I3) s.metric := RiemannianMetricComplete.of_compact _
    have h := hS s.metric hg Hp.epsilon_small ((Hp.parameters.neckRadius s.time ^ 2)⁻¹)
      (fun z hz => slice_canonical_above_neck_S22 Hp s z hz) hε x0 hr0 hEuc y hy
    refine h.trans (max_le ?_ le_rfl)
    have hsq : r0 ^ 2 ≤ Hp.parameters.neckRadius s.time ^ 2 := pow_le_pow_left₀ hr0.le hrad 2
    calc (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ (r0 ^ 2)⁻¹ := inv_anti₀ (by positivity) hsq
      _ = 1 / r0 ^ 2 := by rw [one_div]
      _ ≤ A / r0 ^ 2 := div_le_div_of_nonneg_right hA (by positivity)
  exact gen _ rfl

end GC.LongTime.Ch12
