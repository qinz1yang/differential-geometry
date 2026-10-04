import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.HistorySliceScalarBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.InitialScalarBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HamiltonIveyCurvatureBound
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal NNReal Topology
namespace FILL910
universe u
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness

theorem A04a_postMetric_pinching (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a₀ : ℝ, 0 < a₀ ∧
      ∀ (F : GC.Interface.RawSurgery P g) (p : ℕ → CutoffParameters),
        (∀ n (i : Fin (F.tower.history n).eventCount),
          GeometricCutoffRecord (F.tower.history n).toHistory i (p n)) →
        ∀ t : ℝ, 0 ≤ t → ∀ x : (GC.LongTime.postStage F.observation t).Carrier,
          InFixedHamiltonIveyRegion (GC.LongTime.postMetric F.observation t) (a₀ + t) x := by
  obtain ⟨a₀, ha₀, hi⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  refine ⟨a₀, ha₀, ?_⟩
  intro F p records t ht
  let O := F.observation
  let H := O.history (Nat.ceil t)
  let a : Icc (0 : ℝ) H.horizon := ⟨t, ht, by rw [O.horizon_eq]; exact Nat.le_ceil t⟩
  obtain ⟨hfixed, hscalar⟩ := hi H (O.initial (Nat.ceil t))
  have hb := (H.fixedHamiltonIveyRegion_and_scalar_lower (records (Nat.ceil t))
    ha₀ hfixed hscalar).1 (H.activeStage a) t (H.activeStage_mem a)
  exact stageMetricAssertion_of_heq (postStage_prefix O t ht).symm
    (postMetric_prefix O t ht).symm
    (fun S m => ∀ x : S.Carrier, InFixedHamiltonIveyRegion m (a₀ + t) x)
    (fun x => (hb x).1)

end FILL910
