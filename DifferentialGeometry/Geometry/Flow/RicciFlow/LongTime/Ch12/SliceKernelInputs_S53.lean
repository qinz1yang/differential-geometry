import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroGlueSliceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CapScalarLower_S53
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence

/-!
# CH12-S53, group 2a: slice-level premises of the cap-window kernel

* `curvDerivNormSq_restrictOpen_S53`: `curvDerivNormSq` is local under `restrictOpen`
  (so jets of `L.metric = (s.metric).restrictOpen univ` are jets of `s.metric`).
* `sliceEndpointMetric_S53`: `((sliceSlabR_O3 F s).endpointTerminalLimitMetric _).metric` is
  `s.metric.restrictOpen _` on the whole carrier, hence `curvDerivNormSq j L.metric x = curvDerivNormSq j s.metric x.val`.
* `slice_hfinal_S53`: the kernel's `hfinal` premise on the slice slab from P2.
* `exists_a0_slice_S53`: the Hamilton-Ivey / scalar-lower constants `a₀` (uniform in the slice).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

theorem curvDerivNormSq_restrictOpen_S53 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (U : TopologicalSpace.Opens M) (j : ℕ) (x : U) :
    CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) j (g.restrictOpen U) x =
      CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) j g x.val := by
  have h := CheegerGromovCompactness.curvDerivNorm_restrictOpen (I := ThreeModel) g U j x
  have h1 : ∀ (N : Type _) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
      [IsManifold ThreeModel ∞ N] [T2Space N] (m : SmoothRiemannianMetric ThreeModel N) (z : N),
      CheegerGromovCompactness.curvDerivNormSq (I := ThreeModel) j m z =
        CheegerGromovCompactness.curvDerivNorm (I := ThreeModel) j m z ^ 2 := by
    intro N _ _ _ _ m z
    unfold CheegerGromovCompactness.curvDerivNorm
    rw [Real.sq_sqrt]
    exact Tensor0SBundle.normSq0S_nonneg _ _ _ _
  rw [h1, h1, h]

theorem slice_hfinal_S53 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (s : RegularSlice F.observation)
    (Ctime : ℝ≥0) (q : ℝ) (hP2 : P2_O2 Hp Ctime)
    (hq : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ ≤ q) :
    ∀ x : ((sliceHistoryR_O3 F s).stage (Fin.last (sliceHistoryR_O3 F s).eventCount)).Carrier,
      ∀ t ∈ Ioo ((sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount)) s.time,
        q < ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt le_rfl).flow.scalar t x →
        |derivWithin (fun v => ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt
            le_rfl).flow.scalar v x) (Iic t) t| ≤
          Ctime * ((sliceSlabR_O3 F s).restrictIncoming le_rfl (sliceSlabR_O3 F s).lt
            le_rfl).flow.scalar t x ^ 2 :=
  fun x t ht hqx => sliceSlab_derivative_O3 Hp s Ctime q hP2 hq x t ht hqx

theorem exists_a0_slice_S53 {P : OrientedThreeStage.{u}} (g : P.Metric)
    (F : GC.Interface.RawSurgery P g) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ s : RegularSlice F.observation,
      (∀ x, InFixedHamiltonIveyRegion ((sliceHistoryR_O3 F s).initialMetric 0) a₀ x) ∧
      ∀ x, -3 / a₀ ≤ metricScalarAt ((sliceHistoryR_O3 F s).initialMetric 0) x := by
  obtain ⟨a₀, ha₀, hi⟩ := exists_pos_fixedHamiltonIveyRegion_for_identified_histories P g
  refine ⟨a₀, ha₀, fun s => ?_⟩
  exact hi (F.tower.history (sliceIndexR_O3 F s)).toHistory (F.observation.initial _)

end GC.LongTime.Ch12
