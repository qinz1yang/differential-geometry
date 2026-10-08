import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageVolumeFromJetsCXSP

set_option autoImplicit false

/-!
# CX-SPINE：原 compact stage 的实际 pointed compactness consumer

canonical base/scalar gap 与内球 normalized jets 经 G45 生产 volume；ambient compactness
直接来自原 stage 的 compact carrier。保留完整 source/target、canonical domains 与 metric bounds。
不引入 volume/trace/global derivative 假设，也不要求正 stage age 或 RegularSlice。
这是实际 kernel consumer；其 sequence jets、canonical base 必须由真实种子/窗口生产。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- 从原 stage 的实际 canonical base 与 jets 生产带全部 metric-domain 数据的 pointed limit。 -/
theorem exists_stage_pointed_convergence_of_jets_CXSP
    (P : ℕ → OrientedThreeStage.{u}) (g : ∀ n, (P n).Metric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) (x : ∀ n, (P n).Carrier)
    (ε C1 C2 : ℝ) {rho : ℝ} (hrho : 0 < rho)
    (hcan : ∀ᶠ n in atTop,
      ∃ W : SpatialCanonicalWitness (g n) ε C1 C2 (x n),
        W.capTubeHasNeckChart ε ∧ ∃ y ∈ connectedComponent (x n),
          C2 * metricScalarAt (g n) y < metricScalarAt (g n) (x n)) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := (P n).Carrier
            basepoint := x n
            metric := scaleMetric (Q n) (hQ n) (g n) } }
    (∀ R : ℝ, 0 < R → R < rho → ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R k J) →
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ (L : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (F : PointedRiemannianConvergenceMaps X.connectedComponent L f),
        let U := fun i => connectedComponentOpen (I := ThreeModel) (X.obj i).basepoint
        let hp := fun i => (mem_connectedComponent : (X.obj i).basepoint ∈ U i)
        let F' := F.liftTargetOpen U hp
        ∃ C : MetricConvergenceData F',
        (∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F' n) ∧
        (∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho) ∧
        (∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f n)).metric (X.obj (f n)).basepoint
          (r n) ⊆ F'.target n) ∧
        ∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ x ∈ F'.source n, ∀ v : TangentSpace ThreeModel x,
          (1 - eps) * L.metric.inner x v v ≤
            (X.obj (f n)).metric.inner (F'.map n x) (mfderiv ThreeModel ThreeModel (F'.map n) x v)
              (mfderiv ThreeModel ThreeModel (F'.map n) x v) ∧
          (X.obj (f n)).metric.inner (F'.map n x) (mfderiv ThreeModel ThreeModel (F'.map n) x v)
              (mfderiv ThreeModel ThreeModel (F'.map n) x v) ≤
            (1 + eps) * L.metric.inner x v v := by
  intro X hjets
  refine exists_pointed_convergence_with_uniform_metric_bounds_on_base_components X hrho ?_
    hjets (stage_volume_window_of_jets_CXSP P g Q hQ x ε C1 C2 hcan hjets)
  intro R _hR _hRrho
  exact Eventually.of_forall fun n =>
    (Geometry.Metric.isClosed_riemannianClosedBallOf (X.obj n).metric
      (X.obj n).basepoint R).isCompact

end GC.LongTime.Ch11
