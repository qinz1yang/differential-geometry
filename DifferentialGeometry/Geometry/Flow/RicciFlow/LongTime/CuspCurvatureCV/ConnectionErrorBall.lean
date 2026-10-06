import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.ConnectionError
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BallPullback
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetRestriction

/-!
# IMS04 / O3 consumer（O-W-CURV, suffix `_CV`）：`↥ball` 上的 (I1)

`cores.metric_error`（k = 0, 1，模型 `(model i).Carrier` 上）经
`tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen` 限制到 `↥ball`，误差 tensor 与
`ĝ_t = cores.pulledMetric_BD`、`h_B = cores.refMetric_BD` 的差逐点一致（`pulledMetric_inner_BD`），
于是 `connection_difference_le_of_metric_error_CV` 给出 BOUNDARY 的 (I1)：

`|difference (metricCov ĝ_t) (metricCov h_B) x u w|_{h_B}
  ≤ 3/2 (1+2acc)³ acc · |u|_{h_B} |w|_{h_B}`。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- `↥ball` 上 `(ĝ_t, h_B)` 的误差 tensor = `metric_error` 误差 tensor 的限制（`ofModel ∘ toModel`）。 -/
theorem PersistentHyperbolicCores.ballError_eq_CV (cores : PersistentHyperbolicCores F K)
    (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t) (hacc : cores.accuracy t < 1) :
    (fun z : ↥(cores.ballOpen_BD i t) =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) z) ℝ).symm.toContinuousLinearMap
        |>.comp ((cores.pulledMetric_BD i t ht hacc).inner z -
          (cores.refMetric_BD i t).inner z)).uncurryLeft) =
      fun z : ↥(cores.ballOpen_BD i t) => Tensor0SSpace.ofModel (I := 𝓡 3) (x := z)
        (Tensor0SSpace.toModel
          (((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) (z : (cores.model i).Carrier))
            ℝ).symm.toContinuousLinearMap.comp ((t⁻¹ : ℝ) • localPullInner
              (postMetric F.observation t) (cores.map i t ht) (z : (cores.model i).Carrier) -
            (cores.model i).metric.inner (z : (cores.model i).Carrier))).uncurryLeft)) := by
  funext z
  apply tensor0SSpace_ext (I := 𝓡 3) 2 z
  intro v
  change ((cores.pulledMetric_BD i t ht hacc).inner z - (cores.refMetric_BD i t).inner z) (v 0)
    (v 1) = ((t⁻¹ : ℝ) • localPullInner (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
      (cores.map i t ht) (z : (cores.model i).Carrier) -
      (cores.model i).metric.inner (z : (cores.model i).Carrier) :
        TangentSpace (𝓡 3) (z : (cores.model i).Carrier) →L[ℝ]
          TangentSpace (𝓡 3) (z : (cores.model i).Carrier) →L[ℝ] ℝ) (v 0) (v 1)
  simp only [SmoothRiemannianMetric.restrictOpen_inner, sub_apply,
    cores.pulledMetric_inner_BD i t ht hacc z]
  rfl

/-- **(I1)（`↥ball` 上，`acc t ≤ 1/2`）**：`cores.metric_error` k = 0, 1 ⇒
`|difference (metricCov ĝ_t) (metricCov h_B) x u w|_{h_B}
  ≤ 3/2 (1+2acc)³ acc · |u|_{h_B} |w|_{h_B}`。
形状与 `sqrt_curvature_pulled_le_BD` 的 `hconn` 逐字一致。 -/
theorem PersistentHyperbolicCores.connection_difference_ball_CV
    (cores : PersistentHyperbolicCores F K) (i : Fin cores.count) (t : ℝ) (ht : cores.start ≤ t)
    (hacc : cores.accuracy t < 1) (hacc2 : cores.accuracy t ≤ 1 / 2)
    (x : ↥(cores.ballOpen_BD i t)) (u w : TangentSpace (𝓡 3) x) :
    Real.sqrt ((cores.refMetric_BD i t).inner x
        (CovariantDerivative.difference (metricCov (cores.pulledMetric_BD i t ht hacc))
          (metricCov (cores.refMetric_BD i t)) x u w)
        (CovariantDerivative.difference (metricCov (cores.pulledMetric_BD i t ht hacc))
          (metricCov (cores.refMetric_BD i t)) x u w)) ≤
      3 / 2 * (1 + 2 * cores.accuracy t) ^ 3 * cores.accuracy t *
        Real.sqrt ((cores.refMetric_BD i t).inner x u u) *
        Real.sqrt ((cores.refMetric_BD i t).inner x w w) := by
  have hpos : 0 < cores.accuracy t := cores.accuracy_pos t ht
  have hk : ∀ k : ℕ, k ≤ 1 →
      tensor0SFiberNorm (cores.refMetric_BD i t) x (2 + k)
        (iteratedMetricCovariantDerivative (cores.refMetric_BD i t) 2
          (fun z : ↥(cores.ballOpen_BD i t) =>
            ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) z) ℝ).symm.toContinuousLinearMap
              |>.comp ((cores.pulledMetric_BD i t ht hacc).inner z -
                (cores.refMetric_BD i t).inner z)).uncurryLeft) k x) < cores.accuracy t := by
    intro k hk1
    have hme := cores.metric_error i t ht k
      (le_max_of_le_right (hk1.trans (Nat.ceil_pos.mpr (inv_pos.mpr hpos)))) x.1 x.2
    have hrestr := tensor0SFiberNorm_iteratedMetricCovariantDerivative_restrictOpen
      (cores.model i).metric (cores.ballOpen_BD i t) (s := 2)
      (fun p : (cores.model i).Carrier =>
        ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          ((t⁻¹ : ℝ) • localPullInner (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation t)
            (cores.map i t ht) p - (cores.model i).metric.inner p)).uncurryLeft) k x
    rw [← hrestr] at hme
    rw [cores.ballError_eq_CV i t ht hacc]
    exact hme
  exact connection_difference_le_of_metric_error_CV _ _ x hacc2 (hk 0 (Nat.zero_le _))
    (hk 1 le_rfl) u w

end GC.LongTime
