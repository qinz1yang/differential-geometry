import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalData


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.BoundedGeometry.NormalTransitionBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.Transition

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology
open scoped Manifold ContDiff Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

namespace BoundedGeometryNormalData


theorem trans_bounds_on
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (x y : ∀ k : Nat, (X.obj k).M) (U V : Set E)
    (hU : IsOpen U) (hV : IsOpen V)
    (hVnorm : ∃ Z : Real, ∀ z ∈ V, ‖z‖ ≤ Z)
    (hVrad : ∀ k,
      V ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (y k) (X.obj k).basepoint)))
    (hovl : ∀ k, d.chartOverlapOn k (x k) (y k) U)
    (hmap : ∀ k, Set.MapsTo (d.chartTransition k (x k) (y k)) U V) :
    IsometryDerivBoundsOn U
      (fun k => d.chartTransition k (x k) (y k)) := by
  apply MetricIsometry.isom_bounds_on
    (CB := d.metricC) (CC := d.metricC)
    (fun k => d.chartMetric k (x k))
    (fun k => d.chartMetric k (y k))
    (fun k => d.chartTransition k (x k) (y k))
    U V hU hV hVnorm
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovl k
    have hUrad :
        U ⊆ Metric.ball (0 : E) (d.chart k (x k)).radius :=
      fun z hz => (hovl' z hz).1
    simpa only [BoundedGeometryNormalData.chartMetric] using
      (d.chart k (x k)).metric_contDiffOn (X.obj k).metric hU
        ((d.chart k (x k)).smooth_to.mono hUrad)
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hVrad' :
        V ⊆ Metric.ball (0 : E) (d.chart k (y k)).radius := by
      simpa only [d.radius_eq k (y k)] using hVrad k
    simpa only [BoundedGeometryNormalData.chartMetric] using
      (d.chart k (y k)).metric_contDiffOn (X.obj k).metric hV
        ((d.chart k (y k)).smooth_to.mono hVrad')
  · intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovl k
    simpa only [BoundedGeometryNormalData.chartTransition] using
      (d.chart k (x k)).transition_smooth (d.chart k (y k)) hovl'
  · exact hmap
  · intro k z hz u v
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovl k
    simpa only [BoundedGeometryNormalData.chartMetric, BoundedGeometryNormalData.chartTransition] using
      ((d.chart k (x k)).transition_isom (X.obj k).metric
        (d.chart k (y k)) hovl' hz u v).symm
  · intro k z _ a b
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    change (d.chart k (y k)).metric (X.obj k).metric z a b =
      (d.chart k (y k)).metric (X.obj k).metric z b a
    rw [(d.chart k (y k)).metric_apply (X.obj k).metric,
      (d.chart k (y k)).metric_apply (X.obj k).metric]
    exact (X.obj k).metric.symm _ _ _
  · intro k z hz q
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovl k
    simpa only [BoundedGeometryNormalData.chartMetric] using
      d.metric_equiv k (x k) z (hovl' z hz).1 q
  · intro k z hz q
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hVrad' :
        V ⊆ Metric.ball (0 : E) (d.chart k (y k)).radius := by
      simpa only [d.radius_eq k (y k)] using hVrad k
    simpa only [BoundedGeometryNormalData.chartMetric] using
      d.metric_equiv k (y k) z (hVrad' hz) q
  · exact d.metricC_nonneg
  · exact d.metricC_nonneg
  · intro k p z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovl k
    simpa only [BoundedGeometryNormalData.chartMetric] using
      d.metric_deriv k p (x k) z (hovl' z hz).1
  · intro k p z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hVrad' :
        V ⊆ Metric.ball (0 : E) (d.chart k (y k)).radius := by
      simpa only [d.radius_eq k (y k)] using hVrad k
    simpa only [BoundedGeometryNormalData.chartMetric] using
      d.metric_deriv k p (y k) z (hVrad' hz)


theorem exists_trans_lim
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {hd : InjRadiusDecayInput (I := I) X}
    (d : BoundedGeometryNormalData (I := I) X hd)
    (x y : ∀ k : Nat, (X.obj k).M)
    {U V Ua Va : Set E}
    (hU : IsOpen U) (hV : IsOpen V)
    (hUa : IsOpen Ua) (hVa : IsOpen Va)
    (hUanorm : ∃ Z : Real, ∀ z ∈ Ua, ‖z‖ ≤ Z)
    (hVanorm : ∃ Z : Real, ∀ z ∈ Va, ‖z‖ ≤ Z)
    (hUarad : ∀ k,
      Ua ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (x k) (X.obj k).basepoint)))
    (hVarad : ∀ k,
      Va ⊆ Metric.ball (0 : E)
        (d.ratio * hd.mu (hd.dist k (y k) (X.obj k).basepoint)))
    (hovlJ : ∀ k, d.chartOverlapOn k (x k) (y k) U)
    (hovlJbar : ∀ k, d.chartOverlapOn k (y k) (x k) V)
    (hmapJ : ∀ k, Set.MapsTo
      (d.chartTransition k (x k) (y k)) U Va)
    (hmapJbar : ∀ k, Set.MapsTo
      (d.chartTransition k (y k) (x k)) V Ua) :
    ∃ (phi : Nat → Nat) (Jinf : E → E) (Jbarinf : E → E),
      StrictMono phi ∧
      ContDiffOn Real (⊤ : ℕ∞) Jinf U ∧
      ContDiffOn Real (⊤ : ℕ∞) Jbarinf V ∧
      MapCInfConvOnCompacts U
        (fun k => d.chartTransition (phi k)
          (x (phi k)) (y (phi k))) Jinf ∧
      MapCInfConvOnCompacts V
        (fun k => d.chartTransition (phi k)
          (y (phi k)) (x (phi k))) Jbarinf ∧
      (∀ z ∈ U, Jinf z ∈ V → Jbarinf (Jinf z) = z) ∧
      (∀ z ∈ V, Jbarinf z ∈ U → Jinf (Jbarinf z) = z) := by
  have hJ : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (d.chartTransition k (x k) (y k)) U := by
    intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovlJ k
    simpa only [BoundedGeometryNormalData.chartTransition] using
      (d.chart k (x k)).transition_smooth (d.chart k (y k)) hovl'
  have hJbar : ∀ k, ContDiffOn Real (⊤ : ℕ∞)
      (d.chartTransition k (y k) (x k)) V := by
    intro k
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (y k)).OverlapOn (d.chart k (x k)) V := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovlJbar k
    simpa only [BoundedGeometryNormalData.chartTransition] using
      (d.chart k (y k)).transition_smooth (d.chart k (x k)) hovl'
  apply exists_transition_limit_on hU hV
    (fun k => d.chartTransition k (x k) (y k))
    (fun k => d.chartTransition k (y k) (x k))
    hJ hJbar
  · exact d.trans_bounds_on x y U Va hU hVa hVanorm hVarad hovlJ hmapJ
  · exact d.trans_bounds_on y x V Ua hV hUa hUanorm hUarad hovlJbar hmapJbar
  · intro k z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (x k)).OverlapOn (d.chart k (y k)) U := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovlJ k
    simpa only [BoundedGeometryNormalData.chartTransition] using
      (d.chart k (x k)).transition_cancel
        (d.chart k (y k)) hovl' hz
  · intro k z hz
    let : TopologicalSpace (X.obj k).M := (X.obj k).topology
    let : ChartedSpace H (X.obj k).M := (X.obj k).charted
    let : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
    let : T2Space (TangentBundle I (X.obj k).M) :=
      (X.obj k).t2TangentBundle
    have hovl' :
        (d.chart k (y k)).OverlapOn (d.chart k (x k)) V := by
      simpa only [BoundedGeometryNormalData.chartOverlapOn] using hovlJbar k
    simpa only [BoundedGeometryNormalData.chartTransition] using
      (d.chart k (y k)).transition_cancel
        (d.chart k (x k)) hovl' hz

end BoundedGeometryNormalData
end HCGCompactness
end DifferentialGeometry
