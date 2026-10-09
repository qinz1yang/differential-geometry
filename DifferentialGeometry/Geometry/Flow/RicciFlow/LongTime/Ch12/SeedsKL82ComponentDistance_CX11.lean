import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82DistSlab_O11
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82EventDistance_CX11
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Comparison.DistanceFamily

set_option autoImplicit false

noncomputable section

open Set Manifold TopologicalSpace DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

/-- O11's slab estimate on one component of a possibly disconnected manifold.
Distance continuity is derived from the solution and completeness, rather than
left as a new hypothesis of the history argument. -/
theorem dist_le_of_ricci_inv_time_component_CX11
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := M) D)
    (hS : IsSolutionOn S) {a v0 v1 C : ℝ} (hC : 0 < C) (hav0 : a ≤ v0)
    (hv01 : v0 ≤ v1) (hcar : Icc v0 v1 ⊆ D.carrier) (hreg : Ioc v0 v1 ⊆ D.regular)
    (hcomplete : ∀ v ∈ Icc v0 v1, RiemannianMetricComplete (S.base.metric v))
    (x y : M) (hy : y ∈ connectedComponent x)
    (hRic : ∀ v ∈ Ioc v0 v1, ∀ z : M, ∀ w : TangentSpace ThreeModel z,
      (riemannianEDistOf (S.base.metric v) x z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C)) ∨
        riemannianEDistOf (S.base.metric v) y z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C))) →
      ricciTensor (S.base.metric v) z w w ≤ C / (v - a) * (S.base.metric v).inner z w w) :
    (riemannianEDistOf (S.base.metric v0) x y).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v0 - a) ≤
      (riemannianEDistOf (S.base.metric v1) x y).toReal +
        16 * Real.sqrt (C / 3) * Real.sqrt (v1 - a) := by
  let U := connectedComponentOpen (I := ThreeModel) x
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := ThreeModel) x
  let : SigmaCompactSpace U :=
    (show IsClosed (U : Set M) from isClosed_connectedComponent).sigmaCompactSpace
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let xU : U := ⟨x, mem_connectedComponent⟩
  let yU : U := ⟨y, hy⟩
  let S' := solutionOnRestrictOpen S U
  have hS' : IsSolutionOn S' := isSolutionOn_restrictOpen S hS U
  have hcomp (v : ℝ) (hv : v ∈ Icc v0 v1) : RiemannianMetricComplete (S'.base.metric v) :=
    riemannianMetricComplete_restrictOpen_connCompOpen (S.base.metric v) x (hcomplete v hv)
  have hd (v : ℝ) (p q : U) :
      riemannianEDistOf (S'.base.metric v) p q = riemannianEDistOf (S.base.metric v) p.val q.val :=
    edistOf_restrictOpen_connCompOpen (S.base.metric v) x p q
  have hc := continuousOn_riemannianEDistOf S'.base.metric ordConnected_Icc
    (hS'.smoothMetric.metricTensor_cont.mono hcar) hcomp xU
  have hc' : ContinuousOn (fun v => riemannianEDistOf (S'.base.metric v) xU yU) (Icc v0 v1) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hv => ⟨hv, mem_univ _⟩)
  have hcR : ContinuousOn (fun v => (riemannianEDistOf (S'.base.metric v) xU yU).toReal)
      (Icc v0 v1) := by
    intro v hv
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top (S'.base.metric v) xU yU)).comp_continuousWithinAt
      (f := fun r => riemannianEDistOf (S'.base.metric r) xU yU) (hc' v hv)
  have hRic' : ∀ v ∈ Ioc v0 v1, ∀ z : U, ∀ w : TangentSpace ThreeModel z,
      (riemannianEDistOf (S'.base.metric v) xU z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C)) ∨
        riemannianEDistOf (S'.base.metric v) yU z <
          ENNReal.ofReal (Real.sqrt (3 * (v - a) / C))) →
      ricciTensor (S'.base.metric v) z w w ≤ C / (v - a) * (S'.base.metric v).inner z w w := by
    intro v hv z w hz
    simp only [hd] at hz
    have hh := hRic v hv z.val (mfderiv ThreeModel ThreeModel (Subtype.val : U → M) z w) hz
    change ricciTensor ((S.base.metric v).restrictOpen U) z w w ≤ _
    rw [Geometry.Curvature.ricciTensor_restrictOpen]
    convert hh using 1
    rw [mfderiv_subtype_val_apply]
    rfl
  have hh := dist_le_of_ricci_inv_time_O11 S' hS' (by simp [ThreeSpace]) hC hav0 hv01 hreg
    (fun v hv => hcomp v ⟨hv.1.le, hv.2⟩) xU yU hcR hRic'
  simpa only [hd] using hh

end GC.LongTime.Ch12
