import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6InnerBallVolumeCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtypeBall

set_option autoImplicit false

/-!
# CX-SPINE G12：closed slab 上的全中心 terminal volume

在原 compact stage 的 scaled endpoint metric 使用 G11，再按真实 restriction 搬运。
canonical witness 与同分支 scalar gap 都在原 stage；常数先于 slab、scale 和所有测试点。
这里只支付 compactness 的 volume 槽，不生产 moving footprint 或 trace survival。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

private local instance {P : OrientedThreeStage.{u}} {b s : ℝ} (A : P.ClosedSlab b s) :
    SigmaCompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen.isOpen)

private theorem scaled_endpoint_restrict_CXSP {P : OrientedThreeStage.{u}} {b s : ℝ}
    (A : P.ClosedSlab b s) (Q : ℝ) (hQ : 0 < Q) :
    scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric =
      (scaleMetric Q hQ (A.flow.base.metric s)).restrictOpen
        (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rfl

private theorem scaled_endpoint_edist_CXSP {P : OrientedThreeStage.{u}} {b s : ℝ}
    (A : P.ClosedSlab b s) (Q : ℝ) (hQ : 0 < Q)
    (x y : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) :
    riemannianEDistOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x y =
      riemannianEDistOf (scaleMetric Q hQ (A.flow.base.metric s)) x.val y.val := by
  rw [scaled_endpoint_restrict_CXSP]
  apply riemannianEDistOf_restrictOpen_of_isClosed
  change IsClosed (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
  rw [A.terminalRegularRegion_eq_univ P]
  exact isClosed_univ

/-- closed slab 的 scaled terminal-open 球与原 stage 球有完全相同的 volume。 -/
theorem scaled_endpoint_ball_volume_CXSP {P : OrientedThreeStage.{u}} {b s : ℝ}
    (A : P.ClosedSlab b s) (Q : ℝ) (hQ : 0 < Q)
    (x : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen) (r : ℝ) :
    riemannianVolumeMeasure ThreeModel _
        (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
        (riemannianBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) x r) =
      ballVolume (scaleMetric Q hQ (A.flow.base.metric s)) x.val r := by
  rw [scaled_endpoint_restrict_CXSP]
  apply riemannianVolumeMeasure_ball_restrictOpen_of_isClosed
  change IsClosed (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
  rw [A.terminalRegularRegion_eq_univ P]
  exact isClosed_univ

/-- 未缩放 canonical base 与 terminal 曲率界生产 G3 所需的全部内球中心 volume。 -/
theorem exists_closed_slab_inner_volume_CXSP (ε C1 C2 : ℝ) {S R J C : ℝ}
    (hS : 0 ≤ S) (hSR : S < R) (hJ : 0 ≤ J) (hC : 0 ≤ C) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ S + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ {P : OrientedThreeStage.{u}} {b s : ℝ} (A : P.ClosedSlab b s)
        (Q : ℝ) (hQ : 0 < Q)
        (p : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
        (W : SpatialCanonicalWitness (A.flow.base.metric s) ε C1 C2 p.val),
        W.capTubeHasNeckChart ε →
        ∀ y ∈ connectedComponent p.val,
          C2 * metricScalarAt (A.flow.base.metric s) y <
            metricScalarAt (A.flow.base.metric s) p.val →
        (∀ z ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) p R,
          Real.sqrt (normSq0S (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
            z 4 (metricRm04At (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) z))
              ≤ J) →
        ∀ x ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) p S,
          ENNReal.ofReal (κ * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel _
            (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
            (riemannianBallOf (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
              x a) := by
  obtain ⟨a, κ, ha, hκ, haR, haC, hvol⟩ :=
    exists_inner_ball_volume_of_canonical_curvature_CXSP.{u} ε C1 C2 hS hSR hJ hC
  refine ⟨a, κ, ha, hκ, haR, haC, ?_⟩
  intro P b s A Q hQ p W hchart y hy hgap hRm x hx
  rw [scaled_endpoint_ball_volume_CXSP]
  have hgapQ : C2 * metricScalarAt (scaleMetric Q hQ (A.flow.base.metric s)) y <
      metricScalarAt (scaleMetric Q hQ (A.flow.base.metric s)) p.val := by
    simp only [metricScalarAt_scaleMetric]
    calc
      _ = Q⁻¹ * (C2 * metricScalarAt (A.flow.base.metric s) y) := by ring
      _ < _ := mul_lt_mul_of_pos_left hgap (inv_pos.mpr hQ)
  refine hvol (W.scaleMetric Q hQ) (hchart.scaleMetric Q hQ) y hy hgapQ ?_ x.val ?_
  · intro z hz
    have hzU : z ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen := by
      change z ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [A.terminalRegularRegion_eq_univ P]
      trivial
    have hzR : (⟨z, hzU⟩ : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
        ∈ riemannianClosedBallOf
          (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) p R := by
      change riemannianEDistOf _ p ⟨z, hzU⟩ ≤ ENNReal.ofReal R
      rw [scaled_endpoint_edist_CXSP]
      exact hz
    have h := hRm ⟨z, hzU⟩ hzR
    rw [scaled_endpoint_restrict_CXSP,
      DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen]
      at h
    exact h
  · change riemannianEDistOf _ p x ≤ ENNReal.ofReal S at hx
    rwa [scaled_endpoint_edist_CXSP] at hx

end GC.LongTime.Ch11
