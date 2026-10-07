import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedSlabVolumeCXSP
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.LocalJetBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs

set_option autoImplicit false

/-!
# CX-SPINE G12：closed-slab 序列的 compactness volume 槽

消费 G3 的 local jets 输出，仅取 order 0；canonical base、capTube chart 和同分支
scalar gap 必须由当前 Claim 2 序列提供。a、κ在 n 之前，输出逐字保持原 hvol 预算。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

private local instance {P : OrientedThreeStage.{u}} {b s : ℝ} (A : P.ClosedSlab b s) :
    SigmaCompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen.isOpen)

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- 原 G3 local-jets 结论和实际 canonical base 生产相同量词次序的 hvol。 -/
theorem closed_slab_volume_window_of_jets_CXSP
    (P : ℕ → OrientedThreeStage.{u}) (b s : ℕ → ℝ)
    (A : ∀ n, (P n).ClosedSlab (b n) (s n)) (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    (x : ∀ n, ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen)
    (ε C1 C2 : ℝ) {rho : ℝ}
    (hcan : ∀ᶠ n in atTop,
      ∃ W : SpatialCanonicalWitness ((A n).flow.base.metric (s n)) ε C1 C2 (x n).val,
        W.capTubeHasNeckChart ε ∧ ∃ y ∈ connectedComponent (x n).val,
          C2 * metricScalarAt ((A n).flow.base.metric (s n)) y <
            metricScalarAt ((A n).flow.base.metric (s n)) (x n).val) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((A n).restrictIncoming le_rfl (A n).lt le_rfl).terminalRegularOpen
            basepoint := x n
            metric := scaleMetric (Q n) (hQ n) ((A n).endpointTerminalLimitMetric (P n)).metric } }
    (∀ R : ℝ, 0 < R → R < rho → ∀ k : ℕ, ∃ J : ℝ, 0 ≤ J ∧
      ∀ᶠ n in atTop, HasLocalCurvDerivBound (X.obj n) (X.obj n).basepoint R k J) →
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
        ∀ᶠ n in atTop, ∀ y ∈ riemannianClosedBallOf
          (scaleMetric (Q n) (hQ n) ((A n).endpointTerminalLimitMetric (P n)).metric) (x n) r,
          ENNReal.ofReal (κ * a ^ 3) ≤ riemannianVolumeMeasure ThreeModel _
            (scaleMetric (Q n) (hQ n) ((A n).endpointTerminalLimitMetric (P n)).metric)
            (riemannianBallOf
              (scaleMetric (Q n) (hQ n) ((A n).endpointTerminalLimitMetric (P n)).metric) y a) := by
  dsimp only
  intro hjets r R hr hrR hRrho C hC
  obtain ⟨J, hJ, hbound⟩ := hjets R (hr.trans hrR) hRrho 0
  obtain ⟨a, κ, ha, hκ, haR, haC, hvol⟩ :=
    exists_closed_slab_inner_volume_CXSP.{u} ε C1 C2 hr.le hrR hJ hC
  refine ⟨a, κ, ha, hκ, haR, haC, ?_⟩
  filter_upwards [hcan, hbound] with n hn hJn
  obtain ⟨W, hchart, y, hy, hgap⟩ := hn
  apply hvol (A n) (Q n) (hQ n) (x n) W hchart y hy hgap
  intro z hz
  have h := hJn z hz
  change Real.sqrt (normSq0S
    (scaleMetric (Q n) (hQ n) ((A n).endpointTerminalLimitMetric (P n)).metric)
    z 4 (metricRm04
      (scaleMetric (Q n) (hQ n) ((A n).endpointTerminalLimitMetric (P n)).metric) z)) ≤ J at h
  rw [metricRm04_apply] at h
  exact h

end GC.LongTime.Ch11
