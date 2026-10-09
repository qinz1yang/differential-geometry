import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6InnerBallVolumeCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedSlabVolumeCXSP
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.IncompleteLocal

set_option autoImplicit false

/-!
# CX-SPINE：原 compact stage 上由 normalized jets 生产 inner-ball volume

先把实际 canonical witness 和同 component scalar gap
搬到 scaleMetric Q，再直接调用 G11；不经过 ClosedSlab、RegularSlice 或 prefix。
序列 consumer 的 a/κ 在 n 之前选择，量词与 IncompleteLocal 的 hvol 相同。
只在给定 rho 内消费较大内球的 jets，不扩大 seed window 或冒领原 seed κ。
-/

noncomputable section

open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- 实际 stage 的 scaled canonical base 与曲率界给全部内球中心 volume。 -/
theorem exists_stage_scaled_inner_volume_CXSP (ε C1 C2 : ℝ) {S R J C : ℝ}
    (hS : 0 ≤ S) (hSR : S < R) (hJ : 0 ≤ J) (hC : 0 ≤ C) :
    ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ S + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
        (Q : ℝ) (hQ : 0 < Q) (p : P.Carrier)
        (W : SpatialCanonicalWitness g ε C1 C2 p), W.capTubeHasNeckChart ε →
        ∀ y ∈ connectedComponent p, C2 * metricScalarAt g y < metricScalarAt g p →
        (∀ z ∈ riemannianClosedBallOf (scaleMetric Q hQ g) p R,
          Real.sqrt (normSq0S (scaleMetric Q hQ g) z 4
            (metricRm04At (scaleMetric Q hQ g) z)) ≤ J) →
        ∀ x ∈ riemannianClosedBallOf (scaleMetric Q hQ g) p S,
          ENNReal.ofReal (κ * a ^ 3) ≤
            riemannianVolumeMeasure ThreeModel P.Carrier (scaleMetric Q hQ g)
              (riemannianBallOf (scaleMetric Q hQ g) x a) := by
  obtain ⟨a, κ, ha, hκ, haR, haC, hvol⟩ :=
    exists_inner_ball_volume_of_canonical_curvature_CXSP.{u} ε C1 C2 hS hSR hJ hC
  refine ⟨a, κ, ha, hκ, haR, haC, ?_⟩
  intro P g Q hQ p W hchart y hy hgap hRm x hx
  have hgapQ : C2 * metricScalarAt (scaleMetric Q hQ g) y <
      metricScalarAt (scaleMetric Q hQ g) p := by
    simp only [metricScalarAt_scaleMetric]
    calc
      _ = Q⁻¹ * (C2 * metricScalarAt g y) := by ring
      _ < _ := mul_lt_mul_of_pos_left hgap (inv_pos.mpr hQ)
  exact hvol (W.scaleMetric Q hQ) (hchart.scaleMetric Q hQ) y hy hgapQ hRm x hx

/-- normalized stage 序列的实际 jets 支付 IncompleteLocal 的 hvol，常数先于 n。 -/
theorem stage_volume_window_of_jets_CXSP
    (P : ℕ → OrientedThreeStage.{u}) (g : ∀ n, (P n).Metric)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n) (x : ∀ n, (P n).Carrier)
    (ε C1 C2 : ℝ) {rho : ℝ}
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
    ∀ r R : ℝ, 0 < r → r < R → R < rho → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
        ∀ᶠ n in atTop,
          ∀ y ∈ riemannianClosedBallOf (X.obj n).metric (X.obj n).basepoint r,
            ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
              riemannianVolumeMeasure ThreeModel (X.obj n).M (X.obj n).metric
                (riemannianBallOf (X.obj n).metric y a) := by
  dsimp only
  intro hjets r R hr hrR hRrho C hC
  obtain ⟨J, hJ, hbound⟩ := hjets R (hr.trans hrR) hRrho 0
  obtain ⟨a, κ, ha, hκ, haR, haC, hvol⟩ :=
    exists_stage_scaled_inner_volume_CXSP.{u} ε C1 C2 hr.le hrR hJ hC
  refine ⟨a, κ, ha, hκ, haR, haC, ?_⟩
  filter_upwards [hcan, hbound] with n hn hJn
  obtain ⟨W, hchart, y, hy, hgap⟩ := hn
  have hRm : ∀ z ∈ riemannianClosedBallOf (scaleMetric (Q n) (hQ n) (g n)) (x n) R,
      Real.sqrt (normSq0S (scaleMetric (Q n) (hQ n) (g n)) z 4
        (metricRm04At (scaleMetric (Q n) (hQ n) (g n)) z)) ≤ J := by
    intro z hz
    have h := hJn z hz
    change Real.sqrt (normSq0S (scaleMetric (Q n) (hQ n) (g n)) z 4
      (metricRm04 (scaleMetric (Q n) (hQ n) (g n)) z)) ≤ J at h
    rw [metricRm04_apply] at h
    exact h
  have hv := hvol (Q n) (hQ n) (x n) W hchart y hy hgap hRm
  simpa only [ThreeSpace, finrank_euclideanSpace, Fintype.card_fin] using hv

end GC.LongTime.Ch11

end
