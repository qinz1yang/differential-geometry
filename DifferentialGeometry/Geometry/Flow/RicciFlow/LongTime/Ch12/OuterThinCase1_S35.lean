import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

/-- **(G1c, Case 1)** A point of the time-`t` stage that is not in the `accuracy(t)⁻¹`-ball
image of any core is `w`-collapsed at its curvature scale as soon as `accuracy t ≤ w`
(contrapositive of `thick_covered`). -/
theorem volumeCollapsed_of_not_covered_S35 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (B : BufferedPersistentCores F K) {w : ℝ}
    (hw : 0 < w) :
    ∃ T : ℝ, ∀ t (ht : B.start ≤ t), T ≤ t →
      ∀ x : (postStage F.observation t).Carrier,
        x ∉ ⋃ i : Fin B.count, B.map i t ht ''
          riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹ →
        volumeCollapsedAtCurvatureScale
          (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht))
            (postMetric F.observation t)) w x := by
  obtain ⟨T, hT⟩ := B.accuracy_decay w hw
  refine ⟨T, fun t ht hTt x hx r hr hcr => ?_⟩
  by_contra hcon
  have hlt : ENNReal.ofReal (w * r ^ 3) < ballVolume
      (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
        x r := not_le.mp hcon
  have hacc : B.accuracy t ≤ w := (hT t hTt).le
  have hle : ENNReal.ofReal (B.accuracy t * r ^ 3) ≤ ballVolume
      (scaleMetric t⁻¹ (inv_pos.mpr (B.start_pos.trans_le ht)) (postMetric F.observation t))
        x r :=
    le_trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hacc (by positivity))) hlt.le
  obtain ⟨i, hi⟩ := B.thick_covered t ht x r hr hcr hle
  exact hx (Set.mem_iUnion.mpr ⟨i, hi⟩)

end GC.LongTime.Ch12
