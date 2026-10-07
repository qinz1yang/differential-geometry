import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessBallVolume

set_option autoImplicit false

/-!
# CX-SPINE G10：scalar gap 支付 canonical 体积条件

同一 connected component 中，若 C2*R(p)<R(x)，则 x 的 canonical witness 不可能是 whole 型。
特别地，实际生产 requiresVolume 后可调用已有 ball-volume theorem。
κ 只依赖 ε/C1/C2，先于 stage、metric、witness、低曲率点和测试半径。
-/

noncomputable section

open Set DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private theorem requiresVolume_of_scalar_gap_CXSP {P : OrientedThreeStage.{u}}
    {g : P.Metric} {ε C1 C2 : ℝ} {x p : P.Carrier}
    (W : SpatialCanonicalWitness g ε C1 C2 x) (hp : p ∈ connectedComponent x)
    (hgap : C2 * metricScalarAt g p < metricScalarAt g x) :
    W.alternative.requiresVolume := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hproper : W.domain.carrier ≠ connectedComponent x := by
    intro hwhole
    have hbound := (W.scalar_bounds p (hwhole.symm ▸ hp)).1
    have hmul := mul_le_mul_of_nonneg_left hbound hC2.le
    rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hmul
    exact not_lt_of_ge hmul hgap
  cases halt : W.alternative with
  | neck data => trivial
  | cap data deep => trivial
  | positive whole data sec => trivial
  | round whole data => exact (hproper whole).elim

/-- 同分支 scalar gap 实际支付 volume 分支，无需把 requiresVolume 当作输入。 -/
theorem exists_ball_volume_of_spatialCanonicalWitness_of_scalar_gap_CXSP (ε C1 C2 : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {x : P.Carrier}
      (W : SpatialCanonicalWitness g ε C1 C2 x), W.capTubeHasNeckChart ε →
      ∀ p ∈ connectedComponent x, C2 * metricScalarAt g p < metricScalarAt g x →
      ∀ r : ℝ, 0 < r → r ^ 4 * normSq0S g x 4 (metricRm04At g x) ≤ 1 →
      ENNReal.ofReal (κ * r ^ 3) ≤
        riemannianVolumeMeasure ThreeModel P.Carrier g (riemannianBallOf g x r) := by
  obtain ⟨κ, hκ, hvol⟩ := exists_ball_volume_of_spatialCanonicalWitness.{u} ε C1 C2
  refine ⟨κ, hκ, ?_⟩
  intro P g x W hchart p hp hgap r hr hcurv
  exact hvol W hchart (requiresVolume_of_scalar_gap_CXSP W hp hgap) r hr hcurv

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
