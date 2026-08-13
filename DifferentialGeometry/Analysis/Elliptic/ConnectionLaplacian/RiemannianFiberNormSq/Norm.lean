import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.Defs
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqNormBridge
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RiemannianFiberNormSq.RiemannianFiberNormSqTensorInnerBridge
import DifferentialGeometry.Geometry.Metric.TensorInner.TensorRSRiemannianBundle


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.TensorRSRiemannianBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

@[implicit_reducible]
noncomputable def riemannianFiberNormedAddCommGroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) := by
  letI : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRS_riemannianBundle (I := I) (M := M) g r s
  let h : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) := inferInstance
  exact (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

noncomputable def riemannianFiberNorm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) : ℝ :=
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  ‖T‖

theorem riemannianFiberNorm_nonneg (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    0 ≤ riemannianFiberNorm g r s b T := by
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_nonneg T

theorem riemannianFiberNorm_eq_sqrt (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T =
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g r s b T) := by
  letI : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRS_riemannianBundle (I := I) (M := M) g r s
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  rw [riemannianFiberNorm, norm_eq_sqrt_tensorInnerPointwise]
  rw [← riemannianFiberNormSq_eq_tensorInnerPointwise]

theorem riemannianFiberNorm_sq (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T ^ 2 = riemannianFiberNormSq (I := I) (M := M) g r s b T := by
  rw [riemannianFiberNorm_eq_sqrt]
  exact Real.sq_sqrt (riemannianFiberNormSq_nonneg (I := I) (M := M) g r s b T)

theorem riemannianFiberNorm_eq_zero (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b T = 0 ↔ T = 0 := by
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_eq_zero

theorem riemannianFiberNorm_add_le (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (S T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b (S + T) ≤
      riemannianFiberNorm g r s b S + riemannianFiberNorm g r s b T := by
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    riemannianFiberNormedAddCommGroup g r s b
  exact norm_add_le S T

theorem riemannianFiberNorm_smul (g : SmoothRiemannianMetric I M) (r s : ℕ) (b : M)
    (c : ℝ) (T : TensorRSSpace r s I b) :
    riemannianFiberNorm g r s b (c • T) = |c| * riemannianFiberNorm g r s b T := by
  letI : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) :=
    tensorRS_riemannianBundle (I := I) (M := M) g r s
  let h : Bundle.RiemannianBundle (fun x : M => TensorRSSpace r s I x) := inferInstance
  letI : NormedAddCommGroup (TensorRSSpace r s I b) :=
    (h.g.toCore b).toNormedAddCommGroupOfTopology
      (h.g.continuousAt b) (h.g.isVonNBounded b)
  letI : NormedSpace ℝ (TensorRSSpace r s I b) :=
    (h.g.toCore b).toNormedSpaceOfTopology
      (h.g.continuousAt b) (h.g.isVonNBounded b)
  exact norm_smul c T

end Elliptic
end Analysis
end DifferentialGeometry
