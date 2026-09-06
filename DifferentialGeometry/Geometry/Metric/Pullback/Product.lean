import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry

open Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N]
variable [T2Space M] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem Diffeomorph.pullbackMetric_prodCongr
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Phi : M ≃ₘ⟮I, I⟯ M) (Psi : N ≃ₘ⟮J, J⟯ N) :
    Diffeomorph.pullbackMetric (g.prod h) (Phi.prodCongr Psi) =
      (Diffeomorph.pullbackMetric g Phi).prod
        (Diffeomorph.pullbackMetric h Psi) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.prod_inner,
    SmoothRiemannianMetric.prod_inner,
    Diffeomorph.pullbackMetric_inner,
    Diffeomorph.pullbackMetric_inner]
  have hPhi : MDiffAt (Phi : M → M) x.1 :=
    Phi.contMDiff.mdifferentiableAt (by simp)
  have hPsi : MDiffAt (Psi : N → N) x.2 :=
    Psi.contMDiff.mdifferentiableAt (by simp)
  rw [Diffeomorph.coe_prodCongr]
  rw [mfderiv_prodMap hPhi hPsi]
  simp [ContinuousLinearMap.prodMap]
  rfl

end DifferentialGeometry
