import DifferentialGeometry.Geometry.Comparison.BusemannLaplacian
import DifferentialGeometry.Geometry.Comparison.BusemannLine

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold

namespace DifferentialGeometry.Geometry.Riemannian

open Geometry.Curvature
open Geometry.Operator
open BonnetMyers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem IsMinimizingLine.busemann_add_reverse_isLaplacianLEDistributionalOn
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsMinimizingLine (I := I) g γ)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g 0) :
    IsLaplacianLEDistributionalOn (I := I) g
      (fun x : M ↦ busemann (I := I) γ x +
        busemann (I := I) (fun t : ℝ ↦ γ (-t)) x)
      (fun _ : M ↦ 0) univ := by
  have hpos := busemann_isLaplacianLEDistributionalOn
    (I := I) g hEnorm hγ.positive_ray hd hRic
  have hneg := busemann_isLaplacianLEDistributionalOn
    (I := I) g hEnorm hγ.negative_ray hd hRic
  have hsum := hpos.add hneg
  have hu :
      busemann (I := I) γ + busemann (I := I) (fun t : ℝ ↦ γ (-t)) =
        fun x : M ↦ busemann (I := I) γ x +
          busemann (I := I) (fun t : ℝ ↦ γ (-t)) x := by
    funext x
    simp only [Pi.add_apply]
  have hz :
      ((fun _ : M ↦ (0 : ℝ)) + fun _ : M ↦ (0 : ℝ)) =
        fun _ : M ↦ (0 : ℝ) := by
    funext x
    simp only [Pi.add_apply, zero_add]
  rw [hu, hz] at hsum
  exact hsum

end DifferentialGeometry.Geometry.Riemannian
