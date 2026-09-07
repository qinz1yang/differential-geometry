import DifferentialGeometry.Geometry.Comparison.Distance.Calabi
import DifferentialGeometry.Geometry.Operator.Laplacian.Barrier

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Operator

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M]

theorem dist_isLaplacianLEBarrierAt
    [RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (riemannianEDist I O x).toReal
    IsLaplacianLEBarrierAt (I := I) g
      (fun y : M => (riemannianEDist I O y).toReal)
      (2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
        ((Module.finrank Real E - 1 : Nat) : Real) * q) x := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let _ : T2Space (TangentBundle I M) := inferInstance
  dsimp only
  obtain ⟨φ, hφ, hφx, huφ, _hgrad, hlap⟩ :=
    calabiDist_support (I := I) (M := M) g hEnorm q hq hRic hOx hfin
  exact IsLaplacianLEBarrierAt.of_upperSupport
    (I := I) (M := M) g hφ hφx huφ hlap

end DifferentialGeometry.Geometry.Riemannian
