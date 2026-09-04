import DifferentialGeometry.Geometry.Operator.Laplacian.TensorInner
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.CovariantDerivative

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem laplacianAt_inner0S_eq_inner_roughLap_flowG_of_flat
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    {s : ℕ} {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    {t : Real} {x : M}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s)
    (nablaB : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 1))
    (nabla2B : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (s + 2))
    (hA : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s (S.base.connection t) A nablaA)
    (h2A : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (S.base.connection t) nablaA nabla2A)
    (hB : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      s (S.base.connection t) B nablaB)
    (h2B : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s + 1) (S.base.connection t) nablaB nabla2B)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (gInv : Idx -> Idx -> Real)
    (hinv : MetricInverseInBasisGen (I := I) (S.base.metric t) x basis gInv)
    (hBflat1 : nablaB x = 0)
    (hBflat2 : metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2B x) = 0) :
    laplacianAt (I := I) (flowG (I := I) S) t
        (fun y : M => inner0S (I := I) (S.base.metric t) y s (A y) (B y)) x =
      inner0S (I := I) (S.base.metric t) x s
        (metricTrace0S2TensorInBasis (I := I) basis gInv (nabla2A x)) (B x) := by
  classical
  have hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally
      ((flowG (I := I) S).connection t) (∞ : WithTop ℕ∞) := by
    simpa [flowG, SolutionFamily.connection] using
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (S.base.metric t))
  simpa [flowG] using
    laplacianAt_inner0S_eq_inner_roughLap_of_flat (I := I)
      (G := flowG (I := I) S) (t := t) (x := x)
      A nablaA nabla2A B nablaB nabla2B
      (by simpa [flowG] using hA) (by simpa [flowG] using h2A)
      (by simpa [flowG] using hB) (by simpa [flowG] using h2B)
      hcov basis gInv (by simpa [flowG] using hinv)
      hBflat1 (by simpa [flowG] using hBflat2)

end

end DifferentialGeometry.PDE.RicciFlow
