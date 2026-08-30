import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.RoughLaplacian
import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.TotalNabla0S

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

def weightedLaplacian
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯) : M → Real :=
  fun x => ΔG (I := I) g u x -
    g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem weightedLaplacian_apply
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯) (x : M) :
    weightedLaplacian (I := I) g f u x = ΔG (I := I) g u x -
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x) := rfl

def weightedRoughLaplacian0S
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) {s : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) (M := M) s x := by
  let cov := DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov
      (∞ : WithTop ℕ∞) := by
    simpa [cov, DifferentialGeometry.Geometry.Connection.LeviCivita] using
      (DifferentialGeometry.Geometry.Connection.leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) g)
  let hA := totalNabla0S_reg (E := E) (H := H) (I := I) (M := M) s cov hcov A
  let nablaA := totalNabla0S (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
    s cov A hA
  let hnablaA := totalNabla0S_reg (E := E) (H := H) (I := I) (M := M)
    (s + 1) cov hcov nablaA
  exact roughLap0STensor (I := I) g
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        (s + 1) cov nablaA x) -
    tensor0SCurry (I := I) (𝕜 := Real) (M := M) s x
      (totalNabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        s cov A x)
      (gradFun (I := I) g f x)

end DifferentialGeometry.Geometry.Operator
