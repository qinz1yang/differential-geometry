import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Connection
import DifferentialGeometry.Geometry.Operator.Laplacian
import DifferentialGeometry.Geometry.Operator.LaplacianBridge
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

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [T2Space M] in
theorem weightedLaplacian_add
    (g : SmoothRiemannianMetric I M) (f u v : C^∞⟮I, M; Real⟯) (x : M) :
    weightedLaplacian (I := I) g f (u + v) x =
      weightedLaplacian (I := I) g f u x +
        weightedLaplacian (I := I) g f v x := by
  rw [weightedLaplacian_apply, weightedLaplacian_apply,
    weightedLaplacian_apply, Δ_g_add]
  have hgrad : gradFun (I := I) g (u + v) x =
      gradFun (I := I) g u x + gradFun (I := I) g v x := by
    simpa only [ContMDiffMap.coe_add] using
      Operator.gradFun_add (I := I) g
        ((u.contMDiff x).mdifferentiableAt (by simp))
        ((v.contMDiff x).mdifferentiableAt (by simp))
  simp only [ContMDiffMap.coe_add]
  rw [hgrad]
  simp only [map_add]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem weightedLaplacian_const_smul
    (g : SmoothRiemannianMetric I M) (f u : C^∞⟮I, M; Real⟯)
    (a : Real) (x : M) :
    weightedLaplacian (I := I) g f (a • u) x =
      a * weightedLaplacian (I := I) g f u x := by
  have hgrad : MDiffAt
      (T% fun y : M => gradientFun (I := I) g u y) x :=
    (gradientFun_contMDiffAt (I := I) g (u.contMDiff x)).mdifferentiableAt
      (by simp)
  have hlap := laplacian_const_smul (I := I) (LeviCivita (I := I) g) g a
    (fun y => (u.contMDiff y).mdifferentiableAt (by simp)) hgrad
  have hscaled :
      ΔG (I := I) g (a • u) x =
        laplacian (I := I) (LeviCivita (I := I) g) g (a • u : M → Real) x :=
    (laplacian_levi_eq (I := I) g (a • u).contMDiff x).symm
  have hraw :
      ΔG (I := I) g u x =
        laplacian (I := I) (LeviCivita (I := I) g) g (u : M → Real) x :=
    (laplacian_levi_eq (I := I) g u.contMDiff x).symm
  rw [weightedLaplacian_apply, weightedLaplacian_apply,
    hscaled, hraw, hlap]
  have hgradScaled : gradFun (I := I) g (a • u) x =
      a • gradFun (I := I) g u x := by
    simpa only [ContMDiffMap.coe_smul] using
      Operator.gradFun_const_smul (I := I) g a
        ((u.contMDiff x).mdifferentiableAt (by simp))
  simp only [ContMDiffMap.coe_smul]
  rw [hgradScaled]
  simp only [map_smul, smul_eq_mul]
  ring

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
