import DifferentialGeometry.Geometry.Operator.WeightedLaplacian
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SBochnerProduct
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.Connection

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [SigmaCompactSpace M] in
theorem weightedLaplacian_normSq0S
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) {s : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) s) (x : M) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let nablaA := totalNabla0S (I := I) s cov A
      (totalNabla0S_reg (I := I) s cov hcov A)
    weightedLaplacian (I := I) g f
        (⟨fun y : M => normSq0S (I := I) g y s (A y),
          normSq0S_smooth (I := I) g A⟩ : C^∞⟮I, M; Real⟯) x =
      2 * inner0S (I := I) g x s
          (weightedRoughLaplacian0S (I := I) g f A x) (A x) +
        2 * normSq0S (I := I) g x (s + 1) (nablaA x) := by
  classical
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  have hmc : IsMetricCompatibleGen (I := I) cov g := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  let nablaA := totalNabla0S (I := I) s cov A
    (totalNabla0S_reg (I := I) s cov hcov A)
  let nabla2A := totalNabla0S (I := I) (s + 1) cov nablaA
    (totalNabla0S_reg (I := I) (s + 1) cov hcov nablaA)
  let u : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => normSq0S (I := I) g y s (A y), normSq0S_smooth (I := I) g A⟩
  let du := duSec (I := I) (u : M → Real) u.contMDiff
  let Hess := hessianSec (I := I) cov hcov (u : M → Real) u.contMDiff
  have hA : TotalNabla0SRealizes (I := I) s cov A nablaA :=
    totalNabla0S_realizes (I := I) s cov A _
  have h2A : TotalNabla0SRealizes (I := I) (s + 1) cov nablaA nabla2A :=
    totalNabla0S_realizes (I := I) (s + 1) cov nablaA _
  let Idx := CoordinateIdx (𝕜 := Real) E
  let basis : Module.Basis Idx Real (TangentSpace I x) :=
    coordinateFrameAtToBasis (I := I) x
  let gInv : Idx → Idx → Real := fun i j =>
    inverseMetricFlatModelInChartComponent (I := I) g x i j (extChartAt I x x)
  have hinv : MetricInverseInBasis (I := I) g x basis gInv := by
    exact inverseMetricFlatModelInChart_metricInverseInBasis_center (I := I) g x
  let X : Idx → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _) := fun i =>
    (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis i)).choose
  have hX : SmoothBasisFieldsAt (I := I) basis X := by
    intro i
    exact (ContMDiffSection.exists_eq_at_gen
      (I := I) (F := E) (V := TangentSpace I) (n := (⊤ : ℕ∞))
      x (basis i)).choose_spec
  have hsplit := tensorNormBochnerSplit_mc (I := I) cov g hmc basis gInv hinv X hX
    A nablaA nabla2A hA h2A du Hess
    (duSec_realizes (I := I) (u : M → Real) u.contMDiff)
    (hessianSec_realizesAt (I := I) cov hcov (u : M → Real) u.contMDiff x)
  have hlap : ΔG (I := I) g u x =
      2 * inner0S (I := I) g x s (roughLap0STensor (I := I) g (nabla2A x)) (A x) +
        2 * normSq0S (I := I) g x (s + 1) (nablaA x) := by
    change ΔG (I := I) g ⟨(u : M → Real), u.contMDiff⟩ x = _
    rw [← laplacian_levi_eq (I := I) g u.contMDiff x]
    rw [(scalarLap_smooth (I := I) cov hcov g hmc
      (u : M → Real) u.contMDiff).eq_trace]
    rw [scalarLapTraceAt_eq_firstTwo]
    rw [← metricTrace0S2InBasis_eq_metricTrace (I := I) g basis gInv hinv
      (Hess x) Fin.elim0]
    simpa [roughLap0STensor, metricTraceFirstTwo0STensor, basis, gInv, Hess] using hsplit
  have hdrift :
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x) =
        2 * inner0S (I := I) g x s
          (tensor0SCurry (I := I) (s := s) x (nablaA x)
            (gradFun (I := I) g f x)) (A x) := by
    have hdu := du_norm0S (I := I) cov g hmc A nablaA hA du
      (duSec_realizes (I := I) (u : M → Real) u.contMDiff)
      (gradFun (I := I) g f x)
    calc
      g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g u x) =
          g.inner x (gradFun (I := I) g u x) (gradFun (I := I) g f x) := g.symm x _ _
      _ = differential1FormFun (I := I) (u : M → Real) x
          (fun _ : Fin 1 => gradFun (I := I) g f x) := by
            exact (differential1FormFun_apply_eq_inner_gradientFun
              (I := I) g (u : M → Real) x (gradFun (I := I) g f x)).symm
      _ = du x (fun _ : Fin 1 => gradFun (I := I) g f x) := by
            rw [duSec_apply]
      _ = _ := hdu
  change weightedLaplacian (I := I) g f u x =
    2 * inner0S (I := I) g x s
        (weightedRoughLaplacian0S (I := I) g f A x) (A x) +
      2 * normSq0S (I := I) g x (s + 1) (nablaA x)
  rw [weightedLaplacian_apply, hlap, hdrift]
  rw [weightedRoughLaplacian0S]
  change
    2 * inner0S (I := I) g x s (roughLap0STensor (I := I) g (nabla2A x)) (A x) +
          2 * normSq0S (I := I) g x (s + 1) (nablaA x) -
        2 * inner0S (I := I) g x s
          (tensor0SCurry (I := I) (s := s) x (nablaA x)
            (gradFun (I := I) g f x)) (A x) =
      2 * inner0S (I := I) g x s
          (roughLap0STensor (I := I) g (nabla2A x) -
            tensor0SCurry (I := I) (s := s) x (nablaA x)
              (gradFun (I := I) g f x)) (A x) +
        2 * normSq0S (I := I) g x (s + 1) (nablaA x)
  rw [inner0S_sub_left]
  ring

end DifferentialGeometry.Geometry.Operator
