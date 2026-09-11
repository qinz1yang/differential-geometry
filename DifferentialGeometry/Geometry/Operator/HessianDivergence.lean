import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Hessian.ScalarBochner

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Operator

open Curvature Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem trace_nabla_hessian
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (x : M) (Y : TangentSpace I x) :
    metricTraceLastTwo0SAt3 (I := I) g
        (nablaHessSec (I := I) (metricCov g) (metricCov_smooth g)
          f f.contMDiff x) Y =
      differential1FormFun (I := I) (laplacian (metricCov g) g f) x
        (fun _ : Fin 1 => Y) := by
  have hnabla : TotalNabla0SRealizes (𝕜 := ℝ) (I := I) 2 (metricCov g)
      (hessianSec (metricCov g) (metricCov_smooth g) f f.contMDiff)
      (nablaHessSec (metricCov g) (metricCov_smooth g) f f.contMDiff) :=
    totalNabla0S_realizes 2 (metricCov g) _
      (totalNabla0S_regularity 2 (metricCov g) (metricCov_smooth g) _)
  have htrace (y : M) := (scalarLap_smooth (I := I) (metricCov g)
    (metricCov_smooth g) g (leviCivitaConnectionOfMetric_isMetricCompatible g)
    f f.contMDiff (x := y)).eq_trace (metricCov g) g f _
  have h := traceNablaHessianRealizesDLapAt_of_lapTrace (I := I)
    (metricCov g) g (leviCivitaConnectionOfMetric_isMetricCompatible g)
    f _ _ hnabla htrace x
  exact h Y

theorem hessian_divergence
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    (x : M) (Y : TangentSpace I x) :
    metricTraceFirstTwo0SAt (I := I) g
        (nablaHessSec (I := I) (metricCov g) (metricCov_smooth g)
          f f.contMDiff x) (fun _ : Fin 1 => Y) =
      differential1FormFun (I := I) (laplacian (metricCov g) g f) x
          (fun _ : Fin 1 => Y) +
        metricRicciAt g x (Curvature.vec2 Y (gradientFun g f x)) := by
  classical
  let b := Tensor.Coordinates.coordinateFrameAtToBasis (I := I) x
  let gInv := fun i j => Tensor.Coordinates.inverseMetricFlatModelInChartComponent
    (I := I) g x i j (extChartAt I x x)
  have hinv := Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
    (I := I) g x
  let K := metricCurvatureSections (I := I) g
  let du := duSec (I := I) f f.contMDiff
  let Hess := hessianSec (I := I) (metricCov g) (metricCov_smooth g) f f.contMDiff
  let third := nablaHessSec (I := I) (metricCov g) (metricCov_smooth g) f f.contMDiff
  let roughDu := fun y : M => metricTraceFirstTwo0STensor (I := I) g (third y)
  have hnabla := nablaHess_realizes (I := I) (metricCov g) (metricCov_smooth g)
    f f.contMDiff x
  have hsymm := oneFormLastTwoSymmAt_of_leviCivita_du (I := I) g f f.contMDiff
    du Hess (third x) (duSec_realizes f f.contMDiff) hnabla
  have hthird := oneFormThirdCovDerivCommAt_of_leviCivita (I := I) g
    K.rm13 du Hess (differential1FormFun f x) (third x)
    K.rm13Realizes (duSec_apply f f.contMDiff x) hnabla
  have hskew := rm13MetricSkewAt_of_leviCivita_realizes (I := I) g
    K.rm13 K.rm04 K.rm13Realizes K.rm04Realizes (x := x)
  have hrough : RoughLap0SRealizesMetricTrace (I := I) g (roughDu x) (third x) := by
    intro tail
    exact metricTraceFirstTwo0STensor_apply g (third x) tail
  have hdlap : TraceNablaHessianRealizesDLapAt (I := I) (metricCov g) g f
      (third x) := fun V => trace_nabla_hessian g f x V
  have h := oneForm_commutator_eval_of_lc (I := I) (metricCov g) g
    K.ricci K.rm13 f roughDu b gInv (third x) hinv K.ricciRealizes
    hsymm hthird hskew hrough hdlap
  simpa only [roughDu, metricTraceFirstTwo0STensor_apply, K, metricCurvatureSections,
    metricRicci_apply] using h Y

end DifferentialGeometry.Geometry.Operator
