import DifferentialGeometry.Geometry.Operator.Hessian.TimeDerivative
import DifferentialGeometry.Geometry.Operator.MetricTraceTimeDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.Trace
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

theorem laplacian_leviCivita_hasDerivAt
    (g : ℝ → SmoothRiemannianMetric I M)
    (h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2) (t : ℝ)
    (hg : ∀ x v w, HasDerivAt (fun r => (g r).inner x v w) (h x (vec2 v w)) t)
    (hgs : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (f : ℝ → M → ℝ) (hfs : ∀ r, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f r))
    (ft : M → ℝ) (hft : ContMDiff I 𝓘(ℝ, ℝ) ∞ ft)
    (hf : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (t, y))
    (ht : ∀ y, HasDerivAt (fun r => f r y) (ft y) t) (x : M) :
    HasDerivAt (fun r => laplacian (LeviCivita (g r)) (g r) (f r) x)
      (laplacian (LeviCivita (g t)) (g t) ft x -
        inner0S (g t) x 2 (h x)
          (hessianSec (LeviCivita (g t))
            (leviCivita_contMDiffCovariantDerivativeLocally (g t)) (f t) (hfs t) x) -
        metricTracePair0SAt (g t)
          (connectionDifferenceOutput (leviCivitaVariation g t x) (duSec (f t) (hfs t) x))) t := by
  let H := fun r => hessianSec (I := I) (LeviCivita (g r))
    (leviCivita_contMDiffCovariantDerivativeLocally (g r)) (f r) (hfs r) x
  let Ht := hessianSec (I := I) (LeviCivita (g t))
    (leviCivita_contMDiffCovariantDerivativeLocally (g t)) ft hft x
  let C := connectionDifferenceOutput (I := I) (leviCivitaVariation g t x)
    (duSec (I := I) (f t) (hfs t) x)
  have hH := hessianSec_leviCivita_hasDerivAt g h t hg hgs f hfs ft hft hf ht x
  have hmain := hasDerivAt_metricTracePair0SAt (I := I) g (h x) H (Ht - C) (hg x) hH
  have heq (r : ℝ) : laplacian (LeviCivita (g r)) (g r) (f r) x =
      metricTracePair0SAt (g r) (H r) :=
    (scalarLap_smooth (LeviCivita (g r)) (leviCivita_contMDiffCovariantDerivativeLocally (g r))
      (g r) (leviCivitaConnectionOfMetric_isMetricCompatible (g r)) (f r) (hfs r)).eq_trace
  have htEq : laplacian (LeviCivita (g t)) (g t) ft x =
      metricTracePair0SAt (g t) Ht :=
    (scalarLap_smooth (LeviCivita (g t)) (leviCivita_contMDiffCovariantDerivativeLocally (g t))
      (g t) (leviCivitaConnectionOfMetric_isMetricCompatible (g t)) ft hft).eq_trace
  apply (hmain.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)).congr_deriv
  rw [metricTracePair0SAt_sub, ← htEq]
  dsimp only [H, C]
  ring

end DifferentialGeometry.Geometry.Operator

end

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [I.Boundaryless]

theorem laplacian_leviCivita_hasDerivAt_of_ricci_deriv
    (g : ℝ → SmoothRiemannianMetric I M)
    (c t : ℝ)
    (hg : ∀ x v w, HasDerivAt (fun r => (g r).inner x v w) (c * metricRicci (g t) x (vec2 v w)) t)
    (hgs : ∀ (Y Z : ContMDiffSection I E ∞ (TangentSpace I)), ∀ x,
      ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2
        (fun p : ℝ × M => (g p.1).inner p.2 (Y p.2) (Z p.2)) (t, x))
    (f : ℝ → M → ℝ) (hfs : ∀ r, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f r))
    (ft : M → ℝ) (hft : ContMDiff I 𝓘(ℝ, ℝ) ∞ ft)
    (hf : ∀ y, ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => f p.1 p.2) (t, y))
    (ht : ∀ y, HasDerivAt (fun r => f r y) (ft y) t) (x : M) :
    HasDerivAt (fun r => laplacian (LeviCivita (g r)) (g r) (f r) x)
      (laplacian (LeviCivita (g t)) (g t) ft x -
        c * inner0S (g t) x 2 (metricRicci (g t) x)
          (hessianSec (LeviCivita (g t))
            (leviCivita_contMDiffCovariantDerivativeLocally (g t)) (f t) (hfs t) x)) t := by
  let h : Tensor0SField (𝕜 := ℝ) (I := I) (M := M) (n := ∞) 2 := c • metricRicci (g t)
  have hd (y : M) (v w : TangentSpace I y) :
      HasDerivAt (fun r => (g r).inner y v w) (h y (vec2 v w)) t := by
    change HasDerivAt (fun r => (g r).inner y v w) (c * metricRicci (g t) y (vec2 v w)) t
    exact hg y v w
  have hl := laplacian_leviCivita_hasDerivAt g h t hd hgs f hfs ft hft hf ht x
  have hz := metricTracePair0SAt_connectionDifferenceOutput_leviCivitaVariation_eq_zero_of_ricci_deriv
    g c t hg hgs x (duSec (I := I) (f t) (hfs t) x)
  rw [hz, sub_zero] at hl
  change HasDerivAt _ (laplacian (LeviCivita (g t)) (g t) ft x -
    inner0S (g t) x 2 (c • metricRicci (g t) x) _) t at hl
  simpa only [_root_.Tensor0SBundle.inner0S_smul_left] using hl

end DifferentialGeometry.Geometry.Operator

end
