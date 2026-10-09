import DifferentialGeometry.Topology.ProjectiveSpace.SphereHalfTurnFrame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelCurvatureTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Metric.Scaling

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Module
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

local notation "S" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "CI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance cylinderNullSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  [Inhabited M]

private local instance cylinderNullC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

theorem cylinderCover_exists_null_plane
    (g : SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    (Psi : (S × ℝ) ≃ₘ⟮CI, I⟯ UniversalCover M)
    (hproduct : ∀ (y : S) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Psi (y, s))
          (mfderiv CI I Psi (y, s) (v, a)) (mfderiv CI I Psi (y, s) (w, b)) =
        lambda * (gS).inner y v w + a * b) :
    ∃ x : M, ∃ a b : TangentSpace I x,
      0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 ∧
        metricRm04StandardAt g x a b b a = 0 := by
  let h := scaleMetric lambda hlambda gS
  let gP := Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi
  have hprod : ∀ (y : S) (s : ℝ) (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      gP.inner (y, s) (v, a) (w, b) = h.inner y v w + a * b := by
    intro y s v w a b
    exact (Diffeomorph.pullbackMetricCross_inner
      (UniversalCover.liftedMetric (I := I) g) Psi (y, s) (v, a) (w, b)).trans
        (by simpa only [h, scaleMetric_inner] using hproduct y s v w a b)
  let y : S := sphereEquator 0
  let v : TangentSpace (𝓡 2) y := sphereHalfTurnBasis 0 0
  have hv : v ≠ 0 := (sphereHalfTurnBasis 0).ne_zero 0
  let p : S × ℝ := (y, 0)
  let x : M := UniversalCover.proj (Psi p)
  let a : TangentSpace I x := mfderiv CI I Psi p (v, 0)
  let b : TangentSpace I x := mfderiv CI I Psi p ((0 : TangentSpace (𝓡 2) y), 1)
  have hAA : g.inner x a a = lambda * (gS).inner y v v := by
    refine (UniversalCover.liftedMetric_inner_eq g (Psi p) a a).trans ?_
    have hh := hproduct y 0 v v 0 0
    simpa only [mul_zero, add_zero] using hh
  have hBB : g.inner x b b = 1 := by
    refine (UniversalCover.liftedMetric_inner_eq g (Psi p) b b).trans ?_
    have hh := hproduct y 0 0 0 1 1
    simpa only [b, p, map_zero, zero_mul, mul_zero, one_mul, add_zero, zero_add] using hh
  have hAB : g.inner x a b = 0 := by
    refine (UniversalCover.liftedMetric_inner_eq g (Psi p) a b).trans ?_
    have hh := hproduct y 0 v 0 0 1
    simpa only [a, b, p, map_zero, mul_zero, zero_mul, add_zero] using hh
  refine ⟨x, a, b, ?_, ?_⟩
  · rw [hAA, hBB, hAB, zero_pow (by decide : 2 ≠ 0), sub_zero, mul_one]
    exact mul_pos hlambda ((gS).pos y v hv)
  · have hprodRm := metricRm04At_product_real_of_inner_eq h gP hprod y 0
      (vec4 (I := 𝓡 2) (M := S) (x := y) v 0 0 v) (![0, 1, 1, 0] : Fin 4 → ℝ)
    have hslots : (fun i : Fin 4 => ((vec4 (I := 𝓡 2) (M := S) (x := y) v 0 0 v) i,
        (![0, 1, 1, 0] : Fin 4 → ℝ) i)) =
          vec4 (I := CI) (M := S × ℝ) (x := p) (v, 0) (0, 1) (0, 1) (v, 0) := by
      funext i
      fin_cases i <;> rfl
    have hzero : metricRm04StandardAt (I := CI) gP p (v, 0) (0, 1) (0, 1) (v, 0) = 0 := by
      exact (congrArg (metricRm04At gP p) hslots.symm).trans
        (hprodRm.trans ((metricRm04At h y).map_coord_zero (1 : Fin 4) (by rfl)))
    have hpull := metricRm04Standard_pullbackCross
      (UniversalCover.liftedMetric (I := I) g) Psi p (v, 0) (0, 1) (0, 1) (v, 0)
    have hlift := UniversalCover.metricRm_lifted g (Psi p) a b b a
    exact hlift.symm.trans (hpull.symm.trans hzero)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
