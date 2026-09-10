import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

namespace Poincare.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]


theorem secondVariation_curveEnergy_geodesicEndpoints
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g (f 0) (Icc 0 L))
    (hinitial : HasGeodesicEquationAt (I := I) g (fun s => f s 0) 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s => f s L) 0) :
    HasDerivAt (fun s => deriv (fun r => curveEnergy (I := I) g (f r) 0 L) s)
      (2 * indexForm (I := I) g (f 0) 0 L
        (centralVariationField (I := I) f) (centralVariationField (I := I) f)) 0 := by
  have h := secondVariation_curveEnergy_eq_indexForm_add_boundary g f L hf hL hcentral
  have h0 := centralVariationAcceleration_eq_zero_of_geodesicEndpoint g f hf 0 hinitial
  have h1 := centralVariationAcceleration_eq_zero_of_geodesicEndpoint g f hf L hterminal
  simpa only [DifferentialGeometry.Geometry.Riemannian.Variation.secondVariationBoundary,
    h0, h1, map_zero, zero_apply, add_zero, sub_zero] using h

def centralCurvatureDensity (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ) : ℝ :=
  g.inner (f 0 t) (riemannOp (LeviCivita (I := I) g) (f 0 t)
    (centralVariationField (I := I) f t) (centralVelocity (I := I) f t)
    (centralVelocity (I := I) f t)) (centralVariationField (I := I) f t)


lemma indexFormIntegrand_eq_neg_centralCurvatureDensity
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (t : ℝ)
    (hparallel : covDerivAlong (I := I) g (f 0) (centralVariationField (I := I) f) t = 0) :
    indexFormIntegrand (I := I) g (f 0) (centralVariationField (I := I) f)
      (centralVariationField (I := I) f) t = -centralCurvatureDensity (I := I) g f t := by
  change g.inner (f 0 t)
    (covDerivAlong (I := I) g (f 0) (centralVariationField (I := I) f) t)
    (covDerivAlong (I := I) g (f 0) (centralVariationField (I := I) f) t) -
    centralCurvatureDensity (I := I) g f t = _
  rw [hparallel, map_zero, zero_sub]

theorem secondVariation_curveEnergy_parallel_geodesicEndpoints
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g (f 0) (Icc 0 L))
    (hinitial : HasGeodesicEquationAt (I := I) g (fun s => f s 0) 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s => f s L) 0)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (f 0) (centralVariationField (I := I) f) t = 0) :
    HasDerivAt (fun s => deriv (fun r => curveEnergy (I := I) g (f r) 0 L) s)
      (-2 * ∫ t in (0 : ℝ)..L, centralCurvatureDensity (I := I) g f t) 0 := by
  have h := secondVariation_curveEnergy_geodesicEndpoints g f L hf hL hcentral hinitial hterminal
  have hi : indexForm (I := I) g (f 0) 0 L
      (centralVariationField (I := I) f) (centralVariationField (I := I) f) =
      -(∫ t in (0 : ℝ)..L, centralCurvatureDensity (I := I) g f t) := by
    rw [indexForm, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hL.le] at ht
    exact indexFormIntegrand_eq_neg_centralCurvatureDensity g f t (hparallel t ht)
  rw [hi] at h
  convert h using 1
  ring

theorem secondVariation_curveEnergy_neg_of_parallel_geodesicEndpoints
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 < L)
    (hcentral : IsGeodesicOn (I := I) g (f 0) (Icc 0 L))
    (hinitial : HasGeodesicEquationAt (I := I) g (fun s => f s 0) 0)
    (hterminal : HasGeodesicEquationAt (I := I) g (fun s => f s L) 0)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) L,
      covDerivAlong (I := I) g (f 0) (centralVariationField (I := I) f) t = 0)
    (hpositive : ∀ t ∈ Icc (0 : ℝ) L, 0 < centralCurvatureDensity (I := I) g f t) :
    deriv (fun s => deriv (fun r => curveEnergy (I := I) g (f r) 0 L) s) 0 < 0 := by
  have hcont : ContinuousOn (centralCurvatureDensity (I := I) g f) (Icc 0 L) := by
    have hc := (centralVariation_indexFormIntegrand_continuousOn g f hf L).neg
    apply hc.congr
    intro t ht
    change centralCurvatureDensity (I := I) g f t =
      -indexFormIntegrand (I := I) g (f 0) (centralVariationField (I := I) f)
        (centralVariationField (I := I) f) t
    rw [indexFormIntegrand_eq_neg_centralCurvatureDensity g f t (hparallel t ht), neg_neg]
  have hpos := intervalIntegral.integral_pos hL hcont
    (fun t ht => (hpositive t ⟨ht.1.le, ht.2⟩).le)
    ⟨0, ⟨le_rfl, hL.le⟩, hpositive 0 ⟨le_rfl, hL.le⟩⟩
  rw [(secondVariation_curveEnergy_parallel_geodesicEndpoints g f L hf hL
    hcentral hinitial hterminal hparallel).deriv]
  linarith

end Poincare.Geometry.Riemannian.Variation
