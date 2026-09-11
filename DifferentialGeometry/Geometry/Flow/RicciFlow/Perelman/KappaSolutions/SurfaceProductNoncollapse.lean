import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductVolume

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance surfaceProductNoncollapseMeasurable : MeasurableSpace M := borel M
private local instance surfaceProductNoncollapseBorel : BorelSpace M := ⟨rfl⟩
private local instance surfaceProductNoncollapseC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem surfaceProduct_tensor_half_noncollapsed
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hnoncollapse : ∀ (p : M × ℝ) (r : ℝ), 0 < r →
      (∀ z : M × ℝ, riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP p z <
          ENNReal.ofReal r →
        r ^ 4 * normSq0S (I := I.prod 𝓘(ℝ, ℝ)) gP z 4
          (metricRm04At (I := I.prod 𝓘(ℝ, ℝ)) gP z) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ 3 ≤
        riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
          {z : M × ℝ | riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP p z <
            ENNReal.ofReal r})
    (y : M) (r : ℝ) (hr : 0 < r)
    (hcurvature : ∀ z : M, riemannianEDistOf (I := I) h y z < ENNReal.ofReal r →
      r ^ 4 * normSq0S (I := I) h z 4 (metricRm04At (I := I) h z) ≤ 1) :
    ENNReal.ofReal (kappa / 2) * ENNReal.ofReal r ^ 2 ≤
      riemannianVolumeMeasure (I := I) (M := M) h
        {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} := by
  apply surfaceProduct_half_noncollapse_of_volume_lower h gP hprod y r kappa hr hkappa
  apply hnoncollapse (y, 0) r hr
  intro z hz
  have hbase : riemannianEDistOf (I := I) h y z.1 < ENNReal.ofReal r :=
    lt_of_le_of_lt (surfaceProduct_fst_edist_le h gP hprod (y, 0) z) hz
  have hproduct (w : M) (s : ℝ) (v u : TangentSpace I w) (a c : ℝ) :
      gP.inner (w, s) (v, a) (u, c) = h.inner w v u + a * c :=
    hprod (w, s) (v, a) (u, c)
  have hnorm := metricRmNormSq_product_real_of_inner_eq h gP hproduct z.1 z.2
  rw [hnorm]
  exact hcurvature z.1 hbase

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
