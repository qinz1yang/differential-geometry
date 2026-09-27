import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceProductBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RiemannianProduct

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

private theorem surfaceProductVolume_cast_apply {X : Type*}
    {m₁ m₂ : MeasurableSpace X} (hm : m₁ = m₂)
    (μ : @Measure X m₁) (A : Set X) :
    (cast (congrArg (fun m : MeasurableSpace X => @Measure X m) hm) μ) A = μ A := by
  cases hm
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance surfaceProductVolumeMeasurable : MeasurableSpace M := borel M
private local instance surfaceProductVolumeBorel : BorelSpace M := ⟨rfl⟩

theorem surfaceProduct_ball_volume_le
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (y : M) (r : ℝ) (hr : 0 < r) :
    riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
        {p : M × ℝ | riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP (y, 0) p <
          ENNReal.ofReal r} ≤
      ENNReal.ofReal (2 * r) * riemannianVolumeMeasure (I := I) (M := M) h
        {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} := by
  have hproduct (z : M) (s : ℝ) (v w : TangentSpace I z) (a c : ℝ) :
      gP.inner (z, s) (v, a) (w, c) = h.inner z v w + a * c :=
    hprod (z, s) (v, a) (w, c)
  calc
    riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
        {p : M × ℝ | riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP (y, 0) p <
          ENNReal.ofReal r} ≤
        riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
          ({z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} ×ˢ
            Set.Ioo (-r) r) :=
      measure_mono (surfaceProduct_ball_subset h gP hprod y r hr)
    _ = riemannianVolumeMeasure (I := I) (M := M) h
          {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} *
        (volume : Measure ℝ) (Set.Ioo (-r) r) := by
      rw [riemannianVolumeMeasure_product_real_of_inner_eq h gP hproduct,
        surfaceProductVolume_cast_apply (BorelSpace.measurable_eq (α := M × ℝ)),
        Measure.prod_prod]
    _ = ENNReal.ofReal (2 * r) * riemannianVolumeMeasure (I := I) (M := M) h
          {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} := by
      rw [Real.volume_Ioo, sub_neg_eq_add, ← two_mul, mul_comm]

theorem surfaceProduct_half_noncollapse_of_volume_lower
    (h : SmoothRiemannianMetric I M)
    (gP : SmoothRiemannianMetric (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))
    (hprod : ∀ (p : M × ℝ) (v w : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p),
      gP.inner p v w = h.inner p.1 v.1 w.1 + v.2 * w.2)
    (y : M) (r kappa : ℝ) (hr : 0 < r) (hkappa : 0 ≤ kappa)
    (hlower : ENNReal.ofReal kappa * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure (I := I.prod 𝓘(ℝ, ℝ)) (M := M × ℝ) gP
        {p : M × ℝ | riemannianEDistOf (I := I.prod 𝓘(ℝ, ℝ)) gP (y, 0) p <
          ENNReal.ofReal r}) :
    ENNReal.ofReal (kappa / 2) * ENNReal.ofReal r ^ 2 ≤
      riemannianVolumeMeasure (I := I) (M := M) h
        {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} := by
  have htwo : 0 < 2 * r := mul_pos (by norm_num) hr
  have htwo_ne : ENNReal.ofReal (2 * r) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr htwo)
  apply (ENNReal.mul_le_mul_iff_right htwo_ne ENNReal.ofReal_ne_top).mp
  calc
    ENNReal.ofReal (2 * r) *
        (ENNReal.ofReal (kappa / 2) * ENNReal.ofReal r ^ 2) =
        ENNReal.ofReal ((2 * r) * ((kappa / 2) * r ^ 2)) := by
      rw [ENNReal.ofReal_mul htwo.le,
        ENNReal.ofReal_mul (div_nonneg hkappa (by norm_num)),
        ENNReal.ofReal_pow hr.le]
    _ = ENNReal.ofReal (kappa * r ^ 3) := by
      congr 1
      ring
    _ = ENNReal.ofReal kappa * ENNReal.ofReal r ^ 3 := by
      rw [ENNReal.ofReal_mul hkappa, ENNReal.ofReal_pow hr.le]
    _ ≤ ENNReal.ofReal (2 * r) * riemannianVolumeMeasure (I := I) (M := M) h
          {z : M | riemannianEDistOf (I := I) h y z < ENNReal.ofReal r} :=
      hlower.trans (surfaceProduct_ball_volume_le h gP hprod y r hr)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
