import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Measure.LocalIsometry

noncomputable section
open Set Function Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N] [SigmaCompactSpace N]
  {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem riemannianVolumeMeasure_preimage_ge_of_curvature_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric J N) (f : M → N)
    (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    {a b K : ℝ} (hK : 0 ≤ K) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (hRm : ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2)
    (hterminal : ∀ x (v w : TangentSpace I x),
      (S.base.metric b).inner x v w =
        g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (U : Set N) (hU : MeasurableSet U) (hinside : U ⊆ range f)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ENNReal.ofReal (Real.exp (-((Module.finrank ℝ E : ℝ) ^ 3 * K * (b - t)))) *
      riemannianVolumeMeasure J N g U ≤
        riemannianVolumeMeasure I M (S.base.metric t) (f ⁻¹' U) := by
  have hB : b ∈ Icc a b := ⟨ht.1.trans ht.2, le_rfl⟩
  let A := (Module.finrank ℝ E : ℝ) ^ 3 * K * (b - t)
  let C := Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * K * (b - t))
  have hpre : MeasurableSet (f ⁻¹' U) := hf.contMDiff.continuous.measurable hU
  have hmetric (x : M) (v : TangentSpace I x) :
      (S.base.metric b).inner x v v ≤ C * (S.base.metric t).inner x v v := by
    have hh := (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular x
      (fun u hu => hRm u hu x) hB ht v).2
    simpa only [Real.sqrt_sq hK, abs_of_nonneg (sub_nonneg.mpr ht.2)] using hh
  have hvol := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    (S.base.metric t) (S.base.metric b) (Real.exp_pos _) hpre (fun x _ => hmetric x)
  have hconst : Real.sqrt (C ^ Module.finrank ℝ E) = Real.exp A := by
    rw [show C = Real.exp (2 * (Module.finrank ℝ E : ℝ) ^ 2 * K * (b - t)) from rfl,
      ← Real.exp_nat_mul, ← Real.exp_half]
    congr 1
    dsimp [A]
    ring
  rw [hconst] at hvol
  have heq := Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    (S.base.metric b) g f hf hinj hterminal hpre
  rw [image_preimage_eq_of_subset hinside] at heq
  rw [heq] at hvol
  change ENNReal.ofReal (Real.exp (-A)) * _ ≤ _
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-A)) *
        (ENNReal.ofReal (Real.exp A) * riemannianVolumeMeasure I M (S.base.metric t) (f ⁻¹' U)) :=
      mul_le_mul' le_rfl hvol
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]

end DifferentialGeometry.PDE.RicciFlow
