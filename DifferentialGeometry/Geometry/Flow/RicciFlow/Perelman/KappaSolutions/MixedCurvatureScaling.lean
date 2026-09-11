import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ParabolicScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MixedCurvatureFields
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.DerivativeNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import Mathlib.Analysis.SpecialFunctions.Pow.Real


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance mixedScalingC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance mixedScalingC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


theorem mixedCurvatureTensor_curvatureNormalizedSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier)
    (p q : ℕ) {s : ℝ} (hs : s ≤ 0) (x : M) :
    mixedCurvatureTensor (curvatureNormalizedSolution S t₀ Q hQ ht₀) p q s x =
      (Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (parabolicTime t₀ Q s) x := by
  have ht₀b : t₀ ≤ b := by simpa only [hcarrier, mem_Iic] using ht₀
  have htime (u : ℝ) (hu : u ≤ 0) : parabolicTime t₀ Q u ≤ b :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hu hQ.le)).trans ht₀b
  obtain ⟨A, hA⟩ := exists_ancient_mixed_curvature_fields S hS hcarrier hregular p
  have hdiff (j : ℕ) (u : ℝ) (hu : u ≤ b) :
      DifferentiableWithinAt ℝ (fun v => mixedCurvatureTensor S p j v x) (Iic b) u := by
    exact ((hA j u hu x).2.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin
        fun v hv => (hA j v hv x).1.symm) (hA j u hu x).1.symm).differentiableWithinAt
  induction q generalizing s with
  | zero =>
      simp only [mixedCurvatureTensor_zero, pow_zero, mul_one]
      have hrestrict : nablaKRm04Field (curvatureNormalizedSolution S t₀ Q hQ ht₀) s p =
          nablaKRm04Field (parabolicSolution S t₀ Q hQ ht₀) s p := by
        rw [nablaKRm_eq_iterCov, nablaKRm_eq_iterCov]
        rfl
      rw [hrestrict]
      rw [parabolicNablaKRm04Field]
      rfl
  | succ q ih =>
      let T := curvatureNormalizedSolution S t₀ Q hQ ht₀
      have heq : (fun u => mixedCurvatureTensor T p q u x) =ᶠ[𝓝[Iic 0] s]
          (fun u => (Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (parabolicTime t₀ Q u) x) :=
        Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun u hu => ih hu
      have hpoint := ih hs
      have hderiv := heq.derivWithin_eq hpoint
      change metricTimeDerivWithin T.base.metric (Iic 0)
          (fun u => mixedCurvatureTensor T p q u x) s = _
      rw [metricTimeDerivWithin]
      erw [hderiv]
      rw [hpoint]
      change metricTimeDerivWithin
          (fun u => scaleMetric Q hQ (S.base.metric (t₀ + u / Q))) (Iic 0)
          (fun u => (Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (t₀ + u / Q) x) s = _
      rw [metricTimeDerivWithin_parabolic S.base.metric
        (fun u => mixedCurvatureTensor S p q u x) hQ ht₀b hs
        (Q * Q⁻¹ ^ q) (hdiff q (parabolicTime t₀ Q s) (htime s hs))]
      have hc : (Q * Q⁻¹ ^ q) * Q⁻¹ = Q * Q⁻¹ ^ (q + 1) := by
        rw [pow_succ, mul_assoc]
      rw [hc]
      simp only [mixedCurvatureTensor, iteratedMetricTimeDerivWithin_succ,
        metricTimeDerivWithin, hcarrier, parabolicTime]


theorem mixedCurvatureNormSq_curvatureNormalizedSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier)
    (p q : ℕ) {s : ℝ} (hs : s ≤ 0) (x : M) :
    normSq0S (I := I) ((curvatureNormalizedSolution S t₀ Q hQ ht₀).base.metric s)
        x (4 + p) (mixedCurvatureTensor (curvatureNormalizedSolution S t₀ Q hQ ht₀) p q s x) =
      Q⁻¹ ^ (2 + p + 2 * q) * normSq0S (I := I) (S.base.metric (parabolicTime t₀ Q s))
        x (4 + p) (mixedCurvatureTensor S p q (parabolicTime t₀ Q s) x) := by
  rw [mixedCurvatureTensor_curvatureNormalizedSolution S hS hcarrier hregular
    t₀ Q hQ ht₀ p q hs x]
  change normSq0S (scaleMetric Q hQ (S.base.metric (parabolicTime t₀ Q s))) x (4 + p)
    ((Q * Q⁻¹ ^ q) • mixedCurvatureTensor S p q (parabolicTime t₀ Q s) x) = _
  rw [normSq0S_scale, normSq0S_smul, ← mul_assoc]
  congr 1
  have hexp : 4 + p = 2 + (2 + p) := by omega
  calc
    Q⁻¹ ^ (4 + p) * (Q * Q⁻¹ ^ q) ^ 2 =
        (Q⁻¹ ^ 2 * Q ^ 2) * (Q⁻¹ ^ (2 + p) * Q⁻¹ ^ (q * 2)) := by
      rw [hexp, pow_add, mul_pow, pow_mul]
      ring
    _ = Q⁻¹ ^ (2 + p + 2 * q) := by
      rw [← mul_pow, inv_mul_cancel₀ hQ.ne', one_pow, one_mul, ← pow_add]
      congr 1
      omega


theorem mixedCurvatureNorm_curvatureNormalizedSolution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b : ℝ} (hcarrier : D.carrier = Iic b) (hregular : D.regular = Iio b)
    (t₀ Q : ℝ) (hQ : 0 < Q) (ht₀ : t₀ ∈ D.carrier)
    (p q : ℕ) {s : ℝ} (hs : s ≤ 0) (x : M) :
    mixedCurvatureNorm (curvatureNormalizedSolution S t₀ Q hQ ht₀) p q s x =
      Q ^ (-(1 : ℝ) - (p : ℝ) / 2 - (q : ℝ)) *
        mixedCurvatureNorm S p q (parabolicTime t₀ Q s) x := by
  unfold mixedCurvatureNorm
  rw [mixedCurvatureNormSq_curvatureNormalizedSolution S hS hcarrier hregular
    t₀ Q hQ ht₀ p q hs x, Real.sqrt_mul (pow_nonneg (inv_nonneg.mpr hQ.le) _)]
  congr 1
  rw [← Real.rpow_natCast, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (inv_nonneg.mpr hQ.le), ← Real.rpow_neg_eq_inv_rpow]
  congr 1
  push_cast
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
