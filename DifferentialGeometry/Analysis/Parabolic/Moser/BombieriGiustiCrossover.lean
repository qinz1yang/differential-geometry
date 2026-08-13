import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiForward
import DifferentialGeometry.Analysis.Parabolic.Moser.BombieriGiustiReciprocal
import DifferentialGeometry.Analysis.Parabolic.Moser.Crossover

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.Parabolic.Moser

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Parabolic.Energy
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

def canonicalEarlyBombieriGiustiThresholdSum
    (n : ℕ) (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (p₀ c₀ A b τ B lower upper : ℝ) : ℝ :=
  ∑' k : ℕ, (3 / 4 : ℝ) ^ k *
    (bombieriGiustiThreshold p₀ c₀
      (canonicalEarlyBombieriGiustiReverseCost (I := I) (M := M)
        n g hdim p₀ A b τ B lower upper k) / 4)

def canonicalLateBombieriGiustiThresholdSum
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho : SmoothScalar g)
    (p₀ c₀ τ c d D lower upper : ℝ) : ℝ :=
  ∑' k : ℕ, (3 / 4 : ℝ) ^ k *
    (bombieriGiustiThreshold p₀ c₀
      (canonicalLateBombieriGiustiReverseCost (I := I) (M := M)
        g hdim rho τ c d D lower upper k) / 4)

def canonicalBombieriGiustiCrossoverBound
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho averagingCutoff : SmoothScalar g)
    (C p₀ A b τ c d D B lower upper : ℝ) : ℝ :=
  let c₀ := 2 * C * cutoffMass (I := I) (M := M) averagingCutoff
  Real.exp
      (logCenterDrift (I := I) (M := M) g averagingCutoff * (d - A)) *
    (Real.exp
        (canonicalEarlyBombieriGiustiThresholdSum (I := I) (M := M)
          (Module.finrank ℝ E) g hdim p₀ c₀ A b τ B lower upper) *
      Real.exp
        (canonicalLateBombieriGiustiThresholdSum (I := I) (M := M)
          g hdim rho p₀ c₀ τ c d D lower upper))

theorem localizedSpacetimeRpowNorm_mul_inv_le_canonicalBombieriGiustiCrossover_of_supersolution
    (g : SmoothRiemannianMetric I M)
    (hdim : 2 < (Module.finrank ℝ E : ℝ))
    (rho outer averagingCutoff : SmoothScalar g)
    (C : ℝ) (hC : 0 < C)
    (hP : HasLocalizedPoincareAtAverage (I := I) (M := M) g
      outer averagingCutoff C)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => u z.1 z.2))
    (hpos : ∀ t x, 0 < u t x)
    {p₀ A b τ c d D B lower upper : ℝ}
    (hp₀ : 0 < p₀) (hp₀_one : p₀ < 1)
    (hAb : A ≤ b) (hbτ : b < τ)
    (hτc : τ < c) (hcd : c ≤ d) (hdD : d < D)
    (hB : 0 ≤ B) (hlowerUpper : lower < upper)
    (hrho : ∀ x : M,
      g.inner x
          (gradFun (I := I) g rho.toFun x)
          (gradFun (I := I) g rho.toFun x) ≤ B)
    (hearlyMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k) ≠ 0)
    (hearlyMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k) A
          (bombieriGiustiIncreasingLevel b τ k)).real Set.univ ≤ 1)
    (hlateMeasure : ∀ k,
      localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k) ≠ 0)
    (hlateMeasure_le_one : ∀ k,
      (localizedSpacetimeMeasure (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper k)
          (bombieriGiustiDescendingLevel τ c k)
          (bombieriGiustiIncreasingLevel d D k)).real Set.univ ≤ 1)
    (houter : ∀ k x,
      (bombieriGiustiSpatialCutoff rho lower upper k).toFun x ^ 2 ≤
        outer.toFun x ^ 2)
    (hmass : 0 < cutoffMass (I := I) (M := M) averagingCutoff)
    (hpde : ∀ t ∈ Icc A D, ∀ x : M,
      Δ_g (I := I) g (smoothScalarSlice (I := I) g u hu t).toContMDiffMap x ≤
        deriv (fun q => u q x) t) :
    localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0) u p₀ A b *
      localizedSpacetimeRpowNorm (I := I) (M := M)
        (bombieriGiustiSpatialCutoff rho lower upper 0)
          (fun t x => (u t x)⁻¹) p₀ c d ≤
      canonicalBombieriGiustiCrossoverBound (I := I) (M := M)
        g hdim rho averagingCutoff C p₀ A b τ c d D B lower upper := by
  let rate := logCenterDrift (I := I) (M := M) g averagingCutoff
  let center := shiftedLogCenter (I := I) (M := M) g averagingCutoff
    u hu hpos τ
  let v := exponentialTimeRescale rate center u
  let c₀ := 2 * C * cutoffMass (I := I) (M := M) averagingCutoff
  let earlyBound := Real.exp
    (canonicalEarlyBombieriGiustiThresholdSum (I := I) (M := M)
      (Module.finrank ℝ E) g hdim p₀ c₀ A b τ B lower upper)
  let lateBound := Real.exp
    (canonicalLateBombieriGiustiThresholdSum (I := I) (M := M)
      g hdim rho p₀ c₀ τ c d D lower upper)
  have hτD : τ ≤ D := hτc.le.trans (hcd.trans hdD.le)
  have hearly : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0) v p₀ A b ≤
      earlyBound := by
    simpa only [v, rate, center, earlyBound, c₀,
      canonicalEarlyBombieriGiustiThresholdSum] using
      early_localizedSpacetimeRpowNorm_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution
        (I := I) (M := M) g hdim rho outer averagingCutoff C hC hP
          u hu hpos hp₀ hp₀_one hAb hbτ hB hlowerUpper hrho
          hearlyMeasure hearlyMeasure_le_one houter hmass
          (fun t ht x => hpde t ⟨ht.1, ht.2.trans hτD⟩ x)
  have hlate : localizedSpacetimeRpowNorm (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
        (fun t x => (v t x)⁻¹) p₀ c d ≤ lateBound := by
    simpa only [v, rate, center, lateBound, c₀,
      canonicalLateBombieriGiustiThresholdSum] using
      late_localizedSpacetimeRpowNorm_inv_le_exp_tsum_canonicalBombieriGiustiThreshold_of_supersolution
        (I := I) (M := M) g hdim rho outer averagingCutoff C hC hP
          u hu hpos hp₀ hτc hcd hdD hlowerUpper hlateMeasure
          hlateMeasure_le_one houter hmass
          (fun t ht x => hpde t ⟨hAb.trans (hbτ.le.trans ht.1), ht.2⟩ x)
  have hbound :=
    localizedSpacetimeRpowNorm_mul_inv_le_of_exponentialTimeRescale_bounds
      (I := I) (M := M)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      (bombieriGiustiSpatialCutoff rho lower upper 0)
      rate center u hu hpos hp₀
      (logCenterDrift_nonneg (I := I) (M := M) g averagingCutoff)
      (Real.exp_pos _).le hearly hlate
  simpa only [canonicalBombieriGiustiCrossoverBound, earlyBound, lateBound,
    c₀, rate, center, v] using hbound

end DifferentialGeometry.Analysis.Parabolic.Moser

end
