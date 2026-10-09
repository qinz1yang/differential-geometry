import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

theorem two_mul_sqrt_mul_arcLength_le_lLength
    (S : SolutionOn (I := I) (M := M) D)
    (T : Real) (gamma : Real → M)
    (gRef : SmoothRiemannianMetric I M)
    (a b c Q : Real)
    (hab : a ≤ b) (hc : 0 ≤ c) (hQ : 0 ≤ Q)
    (hgamma : ContMDiffOn 𝓘(Real, Real) I 1 gamma (Icc a b))
    (hden : IntervalIntegrable (lDensity S T gamma) volume a b)
    (hscalar : ∀ᵐ tau ∂volume.restrict (Icc a b),
      Q ≤ S.scalar (T - tau) (gamma tau))
    (hmetric : ∀ᵐ tau ∂volume.restrict (Icc a b),
      c * gRef.inner (gamma tau)
          (lVelocity (I := I) gamma tau) (lVelocity (I := I) gamma tau) ≤
        lSpeedSq S T gamma tau) :
    2 * Real.sqrt (a * c * Q) * Variation.arcLength (I := I) gRef gamma a b ≤
      lLength S T gamma a b := by
  let speedRef : Real → Real := fun tau ↦
    Real.sqrt (gRef.inner (gamma tau)
      (lVelocity (I := I) gamma tau) (lVelocity (I := I) gamma tau))
  let K : Real := 2 * Real.sqrt (a * c * Q)
  have hrefOn : IntegrableOn speedRef (Icc a b) := by
    simpa only [speedRef, lVelocity] using
      Geodesic.speedSqrt_integrableOn_Icc_of_C1
        (I := I) gRef hab hgamma
  have href : IntervalIntegrable speedRef volume a b := by
    apply IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hrefOn
  have hmono :
      (∫ tau in a..b, K * speedRef tau) ≤ lLength S T gamma a b := by
    unfold lLength
    refine intervalIntegral.integral_mono_ae_restrict hab (href.const_mul K) hden ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc, hscalar, hmetric]
      with tau htau hscalarTau hmetricTau
    let v := lVelocity (I := I) gamma tau
    let q := gRef.inner (gamma tau) v v
    have hq : 0 ≤ q := by
      rcases eq_or_ne v 0 with hv | hv
      · simp only [q, hv, map_zero]
        exact le_rfl
      · exact (gRef.pos (gamma tau) v hv).le
    have hbase : 0 ≤ Q + c * q :=
      add_nonneg hQ (mul_nonneg hc hq)
    have hsum :
        Q + c * q ≤
          S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau := by
      exact add_le_add hscalarTau (by
        simpa only [q, v] using hmetricTau)
    have htime : Real.sqrt a ≤ Real.sqrt tau :=
      Real.sqrt_le_sqrt htau.1
    have hcq : (Real.sqrt c * Real.sqrt q) ^ 2 = c * q := by
      rw [mul_pow, Real.sq_sqrt hc, Real.sq_sqrt hq]
    have hamgm :
        2 * Real.sqrt Q * (Real.sqrt c * Real.sqrt q) ≤ Q + c * q := by
      nlinarith [sq_nonneg (Real.sqrt Q - Real.sqrt c * Real.sqrt q),
        Real.sq_sqrt hQ, hcq]
    have hroot :
        Real.sqrt (a * c * Q) =
          Real.sqrt a * (Real.sqrt c * Real.sqrt Q) := by
      rw [show a * c * Q = a * (c * Q) by ring,
        Real.sqrt_mul' a (mul_nonneg hc hQ), Real.sqrt_mul hc]
    change K * Real.sqrt q ≤
      Real.sqrt tau *
        (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau)
    calc
      K * Real.sqrt q =
          Real.sqrt a *
            (2 * Real.sqrt Q * (Real.sqrt c * Real.sqrt q)) := by
        simp only [K, hroot]
        ring
      _ ≤ Real.sqrt a * (Q + c * q) :=
        mul_le_mul_of_nonneg_left hamgm (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt tau * (Q + c * q) :=
        mul_le_mul_of_nonneg_right htime hbase
      _ ≤ Real.sqrt tau *
          (S.scalar (T - tau) (gamma tau) + lSpeedSq S T gamma tau) :=
        mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
  calc
    2 * Real.sqrt (a * c * Q) * Variation.arcLength (I := I) gRef gamma a b =
        ∫ tau in a..b, K * speedRef tau := by
      simp only [K, Variation.arcLength, speedRef, lVelocity,
        intervalIntegral.integral_const_mul]
    _ ≤ lLength S T gamma a b := hmono

end DifferentialGeometry.PDE.RicciFlow.Perelman
