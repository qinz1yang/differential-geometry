import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finite-dimensional differentiation under a compact integral

For a finite measure on a compact space, joint continuity of a pointwise
Fréchet derivative gives the uniform local domination needed by Mathlib's
parametric-integral theorem.  This file packages that compactness argument for
finite-dimensional parameter spaces.  It is used for the coefficient
derivatives of finite Galerkin energies.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace DifferentialGeometry.Integral.Measure

/-- Differentiate a compact integral with respect to a finite-dimensional
parameter.  Joint continuity of the integrand and its pointwise derivative
supplies all measurability, integrability, and domination hypotheses. -/
theorem hasFDerivAt_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    HasFDerivAt (fun v : V => ∫ x, F v x ∂μ) (∫ x, F' u x ∂μ) u := by
  let K : Set (V × X) := Metric.closedBall u 1 ×ˢ (Set.univ : Set X)
  have hK : IsCompact K :=
    (isCompact_closedBall u 1).prod isCompact_univ
  have hnorm : ContinuousOn (fun p : V × X => ‖F' p.1 p.2‖) K :=
    hF'.norm.continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hnorm
  have hs : Metric.closedBall u 1 ∈ 𝓝 u :=
    Metric.closedBall_mem_nhds u zero_lt_one
  have hmeas : ∀ᶠ v in 𝓝 u, AEStronglyMeasurable (F v) μ := by
    filter_upwards [] with v
    exact (hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hint : Integrable (F u) μ := by
    have hc : Continuous (F u) :=
      hF.comp (continuous_const.prodMk continuous_id)
    exact integrableOn_univ.mp
      (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hmeas' : AEStronglyMeasurable (F' u) μ :=
    (hF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ x ∂μ, ∀ v ∈ Metric.closedBall u 1,
      ‖F' v x‖ ≤ C := by
    filter_upwards [] with x
    intro v hv
    exact hC (v, x) ⟨hv, Set.mem_univ x⟩
  have hCint : Integrable (fun _ : X => C) μ := integrable_const C
  have hdiff' : ∀ᵐ x ∂μ, ∀ v ∈ Metric.closedBall u 1,
      HasFDerivAt (fun w : V => F w x) (F' v x) v := by
    filter_upwards [] with x
    intro v _
    exact hdiff v x
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    hs hmeas hint hmeas' hbound hCint hdiff'

/-- The Fréchet derivative of a compact integral is the integral of the
pointwise derivatives under the same joint-continuity assumptions. -/
theorem fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (u : V) :
    fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u = ∫ x, F' u x ∂μ :=
  (hasFDerivAt_integral_compact μ F F' hF hF' hdiff u).fderiv

/-- If the pointwise first derivative is itself continuously differentiable,
then the derivative of the compact integral varies continuously.  The second
derivative is used only to obtain continuity; no explicit formula for it is
baked into the conclusion. -/
theorem continuous_fderiv_integral_compact
    {X V W : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (μ : Measure X) [IsFiniteMeasure μ]
    (F : V → X → W) (F' : V → X → (V →L[ℝ] W))
    (F'' : V → X → (V →L[ℝ] (V →L[ℝ] W)))
    (hF : Continuous (fun p : V × X => F p.1 p.2))
    (hF' : Continuous (fun p : V × X => F' p.1 p.2))
    (hF'' : Continuous (fun p : V × X => F'' p.1 p.2))
    (hdiff : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F v x) (F' u x) u)
    (hdiff' : ∀ u : V, ∀ x : X,
      HasFDerivAt (fun v : V => F' v x) (F'' u x) u) :
    Continuous (fun u : V => fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u) := by
  let D : V → (V →L[ℝ] W) := fun u => ∫ x, F' u x ∂μ
  have hDdiff : Differentiable ℝ D := by
    intro u
    exact (hasFDerivAt_integral_compact μ F' F'' hF' hF'' hdiff' u).differentiableAt
  have hEq : (fun u : V => fderiv ℝ (fun v : V => ∫ x, F v x ∂μ) u) = D := by
    funext u
    exact fderiv_integral_compact μ F F' hF hF' hdiff u
  rw [hEq]
  exact hDdiff.continuous

end DifferentialGeometry.Integral.Measure

end
