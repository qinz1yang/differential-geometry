import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.RadialFunctionAtScale

/-!
# Consumer of LC30 at scale `R`: the LC55 radial-function hypotheses

With LC55's numerical choices (function error `1/80`, Lipschitz difference `1/64`), LC30 at scale
`R` gives, on the normalized manifold `(M, R⁻¹ d)`, a function `ζ` with `|ζ - d_p| < 1/80`,
`ζ - d_p` `(1/64)`-Lipschitz, and `ζ` smooth on an open set containing the collar
`{3/4 < d_p < 5/4}`: exactly the radial-function hypotheses of `point_distance_core_isotopy`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [CompleteSpace M]

/-- **Consumer of `exists_radialFunction_of_kleinerLottApprox_at_scale`.** The LC55 radial-function
hypotheses (errors `1/80`, `1/64`, smoothness near the collar) at scale `R`. -/
theorem exists_point_distance_core_function_at_scale (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    {p : M} {R : ℝ} (hR : 0 < R) {C : Type*} [MetricSpace C] {o : C} {δ : ℝ}
    (φ : @KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p o δ)
    (H : RadialConeData o)
    (hsec : ∀ y ∈ Metric.ball p (400 * R),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * R⁻¹ ^ 2)))
    (hδ : δ < radialSmoothingConeError ((1 / 64) / 4)) :
    letI := m.rescale R⁻¹ (inv_pos.mpr hR)
    ∃ ζ : M → ℝ, (∀ x, |ζ x - dist p x| < 1 / 80) ∧
      LipschitzWith (Real.toNNReal (1 / 64)) (fun x => ζ x - dist p x) ∧
      ∃ W : Set M, IsOpen W ∧ (∀ x, 3 / 4 < dist p x → dist p x < 5 / 4 → x ∈ W) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ ζ W := by
  obtain ⟨F, -, ⟨O, hO, hshell, hFO⟩, hclose, -, hlip, -⟩ :=
    exists_radialFunction_of_kleinerLottApprox_at_scale g hmetric hR φ H hsec
      (by norm_num : (0 : ℝ) < 1 / 64) (by norm_num) hδ (by norm_num : (0 : ℝ) < 1 / 80)
      (by norm_num)
  let := m.rescale R⁻¹ (inv_pos.mpr hR)
  refine ⟨F, fun x => ?_, ?_, O, hO, fun x h1 h2 => hshell ⟨?_, ?_⟩, hFO⟩
  · have h := hclose x
    rwa [Metric.infDist_singleton, dist_comm] at h
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hlip x y
    rw [Metric.infDist_singleton, Metric.infDist_singleton] at h
    rw [Real.dist_eq, Real.coe_toNNReal _ (by norm_num), dist_comm p x, dist_comm p y]
    exact h
  · rw [dist_comm]; linarith
  · rw [dist_comm]; linarith

end DifferentialGeometry.Geometry.Collapse
