import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.BufferedRadialFunctionAtScale

/-!
# Consumer: LCP04's radial function at a selected scale, thresholds first

`exists_coneError_lcp04_radial_function`: for every `0 < ε < 1` and every threshold `δ' > 0` fixed
first, one cone error `δ < min{1, δ'}` serves every manifold, center and scale `R`: a Kleiner–Lott
`δ`-map of `(M, R⁻¹ d, p)` to a radial cone and the original buffer at `R` give a function `η` with
LCP04's two radial hypotheses (smooth on `{3/40 ≤ R⁻¹ d(·, p) ≤ 11}`, difference-Lipschitz error
`ε`) and value error `e` against `R⁻¹ d(·, p)`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LCP04's radial function at a selected scale, with the thresholds fixed first.** For
`0 < ε < 1` and `δ' > 0` there is `δ ∈ (0, 1)`, `δ < δ'`, such that for every manifold, center `p`
and scale `R > 0`, a Kleiner–Lott `δ`-map of `(M, R⁻¹ d, p)` to a radial cone and the original
buffer `sec_g ≥ -(1/60)² R⁻²` on `B(p, 400 R)` give, for every `0 < e < 1/40`, a function `η`
smooth on `{3/40 ≤ R⁻¹ d(x, p) ≤ 11}`, with `|(η x - R⁻¹ d(p, x)) - (η y - R⁻¹ d(p, y))| ≤
ε R⁻¹ d(x, y)` and `|η x - R⁻¹ d(x, p)| < e`. -/
theorem exists_coneError_lcp04_radial_function {ε δ' : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hδ' : 0 < δ') :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ < δ' ∧
      ∀ (M : Type*) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ (p : M) (R : ℝ) (hR : 0 < R) (C : Type*) [MetricSpace C] (o : C),
      @KleinerLottApprox M C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ p o δ → RadialConeData o →
      (∀ y ∈ Metric.ball p (400 * R),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * R⁻¹ ^ 2))) →
      ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∃ η : M → ℝ,
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η {x | 3 / 40 ≤ R⁻¹ * dist x p ∧ R⁻¹ * dist x p ≤ 11} ∧
        (∀ x y, |(η x - R⁻¹ * dist p x) - (η y - R⁻¹ * dist p y)| ≤ ε * (R⁻¹ * dist x y)) ∧
        ∀ x, |η x - R⁻¹ * dist x p| < e := by
  obtain ⟨δ, hδ0, hδ1, hδδ', hδr⟩ := exists_coneError_below_thresholds hε hδ'
  refine ⟨δ, hδ0, hδ1, hδδ', ?_⟩
  intro M m _ _ _ _ g hmetric p R hR C _ o φ Hc hsec e he he1
  obtain ⟨F, -, hFO, hclose, -, hdiff, -⟩ :=
    exists_buffered_radial_cutoff_at_scale g hmetric hR φ Hc hsec hε hε1 hδr he he1
  obtain ⟨hsmooth, hlip⟩ := radial_original_clauses_of_rescaled (I := I) hR hFO hdiff
  refine ⟨F, hsmooth, hlip, fun x => ?_⟩
  have h := hclose x
  simp only [Metric.infDist_singleton] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
