import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScaleConeRadial

/-!
# Consumer of the LC58 binding, items (1)–(2), in the original metrics

From `exists_uniform_scale_interval_cone_radial_witnesses`: for `α > α₀` every point `p` has a
scale `s ∈ [T, V]` and a function `η` with `η p = 0`, `|η x - d_α(x, p)/(s ρ_α(p))| < e` for the
ORIGINAL distance `d_α`, and a smooth LC31 cutoff `Φ ∘ η`, together with a Kleiner–Lott `δ`-map of
the rescaled manifold to the cone of one model.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **Consumer of `exists_uniform_scale_interval_cone_radial_witnesses`.** The radial function of
the uniform LC58 scale, read in the original distance: `|η x - d(x, p)/(s ρ_α(p))| < e`. -/
theorem uniform_scale_interval_radial_value
    {M : ℕ → Type*} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [∀ α, SigmaCompactSpace (M α)] [∀ α, CompleteSpace (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type*} {N C : ι → Type*} [mN : ∀ b, MetricSpace (N b)] [mC : ∀ b, MetricSpace (C b)]
    (n : ∀ b, N b) (o : ∀ b, C b) (Hc : ∀ b, RadialConeData (o b))
    (hcone : ∀ b : ι, ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b)
        (n b) (o b) τ))
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {δ ε e T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α, ∃ s ∈ Icc T V,
      ∃ hs : 0 < s, ∃ b : ι,
        Nonempty (@KleinerLottApprox (M α) (C b)
          ((mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))) (mC b)
          p (o b) δ) ∧
        ∃ η : M α → ℝ, η p = 0 ∧ (∀ x, |η x - dist x p / (s * ρ α p)| < e) ∧
          ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (η x)) := by
  obtain ⟨V, hTV, α₀, hα₀⟩ := exists_uniform_scale_interval_cone_radial_witnesses g hmetric ρ hρ
    n o Hc hcone hmodel hδ hδ1 hε hε1 he he1 (T := T)
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hsI, hs, b, hKL, F, -, -, hclose, -, -, -, hp0, -, -, -, -, -, -, -, hsmooth, -⟩ :=
    hα₀ α hα p
  refine ⟨s, hsI, hs, b, hKL, F, hp0, fun x => ?_, hsmooth⟩
  have h := hclose x
  rw [@Metric.infDist_singleton (M α)
    ((mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))).toPseudoMetricSpace,
    MetricSpace.rescale_dist, inv_mul_eq_div] at h
  exact h

end DifferentialGeometry.Geometry.Collapse
