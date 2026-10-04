import DifferentialGeometry.Geometry.Collapse.SublevelCore.JointWitnessConeRadial
import DifferentialGeometry.Geometry.Collapse.RiemannianConeScaleApplications

/-!
# Consumer of LC57 (1)–(2): a compact nonnegatively curved model and its constant sequence

For a compact Riemannian manifold `(N, g)` with `sec ≥ 0` (complete, its distance realizing the
`g`-length distance), the constant sequence with the point cone (LC21 for compact manifolds,
`exists_riemannian_point_cone_of_compactSpace`), `H_i = i + 1` and LC57 (1)–(2) give `R₀` such
that at every scale `R ≥ R₀` there are a Kleiner–Lott `δ`-map of `(N, R⁻¹ d, n)` to the point and
an LC30 radial function `η` with value error `e`, `η n = 0`, whose LC31 cutoff is smooth.
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

/-- **Consumer of `exists_scale_eventually_cone_radial_witnesses`.** A compact model with
`sec ≥ 0`, as its own constant sequence: at every scale `R ≥ R₀`, a Kleiner–Lott `δ`-map to the
point and an LC30 function with value error `e`, vanishing at `n`, with smooth LC31 cutoff. -/
theorem compact_nonneg_cone_radial_witnesses {N : Type*} [mN : MetricSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [SigmaCompactSpace N] [CompleteSpace N] [CompactSpace N]
    (g : SmoothRiemannianMetric I N)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
    (hsec : ∀ y, SectionalBoundedBelowAt g y 0) (n : N) {δ ε e : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e) (he1 : e < 1 / 40) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N PUnit (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n PUnit.unit δ) ∧
      (letI := mN.rescale R⁻¹ (inv_pos.mpr hR)
      ∃ F : N → ℝ, (∀ x, |F x - Metric.infDist x {n}| < e) ∧ F n = 0 ∧
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x))) := by
  have hHb : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  obtain ⟨R₀, hR₀, hall⟩ := exists_scale_eventually_cone_radial_witnesses (M := fun _ : ℕ => N)
    (fun _ => g) (fun _ => hmetric) (pointedGHConverges_const n) RadialConeData.punit
    (fun τ hτ hτ1 => by
      obtain ⟨R₁, hR₁⟩ := exists_riemannian_point_cone_of_compactSpace g hmetric n hτ hτ1
      exact ⟨R₁, fun R hR h => (hR₁ R hR h).2⟩)
    (fun i : ℕ => (i : ℝ) + 1) hHb
    (fun _ y _ => (hsec y).mono (neg_nonpos.mpr (sq_nonneg _)))
    hδ hδ1 hε hε1 he he1
  refine ⟨R₀, hR₀, fun R hR hRR => ?_⟩
  obtain ⟨_, hKL, F, -, -, hclose, -, -, -, hn, -, -, -, -, -, -, -, hsmooth, -⟩ :=
    (hall R hR hRR).exists
  exact ⟨hKL, F, hclose, hn, hsmooth⟩

end DifferentialGeometry.Geometry.Collapse
