import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelInputs

/-!
# Consumers of LCP04's model clauses and original buffer

* `model_lcp04_data_of_sectional_nonneg`: every model-side datum of LCP04's selected-center
  hypothesis for a complete Riemannian model with `sec ≥ 0`: properness, four-point comparison,
  geodesic segments, and an LC21 cone (proper, radial cone data) with Kleiner–Lott maps from every
  large blow-down, in LCP04's argument order.
* `eventually_original_buffer_of_expanding_bounds`: the original buffer at every scale `s ρ_α(p)`,
  `s ≤ V`, from expanding normalized curvature bounds that hold for every index (no subsequence).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The model side of LCP04's hypothesis, from a complete model with `sec ≥ 0`.** The model is
proper, four-point nonnegatively curved and geodesic, and has an LC21 cone `(C, o)` (proper, with
radial cone data) with Kleiner–Lott `δ₁`-maps of `(N, R⁻¹ d, n)` for every `R ≥ R₀(δ₁)`, stated in
LCP04's argument order. -/
theorem model_lcp04_data_of_sectional_nonneg {N : Type u} [mN : MetricSpace N] [ChartedSpace H N]
    [IsManifold I ∞ N] [SigmaCompactSpace N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
    (gN : SmoothRiemannianMetric I N) (hgN : IsMetricNorm (I := I) gN)
    (hsec : ∀ x, SectionalBoundedBelowAt gN x 0) (n : N) :
    ProperSpace N ∧ fourPointComparison 0 (univ : Set N) ∧
      (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
        f ⟨1, by norm_num⟩ = y ∧ ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
      ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧ ProperSpace C ∧
        ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ hR : 0 < R,
          Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) mC n o δ₁) := by
  obtain ⟨hprop, hfour, hseg⟩ := model_lcp04_clauses_of_sectional_nonneg gN hgN hsec
  have hmetric : ∀ a b : N, riemannianEDistOf (I := I) gN a b = ENNReal.ofReal (dist a b) := by
    intro a b
    rw [riemannianEDistOf_eq_riemannianEDist gN hgN, ← IsRiemannianManifold.out (I := I)]
    exact edist_dist a b
  obtain ⟨C, mC, o, hC, hCprop, -, -, -, -, hKL⟩ :=
    exists_cone_at_infinity_package_of_sectional_nonneg gN hmetric hsec n
  refine ⟨hprop, hfour, hseg, C, mC, o, hC, hCprop, fun δ₁ hδ₁ hδ₁1 => ?_⟩
  obtain ⟨R₀, hR₀⟩ := hKL δ₁ hδ₁ hδ₁1
  exact ⟨R₀, fun R hR hRpos => hR₀ R hRpos hR⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **The original buffer from expanding curvature bounds at every index.** If
`sec_{ρ_α(p)⁻² g^α} ≥ -H_α⁻²` on `B_{ρ_α(p)⁻¹ d}(p, H_α)` for every `α` and `p`, with `H_α → ∞`,
then for every `V` and all large `α`, every `p` and every `0 < s ≤ V`, the original buffer
`sec_g ≥ -(1/60)² (s ρ_α(p))⁻²` holds on `B(p, 400 s ρ_α(p))`. -/
theorem eventually_original_buffer_of_expanding_bounds
    {M : ℕ → Type*} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α)) (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    (Hs : ℕ → ℝ) (hHs : Tendsto Hs atTop atTop)
    (hbd : ∀ α (p : M α), ∀ y ∈ @Metric.ball (M α)
        ((mM α).rescale (ρ α p)⁻¹ (inv_pos.mpr (hρ α p))).toPseudoMetricSpace p (Hs α),
      SectionalBoundedBelowAt (scaleMetric ((ρ α p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ α p)) 2)
        (g α)) y (-((Hs α)⁻¹ ^ 2)))
    (V : ℝ) :
    ∃ α₁ : ℕ, ∀ α, α₁ < α → ∀ p : M α, ∀ s : ℝ, 0 < s → s ≤ V →
      ∀ y ∈ Metric.ball p (400 * (s * ρ α p)),
        SectionalBoundedBelowAt (g α) y (-((1 / 60) ^ 2 * (s * ρ α p)⁻¹ ^ 2)) :=
  eventually_original_buffer_of_sequential_curvature g ρ hρ
    (fun a ha z => ⟨id, strictMono_id, fun j => Hs (a j), hHs.comp ha,
      fun j y hy => hbd (a j) (z j) y hy⟩) V

end DifferentialGeometry.Geometry.Collapse
