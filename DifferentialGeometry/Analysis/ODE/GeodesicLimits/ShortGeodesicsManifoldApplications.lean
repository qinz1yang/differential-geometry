import DifferentialGeometry.Analysis.ODE.GeodesicLimits.ShortGeodesicsManifold
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteOrder

/-!
# Consumers of LFR09 (coefficient and manifold forms)

* `exists_short_geodesics_const_metric`: constant coefficient fields `B₀ + c i`, `B₀` coercive,
  `c i → 0` (the chart kernel through adapter (1), no coercivity hypothesis on the `b i`).
* `exists_short_geodesics_vectorSpace`: the manifold form on a finite-dimensional inner product
  space with its standard metric (`riemannianMetricVectorSpace`, Riemannian distance = norm
  distance by Mathlib's `IsRiemannianManifold` instance).
* The verbatim blueprint form of LFR09 (both endpoints in `C`) is recorded as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric Bundle
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.MetricKoszul

section Chart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

omit [FiniteDimensional ℝ E] [ContinuousDualEquiv E] in
/-- Constant coefficient fields `B₀ + c i` with `c i → 0` converge in `C²` on every set. -/
theorem mapCPConvergenceOn_two_const_add (B₀ : E →L[ℝ] E →L[ℝ] ℝ) {c : ℕ → E →L[ℝ] E →L[ℝ] ℝ}
    (hc : Tendsto c atTop (𝓝 0)) (K : Set E) :
    MapCPConvergenceOn K 2 (fun i (_ : E) => B₀ + c i) (fun _ => B₀) := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := Metric.tendsto_atTop.mp hc ε hε
  refine ⟨k₀, fun k hk r _ x _ => ?_⟩
  simp only [mapDerivNorm, add_sub_cancel_left]
  rcases r with _ | r
  · rw [norm_iteratedFDeriv_zero, ← dist_zero_right]
    exact (hk₀ k hk).le
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero r), Pi.zero_apply]
    exact (le_of_eq ContinuousMultilinearMap.opNorm_zero).trans hε.le

/-- **Consumer of LFR09 (chart kernel, coefficient form).** For constant coefficient fields
`B₀ + c i`, `B₀` coercive and `c i → 0`, close points of a compact set are joined, for a tail, by
`B₀ + c i`-geodesics with metric speed `O(‖y - x‖)`. -/
theorem exists_short_geodesics_const_metric (B₀ : E →L[ℝ] E →L[ℝ] ℝ) (hB₀ : IsCoercive B₀)
    {c : ℕ → E →L[ℝ] E →L[ℝ] ℝ} (hc : Tendsto c atTop (𝓝 0)) {C : Set E} (hC : IsCompact C) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y : E, ‖y - x‖ ≤ τ →
      ∃ γ γ' : ℝ → E, γ 0 = x ∧ γ 1 = y ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
        HasDerivWithinAt γ' (-(raisedKoszulOp (B₀ + c i) (fderiv ℝ (fun _ : E => B₀ + c i) (γ t))
          (γ' t) (γ' t))) (Icc 0 1) t ∧
        (B₀ + c i) (γ' t) (γ' t) ≤ (L * ‖y - x‖) ^ 2 := by
  obtain ⟨τ, L, hτ, hL, hev⟩ := exists_short_geodesics_of_metric_C2_eventually isOpen_univ
    (b := fun i (_ : E) => B₀ + c i) (bInf := fun _ => B₀)
    (Eventually.of_forall fun _ => contDiffOn_const) contDiffOn_const (fun _ _ => hB₀)
    (fun K _ _ => mapCPConvergenceOn_two_const_add B₀ hc K) hC (subset_univ C)
  refine ⟨τ, L, hτ, hL, ?_⟩
  filter_upwards [hev] with i hi x hx y hy
  obtain ⟨γ, γ', h0, h1, hγ⟩ := hi x hx y hy
  exact ⟨γ, γ', h0, h1, fun t ht => ⟨(hγ t ht).2.1, (hγ t ht).2.2.1, (hγ t ht).2.2.2.2⟩⟩

end Chart

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

open DifferentialGeometry.Geometry.MetricSmoothing in
/-- The verbatim blueprint form of LFR09 (A:25443): both endpoints in `C`, an `h_i`-geodesic
inside `W` of `h_i`-speed (hence length) at most `L d_G(x, y)`. -/
example {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : N → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hG : letI : RiemannianBundle (fun x : N => TangentSpace I x) := ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold I N)
    (b : ℕ → N → E → E →L[ℝ] E →L[ℝ] ℝ) {W : Set N} (hW : IsOpen W)
    (hb : ∀ z, ∀ᶠ i in atTop,
      ContDiffOn ℝ 2 (b i z) ((extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W))
    (hconv : ∀ z K, IsCompact K → K ⊆ (extChartAt I z).target ∩ (extChartAt I z).symm ⁻¹' W →
      MapCPConvergenceOn K 2 (fun i => b i z) (chartCoeff G z))
    {C : Set N} (hC : IsCompact C) (hCW : C ⊆ W) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y ∈ C, dist x y < τ →
      ∃ z : N, ∃ γ γ' : ℝ → E, (extChartAt I z).symm (γ 0) = x ∧ (extChartAt I z).symm (γ 1) = y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, (extChartAt I z).symm (γ t) ∈ W ∧
          HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
          HasDerivWithinAt γ'
            (-(raisedKoszulOp (b i z (γ t)) (fderiv ℝ (b i z) (γ t)) (γ' t) (γ' t))) (Icc 0 1) t ∧
          Real.sqrt (b i z (γ t) (γ' t) (γ' t)) ≤ L * dist x y := by
  obtain ⟨τ, L, hτ, hL, hev⟩ :=
    exists_short_geodesics_of_contMDiffRiemannianMetric G hn hG b hW hb hconv hC hCW
  refine ⟨τ, L, hτ, hL, ?_⟩
  filter_upwards [hev] with i hi x hx y _ hxy
  obtain ⟨z, γ, γ', hxs, hys, h0, h1, hγ⟩ := hi x hx y hxy
  refine ⟨z, γ, γ', by rw [h0, (extChartAt I z).left_inv hxs],
    by rw [h1, (extChartAt I z).left_inv hys], fun t ht => ?_⟩
  obtain ⟨-, hW', hd, hd', -, hsp⟩ := hγ t ht
  refine ⟨hW', hd, hd', ?_⟩
  rw [← Real.sqrt_sq (mul_nonneg hL.le dist_nonneg)]
  exact Real.sqrt_le_sqrt hsp

end Manifold

section VectorSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

private noncomputable local instance shortGeodManifoldDual : ContinuousDualEquiv F :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

open DifferentialGeometry.Geometry.MetricSmoothing in
/-- **Consumer of LFR09 (manifold form).** On a finite-dimensional inner product space with its
standard Riemannian metric (Riemannian distance = norm distance), the constant sequence of chart
coefficients: close points of a compact `C ⊆ W` are joined inside `W` by chart geodesics of
speed `O(dist x y)`. -/
theorem exists_short_geodesics_vectorSpace {W : Set F} (hW : IsOpen W) {C : Set F}
    (hC : IsCompact C) (hCW : C ⊆ W) :
    ∃ τ L : ℝ, 0 < τ ∧ 0 < L ∧ ∀ᶠ (_ : ℕ) in atTop, ∀ x ∈ C, ∀ y : F, dist x y < τ →
      ∃ z : F, ∃ γ γ' : ℝ → F, γ 0 = extChartAt 𝓘(ℝ, F) z x ∧ γ 1 = extChartAt 𝓘(ℝ, F) z y ∧
        ∀ t ∈ Icc (0 : ℝ) 1, (extChartAt 𝓘(ℝ, F) z).symm (γ t) ∈ W ∧
          HasDerivWithinAt γ (γ' t) (Icc 0 1) t ∧
          ‖γ' t‖ ≤ L * dist x y := by
  have hn : (2 : ℕ∞ω) ≤ ω := le_top
  obtain ⟨τ, L, hτ, hL, hev⟩ := exists_short_geodesics_of_contMDiffRiemannianMetric
    (riemannianMetricVectorSpace F) hn inferInstance
    (fun _ z => chartCoeff (riemannianMetricVectorSpace F) z) hW
    (fun z => Eventually.of_forall fun _ =>
      (contDiffOn_chartCoeff (riemannianMetricVectorSpace F) hn z).mono inter_subset_left)
    (fun z K _ _ => MapCPConvergenceOn.const_seq _) hC hCW
  refine ⟨τ, L, hτ, hL, ?_⟩
  filter_upwards [hev] with i hi x hx y hxy
  obtain ⟨z, γ, γ', -, -, h0, h1, hγ⟩ := hi x hx y hxy
  exact ⟨z, γ, γ', h0, h1, fun t ht =>
    ⟨(hγ t ht).2.1, (hγ t ht).2.2.1, (hγ t ht).2.2.2.2.1⟩⟩

end VectorSpace

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
