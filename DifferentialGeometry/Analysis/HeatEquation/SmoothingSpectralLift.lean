import DifferentialGeometry.Analysis.HeatEquation.HeatSemigroupIteratedDomain

/-!
# Spectral lift of the heat semigroup into every iterated Laplacian domain

For a closed Riemannian manifold `(M, g)`, time `t > 0`, and any initial datum
`u_0 ∈ Lp ℝ 2 μ_g`, the heat-evolved `Lp` element `heatSemigroup g t u_0` lifts
to an element of `H1Compl g` lying in `laplacianDomainPow g k` for every
`k : ℕ`.

This file packages the spectral construction of such a lift in a single
headline theorem, together with a canonical witness definition selected via
`Classical.choose` for downstream use, and an explicit-form witness
constructed directly from the spectral binomial-sum operator.

## Construction

With the L² eigenbasis `b := resolventHilbertEigenbasisSigma g` and Laplacian
eigenvalues `λ_i ≥ 0`, the basic spectral identities are:

* `resolventL2 g (b i) = μ_i • b i` with `μ_i := 1/(1+λ_i)`;
* `heatSemigroup g t (b i) = exp(-λ_i t) • b i`;
* `(resolventL2 g)^k (b i) = μ_i^k • b i = (1+λ_i)^{-k} • b i`.

The witness is the explicit spectral lift

  `u_h := resolvent g ((resolventL2 g)^{k} (oneMinusLapHeat g (k+1) t u_0))`

where `oneMinusLapHeat g k t = (1-Δ_g)^k · e^{tΔ_g}` is the binomial finite
sum from `HeatSemigroupIteratedDomain.lean`. Membership in
`laplacianDomainPow g (k+1)` is immediate from the `succ` characterisation,
and the `H1ComplToLp`-image identity follows by combining the resolvent /
iterated-resolvent definitions with the operator-level spectral identity
`iteratedResolventL2_oneMinusLapHeat_apply`. For `k = 0` the membership in
`laplacianDomainPow g 0 = ⊤` is trivial.

## Main results

* `heatSemigroup_in_laplacianDomainPow` — headline theorem: there exists an
  `H1Compl g` lift of `heatSemigroup g t u_0` in `laplacianDomainPow g k`.
* `heatSemigroupSpectralLift g t u_0 k` — a `Classical.choose`-based canonical
  witness, packaged as a definition, together with its specifications
  `heatSemigroupSpectralLift_mem`,
  `H1ComplToLp_heatSemigroupSpectralLift`.
* `heatSemigroupExplicitLift g k t u_0` — an explicit-form witness in
  `laplacianDomainPow g (k+1)`, with the projection identity
  `H1ComplToLp_heatSemigroupExplicitLift`.
* `heatSemigroup_in_laplacianDomainPow_explicit` — convenient existence with
  the explicit witness, parameterised on `k + 1` (the form that downstream
  bridge code commonly consumes).

## Sign convention

Geometer convention `Δ_g = div_g ∘ grad_g`. The resolvent is `(1 - Δ_g)⁻¹`.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

/-- **Headline.** For a closed Riemannian manifold `(M, g)`, any `t > 0`, any
initial datum `u_0 ∈ Lp ℝ 2 μ_g`, and any `k : ℕ`, the heat-evolved `Lp`
element `heatSemigroup g t u_0` admits an `H1Compl g` lift lying in the
`k`-th iterated Laplacian domain `laplacianDomainPow g k`.

The construction is spectral: the witness is built via the auxiliary
binomial-sum operator `oneMinusLapHeat g k t = (1-Δ_g)^k · e^{tΔ_g}` and the
resolvent, yielding `resolvent g ((resolventL2 g)^{k-1} (oneMinusLapHeat g k t u_0))`
for `k ≥ 1`, and (e.g.) the `k = 1` witness for `k = 0` (any lift suffices
when the target submodule is `⊤`). -/
theorem heatSemigroup_in_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  heatSemigroup_mem_laplacianDomainPow_all (I := I) (M := M) g ht u_0 k

/-- The canonical `Classical.choose`-based lift of `heatSemigroup g t u_0` to
`H1Compl g`, selected so as to lie in `laplacianDomainPow g k`.

By `heatSemigroupSpectralLift_mem` and `H1ComplToLp_heatSemigroupSpectralLift`,
this lift satisfies the two defining properties:

* `heatSemigroupSpectralLift g ht u_0 k ∈ laplacianDomainPow g k`;
* `H1ComplToLp g (heatSemigroupSpectralLift g ht u_0 k) = heatSemigroup g t u_0`.
-/
noncomputable def heatSemigroupSpectralLift
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    H1Compl (I := I) (M := M) g :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose

/-- Membership of the canonical lift in `laplacianDomainPow g k`. -/
theorem heatSemigroupSpectralLift_mem
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k ∈
      laplacianDomainPow (I := I) (M := M) g k :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose_spec.1

/-- The canonical lift projects back to the heat output:
`H1ComplToLp g (heatSemigroupSpectralLift g ht u_0 k) = heatSemigroup g t u_0`. -/
theorem H1ComplToLp_heatSemigroupSpectralLift
    (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    H1ComplToLp (I := I) (M := M) g
        (heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k) =
      heatSemigroup (I := I) (M := M) g t u_0 :=
  (heatSemigroup_in_laplacianDomainPow
    (I := I) (M := M) g ht u_0 k).choose_spec.2

/-- The explicit-form spectral lift of `heatSemigroup g t u_0` into the
`(k+1)`-th iterated Laplacian domain:

  `heatSemigroupExplicitLift g k t u_0 :=`
  `  resolvent g ((iteratedResolventL2 g k) (oneMinusLapHeat g (k+1) t u_0))`.

The trailing `+1` in the target index reflects the `succ`-indexed form of
`laplacianDomainPow_succ_mem_iff`. The associated specification lemmas are
`heatSemigroupExplicitLift_mem` and `H1ComplToLp_heatSemigroupExplicitLift`. -/
noncomputable def heatSemigroupExplicitLift
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    H1Compl (I := I) (M := M) g :=
  resolvent (I := I) (M := M) g
    (iteratedResolventL2 (I := I) (M := M) g k
      (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0))

/-- The explicit-form lift lies in `laplacianDomainPow g (k+1)`. -/
theorem heatSemigroupExplicitLift_mem
    (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g k t u_0 ∈
      laplacianDomainPow (I := I) (M := M) g (k + 1) := by
  unfold heatSemigroupExplicitLift
  rw [laplacianDomainPow_succ_mem_iff]
  exact ⟨oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0, rfl⟩

/-- The explicit-form lift projects back to the heat output (for `t > 0`):
`H1ComplToLp g (heatSemigroupExplicitLift g k t u_0) = heatSemigroup g t u_0`. -/
theorem H1ComplToLp_heatSemigroupExplicitLift
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    H1ComplToLp (I := I) (M := M) g
        (heatSemigroupExplicitLift (I := I) (M := M) g k t u_0) =
      heatSemigroup (I := I) (M := M) g t u_0 := by
  unfold heatSemigroupExplicitLift
  rw [show H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k
            (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0))) =
      resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k
          (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0)) from
    (resolventL2_apply (I := I) (M := M) g _).symm]
  rw [show resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k
          (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0)) =
      iteratedResolventL2 (I := I) (M := M) g (k + 1)
        (oneMinusLapHeat (I := I) (M := M) g (k + 1) t u_0) from
    (iteratedResolventL2_succ_apply (I := I) (M := M) g k _).symm]
  exact iteratedResolventL2_oneMinusLapHeat_apply (I := I) (M := M) g (k + 1) ht u_0

/-- **Existence with the explicit witness**, packaged at index `k + 1` so the
witness is visible in `laplacianDomainPow g (k + 1)`. -/
theorem heatSemigroup_in_laplacianDomainPow_succ_explicit
    (g : SmoothRiemannianMetric I M) (k : ℕ) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1) ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  ⟨heatSemigroupExplicitLift (I := I) (M := M) g k t u_0,
    heatSemigroupExplicitLift_mem (I := I) (M := M) g k t u_0,
    H1ComplToLp_heatSemigroupExplicitLift (I := I) (M := M) g k ht u_0⟩

example (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    ∃ u_h : H1Compl (I := I) (M := M) g,
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
        H1ComplToLp (I := I) (M := M) g u_h =
          heatSemigroup (I := I) (M := M) g t u_0 :=
  heatSemigroup_in_laplacianDomainPow (I := I) (M := M) g ht u_0 k

example (g : SmoothRiemannianMetric I M) {t : ℝ} (ht : 0 < t)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) (k : ℕ) :
    heatSemigroupSpectralLift (I := I) (M := M) g ht u_0 k ∈
      laplacianDomainPow (I := I) (M := M) g k :=
  heatSemigroupSpectralLift_mem (I := I) (M := M) g ht u_0 k

example (g : SmoothRiemannianMetric I M) (k : ℕ) (t : ℝ)
    (u_0 : Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) :
    heatSemigroupExplicitLift (I := I) (M := M) g k t u_0 ∈
      laplacianDomainPow (I := I) (M := M) g (k + 1) :=
  heatSemigroupExplicitLift_mem (I := I) (M := M) g k t u_0

end HeatEquation
end Analysis
end DifferentialGeometry

end
