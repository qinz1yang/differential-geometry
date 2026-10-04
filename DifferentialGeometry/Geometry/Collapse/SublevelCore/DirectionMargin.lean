import DifferentialGeometry.Geometry.Collapse.SublevelCore.Defs
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceGradient

/-!
# LC44: Lipschitz radial perturbations preserve a direction margin

Blueprint LC44 (master207A:22067). On a complete Riemannian manifold let `F` be
differentiable at `q ≠ p` with `F - d_p` globally `ε`-Lipschitz, and let `Z ∈ T_qM` satisfy
`|Z| ≤ B` and `g(Z, u) ≤ -a` for every inward unit minimizing direction `u` from `q` to `p`.
Then `dF_q(Z) ≥ a - εB`.

Route. The blueprint argues through Rademacher's theorem and density of differentiability
points. Here the inequality is proved pointwise from the inherited smooth upper support
function of the distance (`infDist_upper_support` with `S = {p}`): it touches `d_p` from above
at `q` and has gradient `-u` for one inward unit minimizing direction `u`. The difference
`F - ρ` is then `ε`-Lipschitz from above at `q`, so its differential has norm at most `ε`.
Only differentiability of `F` at `q` is used; no open set, continuity of `Z` or smoothness of
`F` on a neighbourhood is needed (the blueprint-shaped statement is replayed in the consumer).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
private theorem riemannianEDist_toReal_eq_dist (x y : M) :
    (riemannianEDist I x y).toReal = dist x y := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

/-- One-sided slope test: a function with derivative `D` at `0` that stays below
`c t` (after subtracting its value at `0`) for small `t > 0` has `D ≤ c`. -/
private theorem deriv_le_of_eventually_sub_le {k : ℝ → ℝ} {D c : ℝ} (hk : HasDerivAt k D 0)
    (hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), k t - k 0 ≤ c * t) : D ≤ c := by
  by_contra hDc
  push Not at hDc
  have hsl : ∀ᶠ t in 𝓝[>] (0 : ℝ), c < slope k 0 t :=
    (hk.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)).eventually (lt_mem_nhds hDc)
  obtain ⟨t, ht, hct, hpos⟩ := (hsl.and (hle.and self_mem_nhdsWithin)).exists
  rw [slope_def_field, sub_zero, lt_div_iff₀ hpos] at ht
  linarith [hct]

/-- The differential of a function that is `ε`-Lipschitz from above at `q` (relative to the
Riemannian distance) is bounded by `ε |v|`, along the geodesic with initial velocity `v`. -/
private theorem mvfderiv_sub_le_of_upper_lipschitz (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {F ρ : M → ℝ} {q : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F q) (hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ q)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hupper : ∀ᶠ y in 𝓝 q, (F y - ρ y) - (F q - ρ q) ≤ ε * dist y q)
    (v : TangentSpace I q) :
    mvfderiv (I := I) F q v - mvfderiv (I := I) ρ q v ≤ ε * √(g.inner q v v) := by
  let γ := intrinsicGeodesic (I := I) g hEnorm q v
  have hγ0 : γ 0 = q := intrinsicGeodesic_zero (I := I) g hEnorm q v
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff (I := I) g hEnorm q v
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := hγ.contMDiffAt.mdifferentiableAt (by simp)
  have hvel : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm q v
  have hFd := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I F γ 0
    (by rw [hγ0]; exact hF) hγd
  have hρd := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I ρ γ 0
    (by rw [hγ0]; exact hρ) hγd
  have hsub := hFd.sub hρd
  change HasDerivAt (fun s => F (γ s) - ρ (γ s))
    (mvfderiv (I := I) F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) -
      mvfderiv (I := I) ρ (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ))) 0 at hsub
  rw [hvel] at hsub
  erw [hγ0] at hsub
  apply deriv_le_of_eventually_sub_le hsub
  have hcont : Continuous γ := hγ.continuous
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), (F (γ t) - ρ (γ t)) - (F q - ρ q) ≤ ε * dist (γ t) q := by
    have h := hcont.continuousAt (x := 0)
    rw [ContinuousAt, hγ0] at h
    exact h.eventually hupper
  filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with t ht htpos
  have hdist : dist (γ t) q ≤ √(g.inner q v v) * t := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm q v
      (le_of_lt (show (0 : ℝ) < t from htpos))
    change riemannianEDist I (γ 0) (γ t) ≤ _ at h
    rw [hγ0, sub_zero] at h
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [riemannianEDist_toReal_eq_dist (I := I),
      ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt htpos))] at h'
    rwa [dist_comm]
  rw [hγ0]
  calc (F (γ t) - ρ (γ t)) - (F q - ρ q) ≤ ε * dist (γ t) q := ht
    _ ≤ ε * (√(g.inner q v v) * t) := mul_le_mul_of_nonneg_left hdist hε
    _ = ε * √(g.inner q v v) * t := by ring

/-- LC44 (pointwise form). If `F - d_p` is `ε`-Lipschitz, `F` is differentiable at `q ≠ p`,
`|Z| ≤ B` and every inward unit minimizing direction `u` from `q` to `p` has `g(Z, u) ≤ -a`, then
`dF_q(Z) ≥ a - εB`. -/
theorem sub_mul_le_mvfderiv_of_lipschitz_sub_dist (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p q : M} (hpq : p ≠ q) {F : M → ℝ}
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F q) {ε : ℝ≥0}
    (hlip : LipschitzWith ε (fun x => F x - dist p x)) {Z : TangentSpace I q} {a B : ℝ}
    (hZB : √(g.inner q Z Z) ≤ B)
    (hdir : ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm p q, g.inner q Z u ≤ -a) :
    a - ε * B ≤ mvfderiv (I := I) F q Z := by
  have hq : 0 < Metric.infDist q ({p} : Set M) := by
    rw [Metric.infDist_singleton]
    exact dist_pos.mpr hpq.symm
  obtain ⟨ρ, u, hρ, hval, hup, hu, hend, hgrad⟩ :=
    DifferentialGeometry.Geometry.Topology.infDist_upper_support (I := I) g hEnorm
      isCompact_singleton (singleton_nonempty p) q hq
  rw [Metric.infDist_singleton] at hval
  have hdq : Metric.infDist q ({p} : Set M) = dist p q := by
    rw [Metric.infDist_singleton, dist_comm]
  have hmem : u ∈ inwardMinimizingDirections (I := I) g hEnorm p q := by
    refine ⟨hu, ?_⟩
    rw [hdq] at hend
    exact hend
  have hZu := hdir u hmem
  have hρd : MDifferentiableAt I 𝓘(ℝ, ℝ) ρ q := hρ.mdifferentiableAt (by simp)
  have hupper : ∀ᶠ y in 𝓝 q, (F y - ρ y) - (F q - ρ q) ≤ (ε : ℝ) * dist y q := by
    filter_upwards [hup] with y hy
    rw [Metric.infDist_singleton] at hy
    have hl : (F y - dist p y) - (F q - dist p q) ≤ ε * dist y q := by
      have h := hlip.dist_le_mul y q
      rw [Real.dist_eq] at h
      exact (le_abs_self _).trans h
    rw [hval]
    rw [dist_comm y p] at hy
    rw [dist_comm q p]
    linarith
  have hmain := mvfderiv_sub_le_of_upper_lipschitz (I := I) g hEnorm hF hρd ε.2 hupper (-Z)
  have hρZ : mvfderiv (I := I) ρ q Z = -g.inner q Z u := by
    rw [← inner_gradientFun (I := I) g ρ q Z, hgrad, map_neg, neg_apply, g.symm q u Z]
  have e1 : mvfderiv (I := I) F q (-Z) = -mvfderiv (I := I) F q Z := map_neg _ _
  have e2 : mvfderiv (I := I) ρ q (-Z) = -mvfderiv (I := I) ρ q Z := map_neg _ _
  have hgZZ : g.inner q (-Z) (-Z) = g.inner q Z Z := by
    simp only [map_neg, neg_apply, neg_neg]
  rw [hgZZ, e1, e2, hρZ] at hmain
  have hεB : (ε : ℝ) * √(g.inner q Z Z) ≤ ε * B := mul_le_mul_of_nonneg_left hZB ε.2
  have hmain' : -mvfderiv (I := I) F q Z + -g.inner q Z u ≤ ε * √(g.inner q Z Z) := by
    simp only [neg_neg, sub_eq_add_neg] at hmain
    exact hmain
  linarith

/-- LC44, outward clause: under the strict margin `εB < a`, the gradient of `F` has positive
`g`-pairing with `Z` (for instance the outward unit normal of a domain at `q`). -/
theorem inner_gradientFun_pos_of_lipschitz_sub_dist (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) {p q : M} (hpq : p ≠ q) {F : M → ℝ}
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F q) {ε : ℝ≥0}
    (hlip : LipschitzWith ε (fun x => F x - dist p x)) {Z : TangentSpace I q} {a B : ℝ}
    (hZB : √(g.inner q Z Z) ≤ B)
    (hdir : ∀ u ∈ inwardMinimizingDirections (I := I) g hEnorm p q, g.inner q Z u ≤ -a)
    (hmargin : ε * B < a) :
    0 < g.inner q (gradientFun (I := I) g F q) Z := by
  rw [inner_gradientFun]
  have h := sub_mul_le_mvfderiv_of_lipschitz_sub_dist (I := I) g hEnorm hpq hF hlip hZB hdir
  linarith

end DifferentialGeometry.Geometry.Collapse
