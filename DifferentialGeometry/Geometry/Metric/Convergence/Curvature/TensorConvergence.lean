import DifferentialGeometry.Geometry.Curvature.RiemannPerturbation
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Evaluation
import DifferentialGeometry.Geometry.Curvature.MetricDifference
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Geometry.Metric.Family.TensorNorm

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.CheegerGromovCompactness

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable [I.Boundaryless]

theorem MetricCPConvergenceOn.tendsto_metricRm04StandardAt
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 2 G g R) (hK : IsCompact K)
    {x : M} (hx : x ∈ K) (v w u z : TangentSpace I x) :
    Tendsto (fun n => metricRm04StandardAt (G n) x v w u z) atTop
      (𝓝 (metricRm04StandardAt g x v w u z)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hc := hconv.change_reference hK g
  apply Metric.tendsto_atTop.mpr
  intro e he
  let n : ℝ := Module.finrank ℝ E
  let V := riemannOp (cov := LeviCivita (I := I) g) x v w u
  let A := Real.sqrt (g.inner x z z) * Real.sqrt (g.inner x V V) +
    864 * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) *
      Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x z z)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let d := min (1 / (2 * (n + 1))) (min 1 (e / (A + 1)))
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdn : n * d ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp
      (min_le_left (1 / (2 * (n + 1))) (min 1 (e / (A + 1))))
    change d * (2 * (n + 1)) ≤ 1 at h
    nlinarith
  have hdA : d * A < e := by
    have h := (le_div_iff₀ (by positivity : 0 < A + 1)).mp
      ((min_le_right _ _).trans (min_le_right _ _) : d ≤ e / (A + 1))
    nlinarith
  obtain ⟨N, hN⟩ := hc d hd
  refine ⟨N, fun k hk => ?_⟩
  have hjet (q : ℕ) (hq : q ≤ 2) : metricDerivNorm q (G k) g g x ≤ d :=
    (derivNorm_le_sup hK hq (G k) g g hx).trans (hN k hk).le
  have hb := PDE.RicciFlow.Perelman.KappaSolutions.metricRm04_difference_le_of_metricDerivNorm_le
    g (G k) x hd.le hd1 hdn hjet v w u z
  rw [Real.dist_eq]
  exact hb.trans_lt hdA

theorem MetricCPConvergenceOn.tendsto_normSq_metricRm04At
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 2 G g R) (hK : IsCompact K)
    {x : M} (hx : x ∈ K) :
    Tendsto (fun n => normSq0S (G n) x 4 (metricRm04At (G n) x)) atTop
      (𝓝 (normSq0S g x 4 (metricRm04At g x))) := by
  apply tendsto_normSq0S_of_chart_components G g x (fun n => metricRm04At (G n) x)
    (metricRm04At g x)
  · intro i j
    exact hconv.tendsto_inner hK hx _ _
  · intro v
    have h := hconv.tendsto_metricRm04StandardAt hK hx
      (chartBasisVecFiber (I := I) x (v 0) x) (chartBasisVecFiber (I := I) x (v 1) x)
      (chartBasisVecFiber (I := I) x (v 2) x) (chartBasisVecFiber (I := I) x (v 3) x)
    have hv : (fun j => chartBasisVecFiber (I := I) x (v j) x) =
        vec4 (chartBasisVecFiber (I := I) x (v 0) x) (chartBasisVecFiber (I := I) x (v 1) x)
          (chartBasisVecFiber (I := I) x (v 2) x) (chartBasisVecFiber (I := I) x (v 3) x) := by
      funext j
      fin_cases j <;> rfl
    simpa only [metricRm04StandardAt_apply, hv] using h

theorem MetricCPConvergenceOn.normSq_metricRm04At_le
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 2 G g R) (hK : IsCompact K)
    {x : M} (hx : x ∈ K) {C : ℝ}
    (hbound : ∀ᶠ n in atTop, normSq0S (G n) x 4 (metricRm04At (G n) x) ≤ C) :
    normSq0S g x 4 (metricRm04At g x) ≤ C :=
  le_of_tendsto (hconv.tendsto_normSq_metricRm04At hK hx) hbound

theorem MetricCPConvergenceOn.tendsto_curvDerivNorm_zero
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 2 G g R) (hK : IsCompact K)
    {x : M} (hx : x ∈ K) :
    Tendsto (fun n => curvDerivNorm 0 (G n) x) atTop (𝓝 (curvDerivNorm 0 g x)) := by
  change Tendsto (fun n => Real.sqrt (normSq0S (G n) x 4 (metricRm04 (G n) x))) atTop
    (𝓝 (Real.sqrt (normSq0S g x 4 (metricRm04 g x))))
  simpa only [metricRm04_apply] using (hconv.tendsto_normSq_metricRm04At hK hx).sqrt

theorem curvDerivNorm_zero_le_of_open_cover_metric_limits
    {ι : Type*} (U : ι → TopologicalSpace.Opens M) (hcover : ∀ x : M, ∃ n, x ∈ U n)
    (G : ∀ n, ℕ → SmoothRiemannianMetric I (U n)) (g R : SmoothRiemannianMetric I M)
    (hconv : ∀ n, ∀ K : Set (U n), IsCompact K →
      MetricCPConvergenceOn K 2 (G n) (g.restrictOpen (U n)) (R.restrictOpen (U n)))
    {C : ℝ} (hbound : ∀ n (x : U n), ∀ᶠ i in atTop, curvDerivNorm 0 (G n i) x ≤ C)
    (x : M) : curvDerivNorm 0 g x ≤ C := by
  obtain ⟨n, hx⟩ := hcover x
  let y : U n := ⟨x,hx⟩
  have h := le_of_tendsto
    ((hconv n {y} isCompact_singleton).tendsto_curvDerivNorm_zero isCompact_singleton
      (mem_singleton y)) (hbound n y)
  rwa [curvDerivNorm_restrictOpen] at h

omit [I.Boundaryless] in
theorem MetricCPConvergenceOn.eventually_curvDerivNorm_zero_le [BoundarylessManifold I M]
    {G : ℕ → SmoothRiemannianMetric I M} {g R : SmoothRiemannianMetric I M}
    {K : Set M} (hconv : MetricCPConvergenceOn K 2 G g R) (hK : IsCompact K)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ∈ K, curvDerivNorm 0 g x ≤ C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, curvDerivNorm 0 (G k) x ≤ 4 * (C + 1) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let n : ℝ := Module.finrank ℝ E
  let delta := min (1 / 2 : ℝ) (1 / (n^2 * (C + 360) + 1))
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdhalf : delta ≤ 1 / 2 := min_le_left _ _
  have hdC : n^2 * delta * (C + 360) ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < n^2 * (C + 360) + 1)).mp
      (min_le_right _ _ : delta ≤ 1 / (n^2 * (C + 360) + 1))
    nlinarith
  obtain ⟨N, hN⟩ := (hconv.change_reference hK g) delta hd
  filter_upwards [eventually_ge_atTop N] with k hk
  intro x hx
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm a (G k) g g x ≤ delta :=
    (derivNorm_le_sup hK ha (G k) g g hx).trans (hN k hk).le
  have hh := sqrt_normSq_metricRm04At_le_of_metricDerivNorm_le
    g (G k) x hdhalf hjet
  have hcurv := hbound x hx
  change Real.sqrt (normSq0S g x 4 (metricRm04 g x)) ≤ C at hcurv
  rw [metricRm04_apply] at hcurv
  change Real.sqrt (normSq0S (G k) x 4 (metricRm04 (G k) x)) ≤ _
  rw [metricRm04_apply]
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_left (add_le_add hcurv (le_refl 360))
    (mul_nonneg (sq_nonneg n) hd.le)
  change n^2 * delta * (Real.sqrt (normSq0S g x 4 (metricRm04At g x)) + 360) ≤ _ at hmul
  change 4 * (Real.sqrt (normSq0S g x 4 (metricRm04At g x)) +
    n^2 * delta * (Real.sqrt (normSq0S g x 4 (metricRm04At g x)) + 360)) ≤ _
  linarith

variable {A : Type*} [PseudoMetricSpace A]

omit [I.Boundaryless] in
theorem eventually_curvDerivNorm_zero_le_of_uniform_metric_approximation [BoundarylessManifold I M]
    {G : ℕ → A → SmoothRiemannianMetric I M} {g : A → SmoothRiemannianMetric I M}
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K)
    {U : Set A} (hU : IsCompact U) {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ U,
      metricDerivNormSupOn K 2 (G i t) (g t) R < ε)
    (hlip : ∀ s ∈ U, ∀ t ∈ U, ∀ q : ℕ, q ≤ 2 → ∀ x ∈ K,
      metricDerivNorm q (g s) (g t) R x ≤ L * dist s t)
    (hcurv : ∀ t ∈ U, ∀ x ∈ K, curvDerivNorm 0 (g t) x ≤ C) :
    ∃ N : ℕ, ∀ i ≥ N, ∀ t ∈ U, ∀ x ∈ K,
      curvDerivNorm 0 (G i t) x ≤ 4 * (C + 1) := by
  classical
  by_contra! hnot
  choose n hn t ht x hx hbad using hnot
  obtain ⟨a, ha, rho, hrho, htime⟩ := hU.tendsto_subseq ht
  have hcp : MetricCPConvergenceOn K 2
      (fun i => G (n (rho i)) (t (rho i))) (g a) R := by
    apply metricCPConvergenceOn_of_uniform_approximation_of_lipschitz
      (G := fun i r => G (n (rho i)) r) (g := g) R hK hL ?_ hlip
      (Eventually.of_forall fun i => ht (rho i)) ha htime
    intro ε hε
    obtain ⟨N, hN⟩ := hconv ε hε
    exact ⟨N, fun i hi r hr => hN (n (rho i))
      (hi.trans ((hrho.id_le i).trans (hn (rho i)))) r hr⟩
  obtain ⟨i, hi⟩ := (hcp.eventually_curvDerivNorm_zero_le hK hC (hcurv a ha)).exists
  exact (not_lt_of_ge (hi (x (rho i)) (hx (rho i)))) (hbad (rho i))

end DifferentialGeometry.CheegerGromovCompactness
