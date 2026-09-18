import DifferentialGeometry.Geometry.Metric.Convergence.Metric.PullbackParameter
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactTimeComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabChartBootstrap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem eventually_metricComparisonOn_of_diffeomorph_tendsto
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := M) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hcarrier : D.carrier = Icc a b) (hregular : Ioo a b ⊆ D.regular)
    (Y : P → M ≃ₘ⟮I3, I3⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I3) I3 ∞ (fun p : P × M => Y p.1 p.2))
    {p₀ : P} (hY₀ : Y p₀ = _root_.Diffeomorph.refl I3 M ∞)
    (τ : ℕ → P) (hτ : Tendsto τ atTop (𝓝 p₀))
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hJsub : J ⊆ Icc c b)
    {K : Set M} (hK : IsCompact K) (order : ℕ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, Nonempty (MetricComparisonOn S.base.metric S.base.metric
      (Y (τ n)) K J order epsilon) := by
  let U : TopologicalSpace.Opens M := ⊤
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  let T (n : ℕ) := solutionOnRestrictOpen (S.pullback (Y (τ n))) U
  have hT (n : ℕ) : IsSolutionOn (T n) :=
    isSolutionOn_restrictOpen _ (IsSolutionOn.pullback S hS (Y (τ n))) U
  let R := S.base.metric c
  have hclosed := solution_metricCLMSection_contMDiffOn_closed
    S hS hac hcb (by rw [hcarrier]) hregular
  have hconv : ∀ L : Set U, IsCompact L → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b,
        metricDerivNormSupOn L r ((T n).base.metric t)
          ((S.base.metric t).restrictOpen U) (R.restrictOpen U) < ε := by
    intro L hL r ε hε
    have hu := metricDerivNormSupOn_pullback_tendstoUniformlyOn
      S.base.metric isCompact_Icc hclosed Y hY hY₀ R (hL.image continuous_subtype_val) r
    have hh := (Metric.tendstoUniformlyOn_iff.mp hu) ε hε
    have hn := hτ.eventually hh
    apply eventually_atTop.mp
    filter_upwards [hn] with n hn
    intro t ht
    change metricDerivNormSupOn L r
      ((Diffeomorph.pullbackMetricCross (S.base.metric t) (Y (τ n))).restrictOpen U)
      ((S.base.metric t).restrictOpen U) (R.restrictOpen U) < ε
    rw [metricDerivNormSupOn_restrictOpen]
    have hb := hn t ht
    simp only [Real.dist_eq, zero_sub, abs_neg] at hb
    exact (le_abs_self _).trans_lt hb
  apply eventually_metricComparisonOn_of_local_flow_convergence U T hT S hS hac hcb
    hcarrier hregular (R.restrictOpen U) hconv (fun _ => S.base.metric)
    (fun n => Y (τ n)) _ hJ hJsub hK (subset_univ K) order hepsilon
  intro n t x v w
  change ((Diffeomorph.pullbackMetricCross (S.base.metric t) (Y (τ n))).restrictOpen U).inner
    x v w = _
  rw [SmoothRiemannianMetric.restrictOpen_inner]
  exact Diffeomorph.pullbackMetricCross_inner (S.base.metric t) (Y (τ n)) (x : M) v w

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
