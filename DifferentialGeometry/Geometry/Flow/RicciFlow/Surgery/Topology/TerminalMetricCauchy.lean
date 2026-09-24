import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricPrelimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricTimeLipschitz

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ}

private local instance terminalSigmaCompact (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

private local instance terminalC1 (G : P.IncomingSlab a s) :
    IsManifold ThreeModel 1 G.terminalRegularOpen := IsManifold.of_le (n := ∞) (by decide)
private local instance terminalC2 (G : P.IncomingSlab a s) :
    IsManifold ThreeModel 2 G.terminalRegularOpen := IsManifold.of_le (n := ∞) (by decide)

theorem IncomingSlab.exists_metric_time_lipschitz_on_terminalRegularOpen
    (G : P.IncomingSlab a s) {K : Set G.terminalRegularOpen} (hK : IsCompact K) (N : ℕ) :
    ∃ c ∈ Ioo a s, ∃ L : ℝ, 0 ≤ L ∧
      ∀ q ≤ N, ∀ t ∈ Ico c s, ∀ u ∈ Ico c s, ∀ y ∈ K,
        metricDerivNorm q ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
          ((G.flow.base.metric u).restrictOpen G.terminalRegularOpen)
          ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen) y ≤ L * |t - u| := by
  obtain ⟨c, hc, L, hL, hb⟩ := G.exists_metric_time_lipschitz_on_compact_regularRegion
    (hK.image continuous_subtype_val) (by rintro _ ⟨x, _, rfl⟩; exact x.property) N
  refine ⟨c, hc, L, hL, ?_⟩
  intro q hq t ht u hu y hy
  rw [metricDerivNorm_restrictOpen]
  exact hb q hq t ht u hu y ⟨y, hy, rfl⟩

theorem IncomingSlab.metric_sequence_cauchy_on_compacts
    (G : P.IncomingSlab a s) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {K : Set G.terminalRegularOpen} (hK : IsCompact K) (N : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ m, n₀ ≤ m → ∀ n, n₀ ≤ n →
      ∀ q ≤ N, ∀ x ∈ K,
        metricDerivNorm q ((G.flow.base.metric (τ m)).restrictOpen G.terminalRegularOpen)
          ((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen)
          ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen) x < ε := by
  obtain ⟨c, hc, L, hL, hlip⟩ := G.exists_metric_time_lipschitz_on_terminalRegularOpen hK N
  have hcauchy : CauchySeq τ := Filter.Tendsto.cauchySeq (hτ.mono_right nhdsWithin_le_nhds)
  intro ε hε
  have hδ : 0 < ε / (L + 1) := div_pos hε (by linarith)
  obtain ⟨n₁, hn₁⟩ := Metric.cauchySeq_iff.mp hcauchy (ε / (L + 1)) hδ
  obtain ⟨n₂, hn₂⟩ := eventually_atTop.mp (hτ.eventually (Ico_mem_nhdsLT hc.2))
  refine ⟨max n₁ n₂, ?_⟩
  intro m hm n hn q hq x hx
  have htimes := hn₁ m ((le_max_left _ _).trans hm) n ((le_max_left _ _).trans hn)
  rw [Real.dist_eq] at htimes
  have hprod : L * |τ m - τ n| < ε := by
    have hmul : |τ m - τ n| * (L + 1) < ε :=
      (lt_div_iff₀ (by linarith : 0 < L + 1)).mp htimes
    nlinarith [abs_nonneg (τ m - τ n)]
  exact (hlip q hq (τ m) (hn₂ m ((le_max_right _ _).trans hm))
    (τ n) (hn₂ n ((le_max_right _ _).trans hn)) x hx).trans_lt hprod

theorem IncomingSlab.metric_sequence_inner_cauchy
    (G : P.IncomingSlab a s) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (v w : TangentSpace ThreeModel x) :
    CauchySeq (fun n => ((G.flow.base.metric (τ n)).restrictOpen
      G.terminalRegularOpen).inner x v w) := by
  apply metricInner_cauchy _ ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen) x v w
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := G.metric_sequence_cauchy_on_compacts hτ
    (isCompact_singleton (x := x)) 0 ε hε
  exact ⟨n₀, fun m hm n hn => hn₀ m hm n hn 0 le_rfl x (mem_singleton x)⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
