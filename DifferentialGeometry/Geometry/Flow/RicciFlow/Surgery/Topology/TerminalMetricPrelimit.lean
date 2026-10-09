import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricJetBounds
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Compactness
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.SigmaCompactOpen
import Mathlib.Topology.Order.IsLUB

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

theorem IncomingSlab.terminal_metric_sequence_bounds
    (G : P.IncomingSlab a s) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s)) :
    (∀ q : ℕ, ∀ K : Set G.terminalRegularOpen, IsCompact K →
      ∃ C : ℝ, ∀ n : ℕ, ∀ x ∈ K,
        metricCovDerivNorm q ((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen)
          ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen) x ≤ C) ∧
    (∀ x : G.terminalRegularOpen, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      ∀ v : TangentSpace ThreeModel x,
        c * ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen).inner x v v ≤
          ((G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen).inner x v v) := by
  let gRef := (G.flow.base.metric a).restrictOpen G.terminalRegularOpen
  let gSeq := fun n => (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen
  have hbdd : ∀ q : ℕ, ∀ K : Set G.terminalRegularOpen, IsCompact K →
      ∃ C : ℝ, ∀ n : ℕ, ∀ x ∈ K, metricCovDerivNorm q (gSeq n) gRef x ≤ C := by
    intro q K hK
    have hcompact : IsCompact ((Subtype.val : G.terminalRegularOpen → P.Carrier) '' K) :=
      hK.image continuous_subtype_val
    have hsub : (Subtype.val : G.terminalRegularOpen → P.Carrier) '' K ⊆
        G.terminalRegularRegion := by
      rintro _ ⟨x, _, rfl⟩
      exact x.property
    obtain ⟨C, _, hC⟩ := G.eventually_metric_jets_on_compact_regularRegion hcompact hsub q
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hτ.eventually hC)
    apply cov_bdd_of_eventual hK q gSeq gRef
    refine ⟨n₀, C, fun n hn x hx => ?_⟩
    rw [covNorm_restrictOpen]
    exact hn₀ n hn q le_rfl x ⟨x, hx, rfl⟩
  have hlow : ∀ x : G.terminalRegularOpen, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n in atTop, ∀ v : TangentSpace ThreeModel x,
        c * gRef.inner x v v ≤ (gSeq n).inner x v v := by
    intro x
    obtain ⟨V, c, B, _, _, _, hxV, _, _, hc, hB, _, _, heq, _, _⟩ :=
      G.exists_terminalRegular_fixed_reference_metric_jets x.property
    refine ⟨B⁻¹, inv_pos.mpr (zero_lt_one.trans_le hB), ?_⟩
    filter_upwards [hτ.eventually (Ico_mem_nhdsLT hc.2)] with n hn
    intro v
    exact (heq (τ n) hn).2 x (subset_closure hxV) v |>.1
  exact ⟨hbdd, hlow⟩

theorem IncomingSlab.exists_smooth_positive_metric_prelimit
    (G : P.IncomingSlab a s) (hne : Nonempty G.terminalRegularOpen)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ gInf : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen,
        ∀ x : G.terminalRegularOpen,
          Tendsto (fun n => ((G.flow.base.metric (τ (φ n))).restrictOpen
            G.terminalRegularOpen).inner x) atTop (𝓝 (gInf.inner x)) := by
  obtain ⟨hbdd, hlow⟩ := G.terminal_metric_sequence_bounds hτ
  exact metricPreconv_gInf_of_eventual_pointwise_lower hne
    ((G.flow.base.metric a).restrictOpen G.terminalRegularOpen)
    (fun n => (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen) hbdd hlow

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage
