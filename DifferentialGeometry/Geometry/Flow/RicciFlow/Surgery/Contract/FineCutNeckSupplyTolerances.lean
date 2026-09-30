import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapSideExclusion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSliceSeparatedSides

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem inv_add_one_le_inv_of_le_div_one_add {εc eps : ℝ} (hεc : 0 < εc) (heps : 0 < eps)
    (h : eps ≤ εc / (1 + εc)) : εc⁻¹ + 1 ≤ eps⁻¹ := by
  have hpos : 0 < εc / (1 + εc) := div_pos hεc (by linarith)
  calc εc⁻¹ + 1 = (εc / (1 + εc))⁻¹ := by
        rw [inv_div, add_div, div_self hεc.ne', one_div, add_comm]
    _ ≤ eps⁻¹ := inv_anti₀ heps h

theorem exists_fineCutNeckSupplyStrong_tolerances :
    ∃ eta εcone : ℝ, 0 < eta ∧ 0 < εcone ∧ εcone ≤ eta ∧ εcone ≤ 1 / 1000 ∧
    (∀ (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))
      {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s) (L : G.TerminalLimitMetric)
      (hsing : G.SingularEndpoint) (parameters : CutoffParameters) {εP Λ : ℝ}
      (P : TerminalCorePresentation
        { stage := H.stage k
          startTime := H.time k
          endTime := s
          startTime_nonneg := H.toHistory.time_nonneg k
          startTime_lt_endTime := G.lt
          slab := G
          terminal := L
          singular := hsing
          parameters := parameters } εP Λ), εP ≤ eta →
    ∀ (c : ConnectedComponents G.terminalRegularOpen) (e : P.hornIndex c)
      {B : Set G.terminalRegularOpen}, IsCompact B → B ⊆ P.hornHalfRange c e →
    ∀ {ε ε₁ C1 C2 qcan : ℝ}, 0 < ε → ε ≤ eta →
      (∀ x ∈ B, 4 * C2 * (Λ * (P.coreRadius ^ 2)⁻¹) < metricScalarAt L.metric x) →
      (∀ x ∈ B, qcan < metricScalarAt L.metric x) →
      H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan s →
      ∀ᶠ t in 𝓝[<] s, ∀ x ∈ B, H.toHistory.HistoryStrongNeck k G ε₁ x.val t) ∧
    (∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
    ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
    ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
      δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ P.hornHalfRange c e →
    ∀ (W : Set D.slab.terminalRegularOpen) {cQ U : ℝ}, IsOpen W → IsConnected W →
      frontier W = N.chart '' {z | z.val.2 = 0} →
      2 * (Λ * (P.coreRadius ^ 2)⁻¹) < cQ →
      (∀ z ∈ closure W, cQ ≤ metricScalarAt D.terminal.metric z ∧
        metricScalarAt D.terminal.metric z ≤ U) →
      False) ∧
    (∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
      ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
      ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
        δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ P.hornHalfRange c e →
        (∀ w ∈ frontier (P.core c), 2 * metricScalarAt D.terminal.metric w < N.scale) →
        ∃ S V W : Set D.stage.Carrier, IsOpen V ∧ IsOpen W ∧ Disjoint V W ∧
          (∀ᶠ τ in 𝓝[<] D.endTime, ∀ z ∈ S,
            riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val z ≤
              ENNReal.ofReal (7 / Real.sqrt (D.slab.flow.scalar τ N.center.val))) ∧
          ∀ {A : ℝ}, 0 < A →
            IsCompact (riemannianClosedBallOf D.terminal.metric N.center
              (4 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center))) →
            (∀ w ∈ frontier (P.core c), ENNReal.ofReal
                (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) <
              riemannianEDistOf D.terminal.metric N.center w) →
            ∀ᶠ τ in 𝓝[<] D.endTime,
              riemannianClosedBallOf (D.slab.flow.base.metric τ) N.center.val
                  (3 * A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) \ S ⊆ V ∪ W ∧
              ∃ p ∈ V, ∃ q ∈ W,
                ENNReal.ofReal (A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) ≤
                  riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val p ∧
                riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val p <
                  ENNReal.ofReal (3 * A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) ∧
                ENNReal.ofReal (A / Real.sqrt (D.slab.flow.scalar τ N.center.val)) ≤
                  riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val q ∧
                riemannianEDistOf (D.slab.flow.base.metric τ) N.center.val q <
                  ENNReal.ofReal (3 * A / Real.sqrt (D.slab.flow.scalar τ N.center.val))) := by
  obtain ⟨eta₁, heta₁, h₁⟩ :=
    RetainedCoreHistory.eventually_forall_historyStrongNeck_of_subset_hornHalfRange.{u}
  obtain ⟨eta₂, heta₂, h₂⟩ := TerminalCorePresentation.false_of_terminal_capSide.{u}
  obtain ⟨eta₃, heta₃, h₃⟩ :=
    TerminalCorePresentation.exists_eventually_separated_sides_of_frontier_scalar_lt.{u}
  have heta : 0 < min eta₁ (min eta₂ eta₃) := lt_min heta₁ (lt_min heta₂ heta₃)
  refine ⟨min eta₁ (min eta₂ eta₃), min (min eta₁ (min eta₂ eta₃)) (1 / 1000), heta,
    lt_min heta (by norm_num), min_le_left _ _, min_le_right _ _, ?_, ?_, ?_⟩
  · intro H k s G L hsing parameters εP Λ P hεP c e B hB hBsub ε ε₁ C1 C2 qcan hε hεη
    exact h₁ H k G L hsing parameters P (hεP.trans (min_le_left _ _)) c e hB hBsub hε
      (hεη.trans (min_le_left _ _))
  · intro D ε Λ P hε
    exact h₂ P (hε.trans ((min_le_right _ _).trans (min_le_left _ _)))
  · intro D ε Λ P hε
    exact h₃ P (hε.trans ((min_le_right _ _).trans (min_le_right _ _)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
