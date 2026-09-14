import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionTerminalInputs
import DifferentialGeometry.Topology.Exhaustion

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem connectedSpace_of_exhaustsByOpen_isConnected {M : Type*} [TopologicalSpace M]
    {U : ℕ → Set M} (hU : ExhaustsByOpen U) (hconn : ∀ k, IsConnected (U k)) :
    ConnectedSpace M := by
  have hcover : (⋃ k, U k) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨k₀, hk₀⟩ := hU.subset ({x} : Set M) isCompact_singleton
    refine Set.mem_iUnion.2 ⟨k₀, ?_⟩
    exact hk₀ k₀ le_rfl (Set.mem_singleton x)
  rw [connectedSpace_iff_univ, ← hcover]
  refine ⟨?_, isPreconnected_of_forall_pair fun x hx y hy => ?_⟩
  · obtain ⟨x, hx⟩ := (hconn 0).1
    exact ⟨x, Set.subset_iUnion U 0 hx⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hy
    exact ⟨U (max i j), Set.subset_iUnion U _,
      hU.subset_of_le (le_max_left i j) hi, hU.subset_of_le (le_max_right i j) hj,
      (hconn (max i j)).isPreconnected⟩

theorem not_connectedSpace_bool : ¬ ConnectedSpace Bool := by
  intro hconn
  exact Bool.false_ne_true
    (PreconnectedSpace.constant hconn.toPreconnectedSpace (f := id) continuous_id
      (x := false) (y := true))

theorem exists_exhaustsByOpen_not_connected :
    ∃ U : ℕ → Set Bool, ExhaustsByOpen U ∧ ¬ ConnectedSpace Bool :=
  ⟨fun _ => Set.univ,
    ⟨fun _ => isOpen_univ, fun _ => Set.subset_univ _,
      fun _ _ => ⟨0, fun _ _ => Set.subset_univ _⟩⟩,
    not_connectedSpace_bool⟩

theorem terminal_compactnessInput_of_terminalLimit_exists {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X)) :
    TerminalCompactnessInput.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hpos, hmain⟩ := h
  refine ⟨epsStar, hpos, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨L⟩ := hmain eps heps hle X hb hd
  let P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0) :=
    { subseq := L.subseq
      strictMono := L.strictMono
      limit := L.space
      limit_complete := L.complete
      maps := L.maps
      convergence := { metrics := L.converges } }
  exact ⟨P, L.canonical_domains, L.connected, L.capture, L.precompact, L.connected_domains,
    L.nested, ⟨L.orientation, L.orientation_preserved⟩, L.scalar_bound, L.noncollapse⟩

theorem terminal_compactnessInput_iff_exists_terminalLimit {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) :
    TerminalCompactnessInput.{u} kappa sigma Phi ↔
      (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X)) :=
  ⟨fun h => terminal_limit_global_bound_of_compactnessInput hkappa hsigma hPhi h,
    terminal_compactnessInput_of_terminalLimit_exists⟩

def TerminalLimitMetricCompactnessInput (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
      ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
        (∀ k, P.convergence.metrics.domain k =
          CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
        MetricSourceCapture P.maps ∧
        (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
        (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) ∧
        (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
          (P.maps.partialDiffeomorph (i + 1)).source) ∧
        (∃ o : TangentOrientationSection P.limit.M,
          ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
            ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
              PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                (P.maps.partialDiffeomorph i) y hf) ∧
        (∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C) ∧
        MetricNoncollapsed P.limit kappa Set.univ

theorem terminalLimitMetricCompactnessInput_of_terminalCompactnessInput {kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (h : TerminalCompactnessInput.{u} kappa sigma Phi) :
    TerminalLimitMetricCompactnessInput.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hpos, hmain⟩ := h
  refine ⟨epsStar, hpos, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanon, _hconn, hcap, hpre, hcd, hnested, hor, hsb, hnc⟩ :=
    hmain eps heps hle X hb hd
  exact ⟨P, hcanon, hcap, hpre, hcd, hnested, hor, hsb, hnc⟩

theorem terminal_compactnessInput_of_metricCompactnessInput {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalLimitMetricCompactnessInput.{u} kappa sigma Phi) :
    TerminalCompactnessInput.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hpos, hmain⟩ := h
  refine ⟨epsStar, hpos, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanon, hcap, hpre, hcd, hnested, hor, hsb, hnc⟩ := hmain eps heps hle X hb hd
  have hconn : ConnectedSpace P.limit.M :=
    connectedSpace_of_exhaustsByOpen_isConnected P.maps.source_exhausts hcd
  exact ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, hsb, hnc⟩

theorem terminal_limit_global_bound_of_metricCompactnessInput {kappa sigma : ℝ}
    {Phi : ℝ → ℝ} (hkappa : 0 < kappa) (hsigma : 0 < sigma)
    (hPhi : AdmissiblePinchingFunction Phi)
    (h : TerminalLimitMetricCompactnessInput.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) :=
  terminal_limit_global_bound_of_compactnessInput hkappa hsigma hPhi
    (terminal_compactnessInput_of_metricCompactnessInput h)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
