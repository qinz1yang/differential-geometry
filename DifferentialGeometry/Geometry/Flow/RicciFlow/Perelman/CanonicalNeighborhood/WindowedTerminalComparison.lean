import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FlowConvergenceAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

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

def WindowedTerminalComparison {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I3 L.space.M) : Prop :=
  g 0 = L.space.metric ∧
    ∃ diagonal : ℕ → ℕ, StrictMono diagonal ∧
      ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
        Set.Icc a b ⊆ D.carrier → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps →
          ∀ᶠ i in Filter.atTop,
            Nonempty (MetricComparisonOn (fun s => g s)
              (fun s => (X.term (L.subseq (B.subseq (diagonal i)))).S.base.metric s)
              (L.maps.partialDiffeomorph (B.subseq (diagonal i)))
              K (Set.Icc a b) order eps)

theorem windowedTerminalComparison_comp {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (h : WindowedTerminalComparison B D g) {e : ℕ → ℕ} (he : StrictMono e) :
    WindowedTerminalComparison B D g := by
  obtain ⟨hg0, diagonal, hdiag, hcomp⟩ := h
  refine ⟨hg0, diagonal ∘ e, hdiag.comp he, ?_⟩
  intro K hK a b hab hsub order eps heps
  filter_upwards [he.tendsto_atTop.eventually (hcomp K hK a b hab hsub order eps heps)]
    with i hi
  simpa only [Function.comp_apply] using hi

theorem terminalComparison_of_backwardExtension {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) :
    WindowedTerminalComparison B J B.solution.base.metric := by
  refine ⟨B.terminal, id, strictMono_id, ?_⟩
  · intro K hK a b hab hsub order eps heps
    filter_upwards [B.convergence K hK a b hab hsub order eps heps] with i hi
    simpa only [subsequenceMaps, Function.comp_apply, id_eq] using hi.2.2

theorem halfLineExtensionExists_of_windowedTerminalComparison {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    (h : WindowedTerminalComparison B ancientTimeInterval B.solution.base.metric) :
    HalfLineExtensionExists B := by
  obtain ⟨hg0, diagonal, hdiag, hcomp⟩ := h
  exact ⟨B.solution.base.metric,
    isHalfLineExtension_of_eventually_metricComparisonOn B hdiag hg0 (fun _ _ => rfl)
      (fun K hK a b hab hb order eps heps =>
        hcomp K hK a b hab (fun s hs => by
          rw [ancientTimeInterval_carrier]
          exact le_trans hs.2 hb) order eps heps)⟩

theorem halfLineExtensionExists_uniform_of_windowedTerminalComparison {kappa sigma : ℝ}
    {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
        WindowedTerminalComparison B ancientTimeInterval B.solution.base.metric) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
        HalfLineExtensionExists B := by
  obtain ⟨epsStar, hpos, hI⟩ := h
  exact ⟨epsStar, hpos, fun eps heps hle X L delta hd B =>
    halfLineExtensionExists_of_windowedTerminalComparison B (hI eps heps hle X L delta hd B)⟩

theorem slabLimitExists_of_windowedTerminalComparison {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {Y : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit Y}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (h : WindowedTerminalComparison B ancientTimeInterval g)
    {depthBound : ℝ} (hdepth : depthBound ≤ 2 * modelDepth eps)
    (hb : TerminalSlabBounds L depthBound) {delta : ℝ} :
    SlabLimitExists (L.toStatic hdepth hb) delta := by
  obtain ⟨hg0, diagonal, hdiag, hcomp⟩ := h
  refine ⟨g, hg0, B.subseq ∘ diagonal, B.strictMono.comp hdiag, ?_⟩
  intro K hK a b hab hsub order eps heps
  filter_upwards [hcomp K hK a b hab (fun s hs => by
    rw [ancientTimeInterval_carrier]
    exact (hsub hs).2) order eps heps] with i hi
  simpa only [TerminalLimit.toStatic, subsequenceMaps, Function.comp_apply] using hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
