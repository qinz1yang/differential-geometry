import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionLimitInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedTerminalComparison

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

private theorem subsequenceMaps_strictMono_congr {X : PointedRiemannianSeq.{u, 0, 0} I3}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) {k : ℕ → ℕ}
    (hk₁ hk₂ : StrictMono k) :
    subsequenceMaps F k hk₁ = subsequenceMaps F k hk₂ := by
  cases Subsingleton.elim hk₁ hk₂
  rfl

private theorem convergesOn_subsequenceMaps_of_eq {X : FlowSequence.{u}}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f) {k₁ k₂ : ℕ → ℕ}
    (hk₁ : StrictMono k₁) (hk₂ : StrictMono k₂) (h : k₁ = k₂)
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P.M) D} :
    ConvergesOn (subsequenceMaps F k₁ hk₁) S →
      ConvergesOn (subsequenceMaps F k₂ hk₂) S := by
  cases h
  intro hc
  rwa [subsequenceMaps_strictMono_congr F hk₁ hk₂]

theorem ancientExtension_nonempty_iff_halfLineAncientLimitFrontier {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) :
    Nonempty (AncientExtension B) ↔ HalfLineAncientLimitFrontier B := by
  constructor
  · rintro ⟨E⟩
    refine ⟨fun s => E.extension.solution.base.metric s,
      ⟨?_, ?_, E.diagonal, E.strictMono, ?_⟩, E.extension.isSolution, E.ancient⟩
    · exact E.extension.terminal
    · exact E.agrees
    · exact convergesOn_subsequenceMaps_of_eq (X := X.toFlowSequence) L.maps
        E.extension.strictMono
        (B.strictMono.comp E.strictMono) E.maps_agree E.extension.convergence
  · intro h
    exact ancientExtension_nonempty_of_halfLineAncientLimitFrontier B h

theorem ancient_extension_iff_halfLineAncientExtensionFrontier {kappa sigma : ℝ}
    {Phi : ℝ → ℝ} :
    (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (delta : ℝ) (hd : 0 < delta)
        (B : BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))),
          Nonempty (AncientExtension B)) ↔
      HalfLineAncientExtensionFrontier.{u} kappa sigma Phi := by
  constructor
  · rintro ⟨epsStar, hpos, hmain⟩
    refine ⟨epsStar, hpos, fun eps heps hle X L delta hd B =>
      (ancientExtension_nonempty_iff_halfLineAncientLimitFrontier B).mp
        (hmain eps heps hle X L delta hd B)⟩
  · intro h
    exact ancient_extension_of_halfLineAncientLimitFrontier h

theorem halfLineAncientLimitFrontier_of_windowedTerminalComparison {eps kappa sigma : ℝ}
    {Phi : ℝ → ℝ} {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} {B : BackwardExtension L J}
    (hconv : WindowedTerminalComparison B ancientTimeInterval B.solution.base.metric)
    (hancient : HalfLineExtensionAncient B) :
    HalfLineAncientLimitFrontier B :=
  halfLineAncientLimitFrontier_of_exists_ancient
    (halfLineExtensionExists_of_windowedTerminalComparison B hconv) hancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
