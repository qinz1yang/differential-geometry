import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricFinal
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5DecayOfIII
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorTower
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5CommutatorLimit

/-!
# The surface lemma U1 without hypotheses

Chapter 7, surface lemma U1, closure of the ledger row. Lane U1C2 proved the frozen (iii)
`surfaceFlow_tracelessHess_derivative_decay`, so `a5_decay_of_iii` gives the scalar curvature
rate `|2 (Tm - t) R - 2| ≤ C (Tm - t)^δ` for every maximal surface Ricci flow of positive scalar
curvature (`a5_decay_unconditional`). Through `surfaceFlow_ha5_of_scalar_rate` (lane U1C) this is
the hypothesis `ha5` of `exists_isometryInvariant_roundMetric_of_a5` (lane U1E2), and
`exists_isometryInvariant_roundMetric_proved` has exactly the statement of the ledger lemma
`exists_isometryInvariant_roundMetric` of `NonnegativeClassificationProof.lean`, which keeps its
`sorry`; the chapter-7 consumers use the proved statement
(`NonnegativeClassificationUnconditional.lean`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2

theorem a5_decay_unconditional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hscal : ∀ x, 0 < S.scalar 0 x)
    (hmax : IsMaximalAtEndpoint (I := I) hTm S) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ :=
  a5_decay_of_iii hdim hTm S hS hscal hmax
    (fun f hf hfeq _ hft Mf hM _ _ _ ht₀ hc hdecay hshi =>
      surfaceFlow_tracelessHess_derivative_decay hdim S hS hscal f hf hfeq hft Mf hM ht₀ hc
        hdecay hshi)

theorem exists_isometryInvariant_roundMetric_proved {N : Type*} [TopologicalSpace N]
    [ChartedSpace MM2 N] [IsManifold 𝓘(ℝ, MM2) ∞ N] [T2Space N] [CompactSpace N]
    [ConnectedSpace N] [SimplyConnectedSpace N]
    (h : SmoothRiemannianMetric 𝓘(ℝ, MM2) N) (hscal : ∀ y, 0 < metricScalarAt h y) :
    ∃ h₁ : SmoothRiemannianMetric 𝓘(ℝ, MM2) N,
      (∀ (y : N) (X Y : TangentSpace 𝓘(ℝ, MM2) y),
        metricRm04StandardAt h₁ y X Y Y X =
          1 * (h₁.inner y X X * h₁.inner y Y Y - h₁.inner y X Y * h₁.inner y X Y)) ∧
      ∀ φ : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ N,
        Diffeomorph.pullbackMetric h φ = h → Diffeomorph.pullbackMetric h₁ φ = h₁ :=
  exists_isometryInvariant_roundMetric_of_a5
    (fun hTm S hS hscal hmax =>
      surfaceFlow_ha5_of_scalar_rate finrank_euclideanSpace_fin hTm S hS hscal
        (a5_decay_unconditional finrank_euclideanSpace_fin hTm S hS hscal hmax))
    h hscal

end GC.Geometry
