import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5EvolutionAssembly
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Limit
import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Potential

/-!
# The decay of the normalized surface flow modulo step (iii)

INT connector for U1 a5.2 (design D18 (viii)). `a5_decay_of_iii` is P8b's `a5_decay` with the
hypotheses `hpot` and `hgauge` discharged: `hpot` by U1V's `surfaceFlow_exists_potential_family`
(step (i)) and `hgauge` by U1V's `surfaceFlow_gauge_limit_round` (steps (v) and (vi)), whose
`hTeq` comes from `surfaceFlow_maximal_time_eq` (a2). Only the frozen step (iii), the higher decay
of the trace-free Hessian, remains a hypothesis.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.Measure
open Bundle Filter Topology Set MeasureTheory
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem a5_decay_of_iii [NeZero (Module.finrank ℝ E)] [CompactSpace M] [ConnectedSpace M]
    (hdim : Module.finrank ℝ E = 2) {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hscal : ∀ x, 0 < S.scalar 0 x)
    (hmax : IsMaximalAtEndpoint (I := I) hTm S)
    (hiii : ∀ (f : ℝ → C^∞⟮I, M; ℝ⟯)
      (_ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun q : ℝ × M => f q.1 q.2)
        (Ioo 0 Tm ×ˢ univ))
      (_ : ∀ t ∈ Ioo 0 Tm, ∀ x,
        ΔG (S.family.metric t) (f t) x = S.scalar t x - 1 / (flowExtinctionTime S - t))
      (a : ℝ → ℝ) (_ : ∀ t ∈ Ioo 0 Tm, ∀ x, HasDerivAt (fun s => f s x)
        (S.scalar t x + f t x / (flowExtinctionTime S - t) + a t) t)
      (Mf : ℝ → Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
        (n := (∞ : WithTop ℕ∞)) 2)
      (_ : ∀ t ∈ Ioo 0 Tm, ∀ x, Mf t x = tracelessHessAt (S.family.metric t) (f t) x)
      (t₀ C₀ c : ℝ) (_ : t₀ ∈ Ioo 0 Tm) (_ : 0 < c)
      (_ : ∀ t ∈ Ico t₀ Tm, ∀ x,
        (flowExtinctionTime S - t) ^ 2 * normSq0S (S.family.metric t) x 2 (Mf t x) ≤
          C₀ * (flowExtinctionTime S - t) ^ c)
      (_ : ∀ q : ℕ, ∃ B : ℝ, ∀ t ∈ Ico t₀ Tm, ∀ x,
        normSq0S (S.family.metric t) x (4 + q)
            (iterCov (S.family.metric t) 4 (metricRm04 (S.family.metric t)) q x) ≤
          B * (flowExtinctionTime S - t) ^ (-(2 + q : ℝ))),
      ∀ q : ℕ, ∃ C γ : ℝ, 0 < γ ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
        (flowExtinctionTime S - t) ^ (2 + q) *
            normSq0S (S.family.metric t) x (2 + q) (iterCov (S.family.metric t) 2 (Mf t) q x) ≤
          C * (flowExtinctionTime S - t) ^ γ) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ :=
  a5_decay hdim hTm S hS hscal hmax (surfaceFlow_exists_potential_family hdim S hS hscal) hiii
    (fun f hf hfeq Mf hM _ ht₀ hdecay ψ hψ0 hψ hψc hψd _ hc hlow =>
      surfaceFlow_gauge_limit_round hdim S hS hscal
        (surfaceFlow_maximal_time_eq hdim hTm S hS hscal hmax) f hf hfeq Mf hM ht₀ hdecay ψ hψ0
        hψ hψc hψd hc hlow)

end GC.Geometry
