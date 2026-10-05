import DifferentialGeometry.Geometry.Fibration.ActualStageChainCentresEmpty
import DifferentialGeometry.Geometry.Fibration.ActualStageChainInhabitant

/-!
# Consumers of the constructor-independent empty-stage helpers

* `Gaf02Chain.E_eq_globalMap_of_centres_empty_BASP`: if all three stage families are empty, the
  chain's final map is the original map, `E = 𝓔⁰` (for ANY slots).
* `dihedralTiny_active_empty_stages_BASP`: on lane C14-CHAIN-INST's nonempty closed fixture
  (`RP³ # RP³`, empty stage families) the chain with three `.active` slots
  (`exists_gaf02Chain_active_CHI`) has identity stages, empty native zero sets, empty marked and
  final bases, empty plateaus and threshold-5 domains — the case review 71 (D71-11) singles out:
  `.active` on an empty family.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

namespace Gaf02Chain

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
  {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **Three empty stages give `E = 𝓔⁰`** (for any slots, by the cutoffs). -/
theorem E_eq_globalMap_of_centres_empty_BASP (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (h : ∀ st, gafStageCentres P st = ∅) : C.E = cgpGlobalMap P.toLocalChartFamily P.zero := by
  have h0 := C.stageOut_eq_stageIn_of_centres_empty_BASP (h 0)
  have h1 := C.stageOut_eq_stageIn_of_centres_empty_BASP (h 1)
  have h2 := C.stageOut_eq_stageIn_of_centres_empty_BASP (h 2)
  change C.g₁ = cgpGlobalMap P.toLocalChartFamily P.zero at h0
  change C.g₂ = C.g₁ at h1
  change C.E = C.g₂ at h2
  rw [h2, h1, h0]

end Gaf02Chain

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **`.active` on an empty family** (D71-11), on the dihedral fixture: the chain with three active
slots has identity stages, empty native zero sets, empty marked and final bases, empty plateaus and
empty threshold-5 domains, and `E = 𝓔⁰`. -/
theorem dihedralTiny_active_empty_stages_BASP (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (C : Gaf02Chain dihedralTinyStdBase_CHI Kj Ξ Γ S eg c cw),
      (∀ st, ∃ O, C.slot st = Gaf02StageSlot.active O) ∧
      (∀ st, C.stageOut_BAS st = C.stageIn_BAS st) ∧
      (∀ st, (C.slot st).zeroSet = ∅) ∧
      (∀ st, C.markedBase_BAS st = ∅) ∧ (∀ st, C.finalBase_BAS st = ∅) ∧
      (∀ st, gafStagePlateau_BAS dihedralTinyStdBase_CHI st = ∅) ∧
      (∀ st, gafStageDomain5_BAS dihedralTinyStdBase_CHI st = ∅) ∧
      C.E = cgpGlobalMap dihedralTinyStdBase_CHI.toLocalChartFamily
        dihedralTinyStdBase_CHI.zero := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, C, hact, -, -⟩ := exists_gaf02Chain_active_CHI Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, C, hact,
    fun st => C.stageOut_eq_stageIn_of_centres_empty_BASP (dihedralTinyStd_stageCentres_CHI st),
    fun st => C.zeroSet_eq_empty_of_centres_empty_BASP (dihedralTinyStd_stageCentres_CHI st),
    fun st => C.markedBase_eq_empty_of_centres_empty_BASP (dihedralTinyStd_stageCentres_CHI st),
    fun st => C.finalBase_eq_empty_of_centres_empty_BASP (dihedralTinyStd_stageCentres_CHI st),
    fun st => plateau_eq_empty_of_centres_empty_BASP _ (dihedralTinyStd_stageCentres_CHI st),
    fun st => domain5_eq_empty_of_centres_empty_BASP _ (dihedralTinyStd_stageCentres_CHI st),
    C.E_eq_globalMap_of_centres_empty_BASP dihedralTinyStd_stageCentres_CHI⟩

end DifferentialGeometry.Geometry.Collapse
