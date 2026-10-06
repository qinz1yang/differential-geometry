import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesManifold
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesKernelApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCentresEmpty

/-!
# Consumer of the manifold-level threshold-5 submersions: the `RP³ # RP³` fixture

Lane S-BASES-KER, group G10. On the dihedral fixture of lane C14-CHAIN-INST the `Gaf02ChainE` of
`exists_gaf02ChainE_row_dihedralTiny_CHI` carries the bases object, hence (by
`Gaf02Bases.final_submersion_manifold_*_BAS`) the manifold-level submersions. The fixture's stage
families are EMPTY (stated: all three domains `U_st` are empty, so is every `W_st`): the
statements are vacuous there — joint satisfiability only (non-empty fixtures: review 75).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **The manifold-level submersions on the `RP³ # RP³` fixture** (stage families EMPTY, stated):
the chain on the enhanced planes carries the bases object, all three threshold-5 domains `U_st`
are empty (so the submersion statements are vacuous at the fixture), and the bases are empty. -/
theorem final_submersion_manifold_dihedralTiny_BAS (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainE (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw),
      Nonempty (Gaf02Bases C.toChain C.rough) ∧
      (∀ st, gafStageDomain5_BAS (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartPackets
        st = ∅) ∧
      ∀ st, C.toChain.finalBase_BAS st = ∅ := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨B⟩, -⟩ := gaf02Bases_dihedralTiny_BAS Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨B⟩,
    fun st => domain5_eq_empty_of_centres_empty_BASP _
      (dihedralTinyRow_stageCentres_BAS β₂ γc Lmax σs ζ h st),
    fun st => C.toChain.finalBase_eq_empty_of_centres_empty_BASP
      (dihedralTinyRow_stageCentres_BAS β₂ γc Lmax σs ζ h st)⟩

end DifferentialGeometry.Geometry.Collapse
