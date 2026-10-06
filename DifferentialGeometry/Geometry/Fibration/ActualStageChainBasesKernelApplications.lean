import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesKernel
import DifferentialGeometry.Geometry.Fibration.ActualStageChainBasesApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCentresEmpty

/-!
# Consumer of the kernel identification: the `RP³ # RP³` fixture

Lane S-BASES-KER, group G9. On the dihedral fixture of lane C14-CHAIN-INST the `Gaf02ChainE` of
`exists_gaf02ChainE_row_dihedralTiny_CHI` carries the bases object `Ĉ.bases_BAS`, and the kernel
identification `Gaf02Bases.ker_final_eq_BAS` is stated at it. The fixture's stage families are
EMPTY (so are the carriers `D_st`): the identification is vacuous there, and the vacuity is
stated (`∀ st, carrier_BAS st = ∅`) — joint satisfiability of the row's premises and of the
statement, not a non-trivial instance (non-empty fixtures: review 75, outstanding).
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

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- The three stage families of the row fixture `dihedralTinyRowPackets_CHI` are empty. -/
theorem dihedralTinyRow_stageCentres_BAS (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4) (st : Fin 3) :
    gafStageCentres (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartPackets st = ∅ := by
  fin_cases st <;> rfl

/-- The kernel identification at every chain on the enhanced planes of the fixture. -/
theorem ker_final_dihedralRow_BAS (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4) (Kj : ℕ)
    {Ξ Γ S eg c cw : Fin 3 → ℝ}
    (C : Gaf02ChainE (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw)
    (st : Fin 3) (p : dihedralZeroSource) (hp : p ∈ C.toChain.carrier_BAS st) :
    type_of% (C.bases_BAS.ker_final_eq_BAS st hp) :=
  C.bases_BAS.ker_final_eq_BAS st hp

/-- **Kernel identification on the `RP³ # RP³` fixture** (stage families EMPTY, stated): the
chain on the enhanced planes of `exists_gaf02ChainE_row_dihedralTiny_CHI` carries the bases object
(whose kernel identification is `ker_final_dihedralRow_BAS` at this chain) and ALL carriers `D_st`
are empty, so the identification is vacuous at the fixture (joint satisfiability of the row's
premises and of the object; non-empty fixtures: review 75, outstanding). -/
theorem ker_final_dihedralTiny_BAS (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainE (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw),
      (∀ st, C.toChain.carrier_BAS st = ∅) ∧ Nonempty (Gaf02Bases C.toChain C.rough) := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -, -, -, -, -⟩ :=
    exists_gaf02ChainE_row_dihedralTiny_CHI Kj
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C,
    fun st => C.toChain.rfDomain_eq_empty_of_centres_empty_BASP
      (dihedralTinyRow_stageCentres_BAS β₂ γc Lmax σs ζ h st), ⟨C.bases_BAS⟩⟩

end DifferentialGeometry.Geometry.Collapse
