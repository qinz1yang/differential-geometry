import DifferentialGeometry.Geometry.Fibration.ActualStageChainFc33Row
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowDihedral

/-!
# Consumer of the FC33 row: the `K = 5` dihedral final-family fixture

Lane S-BASES-KER, group G11. On the dihedral final family `LocalChartPacketsC14Z` at `K = 5`
(`dihedralRowZ5_GAFD`) the chain with (JA) of `exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD`
(`c_adjust = 10⁻⁵`, `c₃ < c_adjust`) carries FC33's row on its OWN bases object
`C.toChain.gaf02Bases_BAS C.rough`. The fixture's circle, edge and slim families are EMPTY
(stated): every stage clause of the row is vacuous there (marked bases, final bases, plateaux,
domains `U_j` and carriers `D_j` are empty) — joint satisfiability of the row's premises and of its
conclusion (clause 1 included, which is not vacuous), not a non-trivial instance of the stage
clauses (non-empty fixtures: review 75, outstanding).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **The FC33 row on the `K = 5` dihedral final-family fixture** (stage families EMPTY, stated:
the stage clauses are vacuous there, D71-7 / D70-8; clause 1 is not). -/
theorem exists_fc33_row_dihedralTiny_BAS (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).circle.centres = ∅ ∧
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).edge.centres = ∅ ∧
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        type_of% (C.toChain.fc33_row_BAS C.rough C.c_lt_adj) := by
  exact (exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD Kj).imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ => ⟨rfl, rfl, rfl, C.toChain.fc33_row_BAS C.rough C.c_lt_adj⟩

end DifferentialGeometry.Geometry.Collapse
