import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimFullRowZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowDihedral

/-!
# ZSP04's full row on the dihedral final-family fixture (empty-truth test)

Lane S-ZSP04, group G19 (instance). The premises of `Gaf02ChainEJA.zsp04_full_row_ZSP35` are the
chain, `εr < 1/2` and `K ≥ 5`; all hold on the `K = 5` dihedral `LocalChartPacketsC14Z` fixture of
`ActualStageChainGaf07RowDihedral` (`εr = 0`). Its slim family is EMPTY, so the row is an
EMPTY-TRUTH test there: the slim piece is empty (and so are the arc and loop clauses' content);
it checks that the premises are satisfiable and the statement is well typed on the closed family,
not the bundle construction itself (the fixture has no slim component; known gap D71-7).
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

/-- **ZSP04's full row on the dihedral fixture**: a chain with (JA), an empty slim family, and the
whole row (`K₃, D₃`, `D₃ = K₃ ∩ C₃`, arcs, ends, loops) with the slim piece EMPTY. -/
theorem zsp04_full_row_dihedralTiny_ZSP35 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        ∃ (hεr : (0 : ℝ) < 1 / 2) (hK : 5 ≤ 5),
          (∃ K₃ D₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
            D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧ C.slimPiece_ZSP35 K₃.carrier = ∅) ∧
          type_of% (Gaf02ChainEJA.zsp04_full_row_ZSP35
            (P := dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h) C hεr hK) := by
  have hεr : (0 : ℝ) < 1 / 2 := by norm_num
  have hK : 5 ≤ 5 := le_rfl
  exact (exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD Kj).imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ =>
    ⟨rfl, hεr, hK,
      (C.zsp04_D3_ZSP35 hεr).imp fun K₃ hK₃ => hK₃.imp fun D₃ hD₃ =>
        ⟨hD₃.1, C.slim_piece_empty_ZSP35 hεr K₃.carrier rfl⟩,
      Gaf02ChainEJA.zsp04_full_row_ZSP35 (P := dihedralRowZ5_GAFD _ _ _ _ _ _) C hεr hK⟩

end DifferentialGeometry.Geometry.Collapse
