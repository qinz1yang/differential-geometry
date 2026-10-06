import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimEndFaceZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowDihedral

/-!
# ZSP05's free-end faces on the dihedral final-family fixture (empty-truth test)

Lane S-ZSP04, group G20 (instance). `Gaf02ChainEJA.zsp05_free_end_faces_ZSP35` needs the chain,
`εr < 1/2` and `K ≥ 5`, all of which hold on the `K = 5` dihedral `LocalChartPacketsC14Z` fixture.
Its slim family is EMPTY: the row is an empty-truth test (satisfiability and typing on the closed
family), not a test of the end tubes (the fixture has no slim component; known gap D71-7).
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

/-- **ZSP05's free-end faces on the dihedral fixture**: a chain with (JA), an empty slim family and
the whole row (vacuous over the arcs of the empty `D₃`). -/
theorem zsp05_free_end_faces_dihedralTiny_ZSP35 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        ∃ (hεr : (0 : ℝ) < 1 / 2) (hK : 5 ≤ 5),
          type_of% (Gaf02ChainEJA.zsp05_free_end_faces_ZSP35
            (P := dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h) C hεr hK) := by
  have hεr : (0 : ℝ) < 1 / 2 := by norm_num
  have hK : 5 ≤ 5 := le_rfl
  exact (exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD Kj).imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ =>
    ⟨rfl, hεr, hK,
      Gaf02ChainEJA.zsp05_free_end_faces_ZSP35 (P := dihedralRowZ5_GAFD _ _ _ _ _ _) C hεr hK⟩

end DifferentialGeometry.Geometry.Collapse
