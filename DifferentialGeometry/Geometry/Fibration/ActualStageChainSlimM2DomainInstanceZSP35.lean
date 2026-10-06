import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimM2DomainZSP35
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07RowDihedral

/-!
# ZSP05's smooth domain `M₂` on the dihedral final-family fixture

Lane S-ZSP04, group G21 (instance). `Gaf02ChainEJA.zsp05_M2_domain_ZSP35` needs the chain and
`εr < 1/2`, which hold on the `K = 5` dihedral `LocalChartPacketsC14Z` fixture (`εr = 0`). Its
ZERO family is NONEMPTY (one ball at `dihedralTinyBase_CHI`) and its slim family is EMPTY, so here
the zero side of the statement (`M₂ = M₁`, smooth domain along the actual zero sphere) is exercised
and the slim side is an empty-truth test.
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

/-- **ZSP05's smooth domain `M₂` on the dihedral fixture**: a chain with (JA), an empty slim family
and the whole domain statement for `M₂`. -/
theorem zsp05_M2_domain_dihedralTiny_ZSP35 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA
        (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).toLocalChartPacketsC14D.toLocalChartPacketsC14
        Kj Ξ Γ S eg c cw (1 / 100000)),
      (dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h).slim.centres = ∅ ∧
        ∃ (hεr : (0 : ℝ) < 1 / 2),
          type_of% (Gaf02ChainEJA.zsp05_M2_domain_ZSP35
            (P := dihedralRowZ5_GAFD β₂ γc Lmax σs ζ h) C hεr) := by
  have hεr : (0 : ℝ) < 1 / 2 := by norm_num
  exact (exists_gaf02ChainEJA_rowsZ5_dihedralTiny_GAFD Kj).imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun _ h => h.imp fun _ h => h.imp fun _ h =>
    h.imp fun C _ =>
    ⟨rfl, hεr,
      Gaf02ChainEJA.zsp05_M2_domain_ZSP35 (P := dihedralRowZ5_GAFD _ _ _ _ _ _) C hεr⟩

end DifferentialGeometry.Geometry.Collapse
