import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomainsSupported
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJAInhabitant

/-!
# The supported ZSP02 isotopy on the dihedral fixture (satisfiability instance, D71)

Lane C14-ZSP35c. The premises of `Gaf02ChainE.zsp02_supported_isotopy_ZSP35` are the chain and
the radial bound `εr < 1/2`; both hold on the dihedral `LocalChartPacketsC14` fixture
(`εr = 0`; chain from `exists_gaf02ChainEJA_row_dihedralTiny_CHI`), whose zero family is
NONEMPTY (one ball at `dihedralTinyBase_CHI`), so the isotopy is produced for an actual index.
The fixture's circle, edge and slim families are empty.
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

/-- **The supported ZSP02 isotopy exists on a nonempty instance**: on the dihedral fixture there
are a chain, a zero index and an isotopy `Φ` from the identity whose time one carries the original
sublevel `{η ≤ .4}` onto the actual zero domain `Z`. -/
theorem zsp02_supported_isotopy_dihedralTiny_ZSP35 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw
        (1 / 100000))
      (k : (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset)
      (Φ : ℝ → dihedralZeroSource ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ dihedralZeroSource),
      (∀ x, Φ 0 x = x) ∧
      Φ 1 '' {z | ((dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.zero k.1
          ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero k C.toChain.E := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -, -, -, -, -⟩ :=
    exists_gaf02ChainEJA_row_dihedralTiny_CHI Kj (cadj := 1 / 100000) (by norm_num)
  have hk : dihedralTinyBase_CHI ∈
      (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset :=
    (Set.Finite.mem_toFinset _).mpr rfl
  obtain ⟨-, Φ, -, -, -, hΦ0, -, -, h1, -⟩ :=
    C.toGaf02ChainE.zsp02_supported_isotopy_ZSP35 (by norm_num) ⟨dihedralTinyBase_CHI, hk⟩
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨dihedralTinyBase_CHI, hk⟩, Φ, hΦ0, h1⟩

end DifferentialGeometry.Geometry.Collapse
