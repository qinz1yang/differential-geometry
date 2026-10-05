import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroRatio
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJAInhabitant

/-!
# ZSP02's global ratio on the dihedral fixture (satisfiability instance, D71)

Lane C14-ZSP35d. The premises of `Gaf02ChainE.zsp02_global_ratio_ZSP35` are the chain and the
radial bound `εr < 1/2`; both hold on the dihedral `LocalChartPacketsC14` fixture (`εr = 0`; chain
from `exists_gaf02ChainEJA_row_dihedralTiny_CHI`), whose zero family is NONEMPTY (one ball at
`dihedralTinyBase_CHI`), so the global ratio is produced for an actual index. The fixture's
circle, edge and slim families are empty.
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

/-- **The global ratio exists on a nonempty instance**: on the dihedral fixture there are a chain,
a zero index, a smooth `F` and an open `N ⊇ ∂Z` with `F = u/v − .4` on `N`, `Z = {F ≤ 0}` and
`(ZF) = {F = 0}`. -/
theorem zsp02_global_ratio_dihedralTiny_ZSP35 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw
        (1 / 100000))
      (k : (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset)
      (F : dihedralZeroSource → ℝ) (N : Set dihedralZeroSource), IsOpen N ∧
      zspFace_ZSP35 (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero k C.toChain.E ⊆ N ∧
      ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ z ∈ N, F z = ((C.toChain.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.toChain.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) ∧
      {z | F z ≤ 0} = zspDomain_ZSP35
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero k C.toChain.E ∧
      {z | F z = 0} = zspFace_ZSP35
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero k C.toChain.E := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -, -, -, -, -⟩ :=
    exists_gaf02ChainEJA_row_dihedralTiny_CHI Kj (cadj := 1 / 100000) (by norm_num)
  have hk : dihedralTinyBase_CHI ∈
      (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset :=
    (Set.Finite.mem_toFinset _).mpr rfl
  obtain ⟨F, N, hNo, hZN, -, hFs, hFr, hFle, hF0, -⟩ :=
    C.toGaf02ChainE.zsp02_global_ratio_ZSP35 (by norm_num) ⟨dihedralTinyBase_CHI, hk⟩
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨dihedralTinyBase_CHI, hk⟩, F, N, hNo,
    hZN, hFs, hFr, hFle, hF0⟩

end DifferentialGeometry.Geometry.Collapse
