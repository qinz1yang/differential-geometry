import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroIsolationRow
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEJAInhabitant

/-!
# ZSP01's row on the dihedral fixture (satisfiability instance, D71)

Lane C14-ZSP35c. The only premise of `Gaf02ChainE.zsp01_row_ZSP35` is the chain `Ĉ`; it is met on
the dihedral `LocalChartPacketsC14` fixture on `RP³ # RP³` by lane C14-CHAIN-INST's producer run
`exists_gaf02ChainEJA_row_dihedralTiny_CHI` (`Ĉ = C.toGaf02ChainE`). The fixture has ONE zero ball
(nonempty zero family), so (ZE) is exercised on a nonempty index set; its circle, edge and slim
families are empty (the stage clauses are checked vacuously there).

* `zsp01_row_dihedralTiny_ZSP35`.
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

/-- **ZSP01's row holds on a nonempty instance**: on the dihedral fixture there is a
`Gaf02ChainEJA` whose zero family is nonempty, with `δ₀ = 200c₃/T < 1/1000` and (ZE) for `E` at
every zero index and every point. -/
theorem zsp01_row_dihedralTiny_ZSP35 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw
        (1 / 100000)),
      (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.centres.Nonempty ∧
      200 * c 2 / (1600 * (1000000 * 1200)) < 1 / 1000 ∧
      ∀ (i : (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset)
        (p : dihedralZeroSource),
        ‖C.toChain.E p (.inr (.inr (.inr (.inl i)))) -
            cgpGlobalMap (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
              (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero p (.inr (.inr (.inr (.inl i))))‖ <
          200 * c 2 / (1600 * (1000000 * 1200)) *
            ((dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.zero i.1
              ((Set.Finite.mem_toFinset _).mp i.2)).radius := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -, -, -, -, -⟩ :=
    exists_gaf02ChainEJA_row_dihedralTiny_CHI Kj (cadj := 1 / 100000) (by norm_num)
  obtain ⟨hδ, hrow⟩ := C.toGaf02ChainE.zsp01_row_ZSP35
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨dihedralTinyBase_CHI, rfl⟩, hδ,
    fun i p => ((hrow i).2 p).1 2⟩

end DifferentialGeometry.Geometry.Collapse
