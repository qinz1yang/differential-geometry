import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainCusp74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainRowsEZ
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroDomains74
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroRatioInstance

/-!
# Draft 74 Z2 on the closed source `S`, and a non-vacuous consumer of the zero exits

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G28 (closed binding + consumer).

* `ClosedChainEZRowsSource_RGC.zeroDomains_exists_74`: the closed-route `zero` field. On the
  source's own chain `S.chain.toGaf02ChainE`, with `φ = M.ψ` and `∂W = ∅` from the model
  (`ClosedModel.boundary_empty_R74`): given the selected solid cores `Q k` of the sublevels
  `{η_k ≤ 2/5}` (Z1 data), a `ZeroDomains W` whose pieces are the `M.ψ`-images of ZSP02's zero
  domains and whose ratios are Z0's definers pulled back by `M.ψ⁻¹` (exact normalization on the
  buffers).
* `zero_exits_data_dihedralTiny74`: the exits of `Gaf02ChainE.zero_exits_data74` on the dihedral
  fixture, whose zero family is NONEMPTY: an index, and the definers with buffers and the exact
  normalization.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open GC.GraphManifold.Assembly.FC39P0 (pieceBoundary)

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **The closed-route `zero` field** (draft 74 Z2 at the closed source): the zero domains of the
source's chain carried to `W` by `M.ψ`, with the selected cores' branches as models. -/
theorem ClosedChainEZRowsSource_RGC.zeroDomains_exists_74 {K : ℕ}
    {T : ClosedThresholdsV4 (earlyDataSharedV4 K)} {R : ClosedRegisterV4 (earlyDataSharedV4 K) T}
    {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {M : ClosedModel W g} {δ εr Λz : ℝ} (S : ClosedChainEZRowsSource_RGC K R M δ εr Λz)
    (hεr : εr < 1 / 2)
    (Q : ∀ k : S.F.family.zero.finite_centres.toFinset, SelectedSmoothCore74.{u, 0}
      {z | (S.F.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5}) :
    ∃ (D : ZeroDomains W) (κ : Fin D.count ≃ S.F.family.zero.finite_centres.toFinset),
      ∀ j : Fin D.count,
        range (D.piece j).map = M.ψ '' zspDomain_ZSP35
            S.F.family.toLocalChartPacketsC14.toLocalChartFamily S.F.family.zero (κ j)
            S.chain.toGaf02ChainE.E ∧
        pieceBoundary (D.piece j) = M.ψ '' zspFace_ZSP35
            S.F.family.toLocalChartPacketsC14.toLocalChartFamily S.F.family.zero (κ j)
            S.chain.toGaf02ChainE.E ∧
        (∃ N : Set M.X, IsOpen N ∧ zspFace_ZSP35
            S.F.family.toLocalChartPacketsC14.toLocalChartFamily S.F.family.zero (κ j)
            S.chain.toGaf02ChainE.E ⊆ N ∧ (D.near j : Set W.Carrier) = M.ψ '' N ∧
          ∀ z ∈ N, D.ratio j (M.ψ z) =
            ((S.chain.toGaf02ChainE.E z (.inr (.inr (.inr (.inl (κ j)))))).fst : ℝ²) 0 /
              (S.chain.toGaf02ChainE.E z (.inr (.inr (.inr (.inl (κ j)))))).snd - 2 / 5) ∧
        ((D.model j).isRight = true ↔ (Q (κ j)).IsClosed) := by
  obtain ⟨D, κ, -, h⟩ := S.chain.toGaf02ChainE.zeroDomains_of_actual_zero_exit74 hεr M.ψ
    M.boundary_empty_R74 Q
  exact ⟨D, κ, h⟩

attribute [local instance] dihedralTinyMetricSpace_CHI

/-- **Non-vacuous consumer of the zero exits**: on the dihedral fixture (zero family NONEMPTY:
one ball) the assembler's exit data exists for an actual index — the definers `F k` with buffers
`N k`, `{F k ≤ 0} = Z_k`, `{F k = 0} = frontier Z_k`, and the exact normalization
`F k = u_k/v_k − 2/5` on `N k`. -/
theorem zero_exits_data_dihedralTiny74 (Kj : ℕ) :
    ∃ (Ξ Γ S eg c cw : Fin 3 → ℝ) (β₂ γc Lmax σs ζ : ℝ) (h : β₂ ≤ 1 / 4)
      (C : Gaf02ChainEJA (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h) Kj Ξ Γ S eg c cw
        (1 / 100000)),
      Nonempty (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset ∧
      ∃ (F : (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset →
          dihedralZeroSource → ℝ) (N : (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ
            h).zero.finite_centres.toFinset → Set dihedralZeroSource),
        (∀ k, {x | F k x ≤ 0} = zspDomain_ZSP35
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).toLocalChartFamily
          (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero k C.toChain.E) ∧
        (∀ k, ∀ z ∈ N k, F k z = ((C.toChain.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
          (C.toChain.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) := by
  obtain ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, -, -, -, -, -⟩ :=
    exists_gaf02ChainEJA_row_dihedralTiny_CHI Kj (cadj := 1 / 100000) (by norm_num)
  have hk : dihedralTinyBase_CHI ∈
      (dihedralTinyRowPackets_CHI β₂ γc Lmax σs ζ h).zero.finite_centres.toFinset :=
    (Set.Finite.mem_toFinset _).mpr rfl
  obtain ⟨-, F, N, -, -, -, -, -, hle, -, -, -, -, hFeq⟩ :=
    C.toGaf02ChainE.zero_exits_data74 (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨Ξ, Γ, S, eg, c, cw, β₂, γc, Lmax, σs, ζ, h, C, ⟨⟨dihedralTinyBase_CHI, hk⟩⟩, F, N,
    hle, hFeq⟩

end DifferentialGeometry.Geometry.Collapse
