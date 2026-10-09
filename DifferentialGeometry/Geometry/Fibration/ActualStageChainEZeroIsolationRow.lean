import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroBlock
import DifferentialGeometry.Geometry.Fibration.ActualStageChainPlateau
import DifferentialGeometry.Geometry.Fibration.ActualZeroBlockIsolationApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes

/-!
# ZSP01, the whole row on `Gaf02ChainE`

Lane C14-ZSP35c. Blueprint `master207B.tex`, ZSP01 (`lem:fibration-actual-zero-block-isolation`,
B:6323–6372), on ONE chain on the enhanced planes `Ĉ : Gaf02ChainE …` (lane C14-GAF8b), with
`F = 𝓔⁰ = cgpGlobalMap`, `J_i` = evaluation at the WHOLE zero block `.inr (.inr (.inr (.inl i)))`,
the intermediate maps `f ∈ {g₁, g₂, E}` (`stageOut_BAS`) and their stage projections
`f_st = π_st g_st` (`stageMap_BAS`), and `δ₀ = 200c₃/T`.

The two halves were closed separately: the ORIGINAL half `J_iF(p) = 0`
(`zsp01_original_zero_block_ZI`, on `LocalChartPacketsR`) and the STAGE half (`(ZI)` at
`g₁, g₂, E` and `(ZE)`: `Gaf02ChainE.zsp01_ZI_GAF8`, `Gaf02ChainE.zsp01_ZE_GAF8`, D71-12). This file
assembles them into the row:

* `Gaf02ChainE.zsp01_ZI_row_ZSP35`: (ZI) for `F`, for every stage output and every stage map, and
  for every point of the straight segment `[F p, E p]`;
* `Gaf02ChainE.zsp01_ZE_row_ZSP35`: (ZE) for every stage output, every stage map and the segment;
* `Gaf02ChainE.zsp01_delta_lt_ZSP35`: `δ₀ = 200c₃/T < 1/1000` (from `c₃ ≤ 1/512`, `T ≥ 1.6·10⁹Δ`);
* `Gaf02ChainE.zsp01_row_ZSP35`: the whole row.

Consumer: `zsp01_row_C14Z_ZSP35` (final family `LocalChartPacketsC14Z`, chain on its `C14`
projection). The row carries no global bound on `ρ/R_i` and no pruning rule (none is a hypothesis).
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

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

section C14

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- The zero block of a point of a segment `[x, y]` is in the segment of the zero blocks. -/
theorem segment_apply_mem_ZSP35 {κ : Type} (t : κ) {x y z : BlockSpace (fun _ : κ => ℝ²)}
    (hz : z ∈ segment ℝ x y) : z t ∈ segment ℝ (x t) (y t) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact ⟨a, b, ha, hb, hab, rfl⟩

/-- **`δ₀ = 200c₃/T < 1/1000`** on the chain (`c₃ ≤ 1/512`, `T ≥ 1600·10⁶Δ`, `Δ ≥ 1`). -/
theorem Gaf02ChainE.zsp01_delta_lt_ZSP35 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    200 * c 2 / T < 1 / 1000 := by
  obtain ⟨-, hΔ, -, -, -, -, -, hT, -⟩ := Ĉ.toChain.std
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := Ĉ.toChain.numbers
  have hT0 : 0 < T := by nlinarith
  rw [div_lt_iff₀ hT0]
  nlinarith

/-- **ZSP01 (ZI), the whole clause** (B:6326–6330): if `200R_i/T < ρ(p)`, the whole `i` block
vanishes for the original map `F = 𝓔⁰`, for every stage output `g₁, g₂, E`, for every stage map
`f_st = π_st g_st`, and at every point of the straight segment `[F p, E p]`. -/
theorem Gaf02ChainE.zsp01_ZI_row_ZSP35 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.zero.finite_centres.toFinset) {p : X}
    (hp : 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p) :
    cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i)))) = 0 ∧
    (∀ st : Fin 3, Ĉ.toChain.stageOut_BAS st p (.inr (.inr (.inr (.inl i)))) = 0) ∧
    (∀ st : Fin 3, Ĉ.toChain.stageMap_BAS st p (.inr (.inr (.inr (.inl i)))) = 0) ∧
    ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (Ĉ.toChain.E p),
      z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0 := by
  obtain ⟨-, hΔ, -, -, -, -, he, hT, -, -, -, -, hεr⟩ := Ĉ.toChain.std
  have hT0 : 0 < T := by nlinarith
  have hF : cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i)))) = 0 :=
    zsp01_original_zero_block_ZI P.toLocalChartPacketsR hT0 (by linarith) (by linarith [hεr.1])
      i hp
  obtain ⟨h1, h2, h3⟩ := Ĉ.zsp01_ZI_GAF8 i hp
  have hout : ∀ st : Fin 3, Ĉ.toChain.stageOut_BAS st p (.inr (.inr (.inr (.inl i)))) = 0 := by
    intro st
    fin_cases st
    · exact h1
    · exact h2
    · exact h3
  refine ⟨hF, hout, fun st => ?_, fun z hz => ?_⟩
  · change (gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (Ĉ.toChain.stageOut_BAS st p) (.inr (.inr (.inr (.inl i)))) = 0
    rw [gafStageQ_starProjection_zeroTag_GAF8 P st i]
    exact hout st
  · have hz' := segment_apply_mem_ZSP35 (.inr (.inr (.inr (.inl i))) :
      CGPTag P.toLocalChartFamily P.zero) hz
    rw [hF, h3, segment_same] at hz'
    exact hz'

/-- **ZSP01 (ZE), the whole clause** (B:6331–6336): with `δ₀ = 200c₃/T`, at EVERY `p`,
`‖J_i(f(p) − F(p))‖ < δ₀R_i` for every stage output `f = g_st`, for every stage map
`f = π_st g_st`, and for every point of the straight segment `[F p, E p]`. -/
theorem Gaf02ChainE.zsp01_ZE_row_ZSP35 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.zero.finite_centres.toFinset) (p : X) :
    (∀ st : Fin 3, ‖Ĉ.toChain.stageOut_BAS st p (.inr (.inr (.inr (.inl i)))) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
      200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius) ∧
    (∀ st : Fin 3, ‖Ĉ.toChain.stageMap_BAS st p (.inr (.inr (.inr (.inl i)))) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
      200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius) ∧
    ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (Ĉ.toChain.E p),
      ‖z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
          cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
        200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius := by
  obtain ⟨h1, h2, h3, h4⟩ := Ĉ.zsp01_ZE_GAF8 i p
  have hout : ∀ st : Fin 3, ‖Ĉ.toChain.stageOut_BAS st p (.inr (.inr (.inr (.inl i)))) -
      cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
      200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius := by
    intro st
    fin_cases st
    · exact h1
    · exact h2
    · exact h3
  refine ⟨hout, fun st => ?_, h4⟩
  change ‖(gafStageQ P.toLocalChartFamily P.zero st).starProjection
      (Ĉ.toChain.stageOut_BAS st p) (.inr (.inr (.inr (.inl i)))) -
    cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ < _
  rw [gafStageQ_starProjection_zeroTag_GAF8 P st i]
  exact hout st

/-- **ZSP01, the whole row on `Gaf02ChainE`** (B:6323–6336): `δ₀ = 200c₃/T < 1/1000`; for every
zero index `i`, (ZI) for `F`, the stage outputs, the stage maps and the segment `[F, E]`; (ZE) for
the stage outputs, the stage maps and the segment, at every point. -/
theorem Gaf02ChainE.zsp01_row_ZSP35 (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    200 * c 2 / T < 1 / 1000 ∧
    ∀ i : P.zero.finite_centres.toFinset,
      (∀ p, 200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p →
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i)))) = 0 ∧
        (∀ st : Fin 3, Ĉ.toChain.stageOut_BAS st p (.inr (.inr (.inr (.inl i)))) = 0) ∧
        (∀ st : Fin 3, Ĉ.toChain.stageMap_BAS st p (.inr (.inr (.inr (.inl i)))) = 0) ∧
        ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (Ĉ.toChain.E p),
          z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) = 0) ∧
      ∀ p,
        (∀ st : Fin 3, ‖Ĉ.toChain.stageOut_BAS st p (.inr (.inr (.inr (.inl i)))) -
            cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
          200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius) ∧
        (∀ st : Fin 3, ‖Ĉ.toChain.stageMap_BAS st p (.inr (.inr (.inr (.inl i)))) -
            cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
          200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius) ∧
        ∀ z ∈ segment ℝ (cgpGlobalMap P.toLocalChartFamily P.zero p) (Ĉ.toChain.E p),
          ‖z (.inr (.inr (.inr (.inl i))) : CGPTag P.toLocalChartFamily P.zero) -
              cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
            200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius :=
  ⟨Ĉ.zsp01_delta_lt_ZSP35, fun i =>
    ⟨fun _ hp => Ĉ.zsp01_ZI_row_ZSP35 i hp, fun p => Ĉ.zsp01_ZE_row_ZSP35 i p⟩⟩

end C14

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **Consumer: ZSP01 on the final family** (`LocalChartPacketsC14Z`, chain on its `C14`
projection): `δ₀ < 1/1000`; in (ZI)'s range the zero block of `E` and of `𝓔⁰` vanishes, and
everywhere the zero block of `E` is within `δ₀R_i` of that of `𝓔⁰`. -/
theorem zsp01_row_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (i : P.zero.finite_centres.toFinset) (p : X) :
    200 * c 2 / T < 1 / 1000 ∧
    (200 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / T < ρ p →
      cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i)))) = 0 ∧
      Ĉ.toChain.E p (.inr (.inr (.inr (.inl i)))) = 0) ∧
    ‖Ĉ.toChain.E p (.inr (.inr (.inr (.inl i)))) -
        cgpGlobalMap P.toLocalChartFamily P.zero p (.inr (.inr (.inr (.inl i))))‖ <
      200 * c 2 / T * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius := by
  obtain ⟨hδ, hrow⟩ := Ĉ.zsp01_row_ZSP35
  obtain ⟨hZI, hZE⟩ := hrow i
  exact ⟨hδ, fun hp => ⟨(hZI p hp).1, (hZI p hp).2.1 2⟩, (hZE p).1 2⟩

end Final

end DifferentialGeometry.Geometry.Collapse
