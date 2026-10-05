import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainNumbers
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4StageOutput
import DifferentialGeometry.Geometry.Fibration.ActualStageChain

/-!
# The native stage output at the register's `Ξ_j(Γ_j)`, with the register's weight constant

Lane C14-REG-CHAIN (review 66, D66-5). On a packet of the final family, at a stage `j` of the
register's stage choice `st : ClosedStage (earlyDataSharedV4 K)`, every selection of original
preimages and every family of stage planes with the (CS) test at quality `Γ_j` and radius
`Σ_jρ ∘ sel` carry a `Cfs15StageOutput` built from the REGISTER'S OWN stage object
(`earlyDataSharedV4_stageOutput_C15 st j`, accuracy `Ξ_j(Γ_j)`, jet order `K`), whose weight budget
is the register's PR10 constant `c_w^{(j)} = stageCwAt_V4C st j`: CFS12's total bound
`Σ_i ‖Dw_i‖ ≤ c_w^{(j)}/r_x` of `nb_cw_stage_selection_GAFS3` is proved for the SAME selection `I`
of the SAME output (the output's own `I`, disjointness and tube inclusion). Nothing else of the
output changes. For `j = 0` the constant is `sharedCw_VAL6 st` (`stageNbAt_zero_V4C`).

* `cfs15StageOutput_withWeightBound_RGC`: replace the weight constant of an output by any constant
  for which the total budget holds on the output's own selection.
* `ClosedStage.stageOutput_RGC`: the stage output at `(K, Ξ_j(Γ_j), stageCwAt_V4C st j)`.
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

/-- **Re-weighting a native output**: the weight constant of a `Cfs15StageOutput` enters only its
field `weight_bound`; any constant `cw'` with the total budget on the output's own selection gives
an output with every other field unchanged. -/
def cfs15StageOutput_withWeightBound_RGC {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ}
    {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) (cw' : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ ball x (8 * ε⁻¹ * r x),
      ∑ i ∈ O.hI.toFinset, ‖fderiv ℝ (cfs15Weight_C15 ε r O.hI i) y‖ ≤ cw' / r x) :
    Cfs15StageOutput k K ε cw' S T r P :=
  { O with weight_bound := h }

/-- The re-weighted output has the same selection. -/
theorem cfs15StageOutput_withWeightBound_I_RGC {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] {k K : ℕ} {ε cw : ℝ} {S T : Set H}
    {r : H → ℝ} {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) (cw' : ℝ)
    (h : ∀ x ∈ S, ∀ y ∈ ball x (8 * ε⁻¹ * r x),
      ∑ i ∈ O.hI.toFinset, ‖fderiv ℝ (cfs15Weight_C15 ε r O.hI i) y‖ ≤ cw' / r x) :
    (cfs15StageOutput_withWeightBound_RGC O cw' h).I = O.I :=
  rfl

/-- **The native stage output on the actual stage cloud at the register's stage data** (D66-5):
for the register's stage choice `st` and a stage `j`, on every packet of the final family with
CFS14's inputs, every selection `sel` of original preimages over `S̃_j` and every family of planes
of the stage dimension with the (CS) test at quality `Γ_j` and radius `Σ_jρ ∘ sel`, there is a
`Cfs15StageOutput k_j K (Ξ_j(Γ_j)) (stageCwAt_V4C st j)` on `S_j ⊆ S̃_j` with these planes, built
from `earlyDataSharedV4_stageOutput_C15 st j` and re-weighted by `nb_cw_stage_selection_GAFS3` on
its own selection. -/
theorem ClosedStage.stageOutput_RGC {K : ℕ} (st : ClosedStage (earlyDataSharedV4 K)) (j : Fin 3)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {Kf : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (he : e ≤ 1 / 8)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (sel : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero j,
      cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero j) (sel x) =
        x)
    (plane : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (hdim : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero j,
      Module.finrank ℝ (plane x) = gafStageDim j)
    (hcloud : ∀ x ∈ gafCloud P.toLocalChartFamily P.zero j,
      hausdorffEDist (gafCloudEnlarged P.toLocalChartFamily P.zero j ∩
          ball x (st.Sig j * ρ (sel x) / st.Γ j))
        ((AffineSubspace.mk' x (plane x) :
            Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))) ∩
          ball x (st.Sig j * ρ (sel x) / st.Γ j)) ≤
            ENNReal.ofReal (st.Γ j * (st.Sig j * ρ (sel x)))) :
    Nonempty (Cfs15StageOutput (gafStageDim j) K ((earlyDataSharedV4 K).Ξ j (st.Γ j))
      (stageCwAt_V4C st j) (gafCloud P.toLocalChartFamily P.zero j)
      (gafCloudEnlarged P.toLocalChartFamily P.zero j) (fun x => st.Sig j * ρ (sel x)) plane) := by
  have hε : 0 < (earlyDataSharedV4 K).Ξ j (st.Γ j) := (st.stage_bounds_RGC j).1
  have hsg : 0 < st.Sig j := st.Sig_pos j
  have hmo := ((st.chain_numbers_RGC).1 j).2.2.1
  obtain ⟨hΓp, -, -, -, -, -, -, -, -, -, hint⟩ := st.chain_ranges_RGC j
  have hin := cfs14_stage_inputs_GAF2 P.toLocalChartPackets hΛ hΔ hμ hτ he hLΛ j sel hsel hε hsg
    hmo
  obtain ⟨rmin, R, hrmin, hlo, hhi⟩ := hin.2.2.1
  obtain ⟨cw₀, -, hout⟩ := earlyDataSharedV4_stageOutput_C15 st j
  have O₀ := (hout (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (gafCloud P.toLocalChartFamily P.zero j) (gafCloudEnlarged P.toLocalChartFamily P.zero j)
    hin.1 hin.2.1 (fun x => st.Sig j * ρ (sel x)) plane hdim rmin R hrmin hlo hhi hin.2.2.2
    hcloud).some
  have hspec := (Classical.choose_spec nb_cw_stage_selection_GAFS3 j (stageBufferAt_V4C st j)
    (st.one_le_stageBufferAt_V4C j)).2 X g hmetric ρ hρ Λ β Δ σs Kf σc μ b s b' s' ε γc βc Lmax τ γ
    δ εr e T V vs ζ Λz P hΛ hΔ hμ hτ he hLΛ sel hsel (st.Sig j) hsg hmo (st.Γ j) hΓp hint plane
    hdim hcloud O₀.I O₀.hI O₀.I_subset O₀.disjoint
  exact ⟨cfs15StageOutput_withWeightBound_RGC O₀ (stageCwAt_V4C st j)
    (fun x hx y hy => hspec.2 O₀.tube x hx y hy)⟩

end DifferentialGeometry.Geometry.Collapse
