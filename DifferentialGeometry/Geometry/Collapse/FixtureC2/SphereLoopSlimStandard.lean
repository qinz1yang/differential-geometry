import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopChainRows
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07FibreTypes

/-!
# SSTD on an actual slim centre of the sphere loop chain (S-FIXTURE-C2c, R2, G7)

`loopChain_slimStandard_FXC2`: on ANY chain `Ĉ : Gaf02ChainEJA` over the closed C2 family `PZ`
(in particular every chain of `loopSlimRows_FXC2`, whose register facts give `5 ≤ K` and
`Δ = 1200 > 0`), at every ACTUAL slim centre `j ∈ PZ.slim.centres` and every level
`|a| < 4·10⁵ Δ`, the whole adjusted level `{p ∈ Y_j | g_j(p) = a}` of the chain's adjusted axis
coordinate is the image of a smooth embedding of the standard `ClosureSphere` or `Torus`:
`gaf07_slim_level_standard_C14Z_GAFC`, which binds the consumer
`SlimCentre.gaf07_slim_fibre_standard_type_SSTD` to the homotopy the ACTUAL chain uses (FC34's
straight line `(1 − τ)η_j + τ g_j`, regular by the gauge estimates, compact trace), not a constant
homotopy. `loopChain_slimStandard_zero_FXC2` is the
level `a = 0` (the fibre through the centre).
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Bundle Manifold Filter GC.MetricGeometry
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete
attribute [local instance] loopMS3_FXC2
attribute [local instance] nezero_finrank_euclideanThree_LC87
attribute [local instance] instMetricNC14_FXC2 instChartedNC14_FXC2 instMetricCC14_FXC2

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "C14of" PZ => LocalChartPacketsC14D.toLocalChartPacketsC14
  (LocalChartPacketsC14Z.toLocalChartPacketsC14D PZ)

/-- **GAF07 `j = 3`, standard smooth type, at an actual slim centre of the C2 chain.** -/
theorem loopChain_slimStandard_FXC2 {ℓ : LoopLen_FXC2} {R : ℝ} {hR : 0 < R} {Lam : ℝ}
    {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3}
    (PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      oM)
    {Kj : ℕ} {Ξ' Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA (C14of PZ) Kj Ξ' Γ S eg c cw cadj) (hK : 5 ≤ K)
    {j : LoopC_FXC2 ℓ} (hj : j ∈ PZ.slim.centres) {a : ℝ} (ha : |a| < 4 * (10 ^ 5 * Δ)) :
    (∃ f : ClosureSphere.{0} → LoopC_FXC2 ℓ, IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC PZ.toLocalChartPackets
            ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ ∧
          C.toChain.gaf07SlimCoord_GAFC ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ p = a}) ∨
      (∃ f : Torus → LoopC_FXC2 ℓ, IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC PZ.toLocalChartPackets
            ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ ∧
          C.toChain.gaf07SlimCoord_GAFC ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ p = a}) :=
  gaf07_slim_level_standard_C14Z_GAFC C hK ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ ha

/-- The level `a = 0` (the fibre through the centre) for `Δ > 0`. -/
theorem loopChain_slimStandard_zero_FXC2 {ℓ : LoopLen_FXC2} {R : ℝ} {hR : 0 < R} {Lam : ℝ}
    {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ} {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    {oM : ManifoldOrientation 𝓘(ℝ, E3) (LoopC_FXC2 ℓ) 3}
    (PZ : LocalChartPacketsC14Z (LoopC_FXC2 ℓ) (loopMetric3_FXC2 ℓ) (loopMS3_hmetric_FXC2 ℓ)
      (fun _ => R) (fun _ => hR) Lam β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
      oM)
    {Kj : ℕ} {Ξ' Γ S eg c cw : Fin 3 → ℝ} {cadj : ℝ}
    (C : Gaf02ChainEJA (C14of PZ) Kj Ξ' Γ S eg c cw cadj) (hK : 5 ≤ K) (hΔ : 0 < Δ)
    {j : LoopC_FXC2 ℓ} (hj : j ∈ PZ.slim.centres) :
    (∃ f : ClosureSphere.{0} → LoopC_FXC2 ℓ, IsSmoothEmbedding (𝓡 2) 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC PZ.toLocalChartPackets
            ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ ∧
          C.toChain.gaf07SlimCoord_GAFC ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ p = 0}) ∨
      (∃ f : Torus → LoopC_FXC2 ℓ, IsSmoothEmbedding torusModel 𝓘(ℝ, E3) ∞ f ∧
        range f = {p | p ∈ gaf07SlimY_GAFC PZ.toLocalChartPackets
            ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ ∧
          C.toChain.gaf07SlimCoord_GAFC ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ p = 0}) :=
  loopChain_slimStandard_FXC2 PZ C hK hj (by rw [abs_zero]; positivity)

end DifferentialGeometry.Geometry.Collapse
